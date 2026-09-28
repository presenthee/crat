use std::{
    fs,
    path::{Path, PathBuf},
};

use pointer_replacer::{
    GatedPrepassResult,
    measurement::{Emission, Measurement},
};
use serde::Serialize;
use serde_json::json;
use utils::{
    compilation::run_compiler_on_path,
    pointer_identity::{
        MeasurementError, crate_hashes, crate_source_paths, hash_sources, reconcile_inventory,
        relative_locations, validate_map,
    },
    pointer_inventory::{DeclarationMap, Inventory},
    pointer_lineage::Ledger,
};

fn invalid(message: impl Into<String>) -> MeasurementError {
    MeasurementError::InvalidEvent(message.into())
}

pub struct Session {
    pub measurement: Measurement,
    dir: PathBuf,
    root: PathBuf,
    lib: PathBuf,
    ledger: Ledger,
    artifacts: Vec<PathBuf>,
}
impl Session {
    pub fn new(origin_map_path: &Path, measurement_dir: &Path) -> Result<Self, MeasurementError> {
        let map: DeclarationMap = serde_json::from_slice(&fs::read(origin_map_path)?)
            .map_err(|e| invalid(e.to_string()))?;
        validate_map(&map)?;
        if let Some(parent) = measurement_dir.parent() {
            fs::create_dir_all(parent)?;
        }
        // Existing attempts must never inherit a stale success marker.
        fs::create_dir(measurement_dir)?;
        Ok(Self {
            measurement: Measurement::new(map.clone()),
            dir: measurement_dir.canonicalize()?,
            root: PathBuf::new(),
            lib: PathBuf::new(),
            ledger: Ledger::new(map),
            artifacts: Vec::new(),
        })
    }

    fn write<T: Serialize>(&mut self, path: &str, value: &T) -> Result<(), MeasurementError> {
        let path = PathBuf::from(path);
        let bytes = serde_json::to_vec_pretty(value).map_err(|e| invalid(e.to_string()))?;
        fs::write(self.dir.join(&path), bytes)?;
        self.artifacts.push(path);
        Ok(())
    }

    pub fn bind_input(&mut self, root: &Path, lib: &Path) -> Result<(), MeasurementError> {
        self.root = root.canonicalize()?;
        if self.dir.starts_with(&self.root) || self.root.starts_with(&self.dir) {
            return Err(invalid(
                "measurement and output crate directories must be disjoint",
            ));
        }
        self.lib = lib.to_owned();
        let hashes = crate_hashes(&self.root)?;
        let map = self.ledger.current_map().clone();
        if map.source_hashes != hashes {
            return Err(MeasurementError::HashMismatch("input origin map".into()));
        }
        let mut inventory = run_compiler_on_path(&self.root.join(lib), |tcx| {
            finders::pointer_finder::find_pointers(tcx, Some(&map), &hashes)
        })
        .map_err(|_| invalid("input type-check failed"))??;
        relative_locations(&mut inventory, &self.root)?;
        self.write("input-inventory.json", &inventory)?;
        self.write("input-declaration-map.json", &map)
    }

    pub fn record_pending(&mut self) -> Result<(), MeasurementError> {
        for emission in self.measurement.take_emissions()? {
            self.record_stage(emission)?;
        }
        Ok(())
    }

    pub fn record_stage(&mut self, mut emission: Emission) -> Result<(), MeasurementError> {
        let stage = emission.delta.map.stage.0.clone();
        if !stage
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || c == b'_')
        {
            return Err(invalid("invalid stage path"));
        }
        let prefix = format!("stages/{stage}");
        let snapshot = self.dir.join(&prefix).join("crate");
        fs::create_dir_all(&snapshot)?;
        for path in crate_source_paths(&self.root)? {
            if let Some(parent) = snapshot.join(&path).parent() {
                fs::create_dir_all(parent)?;
            }
            fs::copy(self.root.join(&path), snapshot.join(&path))?;
        }
        fs::write(snapshot.join(&self.lib), &emission.source)?;
        emission.delta.map.source_hashes = crate_hashes(&snapshot)?;
        let map = &emission.delta.map;
        let mut inventory = run_compiler_on_path(&snapshot.join(&self.lib), |tcx| {
            finders::pointer_finder::find_pointers(tcx, Some(map), &map.source_hashes)
        })
        .map_err(|_| invalid(format!("{stage} type-check failed")))??;
        relative_locations(&mut inventory, &snapshot)?;
        self.ledger.commit(emission.delta.clone())?;
        for path in crate_source_paths(&snapshot)? {
            self.artifacts
                .push(PathBuf::from(&prefix).join("crate").join(path));
        }
        self.write(&format!("{prefix}/inventory.json"), &inventory)?;
        self.write(
            &format!("{prefix}/declaration-map.json"),
            &emission.delta.map,
        )?;
        self.write(&format!("{prefix}/delta.json"), &emission.delta)
    }

    pub fn record_gate(&mut self, gate: &GatedPrepassResult) -> Result<(), MeasurementError> {
        let mut decisions: Vec<_> = gate.decisions.iter().map(|d| json!({
            "candidate": format!("{:?}", d.candidate), "decision": format!("{:?}", d.decision),
        })).collect();
        decisions.sort_by_key(|d| d["candidate"].as_str().unwrap().to_owned());
        self.write(
            "gate.json",
            &json!({"schema_version":1,
                "accepted_epochs":gate.accepted_epochs, "rejected_epochs":gate.rejected_epochs,
                "accepted_arrays":gate.accepted_arrays, "rejected_arrays":gate.rejected_arrays,
                "combined_trial_failed":gate.combined_trial_failed,
                "trial_seconds":gate.trial_time.as_secs_f64(),
                "phases":gate.phases.iter().map(|p| format!("{p:?}")).collect::<Vec<_>>(),
                "decisions":decisions,
            }),
        )
    }

    pub fn collect_final(&self) -> Result<Inventory, MeasurementError> {
        let hashes = crate_hashes(&self.root)?;
        let map = self.ledger.current_map();
        let mut inventory = run_compiler_on_path(&self.root.join(&self.lib), |tcx| {
            finders::pointer_finder::find_pointers(tcx, Some(map), &hashes)
        })
        .map_err(|_| invalid("final type-check failed"))??;
        relative_locations(&mut inventory, &self.root)?;
        Ok(inventory)
    }

    pub fn finish(&mut self, final_inventory: Inventory) -> Result<(), MeasurementError> {
        if self.ledger.stages().is_empty() || self.ledger.current_map().stage.0 != "borrow" {
            return Err(invalid("missing final borrow stage"));
        }
        let map = self.ledger.current_map().clone();
        reconcile_inventory(final_inventory.clone(), &map)?;
        if final_inventory.source_hashes != map.source_hashes {
            return Err(MeasurementError::HashMismatch("final output".into()));
        }
        self.write("final-inventory.json", &final_inventory)?;
        self.write("final-declaration-map.json", &map)?;
        let mut lines = String::new();
        for stage in self.ledger.stages() {
            for event in &stage.events {
                lines.push_str(&serde_json::to_string(event).map_err(|e| invalid(e.to_string()))?);
                lines.push('\n');
            }
        }
        fs::write(self.dir.join("lineage.jsonl"), lines)?;
        self.artifacts.push("lineage.jsonl".into());
        self.artifacts.sort();
        self.artifacts.dedup();
        let hashes = hash_sources(&self.dir, &self.artifacts)?;
        let completion = json!({"schema_version":1,"status":"success", "case_id":map.case_id,
            "profile":map.profile,"stages":self.ledger.stages().iter().map(|s| &s.map.stage).collect::<Vec<_>>(),
            "artifact_hashes":hashes});
        fs::write(
            self.dir.join("complete.tmp"),
            serde_json::to_vec_pretty(&completion).map_err(|e| invalid(e.to_string()))?,
        )?;
        fs::rename(
            self.dir.join("complete.tmp"),
            self.dir.join("complete.json"),
        )?;
        Ok(())
    }
}

pub fn required<T>(result: Result<T, MeasurementError>) -> T {
    result.unwrap_or_else(|error| {
        eprintln!("Pointer measurement: {error}");
        std::process::exit(1);
    })
}
