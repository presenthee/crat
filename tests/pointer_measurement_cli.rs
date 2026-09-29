#![feature(rustc_private)]
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

use serde_json::Value;
use utils::pointer_inventory::{DeclarationMap, Inventory};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = std::env::temp_dir().join(format!(
            "crat-pointer-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(root.join("tiny crate")).unwrap();
        fs::write(root.join("tiny crate/Cargo.toml"), "[package]\nname = 'tiny'\nversion = '0.1.0'\nedition = '2021'\n[lib]\npath = 'lib.rs'\n[dependencies]\n").unwrap();
        fs::write(
            root.join("tiny crate/lib.rs"),
            "pub unsafe fn f(p: *mut i32) { *p = 1; }\n",
        )
        .unwrap();
        Self(root)
    }

    fn input(&self) -> PathBuf {
        self.0.join("tiny crate")
    }

    fn finder(&self, extra: &[&str]) -> Output {
        command(env!("CARGO_BIN_EXE_crat-finder"))
            .arg("pointers")
            .arg(self.input())
            .args(extra)
            .output()
            .unwrap()
    }

    fn seed(&self) -> PathBuf {
        let path = self.0.join("origin.json");
        let out = self.finder(&[
            "--pointer-write-map",
            path.to_str().unwrap(),
            "--pointer-case-id",
            "Public-Tests/demo/tiny",
        ]);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let inventory: Inventory = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(inventory.case_id, "Public-Tests/demo/tiny");
        assert!(
            inventory
                .declarations
                .iter()
                .all(|d| !Path::new(&d.location.file).is_absolute())
        );
        path
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn command(binary: &str) -> Command {
    let mut cmd = Command::new(binary);
    cmd.env("DIR", env!("CARGO_MANIFEST_DIR"))
        .current_dir(env!("CARGO_MANIFEST_DIR"));
    cmd
}
#[test]
fn rejects_unpaired_measurement_flags() {
    let f = Fixture::new();
    for flag in ["--pointer-origin-map", "--pointer-measurement-dir"] {
        let out = command(env!("CARGO_BIN_EXE_crat"))
            .args(["--pass", "pointer", flag, "unused"])
            .arg(f.input())
            .output()
            .unwrap();
        assert!(!out.status.success());
        let error = String::from_utf8_lossy(&out.stderr);
        assert!(error.contains("required"), "{error}");
    }
}
#[test]
fn mapped_finder_rejects_stale_and_invalid_sources() {
    let f = Fixture::new();
    let map = f.seed();
    let out = f.finder(&["--pointer-declaration-map", map.to_str().unwrap()]);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let inventory: Inventory = serde_json::from_slice(&out.stdout).unwrap();
    let mapping: DeclarationMap = serde_json::from_slice(&fs::read(&map).unwrap()).unwrap();
    assert_eq!(
        inventory
            .declarations
            .iter()
            .map(|d| &d.declaration_id)
            .collect::<Vec<_>>(),
        mapping.entries.iter().map(|e| &e.id).collect::<Vec<_>>()
    );
    fs::write(f.input().join("lib.rs"), "pub fn changed() {}\n").unwrap();
    let out = f.finder(&["--pointer-declaration-map", map.to_str().unwrap()]);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("HashMismatch"));
    fs::write(
        f.input().join("lib.rs"),
        "pub fn invalid() { missing(); }\n",
    )
    .unwrap();
    assert!(!f.finder(&[]).status.success());
}
#[test]
fn all_profiles_publish_complete_artifacts_without_changing_output() {
    let f = Fixture::new();
    let origin = f.seed();
    let flags = [
        "struct_arrays",
        "struct_param_fields",
        "epoch_split",
        "aliasing",
        "array_local_provenance",
        "slice_cursor",
    ];
    for (name, bits) in [
        ("base", 0),
        ("full", 63),
        ("pass1", 1),
        ("pass2", 2),
        ("pass3", 4),
        ("pass4", 8),
        ("pass5", 16),
        ("cursor", 32),
    ] {
        let root = f.0.join(name);
        fs::create_dir(&root).unwrap();
        let config = root.join("config.toml");
        fs::write(
            &config,
            format!(
                "[pointer]\n{}",
                flags
                    .iter()
                    .enumerate()
                    .map(|(i, flag)| format!("enable_{flag} = {}\n", bits & (1 << i) != 0))
                    .collect::<String>()
            ),
        )
        .unwrap();
        let mut map: DeclarationMap = serde_json::from_slice(&fs::read(&origin).unwrap()).unwrap();
        map.profile = Some(name.into());
        let job_map = root.join("origin.json");
        fs::write(&job_map, serde_json::to_vec(&map).unwrap()).unwrap();
        let measurement = root.join("measurement");
        for observed in [false, true] {
            let output = root.join(if observed { "measured" } else { "ordinary" });
            fs::create_dir(&output).unwrap();
            let mut cmd = command(env!("CARGO_BIN_EXE_crat"));
            cmd.args(["--pass", "pointer", "--config"])
                .arg(&config)
                .arg("-o")
                .arg(&output);
            if observed {
                cmd.arg("--pointer-origin-map")
                    .arg(&job_map)
                    .arg("--pointer-measurement-dir")
                    .arg(&measurement);
            }
            let out = cmd.arg(f.input()).output().unwrap();
            assert!(
                out.status.success(),
                "{name}: {}",
                String::from_utf8_lossy(&out.stderr)
            );
        }
        assert_eq!(
            fs::read(root.join("ordinary/tiny crate/lib.rs")).unwrap(),
            fs::read(root.join("measured/tiny crate/lib.rs")).unwrap()
        );
        let done: Value =
            serde_json::from_slice(&fs::read(measurement.join("complete.json")).unwrap()).unwrap();
        assert_eq!(done["status"], "artifacts_complete");
        assert_eq!(done["schema_version"], 2);
        assert_eq!(done["counting_contract"], "raw-origins-v2");
        assert_eq!(done["availability"]["baseline_origins"]["status"], "complete");
        assert_eq!(done["availability"]["origin_categories"]["status"], "complete");
        assert_eq!(done["availability"]["final_raw_definitions"]["status"], "complete");
        assert_eq!(
            done["stages"].as_array().unwrap().len(),
            1 + (bits & 31u32).count_ones() as usize
        );
        let final_map = measurement.join("final-declaration-map.json");
        let out = command(env!("CARGO_BIN_EXE_crat-finder"))
            .arg("pointers")
            .arg(root.join("measured/tiny crate"))
            .arg("--pointer-declaration-map")
            .arg(final_map)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(serde_json::from_slice::<Inventory>(&out.stdout).is_ok());
    }
}

#[test]
fn failed_type_check_never_publishes_completion() {
    let f = Fixture::new();
    let path = f.seed();
    fs::write(f.input().join("lib.rs"), "pub fn broken() { missing(); }\n").unwrap();
    let mut map: DeclarationMap = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
    map.source_hashes = utils::pointer_identity::crate_hashes(&f.input()).unwrap();
    fs::write(&path, serde_json::to_vec(&map).unwrap()).unwrap();
    let measurement = f.0.join("measurement");
    let output = f.0.join("out");
    fs::create_dir(&output).unwrap();
    let result = command(env!("CARGO_BIN_EXE_crat"))
        .args(["--pass", "pointer", "-o"])
        .arg(&output)
        .arg("--pointer-origin-map")
        .arg(&path)
        .arg("--pointer-measurement-dir")
        .arg(&measurement)
        .arg(f.input())
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(!measurement.join("complete.json").exists());
}

#[test]
fn finder_seeds_case_and_observation_keys_together() {
    let f = Fixture::new();
    fs::write(f.input().join("lib.rs"), "pub fn f(p: std::ptr::NonNull<u8>) {}\n").unwrap();
    let map = f.0.join("partial-map.json");
    let out = f.finder(&["--pointer-case-id", "Public-Tests/fixture/partial", "--pointer-write-map", map.to_str().unwrap()]);
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let inventory: Inventory = serde_json::from_slice(&out.stdout).unwrap();
    let map: DeclarationMap = serde_json::from_slice(&fs::read(map).unwrap()).unwrap();
    let ids: std::collections::BTreeSet<_> = inventory.declarations.iter().map(|d| d.declaration_id.clone()).collect();
    assert_eq!(ids, inventory.observations.keys().cloned().collect());
    assert_eq!(ids, map.entries.iter().map(|e| e.id.clone()).collect());
    assert!(ids.iter().all(|id| id.0.starts_with("Public-Tests/fixture/partial:")));
    assert!(inventory.structural_errors.is_empty());
    assert!(inventory.observations.values().any(|o| !o.diagnostics.is_empty()));
}

#[test]
fn partial_inventory_can_publish_valid_artifacts() {
    let f=Fixture::new();
    fs::write(f.input().join("lib.rs"),"pub fn f(p: std::ptr::NonNull<u8>) {}\n").unwrap();
    let map=f.seed();
    let config=f.0.join("config.toml");
    fs::write(&config,"[pointer]\nenable_struct_arrays=false\nenable_struct_param_fields=false\nenable_epoch_split=false\nenable_aliasing=false\nenable_array_local_provenance=false\nenable_slice_cursor=false\n").unwrap();
    let measurement=f.0.join("measurement");let output=f.0.join("out");fs::create_dir(&output).unwrap();
    let out=command(env!("CARGO_BIN_EXE_crat")).args(["--pass","pointer","--config"]).arg(config)
        .arg("-o").arg(output).arg("--pointer-origin-map").arg(map)
        .arg("--pointer-measurement-dir").arg(&measurement).arg(f.input()).output().unwrap();
    assert!(out.status.success(),"{}",String::from_utf8_lossy(&out.stderr));
    let done: Value=serde_json::from_slice(&fs::read(measurement.join("complete.json")).unwrap()).unwrap();
    assert_eq!(done["status"],"artifacts_complete");
    assert_eq!(done["availability"]["baseline_origins"]["status"],"unavailable");
    assert_eq!(done["availability"]["final_raw_definitions"]["status"],"unavailable");
    assert_eq!(done["availability"]["baseline_origins"]["reasons"][0]["code"],"baseline_raw_presence_unknown");
}
