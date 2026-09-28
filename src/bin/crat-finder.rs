#![feature(rustc_private)]

use std::path::PathBuf;

use clap::{Parser, ValueEnum};
use utils::compilation::run_compiler_on_path;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(long, help = "Verified declaration map for this exact source version")]
    pointer_declaration_map: Option<PathBuf>,
    #[arg(long, help = "Write the seeded or reconciled declaration map")]
    pointer_write_map: Option<PathBuf>,
    #[arg(
        long,
        conflicts_with = "pointer_declaration_map",
        help = "Stable suite/group/case identity for a new inventory"
    )]
    pointer_case_id: Option<String>,

    #[arg(long, help = "Show spans for unsafe operations")]
    unsafe_show_spans: bool,

    #[arg(help = "Finder to run")]
    finder: Finder,

    #[arg(help = "Path to the input directory containing Cargo.toml")]
    input: PathBuf,
}

#[derive(Clone, Debug, ValueEnum)]
#[clap(rename_all = "lower")]
enum Finder {
    Example,
    Macro,
    Mapper,
    Mir,
    Unsafe,
    Void,
    Pointers,
}

fn main() {
    let args = Args::parse();
    let lib_path = utils::find_lib_path(&args.input).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1);
    });
    let file = args.input.join(&lib_path);
    match args.finder {
        Finder::Pointers => {
            let result = (|| -> Result<_, Box<dyn std::error::Error>> {
                use utils::{
                    pointer_identity::{crate_hashes, relative_locations, seed_map},
                    pointer_inventory::DeclarationMap,
                };
                let map: Option<DeclarationMap> = args
                    .pointer_declaration_map
                    .as_ref()
                    .map(|path| -> Result<_, Box<dyn std::error::Error>> {
                        Ok(serde_json::from_slice(&std::fs::read(path)?)?)
                    })
                    .transpose()?;
                let hashes = crate_hashes(&args.input)?;
                let mut inventory = run_compiler_on_path(&file, |tcx| {
                    finders::pointer_finder::find_pointers(tcx, map.as_ref(), &hashes)
                })
                .map_err(|_| "pointer inventory compilation failed")??;
                relative_locations(&mut inventory, &args.input)?;
                if map.is_none() {
                    inventory.case_id = args.pointer_case_id.unwrap_or_else(|| {
                        args.input
                            .file_name()
                            .unwrap()
                            .to_string_lossy()
                            .into_owned()
                    });
                    for (index, d) in inventory.declarations.iter_mut().enumerate() {
                        d.declaration_id.0 = format!("{}:input:decl:{index}", inventory.case_id);
                    }
                }
                if let Some(path) = args.pointer_write_map {
                    std::fs::write(path, serde_json::to_vec_pretty(&seed_map(&inventory))?)?;
                }
                Ok(inventory)
            })();
            match result {
                Ok(inventory) => println!("{}", serde_json::to_string(&inventory).unwrap()),
                Err(error) => {
                    eprintln!("Pointer inventory: {error}");
                    std::process::exit(1);
                }
            }
        }
        Finder::Example => {
            run_compiler_on_path(&file, finders::example::run).unwrap();
        }
        Finder::Macro => {
            run_compiler_on_path(&file, finders::macro_finder::find_macros).unwrap();
        }
        Finder::Mapper => {
            run_compiler_on_path(&file, |tcx| {
                finders::mapper::run(&args.input, &lib_path, true, tcx)
            })
            .unwrap();
        }
        Finder::Mir => {
            run_compiler_on_path(&file, finders::mir::run).unwrap();
        }
        Finder::Unsafe => {
            run_compiler_on_path(&file, |tcx| {
                finders::unsafe_finder::find_unsafe(args.unsafe_show_spans, tcx)
            })
            .unwrap();
        }
        Finder::Void => {
            let findings = run_compiler_on_path(&file, finders::void_finder::find_void).unwrap();
            println!("{}", serde_json::to_string(&findings).unwrap());
        }
    }
}
