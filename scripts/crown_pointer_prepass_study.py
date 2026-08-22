#!/usr/bin/env python3

import argparse
import csv
import os
import re
import subprocess
from collections import Counter
from pathlib import Path


BENCHMARKS = [
    "avl",
    "bst",
    "genann-1.0.0",
    "json.h",
    "libzahl-1.0",
    "quadtree-0.1.0",
    "tulipindicators",
    "binn-3.0",
    "buffer-0.4.0",
    "heman",
    "libcsv",
    "lil",
    "rgba",
    "urlparser",
    "brotli-1.0.9",
    "bzip2",
    "ht",
    "libtree-3.1.1",
    "lodepng",
    "robotfindskitten",
]

STAGES = [
    "input",
    "struct_arrays",
    "struct_param_fields",
    "epoch_split",
    "aliasing",
    "array_local_provenance",
    "replace_local_borrows",
]

PREPASSES = STAGES[1:-1]
RAW_COUNT_RE = re.compile(r"POINTER_RAW_POINTERS stage=(\S+) count=(\d+)")


def normalize_feature(name: str) -> str:
    if name == "DerefOfRawPointer":
        return "deref"
    if name == "UseOfMutableStatic":
        return "static"
    if name == "AccessToUnionField":
        return "union"
    if name == "CallToUnsafeFunction(None)":
        return "fnptr"
    if name == "transmute":
        return "transmute"
    if name in {"offset", "offset_from"}:
        return "offset"
    if name in {"calloc", "free", "malloc", "realloc"}:
        return "alloc"
    if name in {
        "as_mut",
        "as_ref",
        "from_ptr",
        "from_raw_parts",
        "from_raw_parts_mut",
    }:
        return "std"
    return "lib"


def run(command: list[str], log_base: Path, env: dict[str, str]) -> str:
    result = subprocess.run(command, capture_output=True, text=True, env=env)
    log_base.parent.mkdir(parents=True, exist_ok=True)
    Path(f"{log_base}.stdout.log").write_text(result.stdout, encoding="utf-8")
    Path(f"{log_base}.stderr.log").write_text(result.stderr, encoding="utf-8")
    if result.returncode != 0:
        raise subprocess.CalledProcessError(result.returncode, command)
    return result.stdout


def transform_base(
    crat: Path, source: Path, output: Path, log: Path, env: dict[str, str]
) -> None:
    command = [
        str(crat),
        "-o",
        str(output),
        "--extern-ignore-return-type",
        "--extern-ignore-param-type",
        "--pass",
        "expand,extern,preprocess",
        str(source),
    ]
    run(command, log, env)


def transform_pointer(
    crat: Path,
    source: Path,
    output: Path,
    log: Path,
    env: dict[str, str],
    with_prepasses: bool,
) -> dict[str, int]:
    command = [
        str(crat),
        "-o",
        str(output),
        "--pointer-report-raw-pointers",
        "--unsafe-remove-unused",
        "--unsafe-remove-no-mangle",
        "--unsafe-replace-pub",
        "--unsafe-remove-extern-c",
        "--unexpand-use-print",
        "--pass",
        "pointer,simpl,interface,unsafe,unexpand,split,bin",
        str(source),
    ]
    if not with_prepasses:
        command.insert(3, "--pointer-skip-prepasses")
    stdout = run(command, log, env)
    return {stage: int(count) for stage, count in RAW_COUNT_RE.findall(stdout)}


def measure(
    finder: Path, source: Path, log_dir: Path, env: dict[str, str]
) -> tuple[int, Counter[str]]:
    raw_stdout = run(
        [str(finder), "raw-pointer", str(source)], log_dir / "raw-pointer", env
    )
    unsafe_stdout = run([str(finder), "unsafe", str(source)], log_dir / "unsafe", env)
    return int(raw_stdout.strip()), Counter(unsafe_stdout.splitlines())


def write_csv(path: Path, header: list[str], rows: list[list[object]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as file:
        writer = csv.writer(file)
        writer.writerow(header)
        writer.writerows(rows)


def write_reports(
    output: Path,
    stage_counts: dict[str, dict[str, int]],
    without_stage_counts: dict[str, dict[str, int]],
    remaining: dict[str, dict[str, int]],
    unsafe: dict[str, dict[str, Counter[str]]],
) -> None:
    stage_rows = []
    for benchmark in BENCHMARKS:
        counts = stage_counts[benchmark]
        eliminated = [counts[STAGES[index - 1]] - counts[stage] for index, stage in enumerate(STAGES[1:], 1)]
        stage_rows.append(
            [benchmark, *(counts[stage] for stage in STAGES), *eliminated]
        )
    write_csv(
        output / "subpass_raw_pointers.csv",
        [
            "benchmark",
            *STAGES,
            *(f"eliminated_by_{stage}" for stage in STAGES[1:]),
        ],
        stage_rows,
    )

    remaining_rows = [
        [
            benchmark,
            remaining[benchmark]["with"],
            remaining[benchmark]["without"],
            remaining[benchmark]["without"] - remaining[benchmark]["with"],
        ]
        for benchmark in BENCHMARKS
    ]
    write_csv(
        output / "remaining_raw_pointers.csv",
        ["benchmark", "with_prepasses", "without_prepasses", "additional_without"],
        remaining_rows,
    )

    unsafe_rows = []
    normalized_rows = []
    for benchmark in BENCHMARKS:
        for mode in ["with", "without"]:
            for feature, count in sorted(unsafe[benchmark][mode].items()):
                unsafe_rows.append([benchmark, mode, feature, count])
            normalized = Counter()
            for feature, count in unsafe[benchmark][mode].items():
                normalized[normalize_feature(feature)] += count
            for feature, count in sorted(normalized.items()):
                normalized_rows.append([benchmark, mode, feature, count])
    write_csv(
        output / "unsafe_features.csv",
        ["benchmark", "mode", "feature", "count"],
        unsafe_rows,
    )
    write_csv(
        output / "unsafe_features_normalized.csv",
        ["benchmark", "mode", "feature", "count"],
        normalized_rows,
    )
    write_csv(
        output / "remaining_unsafe_features.csv",
        ["benchmark", "with_prepasses", "without_prepasses", "additional_without"],
        [
            [
                benchmark,
                sum(unsafe[benchmark]["with"].values()),
                sum(unsafe[benchmark]["without"].values()),
                sum(unsafe[benchmark]["without"].values())
                - sum(unsafe[benchmark]["with"].values()),
            ]
            for benchmark in BENCHMARKS
        ],
    )

    stage_totals = {stage: sum(stage_counts[b][stage] for b in BENCHMARKS) for stage in STAGES}
    raw_with = sum(remaining[b]["with"] for b in BENCHMARKS)
    raw_without = sum(remaining[b]["without"] for b in BENCHMARKS)
    unsafe_totals = {mode: Counter() for mode in ["with", "without"]}
    for benchmark in BENCHMARKS:
        for mode in unsafe_totals:
            for feature, count in unsafe[benchmark][mode].items():
                unsafe_totals[mode][normalize_feature(feature)] += count

    lines = [
        "# CROWN pointer pre-pass study",
        "",
        "Raw pointers are expanded-AST `TyKind::Ptr` occurrences. Unsafe features are counted with `crat-finder unsafe` and normalized exactly as in `crat-workspace/scripts/post_summarize_unsafe.py`.",
        "",
        "## Aggregate remaining raw pointers",
        "",
        "| with five pre-passes | without five pre-passes | additional without |",
        "| ---: | ---: | ---: |",
        f"| {raw_with} | {raw_without} | {raw_without - raw_with} |",
        "",
        "## Aggregate raw pointers at sub-pass boundaries",
        "",
        "| sub-pass | before | after | eliminated (net) |",
        "| --- | ---: | ---: | ---: |",
    ]
    for index, stage in enumerate(PREPASSES, 1):
        before = stage_totals[STAGES[index - 1]]
        after = stage_totals[stage]
        lines.append(f"| {stage} | {before} | {after} | {before - after} |")

    without_input = sum(without_stage_counts[b]["input"] for b in BENCHMARKS)
    without_after = sum(
        without_stage_counts[b]["replace_local_borrows"] for b in BENCHMARKS
    )
    lines.extend(
        [
            "",
            "Negative elimination means that the preparatory pass introduced raw-pointer type occurrences.",
            "",
            "## Main replacement context",
            "",
            "| configuration | input to `replace_local_borrows` | after replacement | eliminated by replacement |",
            "| --- | ---: | ---: | ---: |",
            f"| with five pre-passes | {stage_totals['array_local_provenance']} | {stage_totals['replace_local_borrows']} | {stage_totals['array_local_provenance'] - stage_totals['replace_local_borrows']} |",
            f"| without five pre-passes | {without_input} | {without_after} | {without_input - without_after} |",
        ]
    )

    lines.extend(
        [
            "",
            "## Aggregate remaining unsafe features",
            "",
            "| feature | with five pre-passes | without five pre-passes | additional without |",
            "| --- | ---: | ---: | ---: |",
        ]
    )
    features = sorted(unsafe_totals["with"] | unsafe_totals["without"])
    for feature in features:
        with_count = unsafe_totals["with"][feature]
        without_count = unsafe_totals["without"][feature]
        lines.append(
            f"| {feature} | {with_count} | {without_count} | {without_count - with_count} |"
        )
    with_unsafe_total = sum(unsafe_totals["with"].values())
    without_unsafe_total = sum(unsafe_totals["without"].values())
    lines.append(
        f"| **total** | **{with_unsafe_total}** | **{without_unsafe_total}** | **{without_unsafe_total - with_unsafe_total}** |"
    )

    lines.extend(
        [
            "",
            "## Remaining raw pointers by benchmark",
            "",
            "| benchmark | with | without | additional without |",
            "| --- | ---: | ---: | ---: |",
        ]
    )
    for benchmark in BENCHMARKS:
        with_count = remaining[benchmark]["with"]
        without_count = remaining[benchmark]["without"]
        lines.append(
            f"| {benchmark} | {with_count} | {without_count} | {without_count - with_count} |"
        )
    (output / "summary.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output", type=Path, default=Path("benchmarks/crown-pointer-prepass-study")
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parent.parent
    output = args.output.resolve()
    crat = root / "target/release/crat"
    finder = root / "target/release/crat-finder"
    for directory in [output / "base", output / "with", output / "without"]:
        directory.mkdir(parents=True, exist_ok=True)

    env = os.environ.copy()
    sysroot = subprocess.check_output(["rustc", "--print", "sysroot"], text=True).strip()
    old_ld_path = env.get("LD_LIBRARY_PATH")
    env["LD_LIBRARY_PATH"] = f"{sysroot}/lib" + (f":{old_ld_path}" if old_ld_path else "")

    stage_counts: dict[str, dict[str, int]] = {}
    without_stage_counts: dict[str, dict[str, int]] = {}
    remaining: dict[str, dict[str, int]] = {}
    unsafe: dict[str, dict[str, Counter[str]]] = {}
    for index, benchmark in enumerate(BENCHMARKS, 1):
        print(f"[{index}/{len(BENCHMARKS)}] {benchmark}", flush=True)
        source = root / "benchmarks/rs" / benchmark
        transform_base(
            crat,
            source,
            output / "base",
            output / "logs/base" / benchmark,
            env,
        )
        base = output / "base" / benchmark
        stage_counts[benchmark] = transform_pointer(
            crat,
            base,
            output / "with",
            output / "logs/with" / benchmark,
            env,
            with_prepasses=True,
        )
        without_stage_counts[benchmark] = transform_pointer(
            crat,
            base,
            output / "without",
            output / "logs/without" / benchmark,
            env,
            with_prepasses=False,
        )

        remaining[benchmark] = {}
        unsafe[benchmark] = {}
        for mode in ["with", "without"]:
            raw_count, unsafe_counts = measure(
                finder,
                output / mode / benchmark,
                output / "logs/measure" / mode / benchmark,
                env,
            )
            remaining[benchmark][mode] = raw_count
            unsafe[benchmark][mode] = unsafe_counts

    write_reports(output, stage_counts, without_stage_counts, remaining, unsafe)
    print(output / "summary.md")


if __name__ == "__main__":
    main()
