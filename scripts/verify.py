#!/usr/bin/env python3
"""Fresh, sequential kernel check for this standalone Lean certificate package."""
from __future__ import annotations

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FAILURE_MARKER = "Tactic " + chr(96) + "decide" + chr(96) + " proved that the proposition"
CONTROLS = [
    ("weighing", "invalid_alphabet.lean",
     "publishedMatrix i j = -1 ∨ publishedMatrix i j = 0 ∨ publishedMatrix i j = 1"),
    ("weighing", "broken_symmetry.lean",
     "publishedMatrix i j = publishedMatrix j i"),
    ("weighing", "symmetric_nonorthogonal.lean",
     "rowInner publishedMatrix i j = if i = j then 16 else 0"),
    ("sbox", "wrong_maximum.lean",
     "score G3 (plane 1 3 5) (plane 1 3 5) ≤ 25"),
    ("sbox", "damaged_difference_table.lean",
     "differenceCount G3 a b = damaged a b"),
    ("sbox", "missing_plane.lean",
     "plane 12 1 2"),
]
EXPECTED_AXIOM_TARGETS = {
    "weighing-positive": (
        "Weighing22.certificate",
        "Weighing22.exists_symmetric_weighing_22_16",
    ),
    "sbox-certificate": (
        "Sbox.planes_complete",
        "Sbox.G0_exact_plane_maximum",
        "Sbox.G3_exact_plane_maximum",
        "Sbox.same_single_difference_maximum",
        "Sbox.structured_difference_comparison",
    ),
}


def find_lean() -> str:
    configured = os.environ.get("LEAN_BIN")
    if configured:
        candidate = Path(configured).expanduser()
        if not candidate.is_file():
            raise RuntimeError("LEAN_BIN does not name an existing Lean executable")
        return str(candidate)
    found = shutil.which("lean")
    if not found:
        raise RuntimeError("Lean 4.34.1 was not found; set LEAN_BIN or add lean to PATH")
    return found


def clean_output(text: str) -> str:
    """Keep stored logs portable even if Lean emits the checkout's absolute path."""
    root_text = str(ROOT)
    return text.replace(root_text, ".").replace(root_text.replace("\\", "/"), ".")


def main() -> int:
    lean = find_lean()
    output_root = ROOT / ".verification-output"
    run_dir = output_root / (
        datetime.now(timezone.utc).strftime("run-%Y%m%dT%H%M%SZ-") + uuid.uuid4().hex[:8]
    )
    run_dir.mkdir(parents=True, exist_ok=False)
    (run_dir / "controls").mkdir()

    version_proc = subprocess.run(
        [lean, "--version"], cwd=ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=30,
    )
    version = clean_output(version_proc.stdout + version_proc.stderr).strip()
    if version_proc.returncode != 0 or "version 4.34.1" not in version:
        raise RuntimeError("Expected Lean 4.34.1; observed: " + version)

    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    env["LEAN_PATH"] = str(run_dir)
    commands: list[dict[str, object]] = []
    all_axioms: set[str] = set()
    logs_dir = run_dir / "logs"
    logs_dir.mkdir()

    def compile_step(label: str, source: str, target: str, timeout: int,
                     expected_failure: str | None = None,
                     expected_axiom_targets: tuple[str, ...] = ()) -> str:
        target_path = Path(target)
        before = time.perf_counter()
        args = [lean, "-j", "2", "-o", target, source]
        result = subprocess.run(
            args, cwd=ROOT, env=env, capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=timeout,
        )
        elapsed = time.perf_counter() - before
        output = clean_output(result.stdout + result.stderr)
        log_name = re.sub(r"[^A-Za-z0-9_.-]+", "_", label) + ".log"
        (logs_dir / log_name).write_text(output, encoding="utf-8")
        command_display = [
            "lean", "-j", "2", "-o", target_path.relative_to(ROOT).as_posix(), source
        ]
        item: dict[str, object] = {
            "label": label,
            "command": command_display,
            "returncode": result.returncode,
            "elapsed_seconds": round(elapsed, 3),
            "timeout_seconds": timeout,
        }
        commands.append(item)
        if expected_failure is None:
            if result.returncode != 0:
                raise RuntimeError(f"{label} failed; see logs/{log_name}")
            reported_targets = set(re.findall(
                r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)",
                output, flags=re.MULTILINE,
            ))
            missing_targets = set(expected_axiom_targets) - reported_targets
            if missing_targets:
                raise RuntimeError(
                    f"Missing required #print axioms reports {sorted(missing_targets)} "
                    f"in {label}; see logs/{log_name}"
                )
            axiom_groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
            for group in axiom_groups:
                all_axioms.update(x.strip() for x in group.split(",") if x.strip())
            if "sorryAx" in output:
                raise RuntimeError(f"{label} reports sorryAx; see logs/{log_name}")
            unexpected = all_axioms - ALLOWED_AXIOMS
            if unexpected:
                raise RuntimeError(f"Unexpected axioms {sorted(unexpected)} in {label}")
        else:
            if result.returncode == 0:
                raise RuntimeError(f"Damaged control unexpectedly compiled: {label}")
            if FAILURE_MARKER not in output or expected_failure not in output:
                raise RuntimeError(
                    f"{label} failed for an unexpected reason; see logs/{log_name}"
                )
        print(f"{label}: {'REJECTED AS EXPECTED' if expected_failure else 'PASS'} "
              f"({elapsed:.3f}s)", flush=True)
        return output

    started = time.perf_counter()
    try:
        compile_step(
            "weighing-positive", "src/weighing/Weighing22.lean",
            str(run_dir / "Weighing22.olean"), 180,
            expected_axiom_targets=EXPECTED_AXIOM_TARGETS["weighing-positive"],
        )
        compile_step(
            "sbox-data", "src/sbox/SboxData.lean",
            str(run_dir / "SboxData.olean"), 180,
        )
        compile_step(
            "sbox-certificate", "src/sbox/SboxCertificate.lean",
            str(run_dir / "SboxCertificate.olean"), 240,
            expected_axiom_targets=EXPECTED_AXIOM_TARGETS["sbox-certificate"],
        )
        for family, name, marker in CONTROLS:
            source = f"negative-controls/{family}/{name}"
            safe_name = f"{family}-{Path(name).stem}"
            compile_step(
                safe_name, source, str(run_dir / "controls" / f"{safe_name}.olean"),
                180, expected_failure=marker,
            )
        summary = {
            "status": "PASS",
            "lean_version": version,
            "workers": 2,
            "dependency": "Lean 4.34.1 bundled Std only",
            "positive_certificates": [
                "src/weighing/Weighing22.lean",
                "src/sbox/SboxData.lean",
                "src/sbox/SboxCertificate.lean",
            ],
            "axioms_observed": sorted(all_axioms),
            "axioms_allowed": sorted(ALLOWED_AXIOMS),
            "axiom_targets_required": {
                label: list(targets) for label, targets in EXPECTED_AXIOM_TARGETS.items()
            },
            "sorryAx_in_positive_builds": False,
            "negative_controls": [
                {"family": family, "file": name, "status": "rejected on intended false proposition"}
                for family, name, _marker in CONTROLS
            ],
            "commands": commands,
            "elapsed_seconds": round(time.perf_counter() - started, 3),
            "logs": "logs/ (relative to this run directory)",
        }
        (run_dir / "summary.json").write_text(
            json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        print(f"PASS: 3 positive modules, 6 intended negative rejections; logs: "
              f"{run_dir.relative_to(ROOT).as_posix()}", flush=True)
        return 0
    except BaseException as exc:
        failure = {
            "status": "FAIL",
            "lean_version": version,
            "error": str(exc),
            "commands_completed": commands,
            "elapsed_seconds": round(time.perf_counter() - started, 3),
            "logs": "logs/ (relative to this run directory)",
        }
        (run_dir / "summary.json").write_text(
            json.dumps(failure, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        print(f"FAIL: {exc}; logs: {run_dir.relative_to(ROOT).as_posix()}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
