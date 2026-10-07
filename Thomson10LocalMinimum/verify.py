#!/usr/bin/env python3
"""Verify the pinned Thomson10 local-minimum source package, sequentially."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent
EXPECTED_LEAN_TOOLCHAIN = "leanprover/lean4:v4.34.1"
EXPECTED_MATHLIB_REVISION = "d13f23b723b8a846827a245b89c10fc7d3f11612"
EXPECTED_LOCAL_MODULE_COUNT = 183
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_EXTRA_FILES = {
    "src/Audit.lean",
    "src/WitnessControls.lean",
    "negative-controls/False.lean",
    "negative-controls/DamagedMatrixWitness.lean",
}
TOTAL_TIMEOUT_SECONDS = int(os.environ.get("THOMSON_VERIFY_TOTAL_SECONDS", "7200"))
if not 60 <= TOTAL_TIMEOUT_SECONDS <= 7200:
    raise ValueError("THOMSON_VERIFY_TOTAL_SECONDS must be between 60 and 7200")
COMMAND_TIMEOUT_SECONDS = 600


class VerificationError(RuntimeError):
    pass


def relpath(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def resolve_tool(variable: str, default: str) -> str:
    requested = os.environ.get(variable, default)
    found = shutil.which(requested)
    if found is None:
        candidate = Path(requested).expanduser()
        if candidate.is_file():
            found = str(candidate.resolve())
    if found is None:
        raise VerificationError(f"Cannot find {variable} executable ({requested})")
    return str(Path(found).resolve())


def text_or_empty(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def run_logged(
    args: list[str],
    label: str,
    env: dict[str, str],
    deadline: float,
    run_dir: Path,
    records: list[dict[str, Any]],
) -> subprocess.CompletedProcess[str]:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise VerificationError(f"The cumulative {TOTAL_TIMEOUT_SECONDS}-second verification deadline expired")
    timeout = min(COMMAND_TIMEOUT_SECONDS, remaining)
    log_path = run_dir / "logs" / f"{len(records) + 1:03d}-{label}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    timed_out = False
    try:
        result = subprocess.run(
            args,
            cwd=ROOT,
            env=env,
            text=True,
            encoding="utf-8",
            errors="replace",
            capture_output=True,
            check=False,
            timeout=timeout,
        )
        stdout = result.stdout or ""
        stderr = result.stderr or ""
        returncode: int | None = result.returncode
    except subprocess.TimeoutExpired as exc:
        stdout = text_or_empty(exc.stdout)
        stderr = text_or_empty(exc.stderr)
        returncode = None
        timed_out = True
    elapsed = time.monotonic() - started
    with log_path.open("w", encoding="utf-8", errors="replace", newline="\n") as log:
        log.write("command: " + json.dumps(args, ensure_ascii=False) + "\n")
        log.write(f"working_directory: {ROOT}\n")
        log.write(f"timeout_seconds: {timeout:.1f}\n")
        log.write(f"elapsed_seconds: {elapsed:.3f}\n")
        log.write(f"return_code: {returncode}\n")
        log.write("--- stdout ---\n")
        log.write(stdout)
        log.write("\n--- stderr ---\n")
        log.write(stderr)
        if not stderr.endswith("\n"):
            log.write("\n")
    records.append(
        {
            "name": label,
            "log": relpath(log_path),
            "exit_code": returncode,
            "elapsed_seconds": round(elapsed, 3),
            "timed_out": timed_out,
        }
    )
    if timed_out:
        raise VerificationError(f"Command timed out: {label}")
    return subprocess.CompletedProcess(args, returncode or 0, stdout, stderr)


def read_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"Cannot read {label}") from exc
    if not isinstance(value, dict):
        raise VerificationError(f"Malformed {label}")
    return value


def imported_modules(source: str) -> list[str]:
    imports: list[str] = []
    for line in source.splitlines():
        stripped = line.strip()
        if not stripped.startswith("import "):
            continue
        declaration = stripped[len("import ") :].split("--", 1)[0]
        imports.extend(token for token in declaration.split() if token)
    return imports


def check_hashes(manifest: dict[str, Any]) -> list[str]:
    modules = manifest.get("sources")
    order = manifest.get("topological_order_dependency_first")
    if manifest.get("local_module_count") != EXPECTED_LOCAL_MODULE_COUNT or not isinstance(modules, list):
        raise VerificationError(f"The manifest must describe exactly {EXPECTED_LOCAL_MODULE_COUNT} local modules")
    if not isinstance(order, list) or len(order) != EXPECTED_LOCAL_MODULE_COUNT:
        raise VerificationError("The dependency-first module order is missing or incomplete")
    module_by_name: dict[str, dict[str, Any]] = {}
    for item in modules:
        if not isinstance(item, dict) or not isinstance(item.get("module"), str):
            raise VerificationError("Malformed local source manifest entry")
        name = item["module"]
        if name in module_by_name:
            raise VerificationError(f"Duplicate module in source manifest: {name}")
        module_by_name[name] = item
    if len(module_by_name) != EXPECTED_LOCAL_MODULE_COUNT or len(set(order)) != EXPECTED_LOCAL_MODULE_COUNT or set(order) != set(module_by_name):
        raise VerificationError("The local module list and topological order do not match")
    if order[-1] != manifest.get("root_module"):
        raise VerificationError("The root module is not last in the dependency-first order")

    total_bytes = 0
    source_texts: dict[str, str] = {}
    for name in order:
        item = module_by_name[name]
        expected_path = f"src/{name}.lean"
        if item.get("path") != expected_path:
            raise VerificationError(f"Unexpected source path for {name}")
        path = ROOT / expected_path
        try:
            data = path.read_bytes()
        except OSError as exc:
            raise VerificationError(f"Missing source file: {expected_path}") from exc
        if len(data) != item.get("size_bytes") or hashlib.sha256(data).hexdigest() != item.get("sha256"):
            raise VerificationError(f"Source hash mismatch: {expected_path}")
        total_bytes += len(data)
        source = data.decode("utf-8")
        source_texts[name] = source
        if re.search(r"(?m)^\s*(?:private\s+)?axiom\b|\bsorry\b|\bnative_decide\b", source):
            raise VerificationError(f"Untrusted declaration or tactic token in {expected_path}")
    if total_bytes != manifest.get("total_source_bytes"):
        raise VerificationError("Aggregate local source size does not match the manifest")

    local_names = set(module_by_name)
    module_position = {name: index for index, name in enumerate(order)}
    actual_mathlib_imports: set[str] = set()
    actual_standard_imports: set[str] = set()
    for name, source in source_texts.items():
        for imported in imported_modules(source):
            if imported in local_names:
                if module_position[imported] >= module_position[name]:
                    raise VerificationError(f"Dependency order is invalid: {name} imports {imported}")
                continue
            if imported == "Mathlib" or imported.startswith("Mathlib."):
                actual_mathlib_imports.add(imported)
            elif imported in {"Std", "Lean", "Init"} or imported.startswith(("Std.", "Lean.", "Init.")):
                actual_standard_imports.add(imported)
            else:
                raise VerificationError(f"Unresolved bare import {imported} in src/{name}.lean")
    if actual_mathlib_imports != set(manifest.get("mathlib_imports", [])):
        raise VerificationError("The Mathlib import inventory does not match local source imports")
    if actual_standard_imports != set(manifest.get("standard_imports", [])):
        raise VerificationError("The Lean/Std import inventory does not match local source imports")
    if manifest.get("other_external_imports") != []:
        raise VerificationError("All non-Lean and non-Mathlib imports must be included in the local closure")

    extras = manifest.get("extra_files")
    if not isinstance(extras, list):
        raise VerificationError("The manifest has no extra_files hash inventory")
    extra_paths: set[str] = set()
    for item in extras:
        if not isinstance(item, dict) or not isinstance(item.get("path"), str):
            raise VerificationError("Malformed extra_files manifest entry")
        path_text = item["path"]
        if path_text in extra_paths or path_text in {s["path"] for s in modules}:
            raise VerificationError(f"Duplicate extra source inventory entry: {path_text}")
        extra_paths.add(path_text)
        path = ROOT / path_text
        try:
            data = path.read_bytes()
        except OSError as exc:
            raise VerificationError(f"Missing package control file: {path_text}") from exc
        if len(data) != item.get("size_bytes") or hashlib.sha256(data).hexdigest() != item.get("sha256"):
            raise VerificationError(f"Package control hash mismatch: {path_text}")
        if re.search(r"(?m)^\s*(?:private\s+)?axiom\b|\bsorry\b|\bnative_decide\b", data.decode("utf-8")):
            raise VerificationError(f"Untrusted declaration or tactic token in {path_text}")
    if extra_paths != EXPECTED_EXTRA_FILES:
        raise VerificationError("extra_files must hash Audit, WitnessControls, and both negative controls")
    return order


def check_pins(manifest: dict[str, Any]) -> tuple[list[dict[str, str]], str]:
    if manifest.get("lean_toolchain") != EXPECTED_LEAN_TOOLCHAIN:
        raise VerificationError("Source manifest Lean toolchain pin is not 4.34.1")
    if manifest.get("mathlib_commit") != EXPECTED_MATHLIB_REVISION:
        raise VerificationError("Source manifest Mathlib revision does not match the required pin")
    if (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != EXPECTED_LEAN_TOOLCHAIN:
        raise VerificationError("lean-toolchain does not match the required Lean pin")
    lakefile = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    if EXPECTED_MATHLIB_REVISION not in lakefile or "@[default_target]" not in lakefile:
        raise VerificationError("lakefile must pin Mathlib and declare a default target")
    if manifest.get("lake_manifest") != "lake-manifest.json":
        raise VerificationError("source-manifest.json must point to lake-manifest.json")

    lake_manifest = read_json(ROOT / "lake-manifest.json", "lake-manifest.json")
    packages = lake_manifest.get("packages")
    if not isinstance(packages, list):
        raise VerificationError("lake-manifest.json has no package revision list")
    revisions: list[dict[str, str]] = []
    found_mathlib = False
    for package in packages:
        if not isinstance(package, dict):
            raise VerificationError("Malformed lake-manifest package entry")
        name = str(package.get("name", "unknown"))
        kind = str(package.get("type", "unknown"))
        if kind == "git":
            revision = package.get("rev")
            if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-fA-F]{40}", revision):
                raise VerificationError(f"Git dependency has no full revision pin: {name}")
            revisions.append({"name": name, "type": kind, "revision": revision})
            if name == "mathlib":
                found_mathlib = revision.lower() == EXPECTED_MATHLIB_REVISION
        elif kind == "path":
            raise VerificationError("Portable release dependencies must have fixed Git revisions")
        else:
            raise VerificationError(f"Unsupported dependency kind in lake-manifest: {kind}")
    if not found_mathlib:
        raise VerificationError("lake-manifest.json does not pin mathlib to the required revision")
    digest = hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest()
    return revisions, digest


def parse_axioms(target: str, output: str) -> list[str]:
    lines = [line.strip() for line in output.splitlines() if target in line]
    reports = [line for line in lines if "depends on axioms:" in line or "does not depend on any axioms" in line]
    if len(reports) != 1:
        raise VerificationError(f"Expected one axiom report for {target}")
    line = reports[0]
    if "does not depend on any axioms" in line:
        observed: set[str] = set()
    else:
        match = re.search(r"depends on axioms:\s*\[(.*?)\]", line)
        if not match:
            raise VerificationError(f"Cannot parse axiom report for {target}")
        observed = {value.strip() for value in match.group(1).split(",") if value.strip()}
    unexpected = observed - ALLOWED_AXIOMS
    if unexpected:
        raise VerificationError(f"Unexpected axioms for {target}: {sorted(unexpected)}")
    return sorted(observed)


def verify_reported_target(target: str, output: str) -> list[str]:
    if target not in output:
        raise VerificationError(f"Compiler output is missing target {target}")
    if "sorryAx" in output or "native_decide" in output:
        raise VerificationError(f"Compiler output contains an untrusted proof marker for {target}")
    return parse_axioms(target, output)


def external_lean_path(raw_path: str) -> list[str]:
    own_build = os.path.normcase(str((ROOT / ".lake" / "build" / "lib" / "lean").resolve()))
    paths: list[str] = []
    seen: set[str] = set()
    for raw in raw_path.split(os.pathsep):
        value = raw.strip().strip('"')
        if not value:
            continue
        resolved = str(Path(value).expanduser().resolve())
        key = os.path.normcase(resolved)
        if key == own_build or key in seen:
            continue
        seen.add(key)
        paths.append(resolved)
    return paths


def write_summary(path: Path, value: dict[str, Any]) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def static_only() -> int:
    try:
        manifest = read_json(ROOT / "source-manifest.json", "source-manifest.json")
        order = check_hashes(manifest)
        print(f"PASS: {len(order)} local source hashes, import closure, and dependency order")
        return 0
    except VerificationError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1


def main() -> int:
    started_at = datetime.now(timezone.utc)
    deadline = time.monotonic() + TOTAL_TIMEOUT_SECONDS
    run_name = started_at.strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:12]
    run_dir = ROOT / ".verification-output" / run_name
    run_dir.mkdir(parents=True, exist_ok=False)
    build_dir = run_dir / "build"
    build_dir.mkdir(parents=False, exist_ok=False)
    summary_path = run_dir / "summary.json"
    records: list[dict[str, Any]] = []
    summary: dict[str, Any] = {
        "status": "running",
        "started_utc": started_at.isoformat(),
        "run_directory": relpath(run_dir),
        "build_directory": relpath(build_dir),
        "source_manifest": "source-manifest.json",
        "commands": records,
    }
    try:
        source_manifest = read_json(ROOT / "source-manifest.json", "source-manifest.json")
        order = check_hashes(source_manifest)
        revisions, lake_manifest_sha256 = check_pins(source_manifest)
        summary["local_module_count"] = len(order)
        summary["total_source_bytes"] = source_manifest["total_source_bytes"]
        summary["mathlib_revision"] = EXPECTED_MATHLIB_REVISION
        summary["lake_manifest_sha256"] = lake_manifest_sha256
        summary["dependency_revisions"] = revisions

        lake = resolve_tool("LAKE_BIN", "lake")
        lean = resolve_tool("LEAN_BIN", "lean")
        lake_env = os.environ.copy()
        lake_env.pop("LEAN_PATH", None)
        lake_env["LEAN_NUM_THREADS"] = "1"
        lake_env["RAYON_NUM_THREADS"] = "1"
        lake_env["PYTHONIOENCODING"] = "utf-8"
        git = resolve_tool("GIT_BIN", "git")
        git_config_count = int(lake_env.get("GIT_CONFIG_COUNT", "0"))
        for dependency in revisions:
            name = dependency["name"]
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_-]*", name):
                raise VerificationError("Invalid package directory name")
            checkout = (ROOT / ".lake" / "packages" / name).resolve()
            if not checkout.is_dir():
                raise VerificationError(f"Missing pinned dependency checkout: {name}")
            revision = run_logged(
                [git, "-c", "safe.directory=" + checkout.as_posix(), "-C", str(checkout), "rev-parse", "HEAD"],
                "revision-" + name, lake_env, deadline, run_dir, records,
            )
            if revision.returncode != 0 or revision.stdout.strip() != dependency["revision"]:
                raise VerificationError(f"Dependency revision changed: {name}")
            lake_env[f"GIT_CONFIG_KEY_{git_config_count}"] = "safe.directory"
            lake_env[f"GIT_CONFIG_VALUE_{git_config_count}"] = checkout.as_posix()
            git_config_count += 1
        lake_env["GIT_CONFIG_COUNT"] = str(git_config_count)
        summary["actual_dependency_revisions_checked"] = True
        version = run_logged([lean, "--version"], "lean-version", lake_env, deadline, run_dir, records)
        version_text = version.stdout + version.stderr
        if version.returncode != 0 or re.search(r"\bversion\s+4\.34\.1\b", version_text) is None:
            raise VerificationError("LEAN_BIN is not the pinned Lean 4.34.1 compiler")
        env_probe = (
            "import os; "
            "print(os.environ.get('LEAN_PATH', ''))"
        )
        lake_env_path = run_logged(
            [lake, "env", sys.executable, "-X", "utf8", "-c", env_probe],
            "lake-external-lean-path",
            lake_env,
            deadline,
            run_dir,
            records,
        )
        if lake_env_path.returncode != 0:
            raise VerificationError("lake env could not provide dependency search paths")
        path_lines = [line.strip() for line in lake_env_path.stdout.splitlines() if line.strip()]
        if not path_lines:
            raise VerificationError("lake env returned an empty LEAN_PATH")
        dependencies = external_lean_path(path_lines[-1])
        if not dependencies:
            raise VerificationError("No external Lean dependency paths were returned by lake env")
        compiler_env = os.environ.copy()
        compiler_env["LEAN_PATH"] = os.pathsep.join([str(build_dir.resolve()), *dependencies])
        summary["external_lean_path_entries"] = len(dependencies)

        for index, module in enumerate(order, start=1):
            output = build_dir / f"{module}.olean"
            source = ROOT / "src" / f"{module}.lean"
            output.parent.mkdir(parents=True, exist_ok=True)
            result = run_logged(
                [lean, "-j", "1", "-R", str((ROOT / "src").resolve()), "-o", str(output), str(source)],
                f"module-{index:03d}-{module}",
                compiler_env,
                deadline,
                run_dir,
                records,
            )
            if result.returncode != 0:
                raise VerificationError(f"Lean failed while compiling {module}")
            print(f"compiled {index}/{EXPECTED_LOCAL_MODULE_COUNT}: {module}", flush=True)

        control_targets = {
            "Thomson10PublicWitness.original_node_0_check",
            "Thomson10PublicWitness.damaged_node_0_check",
        }
        controls = run_logged(
            [lean, "-j", "1", "-R", str((ROOT / "src").resolve()), "-o", str(build_dir / "WitnessControls.olean"), str(ROOT / "src" / "WitnessControls.lean")],
            "witness-controls",
            compiler_env,
            deadline,
            run_dir,
            records,
        )
        if controls.returncode != 0:
            raise VerificationError("Lean failed while compiling WitnessControls")
        control_output = controls.stdout + controls.stderr
        summary["witness_control_axioms"] = {
            target: verify_reported_target(target, control_output) for target in sorted(control_targets)
        }

        audit = run_logged(
            [lean, "-j", "1", "-R", str((ROOT / "src").resolve()), "-o", str(build_dir / "Audit.olean"), str(ROOT / "src" / "Audit.lean")],
            "main-audit",
            compiler_env,
            deadline,
            run_dir,
            records,
        )
        if audit.returncode != 0:
            raise VerificationError("Lean failed while compiling Audit")
        audit_targets = {
            "Thomson10Stability.certified_full_sphere_local_minimum",
            "Thomson10Stability.certified_gauged_slice_local_minimum",
        }
        audit_output = audit.stdout + audit.stderr
        summary["main_theorem_axioms"] = {
            target: verify_reported_target(target, audit_output) for target in sorted(audit_targets)
        }

        negative_env = compiler_env.copy()
        false_control = run_logged(
            [lean, "-j", "1", str(ROOT / "negative-controls" / "False.lean")],
            "negative-false-proposition",
            negative_env,
            deadline,
            run_dir,
            records,
        )
        false_text = false_control.stdout + false_control.stderr
        false_lowered = false_text.lower()
        if false_control.returncode == 0 or "0 = 1" not in false_text:
            raise VerificationError("The basic false-proposition negative control did not fail as intended")
        if not ("decide" in false_lowered or "unsolved goals" in false_lowered):
            raise VerificationError("The false proposition control did not fail at its intended proof goal")
        missing_markers = (
            "unknown identifier",
            "unknown constant",
            "unknown namespace",
            "invalid import",
            "could not find module",
            "failed to load",
            "no such file",
        )
        if any(marker in false_lowered for marker in missing_markers):
            raise VerificationError("The false proposition control failed because an import or identifier was missing")

        damaged = run_logged(
            [lean, "-j", "1", str(ROOT / "negative-controls" / "DamagedMatrixWitness.lean")],
            "negative-damaged-matrix-witness",
            negative_env,
            deadline,
            run_dir,
            records,
        )
        damaged_text = damaged.stdout + damaged.stderr
        lowered = damaged_text.lower()
        if damaged.returncode == 0:
            raise VerificationError("The damaged matrix witness negative control unexpectedly compiled")
        if "Thomson10PublicWitness.damaged_node_0_check" not in damaged_text:
            raise VerificationError("Damaged witness control failed before importing its positive control")
        if "= true" not in damaged_text or not ("decide" in lowered or "unsolved goals" in lowered):
            raise VerificationError("Damaged witness control did not fail at the deliberately false goal")
        if any(marker in lowered for marker in missing_markers):
            raise VerificationError("Damaged witness control failed because an import or identifier was missing")

        summary["negative_controls"] = {
            "false_proposition": "rejected as expected",
            "damaged_matrix_witness": "rejected at the false checker proposition as expected",
        }
        summary["status"] = "passed"
        summary["elapsed_seconds"] = round(time.monotonic() - deadline + TOTAL_TIMEOUT_SECONDS, 3)
        write_summary(summary_path, summary)
        print(f"PASS: {EXPECTED_LOCAL_MODULE_COUNT} modules, 4 qualified axiom reports, and both negative controls ({relpath(summary_path)})")
        return 0
    except VerificationError as exc:
        summary["status"] = "failed"
        summary["error"] = str(exc)
        summary["elapsed_seconds"] = round(time.monotonic() - deadline + TOTAL_TIMEOUT_SECONDS, 3)
        write_summary(summary_path, summary)
        print(f"FAIL: {exc}", file=sys.stderr)
        print(f"Details: {relpath(run_dir)}", file=sys.stderr)
        return 1
    except Exception as exc:  # Preserve a portable summary even for an unexpected runner error.
        summary["status"] = "failed"
        summary["error"] = f"Unexpected verifier error: {type(exc).__name__}"
        summary["elapsed_seconds"] = round(time.monotonic() - deadline + TOTAL_TIMEOUT_SECONDS, 3)
        write_summary(summary_path, summary)
        print(summary["error"], file=sys.stderr)
        print(f"Details: {relpath(run_dir)}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    if sys.argv[1:] == ["--static-only"]:
        raise SystemExit(static_only())
    raise SystemExit(main())
