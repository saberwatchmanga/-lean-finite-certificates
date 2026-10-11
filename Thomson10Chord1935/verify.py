#!/usr/bin/env python3
"""Draft sequential verifier for the Thomson N=10 chord <= 1.935 source package.

The verifier is deliberately source-based.  --static-only checks package structure
and hashes only; it never reports a mathematical or Lean verification success.
"""

from __future__ import annotations

import argparse
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
from pathlib import Path, PurePosixPath
from typing import Any


LEAN_PIN = "leanprover/lean4:v4.34.1"
LEAN_VERSION = "4.34.1"
MATHLIB_REVISION = "d13f23b723b8a846827a245b89c10fc7d3f11612"
ROOT_MODULE = "M36Chord1935Exclusion"
ROOT_TARGETS = (
    "M36Chord1935Exclusion.actual_summed_certificate_for_physical_energy",
    "M36Chord1935Exclusion.actual_energy_exceeds_32717_when_all_chords_le_1935",
    "M36Chord1935Exclusion.energy_le_32717_forces_a_chord_gt_1935",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMMAND_TIMEOUT = 600
DEFAULT_SECONDS = 5100
MAX_SECONDS = 16200
SOURCE_GUARD = re.compile(
    r"\b(?:sorry|admit|native_decide)\b|^\s*(?:(?:private|protected|noncomputable|unsafe|scoped)\s+)*axiom\b",
    re.MULTILINE,
)
MISSING_IMPORT = re.compile(
    r"unknown module|module .* not found|unknown package|cannot find module|"
    r"unknown constant|unknown identifier|failed to synthesize.*import",
    re.IGNORECASE,
)
TIMEOUT_OR_HEARTBEAT = re.compile(
    r"maximum heartbeats|heartbeat limit|timed? ?out|timeout|deadline exceeded",
    re.IGNORECASE,
)
LEAN_ERROR_LOCATION = re.compile(r"(?m)^.*\.lean:\d+:\d+: error:")


class VerifyError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha256(path: Path) -> str:
    return sha256(path.read_bytes())


def write_json(path: Path, obj: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


def read_json(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise VerifyError(f"cannot read {label}: {path}") from exc
    if not isinstance(value, dict):
        raise VerifyError(f"malformed {label}")
    return value


def contained_path(root: Path, relative: str, label: str) -> Path:
    posix = PurePosixPath(relative)
    if posix.is_absolute() or ".." in posix.parts or "\\" in relative:
        raise VerifyError(f"unsafe {label} path: {relative}")
    candidate = (root / Path(*posix.parts)).resolve()
    try:
        candidate.relative_to(root.resolve())
    except ValueError as exc:
        raise VerifyError(f"{label} escapes package root: {relative}") from exc
    return candidate


def imported_modules(source: str) -> list[str]:
    result: list[str] = []
    for line in source.splitlines():
        line = line.strip()
        if line.startswith("import "):
            declaration = line[len("import ") :].split("--", 1)[0]
            result.extend(token for token in declaration.split() if token)
    return result


def check_sources(root: Path) -> tuple[dict[str, Any], list[str], dict[str, str]]:
    manifest_path = root / "source-manifest.json"
    manifest = read_json(manifest_path, "source-manifest.json")
    order = manifest.get("topological_order_dependency_first")
    entries = manifest.get("sources")
    if manifest.get("root_module") != ROOT_MODULE:
        raise VerifyError(f"root_module must be {ROOT_MODULE}")
    if not isinstance(order, list) or not order or any(not isinstance(x, str) for x in order):
        raise VerifyError("missing topological_order_dependency_first")
    if order[-1] != ROOT_MODULE or len(set(order)) != len(order):
        raise VerifyError("dependency-first order must be unique and end at the root module")
    if not isinstance(entries, list) or len(entries) != len(order):
        raise VerifyError("sources entries do not match the module order")

    by_module: dict[str, dict[str, Any]] = {}
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("module"), str):
            raise VerifyError("malformed sources entry")
        name = entry["module"]
        if name in by_module:
            raise VerifyError(f"duplicate source module {name}")
        by_module[name] = entry
    if set(by_module) != set(order):
        raise VerifyError("module entries and dependency-first order differ")

    texts: dict[str, str] = {}
    total_bytes = 0
    for name in order:
        entry = by_module[name]
        expected = "src/" + name.replace(".", "/") + ".lean"
        if entry.get("path") != expected:
            raise VerifyError(f"unexpected source path for {name}; expected {expected}")
        path = contained_path(root, expected, "source")
        try:
            raw = path.read_bytes()
        except OSError as exc:
            raise VerifyError(f"missing source: {expected}") from exc
        if entry.get("size_bytes") != len(raw) or entry.get("sha256") != sha256(raw):
            raise VerifyError(f"source size/hash mismatch: {expected}")
        try:
            source = raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise VerifyError(f"source is not UTF-8: {expected}") from exc
        if SOURCE_GUARD.search(source):
            raise VerifyError(f"forbidden sorry/admit/native_decide/custom axiom token in {expected}")
        texts[name] = source
        total_bytes += len(raw)
    if "total_source_bytes" in manifest and manifest["total_source_bytes"] != total_bytes:
        raise VerifyError("total_source_bytes mismatch")

    positions = {name: idx for idx, name in enumerate(order)}
    local_edges: dict[str, set[str]] = {name: set() for name in order}
    for name, source in texts.items():
        for imported in imported_modules(source):
            if imported in positions:
                if positions[imported] >= positions[name]:
                    raise VerifyError(f"dependency order violation: {name} imports {imported}")
                local_edges[name].add(imported)
            elif not (imported == "Mathlib" or imported.startswith("Mathlib.") or imported == "Lean" or imported.startswith("Lean.")
                      or imported == "Std" or imported.startswith("Std.")
                      or imported == "Init" or imported.startswith("Init.")):
                raise VerifyError(f"import outside local source closure and pinned upstreams: {name}: {imported}")
    reachable: set[str] = set()
    pending = [ROOT_MODULE]
    while pending:
        module = pending.pop()
        if module in reachable:
            continue
        reachable.add(module)
        pending.extend(local_edges[module] - reachable)
    if reachable != set(order):
        raise VerifyError(f"source manifest is not the root import closure; unreachable modules: {sorted(set(order) - reachable)[:8]}")
    return manifest, order, texts


def check_package_pins(root: Path, manifest: dict[str, Any]) -> tuple[list[dict[str, str]], str]:
    try:
        toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
        lake_bytes = (root / "lake-manifest.json").read_bytes()
    except OSError as exc:
        raise VerifyError("missing lean-toolchain or lake-manifest.json") from exc
    if toolchain != LEAN_PIN:
        raise VerifyError(f"lean-toolchain must be {LEAN_PIN}")
    if manifest.get("lean_toolchain", LEAN_PIN) != LEAN_PIN:
        raise VerifyError("source-manifest Lean pin mismatch")
    if manifest.get("mathlib_commit", MATHLIB_REVISION) != MATHLIB_REVISION:
        raise VerifyError("source-manifest Mathlib pin mismatch")
    lakefile = next((root / n for n in ("lakefile.lean", "lakefile.toml") if (root / n).is_file()), None)
    if lakefile is None or MATHLIB_REVISION not in lakefile.read_text(encoding="utf-8"):
        raise VerifyError("lakefile must pin Mathlib to the required commit")
    try:
        lake_manifest = json.loads(lake_bytes.decode("utf-8"))
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise VerifyError("malformed lake-manifest.json") from exc
    packages = lake_manifest.get("packages") if isinstance(lake_manifest, dict) else None
    if not isinstance(packages, list) or not packages:
        raise VerifyError("lake-manifest.json has no packages")
    deps: list[dict[str, str]] = []
    seen: set[str] = set()
    has_mathlib = False
    for pkg in packages:
        if not isinstance(pkg, dict):
            raise VerifyError("malformed lake-manifest package")
        name, kind, rev = pkg.get("name"), pkg.get("type"), pkg.get("rev")
        if not isinstance(name, str) or name in seen:
            raise VerifyError("invalid or duplicate lake package name")
        seen.add(name)
        if kind != "git" or not isinstance(rev, str) or not re.fullmatch(r"[0-9a-fA-F]{40}", rev):
            raise VerifyError(f"dependency {name} must be a fixed Git revision")
        deps.append({"name": name, "revision": rev.lower()})
        if name.lower() == "mathlib":
            has_mathlib = rev.lower() == MATHLIB_REVISION
    if not has_mathlib:
        raise VerifyError("lake-manifest does not pin Mathlib to the required revision")
    if manifest.get("lake_manifest", "lake-manifest.json") != "lake-manifest.json":
        raise VerifyError("source-manifest lake_manifest must name lake-manifest.json")
    return deps, sha256(lake_bytes)


def resolve_tool(variable: str, default: str) -> str:
    requested = os.environ.get(variable, default)
    found = shutil.which(requested)
    if found:
        return str(Path(found).resolve())
    candidate = Path(requested).expanduser()
    if candidate.is_file():
        return str(candidate.resolve())
    raise VerifyError(f"cannot find {variable} executable: {requested}")


def run_logged(
    args: list[str], label: str, cwd: Path, env: dict[str, str], deadline: float,
    run_dir: Path, summary: dict[str, Any], summary_path: Path,
) -> tuple[int | None, str, str]:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise VerifyError("per-invocation time budget exhausted")
    timeout = min(COMMAND_TIMEOUT, remaining)
    logs = run_dir / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    seq = len(summary["commands"]) + 1
    log_path = logs / f"{seq:04d}-{label}.log"
    started = time.monotonic()
    timed_out = False
    process = subprocess.Popen(
        args, cwd=cwd, env=env, text=True, encoding="utf-8", errors="replace",
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    active_path = run_dir / "active-process.json"
    write_json(active_path, {"active": True, "pid": process.pid, "label": label,
                             "timeout_seconds": timeout})
    try:
        stdout, stderr = process.communicate(timeout=timeout)
        code = process.returncode
    except subprocess.TimeoutExpired:
        process.kill()
        stdout, stderr = process.communicate(timeout=15)
        code = process.returncode
        timed_out = True
    stdout, stderr = stdout or "", stderr or ""
    write_json(active_path, {"active": False, "pid": process.pid, "label": label,
                             "process_gone": process.poll() is not None, "timed_out": timed_out})
    elapsed = time.monotonic() - started
    log_text = (
        "command: " + json.dumps(args, ensure_ascii=False) + "\n"
        + f"cwd: {cwd}\ntimeout_seconds: {timeout:.3f}\nelapsed_seconds: {elapsed:.3f}\n"
        + f"return_code: {code}\ntimed_out: {str(timed_out).lower()}\n"
        + "--- output ---\n" + stdout + ("\n" if stdout and not stdout.endswith("\n") else "")
        + "--- stderr ---\n" + stderr + ("\n" if stderr and not stderr.endswith("\n") else "")
    )
    log_path.write_text(log_text, encoding="utf-8", errors="replace")
    record = {
        "name": label, "log": log_path.relative_to(run_dir).as_posix(),
        "log_sha256": file_sha256(log_path), "exit_code": code,
        "elapsed_seconds": round(elapsed, 3), "timed_out": timed_out,
    }
    summary["commands"].append(record)
    summary["invocations"][-1]["commands"].append(label)
    write_json(summary_path, summary)
    if timed_out:
        raise VerifyError(f"command timed out and was terminated: {label}")
    return int(code), stdout, stderr


def check_upstream_revisions(
    root: Path, deps: list[dict[str, str]], lake: str, git: str, env: dict[str, str],
    deadline: float, run_dir: Path, summary: dict[str, Any], summary_path: Path,
) -> list[Path]:
    # lake env supplies the package search paths; this is setup only, not a proof build.
    probe = "import os; print(os.environ.get('LEAN_PATH', ''))"
    mathlib_override = os.environ.get("MATHLIB_DIR")
    probe_root = Path(mathlib_override).expanduser().resolve() if mathlib_override else root
    if mathlib_override:
        # An existing pinned checkout needs no dependency update or Lake config evaluation.
        lines = []
    else:
        code, stdout, _ = run_logged(
            [lake, "env", sys.executable, "-X", "utf8", "-c", probe], "lake-env-path",
            probe_root, env, deadline, run_dir, summary, summary_path,
        )
        if code != 0:
            raise VerifyError("lake env could not prepare pinned upstream paths")
        lines = [line.strip() for line in stdout.splitlines() if line.strip()]
        if not lines:
            raise VerifyError("lake env returned no LEAN_PATH")

    checkouts: list[tuple[dict[str, str], Path]] = []
    for dep in deps:
        if mathlib_override:
            checkout = probe_root if dep["name"].lower() == "mathlib" else (probe_root / ".lake" / "packages" / dep["name"]).resolve()
        else:
            checkout = (root / ".lake" / "packages" / dep["name"]).resolve()
        if not checkout.is_dir():
            raise VerifyError(f"missing checkout for pinned dependency {dep['name']}: {checkout}")
        checkouts.append((dep, checkout))
    for dep, checkout in checkouts:
        code, stdout, _ = run_logged(
            [git, "-c", "safe.directory=" + checkout.as_posix(), "-C", str(checkout), "rev-parse", "HEAD"],
            "revision-" + dep["name"], root, env, deadline, run_dir, summary, summary_path,
        )
        if code != 0 or stdout.strip().lower() != dep["revision"]:
            raise VerifyError(f"actual Git revision mismatch for dependency {dep['name']}")

    # Keep only pinned dependency build trees and the Lean distribution library.
    allowed_roots = [checkout.resolve() for _, checkout in checkouts]
    paths: list[Path] = []
    seen: set[str] = set()
    for raw in (lines[-1].split(os.pathsep) if lines else []):
        raw = raw.strip().strip('"')
        if not raw:
            continue
        path = Path(raw).expanduser().resolve()
        key = os.path.normcase(str(path))
        if key in seen:
            continue
        seen.add(key)
        is_dep = any(_is_relative(path, dep_root) for dep_root in allowed_roots)
        is_lean_lib = path.name.lower() == "lean" and path.parent.name.lower() == "lib"
        if is_dep or (is_lean_lib and not _is_relative(path, root)):
            paths.append(path)
    # MATHLIB_DIR may point Lake at an already-present checkout outside .lake/packages.
    for _, checkout in checkouts:
        candidate = checkout / ".lake" / "build" / "lib" / "lean"
        if candidate.is_dir() and os.path.normcase(str(candidate.resolve())) not in {
            os.path.normcase(str(p)) for p in paths
        }:
            paths.append(candidate.resolve())
    if mathlib_override:
        lean_library = Path(resolve_tool("LEAN_BIN", "lean")).parent.parent / "lib" / "lean"
        if lean_library.is_dir():
            paths.append(lean_library.resolve())
    if not paths:
        raise VerifyError("no pinned upstream/Lean library paths survived LEAN_PATH filtering")
    summary["actual_dependency_revisions_checked"] = True
    summary["dependency_revisions"] = deps
    summary["upstream_lean_path"] = [str(p) for p in paths]
    write_json(summary_path, summary)
    return paths


def _is_relative(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def verify_resume(
    run_dir: Path, root: Path, fingerprint: str, order: list[str],
    source_hashes: dict[str, str], control_hash: str,
) -> tuple[dict[str, Any], Path]:
    run_dir = run_dir.resolve()
    output_root = (root / ".verification-output").resolve()
    if not _is_relative(run_dir, output_root) or run_dir == output_root:
        raise VerifyError("--resume must name a run directory under this package's .verification-output")
    summary_path = run_dir / "summary.json"
    summary = read_json(summary_path, "resume summary")
    if summary.get("package_root") != str(root.resolve()) or summary.get("provenance_fingerprint") != fingerprint:
        raise VerifyError("resume provenance does not match the current source package")
    if summary.get("control_manifest_sha256") != control_hash:
        raise VerifyError("resume control manifest hash mismatch")
    build_dir = run_dir / "build"
    accepted = summary.get("accepted_modules")
    if not isinstance(accepted, list) or len(accepted) > len(order):
        raise VerifyError("malformed accepted module record")
    for index, item in enumerate(accepted):
        if not isinstance(item, dict) or item.get("module") != order[index]:
            raise VerifyError("accepted module record is not a dependency-first prefix")
        if item.get("source_sha256") != source_hashes[order[index]]:
            raise VerifyError(f"resume source provenance mismatch: {order[index]}")
        artifact = contained_path(run_dir, item.get("artifact", ""), "resume artifact")
        log = contained_path(run_dir, item.get("log", ""), "resume log")
        if not artifact.is_file() or file_sha256(artifact) != item.get("artifact_sha256"):
            raise VerifyError(f"resume artifact missing or changed: {order[index]}")
        if not log.is_file() or file_sha256(log) != item.get("log_sha256"):
            raise VerifyError(f"resume log missing or changed: {order[index]}")
        log_text = log.read_text(encoding="utf-8", errors="replace")
        if "return_code: 0" not in log_text or "timed_out: false" not in log_text:
            raise VerifyError(f"resume log does not attest successful source compile: {order[index]}")
    if not build_dir.is_dir():
        raise VerifyError("resume build directory is missing")
    if not _is_relative(build_dir.resolve(), run_dir):
        raise VerifyError("resume build directory escapes the run directory")
    for command in summary.get("commands", []):
        if not isinstance(command, dict):
            raise VerifyError("malformed prior command record")
        log = contained_path(run_dir, command.get("log", ""), "resume command log")
        if not log.is_file() or file_sha256(log) != command.get("log_sha256"):
            raise VerifyError("a prior command log is missing or changed")
    return summary, build_dir


def parse_axioms(target: str, output: str) -> list[str]:
    pattern = r"'" + re.escape(target) + r"' (?:does not depend on any axioms|depends on axioms:\s*\[[^]]*\])"
    reports = re.findall(pattern, output)
    if len(reports) != 1:
        raise VerifyError(f"expected exactly one #print axioms report for {target}")
    line = reports[0]
    if "does not depend on any axioms" in line:
        observed: set[str] = set()
    else:
        match = re.search(r"depends on axioms:\s*\[([^]]*)\]", line)
        if not match:
            raise VerifyError(f"cannot parse axiom report for {target}")
        observed = {x.strip() for x in match.group(1).split(",") if x.strip()}
    unexpected = observed - ALLOWED_AXIOMS
    if unexpected:
        raise VerifyError(f"unexpected axioms for {target}: {sorted(unexpected)}")
    return sorted(observed)


def check_control_manifest(root: Path, path_text: str) -> tuple[dict[str, Any], str]:
    path = contained_path(root, path_text, "control manifest")
    manifest = read_json(path, "negative control manifest")
    controls = manifest.get("controls")
    expected_names = {"DamagedCoefficient", "BadBudget"}
    if (not isinstance(controls, list) or any(not isinstance(c, dict) for c in controls)
            or {c.get("name") for c in controls} != expected_names):
        raise VerifyError("control manifest must contain exactly DamagedCoefficient and BadBudget")
    seen: set[str] = set()
    for control in controls:
        name, source, pattern = control.get("name"), control.get("source"), control.get("expected_error_regex")
        if name in seen or not isinstance(source, str) or not isinstance(pattern, str) or not pattern:
            raise VerifyError("malformed or duplicate negative control entry")
        seen.add(name)
        if source != f"negative-controls/{name}.lean":
            raise VerifyError(f"{name} must use negative-controls/{name}.lean")
        try:
            re.compile(pattern, re.IGNORECASE | re.MULTILINE)
        except re.error as exc:
            raise VerifyError(f"invalid expected_error_regex for {name}") from exc
        source_path = contained_path(root, source, "negative-control source")
        if not source.startswith("negative-controls/") or not source_path.is_file():
            raise VerifyError(f"missing negative-control source: {source}")
        source_text = source_path.read_text(encoding="utf-8")
        if SOURCE_GUARD.search(source_text):
            raise VerifyError(f"forbidden source token in negative control {name}")
    source_hashes = []
    for control in controls:
        source_path = contained_path(root, control["source"], "negative-control source")
        source_hashes.append((control["name"], file_sha256(source_path)))
    fingerprint = sha256(json.dumps({
        "manifest_sha256": file_sha256(path), "sources": sorted(source_hashes),
    }, sort_keys=True).encode("utf-8"))
    return manifest, fingerprint


def run_controls(
    root: Path, controls: dict[str, Any], lean: str, src: Path, build: Path,
    env: dict[str, str], deadline: float, run_dir: Path, summary: dict[str, Any], summary_path: Path,
) -> None:
    for control in controls["controls"]:
        source = contained_path(root, control["source"], "negative-control source")
        label = "control-" + control["name"]
        code, stdout, stderr = run_logged(
            [lean, "-j", "1", str(source)], label,
            root, env, deadline, run_dir, summary, summary_path,
        )
        output = stdout + "\n" + stderr
        if code == 0:
            raise VerifyError(f"negative control unexpectedly compiled: {control['name']}")
        if MISSING_IMPORT.search(output):
            raise VerifyError(f"negative control failed because of a missing import/name: {control['name']}")
        if TIMEOUT_OR_HEARTBEAT.search(output):
            raise VerifyError(f"negative control failed by timeout/heartbeat limit: {control['name']}")
        if not LEAN_ERROR_LOCATION.search(output):
            raise VerifyError(f"negative control did not produce a Lean source diagnostic: {control['name']}")
        try:
            intended = re.search(control["expected_error_regex"], output, re.IGNORECASE | re.MULTILINE)
        except re.error as exc:
            raise VerifyError(f"invalid expected_error_regex for {control['name']}") from exc
        if intended is None:
            raise VerifyError(f"negative control did not hit its intended failure: {control['name']}")
        summary.setdefault("negative_controls", []).append({"name": control["name"], "intended_failure": True})
        write_json(summary_path, summary)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-root", type=Path, required=True, help="future package directory")
    parser.add_argument("--static-only", action="store_true", help="static checks only; no proof claim")
    parser.add_argument("--resume", type=Path, help="resume a matching run directory")
    parser.add_argument("--seconds", type=int, default=int(os.environ.get("THOMSON_VERIFY_TOTAL_SECONDS", DEFAULT_SECONDS)))
    parser.add_argument("--control-manifest", default="negative-controls/control-manifest.json")
    args = parser.parse_args()
    if not 60 <= args.seconds <= MAX_SECONDS:
        parser.error(f"--seconds must be between 60 and {MAX_SECONDS}")
    root = args.package_root.expanduser().resolve()
    try:
        manifest, order, _ = check_sources(root)
        deps, lake_hash = check_package_pins(root, manifest)
        source_hashes = {e["module"]: e["sha256"] for e in manifest["sources"]}
        source_manifest_hash = file_sha256(root / "source-manifest.json")
        provenance = sha256(json.dumps({
            "source_manifest": source_manifest_hash,
            "lake_manifest": lake_hash,
            "lakefile_sha256": file_sha256(next(root / n for n in ("lakefile.lean", "lakefile.toml") if (root / n).is_file())),
            "lean_toolchain": LEAN_PIN,
            "mathlib_revision": MATHLIB_REVISION,
        }, sort_keys=True).encode("utf-8"))
        if args.static_only:
            print(f"STATIC PASS: {len(order)} source hashes, import closure/order, pins. No Lean proof was built or audited.")
            return 0
        controls, control_hash = check_control_manifest(root, args.control_manifest)

        now = datetime.now(timezone.utc)
        if args.resume:
            run_dir = args.resume.expanduser().resolve()
            summary, build_dir = verify_resume(run_dir, root, provenance, order, source_hashes, control_hash)
            summary["status"] = "running"
            summary["resumed_utc"] = now.isoformat()
        else:
            run_dir = root / ".verification-output" / (now.strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:10])
            run_dir.mkdir(parents=True, exist_ok=False)
            build_dir = run_dir / "build"
            build_dir.mkdir(parents=False, exist_ok=False)
            summary = {
                "status": "running", "run_id": run_dir.name,
                "package_root": str(root), "provenance_fingerprint": provenance,
                "source_manifest_sha256": source_manifest_hash, "lake_manifest_sha256": lake_hash,
                "control_manifest": args.control_manifest, "control_manifest_sha256": control_hash,
                "root_module": ROOT_MODULE, "root_targets": list(ROOT_TARGETS),
                "started_utc": now.isoformat(), "build_directory": "build",
                "commands": [], "accepted_modules": [], "invocations": [],
            }
        summary_path = run_dir / "summary.json"
        invocation = {"started_utc": now.isoformat(), "seconds_budget": args.seconds, "commands": []}
        summary.setdefault("invocations", []).append(invocation)
        write_json(summary_path, summary)
        deadline = time.monotonic() + args.seconds

        lake = resolve_tool("LAKE_BIN", "lake")
        lean = resolve_tool("LEAN_BIN", "lean")
        git = resolve_tool("GIT_BIN", "git")
        base_env = os.environ.copy()
        base_env.pop("LEAN_PATH", None)
        base_env["LEAN_NUM_THREADS"] = "1"
        base_env["RAYON_NUM_THREADS"] = "1"
        base_env["PYTHONIOENCODING"] = "utf-8"
        version_code, version_out, version_err = run_logged(
            [lean, "--version"], "lean-version", root, base_env, deadline, run_dir, summary, summary_path,
        )
        if version_code != 0 or re.search(r"\bversion\s+4\.34\.1\b", version_out + version_err) is None:
            raise VerifyError("LEAN_BIN is not the pinned Lean 4.34.1 compiler")
        upstream = check_upstream_revisions(root, deps, lake, git, base_env, deadline, run_dir, summary, summary_path)
        build_dir = (run_dir / "build").resolve()
        compiler_env = base_env.copy()
        compiler_env["LEAN_PATH"] = os.pathsep.join([str(build_dir), *(str(p) for p in upstream)])
        compiler_env["LEAN_NUM_THREADS"] = "1"
        src = root / "src"

        accepted = summary["accepted_modules"]
        for index in range(len(accepted), len(order)):
            module = order[index]
            output = build_dir / (module.replace(".", os.sep) + ".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            source_rel = "src/" + module.replace(".", "/") + ".lean"
            source = contained_path(root, source_rel, "source")
            code, stdout, stderr = run_logged(
                [lean, "-j", "1", "-R", str(src.resolve()), "-o", str(output), str(source)],
                f"module-{index + 1:03d}-{module}", root, compiler_env, deadline,
                run_dir, summary, summary_path,
            )
            cmd = summary["commands"][-1]
            if code != 0:
                raise VerifyError(f"Lean source compilation failed for {module}")
            if not output.is_file():
                raise VerifyError(f"Lean returned success without an artifact for {module}")
            accepted.append({
                "module": module, "source_sha256": source_hashes[module],
                "artifact": output.relative_to(run_dir).as_posix(),
                "artifact_sha256": file_sha256(output),
                "log": cmd["log"], "log_sha256": cmd["log_sha256"],
                "exit_code": code, "elapsed_seconds": cmd["elapsed_seconds"],
            })
            summary["last_accepted_module"] = module
            write_json(summary_path, summary)
            print(f"compiled {index + 1}/{len(order)}: {module}", flush=True)

        audit = run_dir / "RootAxioms.lean"
        audit.write_text("import " + ROOT_MODULE + "\n" + "\n".join("#print axioms " + t for t in ROOT_TARGETS) + "\n", encoding="utf-8")
        audit_code, audit_out, audit_err = run_logged(
            [lean, str(audit)], "root-axiom-audit", root,
            compiler_env, deadline, run_dir, summary, summary_path,
        )
        if audit_code != 0:
            raise VerifyError("root #print axioms audit did not compile")
        summary["root_axioms"] = {target: parse_axioms(target, audit_out + audit_err) for target in ROOT_TARGETS}
        write_json(summary_path, summary)

        run_controls(root, controls, lean, src, build_dir, compiler_env, deadline, run_dir, summary, summary_path)
        summary["status"] = "source_build_and_audits_passed"
        summary["completed_utc"] = datetime.now(timezone.utc).isoformat()
        summary["claim_scope"] = "Lean source compilation, declared root axiom audit, and configured negative controls only; no independent mathematical validation."
        write_json(summary_path, summary)
        print(f"PASS: {len(order)} modules compiled sequentially from source; root axioms and negative controls recorded.")
        return 0
    except (VerifyError, OSError, ValueError) as exc:
        if "summary" in locals() and "summary_path" in locals():
            summary["status"] = "failed_or_budget_stopped"
            summary["failure"] = str(exc)
            if summary.get("invocations"):
                summary["invocations"][-1]["ended_utc"] = datetime.now(timezone.utc).isoformat()
            write_json(summary_path, summary)
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
