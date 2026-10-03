"""Frozen Windows-x64 JSP309 engine inventory and pure runtime planning.

No compiler, subprocess, network, main entrypoint or source rewriting occurs here.
The eight engine inputs are distinct from the 68 mathematical/audit sources.
"""
from __future__ import annotations

import hashlib
import json
import copy
from pathlib import Path, PurePosixPath
import stat

SCHEMA = "jsp309.engine-inputs.v1"
SCOPE = "Windows x64 compiler adaptation; two engine Lean sources are outside the 68 mathematical source/audit files."
ROLE_PATHS = {
    "lake_launcher_lean": "verification/lakefront309/LakeFrontend309.lean",
    "cached_frontend_lean": "verification/lowinfo309_cached/SequentialDriver.lean",
    "dispatcher_python": "verification/lakefront309/lake_dispatcher309_real_candidate.py",
    "native_bridge_source": "verification/lakefront309/DispatchBridge309.cs",
    "native_bridge_executable": "verification/lakefront309/DispatchBridge309.exe",
    "hash_helper_python": "verification/lakefront309/hash_inputs309.py",
    "baseline_request_inventory": "verification/adapted309/Heavy.request.json",
    "baseline_report_inventory": "verification/adapted309/out/HEAVY_DRIVER_REPORT.json",
}
FROZEN_SHA256 = {
    "lake_launcher_lean": "350a259e5c49e30363c596543f37cb013aece02f96023857826ed9fc23367f16",
    "cached_frontend_lean": "26f73083d233b617829bbf790dcfb8cda4a1a821f9b5e12776ef2cda38d35b16",
    "dispatcher_python": "b53aac7e7311c3d38ab0590105b5f0c7cae423467c3f1415539a7d8ce229d9a3",
    "native_bridge_source": "ba82080bf1328baba61f26c335477e52c0586e364c49f01799c5a52acfb939d1",
    "native_bridge_executable": "30cbbe65657b6fb539072c71a6d6ff74d5a129776549c9b26728d5cfb0aa08c0",
    "hash_helper_python": "519549262c2e5043de88f45e86deb462ce63e71b3da5319d1e21a24e9fa5bc8d",
    "baseline_request_inventory": "e3d5ce1ea103d235e6d5fcfd81a98dc7b5545b707b28d6034b55f5c0dd660df1",
    "baseline_report_inventory": "15facfcaa360ae685ad43e9d25076e8e0cb57abc95377709d77b6b53ec6d6fd7",
}
TOOLCHAIN_RUNTIME = {
    "stock_lean": {"path": "bin/lean.exe", "sha256": "8132256d484b8ecc4561bec70abd1271f4c0d03badbc3bc272f6c4053af9fdbc"},
    "lake_shared": {"path": "bin/libLake_shared.dll", "sha256": "95368a6f8c32697fd2ec0adf11549944730c7e86dd80d41f8ba0e6c00216602b"},
}
HEAVY = {
    "package": "GafniTaoFrozen", "library": "RiemannZeta",
    "module": "RiemannZeta.GuthMaynard.HughesYoungActiveComplementSourceLine",
    "source_sha256": "a39dd8053b3c5ecfe24d673fddb4965e8d355d2d584dc1ef0a3407e3a14f6a9b",
    "source_bytes": 415362,
}
SETUP_OPTIONS = {"pp.unicode.fun": True, "autoImplicit": False}


class MissingStockSetup(RuntimeError):
    """Caller must prepare this file through the real official stock facet."""


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(part)
    return h.hexdigest()


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode("utf-8")


def read_json(path: Path) -> object:
    def unique(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise RuntimeError("Duplicate JSON object field: " + key)
            value[key] = item
        return value
    def reject(value):
        raise RuntimeError("Invalid JSON numeric constant: " + value)
    return json.loads(path.read_bytes().decode("utf-8"), object_pairs_hook=unique, parse_constant=reject)


read_manifest = read_json


def local_file(root: Path, relative: str) -> Path:
    part = PurePosixPath(relative)
    if (not relative or part.is_absolute() or part.as_posix() != relative
            or ".." in part.parts or "\\" in relative or ":" in relative):
        raise RuntimeError("Noncanonical release-relative input path: " + relative)
    path = root.joinpath(*part.parts).resolve(strict=True)
    if not path.is_relative_to(root.resolve(strict=True)) or not stat.S_ISREG(path.stat().st_mode):
        raise RuntimeError("Engine input must be a regular file inside the release: " + relative)
    return path


def file_binding(path: Path) -> dict:
    path = path.resolve(strict=True)
    if not stat.S_ISREG(path.stat().st_mode):
        raise RuntimeError("Runtime binding is not a regular file: " + str(path))
    return {"path": str(path), "sha256": sha256(path)}


def make_manifest(root: Path, pins: dict) -> dict:
    """Inventory only. Callers must never infer execution success from this value."""
    files = []
    for role in sorted(ROLE_PATHS):
        path = local_file(root, ROLE_PATHS[role])
        files.append({"role": role, "path": ROLE_PATHS[role], "bytes": path.stat().st_size, "sha256": sha256(path)})
    return copy.deepcopy({"schema": SCHEMA, "status": "unverified_engine_snapshot", "pins": pins,
            "files": files, "toolchain_runtime": TOOLCHAIN_RUNTIME, "heavy_target": HEAVY, "scope": SCOPE})


def validate_manifest(value: object, pins: dict, root: Path | None = None) -> dict[str, Path]:
    if (not isinstance(value, dict) or set(value) != {"schema", "status", "pins", "files", "toolchain_runtime", "heavy_target", "scope"}
            or value["schema"] != SCHEMA or value["status"] != "verified" or value["pins"] != pins
            or value["toolchain_runtime"] != TOOLCHAIN_RUNTIME or value["heavy_target"] != HEAVY or value["scope"] != SCOPE):
        raise RuntimeError("Frozen engine manifest schema/status/pins/runtime/target/scope mismatch")
    rows = value["files"]
    if not isinstance(rows, list) or len(rows) != 8:
        raise RuntimeError("The engine inventory must contain exactly eight role-bound inputs")
    if [row.get("role") if isinstance(row, dict) else None for row in rows] != sorted(ROLE_PATHS):
        raise RuntimeError("Engine roles must be unique, complete and canonically sorted")
    paths = {}
    for row in rows:
        role = row["role"]
        if (set(row) != {"role", "path", "bytes", "sha256"} or row["path"] != ROLE_PATHS[role]
                or type(row["bytes"]) is not int or row["bytes"] <= 0 or row["sha256"] != FROZEN_SHA256[role]):
            raise RuntimeError("Frozen engine role/path/bytes/SHA mismatch: " + role)
        if root is not None:
            path = local_file(root, row["path"])
            if path.stat().st_size != row["bytes"] or sha256(path) != row["sha256"]:
                raise RuntimeError("Engine bytes differ from the public manifest: " + role)
            paths[role] = path
    return paths


def check_lean_inventory(root: Path, math_files: dict) -> None:
    if len(math_files) != 68 or any(not isinstance(name, str) or not name.endswith(".lean") for name in math_files):
        raise RuntimeError("Mathematical source/audit inventory must remain exactly 68 Lean files")
    engine_lean = {path for path in ROLE_PATHS.values() if path.endswith(".lean")}
    if engine_lean & set(math_files):
        raise RuntimeError("Engine Lean roles overlap the mathematical source inventory")
    actual = {path.relative_to(root).as_posix() for path in root.rglob("*.lean")}
    if actual != set(math_files) | engine_lean:
        raise RuntimeError("Public Lean inventory must be exactly the mathematical 68 plus two engine roles")


def output_root(work: Path, reuse: Path | None) -> Path:
    if reuse is not None and not reuse.is_absolute():
        raise RuntimeError("--reuse-bound-output-root must be an explicit absolute directory")
    root = (reuse if reuse is not None else work / "output").resolve()
    if reuse is not None and not root.is_dir():
        raise RuntimeError("The reused output root must already be an existing directory")
    return root


def check_setup(path: Path) -> dict:
    if not path.is_file():
        raise MissingStockSetup("Missing actual stock setup: " + str(path) +
            ". This pure planner never fabricates setup; use the official stock-facet capture preparation or an exact pinned warm workspace.")
    setup = read_json(path)
    if (not isinstance(setup, dict) or set(setup) != {"plugins", "package", "options", "name", "isModule", "importArts", "dynlibs"}
            or setup["package"] != HEAVY["package"] or setup["name"] != HEAVY["module"] or setup["isModule"] is not False
            or setup["plugins"] != [] or setup["dynlibs"] != [] or not isinstance(setup["importArts"], dict)
            or not isinstance(setup["options"], dict) or set(setup["options"]) != set(SETUP_OPTIONS)
            or any(setup["options"][key] is not expected for key, expected in SETUP_OPTIONS.items())):
        raise RuntimeError("Existing stock setup owner/name/options/importArts schema differs")
    return setup


def plan_runtime(manifest: dict, root: Path, pins: dict, math_files: dict,
                 sysroot: Path, python: Path, project: Path, frozen: Path, outputs: Path) -> dict:
    """Read exact inputs and return JSON bytes/absolute bindings; writes nothing."""
    engine = validate_manifest(manifest, pins, root)
    check_lean_inventory(root, math_files)
    sysroot, project, frozen = (path.resolve(strict=True) for path in (sysroot, project, frozen))
    outputs = outputs.resolve()
    tools = {role: file_binding(sysroot / row["path"]) for role, row in TOOLCHAIN_RUNTIME.items()}
    for role, binding in tools.items():
        if binding["sha256"] != TOOLCHAIN_RUNTIME[role]["sha256"]:
            raise RuntimeError("Official toolchain runtime SHA differs: " + role)
    python_binding = file_binding(python)
    module_path = Path(*HEAVY["module"].split("."))
    source = frozen / "FrozenFoundation" / module_path.with_suffix(".lean")
    source_binding = file_binding(source)
    if source_binding["sha256"] != HEAVY["source_sha256"] or source.stat().st_size != HEAVY["source_bytes"]:
        raise RuntimeError("Original heavy source bytes/SHA differ")
    build_root = (outputs / "gafnitao").resolve()
    setup_path = (build_root / "ir" / module_path.with_suffix(".setup.json")).resolve()
    check_setup(setup_path)
    setup_binding = file_binding(setup_path)
    baseline = read_json(engine["baseline_request_inventory"])
    expected_names = baseline.get("expectedNames") if isinstance(baseline, dict) else None
    if (not isinstance(expected_names, list) or len(expected_names) != 194
            or any(not isinstance(name, str) for name in expected_names) or len(set(expected_names)) != 194):
        raise RuntimeError("Original baseline must contain the exact complete 194-name inventory")
    identity = {"engine_files": manifest["files"], "tools": tools, "python": python_binding,
                "project": str(project), "frozen": str(frozen), "outputs": str(outputs), "setup": setup_binding}
    fingerprint = hashlib.sha256(json_bytes(identity)).hexdigest()
    runtime_dir = engine["dispatcher_python"].parent / "runtime_public" / fingerprint
    config_path, policy_path, request_path = (runtime_dir / name for name in
        ("dispatcher_config309.public.json", "bridge_policy309.public.json", "LauncherPublic.request.json"))
    artifacts = {"olean": build_root / "lib/lean" / module_path.with_suffix(".olean"),
                 "ilean": build_root / "lib/lean" / module_path.with_suffix(".ilean"),
                 "c": build_root / "ir" / module_path.with_suffix(".c")}
    target = {**HEAVY, "cwd": str(project), "source": str(source), "setup": str(setup_path),
              "setup_sha256": setup_binding["sha256"], "setup_options": SETUP_OPTIONS,
              "build_root": str(build_root), "artifacts": {key: str(path) for key, path in artifacts.items()},
              "prefix_args": ["-DElab.async=false", "-j1"]}
    template = {"source": str(source), "setup": str(setup_path), "sysroot": str(sysroot),
                "olean": str(artifacts["olean"]), "ilean": str(artifacts["ilean"]), "cFile": str(artifacts["c"]),
                "report": "@CALL/frontend.report.json", "cmdlineOptions": {"Elab.async": False}, "cliPlugins": [],
                "infoEnabled": True, "failOnWarnings": True, "expectedNames": expected_names,
                "postExportCachedAxioms": True, "provisionalOlean": "@CALL/heavy.provisional.olean",
                "expectedHeavySource": str(source), "prewarmSymbolFrequency": True, "metadataMaxHeartbeats": 20000000}
    config = {"schema": "lakefront309.real-heavy.dispatch.v1", "mode": "frozen_gafnitao_riemann_heavy",
              "sysroot": str(sysroot), "stock_lean": tools["stock_lean"]["path"],
              "stock_lean_sha256": tools["stock_lean"]["sha256"], "driver_path": str(engine["cached_frontend_lean"]),
              "driver_sha256": FROZEN_SHA256["cached_frontend_lean"],
              "evidence": {"request": str(engine["baseline_request_inventory"]),
                           "request_sha256": FROZEN_SHA256["baseline_request_inventory"],
                           "report": str(engine["baseline_report_inventory"]),
                           "report_sha256": FROZEN_SHA256["baseline_report_inventory"]},
              "target": target, "request_template": template}
    policy = {"schema": "lakefront309.bridge.v1", "python": python_binding["path"], "python_sha256": python_binding["sha256"],
              "dispatcher": str(engine["dispatcher_python"]), "dispatcher_sha256": FROZEN_SHA256["dispatcher_python"]}
    config_raw, policy_raw = json_bytes(config), json_bytes(policy)
    config_binding = {"path": str(config_path), "sha256": hashlib.sha256(config_raw).hexdigest()}
    policy_binding = {"path": str(policy_path), "sha256": hashlib.sha256(policy_raw).hexdigest()}
    bindings = [file_binding(engine[role]) for role in sorted(engine)] + [tools[role] for role in sorted(tools)]
    bindings += [python_binding, setup_binding, config_binding, policy_binding]
    request = {"sysroot": str(sysroot), "expectedLeanGithash": pins["actual_compiler_commit"], "workspace": str(project),
               "configFile": "lakefile.toml", "heavyModule": HEAVY["module"], "heavyPackage": HEAVY["package"],
               "heavyLibrary": HEAVY["library"], "heavySource": source_binding,
               "dispatcher": str(engine["native_bridge_executable"]), "bridgePolicy": policy_binding,
               "dispatcherConfig": config_binding, "python": python_binding["path"],
               "hashHelper": str(engine["hash_helper_python"]), "adaptationFiles": bindings, "targets": ["Erdos374Research"]}
    request_raw = json_bytes(request)
    all_bindings = bindings + [source_binding, {"path": str(request_path), "sha256": hashlib.sha256(request_raw).hexdigest()}]
    command = [tools["stock_lean"]["path"], "--load-dynlib=" + tools["lake_shared"]["path"],
               "-t0", "-j3", "-DautoImplicit=false", "--run", str(engine["lake_launcher_lean"]), str(request_path)]
    return {"engine": engine, "config": config, "policy": policy, "request": request,
            "writes": [(config_path, config_raw), (policy_path, policy_raw), (request_path, request_raw)],
            "bindings": all_bindings, "command": command, "setup_binding": setup_binding,
            "environment": {"LAKEFRONT309_CONFIG": str(config_path), "LAKEFRONT309_BRIDGE_POLICY": str(policy_path),
                            "LAKEFRONT309_BRIDGE_POLICY_SHA256": policy_binding["sha256"],
                            "LEAN_PATH": str(sysroot / "lib/lean")},
            "calls_root": engine["dispatcher_python"].parent / "calls_real_candidate"}


def verify_runtime(plan: dict) -> None:
    for binding in plan["bindings"]:
        path = Path(binding["path"])
        if file_binding(path) != binding:
            raise RuntimeError("Bound engine/runtime/source/setup/request changed: " + str(path))


def plan_capture(manifest: dict, root: Path, pins: dict, math_files: dict,
                 sysroot: Path, python: Path, project: Path, frozen: Path, outputs: Path,
                 runner_path: Path, helper_path: Path, run_id: str) -> dict:
    """Plan an official stock-facet setup capture that must stop before Heavy.

    The same public runner is the bridge's capture-only child. No ninth engine
    file or third Lean engine source is created. Actual execution is not implied.
    """
    engine = validate_manifest(manifest, pins, root)
    check_lean_inventory(root, math_files)
    sysroot, project, frozen, root = (path.resolve(strict=True) for path in (sysroot, project, frozen, root))
    outputs = outputs.resolve()
    tools = {role: file_binding(sysroot / row["path"]) for role, row in TOOLCHAIN_RUNTIME.items()}
    if any(tools[role]["sha256"] != row["sha256"] for role, row in TOOLCHAIN_RUNTIME.items()):
        raise RuntimeError("Official capture toolchain SHA differs")
    runner_binding, helper_binding, python_binding = (file_binding(path) for path in (runner_path, helper_path, python))
    proof_binding, manifest_binding = (file_binding(root / name) for name in ("PROOF_INPUTS.json", "ENGINE_INPUTS.json"))
    module_path = Path(*HEAVY["module"].split("."))
    source = frozen / "FrozenFoundation" / module_path.with_suffix(".lean")
    source_binding = file_binding(source)
    if source_binding["sha256"] != HEAVY["source_sha256"] or source.stat().st_size != HEAVY["source_bytes"]:
        raise RuntimeError("Original capture source bytes/SHA differ")
    build_root = (outputs / "gafnitao").resolve()
    setup_path = build_root / "ir" / module_path.with_suffix(".setup.json")
    if setup_path.exists():
        raise RuntimeError("Setup capture is only for a missing genuine stock setup")
    artifacts = {"olean": build_root / "lib/lean" / module_path.with_suffix(".olean"),
                 "ilean": build_root / "lib/lean" / module_path.with_suffix(".ilean"),
                 "c": build_root / "ir" / module_path.with_suffix(".c")}
    identity = {"runner": runner_binding, "helper": helper_binding, "python": python_binding,
                "project": str(project), "outputs": str(outputs), "run_id": run_id, "tools": tools}
    fingerprint = hashlib.sha256(json_bytes(identity)).hexdigest()
    directory = engine["dispatcher_python"].parent / "capture_public" / fingerprint
    config_path, policy_path, request_path = (directory / name for name in
        ("setup_capture309.json", "bridge_policy309.capture.json", "LauncherCapture.request.json"))
    config = {"schema": "jsp309.stock-setup-capture.v1", "release_root": str(root), "pins": pins,
              "runner": runner_binding, "helper": helper_binding, "proof": proof_binding, "engine_manifest": manifest_binding,
              "source": source_binding, "source_bytes": HEAVY["source_bytes"], "sysroot": str(sysroot), "tools": tools,
              "workspace": str(project), "build_root": str(build_root), "setup": str(setup_path),
              "artifacts": {key: str(path) for key, path in artifacts.items()}, "expected_child_exit": 86}
    policy = {"schema": "lakefront309.bridge.v1", "python": python_binding["path"], "python_sha256": python_binding["sha256"],
              "dispatcher": runner_binding["path"], "dispatcher_sha256": runner_binding["sha256"]}
    config_raw, policy_raw = json_bytes(config), json_bytes(policy)
    config_binding = {"path": str(config_path), "sha256": hashlib.sha256(config_raw).hexdigest()}
    policy_binding = {"path": str(policy_path), "sha256": hashlib.sha256(policy_raw).hexdigest()}
    bindings = [file_binding(engine[role]) for role in sorted(engine)] + [tools[role] for role in sorted(tools)]
    bindings += [python_binding, runner_binding, helper_binding, proof_binding, manifest_binding, config_binding, policy_binding]
    request = {"sysroot": str(sysroot), "expectedLeanGithash": pins["actual_compiler_commit"], "workspace": str(project),
               "configFile": "lakefile.toml", "heavyModule": HEAVY["module"], "heavyPackage": HEAVY["package"],
               "heavyLibrary": HEAVY["library"], "heavySource": source_binding, "dispatcher": str(engine["native_bridge_executable"]),
               "bridgePolicy": policy_binding, "dispatcherConfig": config_binding, "python": python_binding["path"],
               "hashHelper": str(engine["hash_helper_python"]), "adaptationFiles": bindings, "targets": ["Erdos374Research"]}
    request_raw = json_bytes(request)
    return {"engine": engine, "config": config, "policy": policy, "request": request,
            "writes": [(config_path, config_raw), (policy_path, policy_raw), (request_path, request_raw)],
            "bindings": bindings + [source_binding, {"path": str(request_path), "sha256": hashlib.sha256(request_raw).hexdigest()}],
            "command": [tools["stock_lean"]["path"], "--load-dynlib=" + tools["lake_shared"]["path"],
                        "-t0", "-j3", "-DautoImplicit=false", "--run", str(engine["lake_launcher_lean"]), str(request_path)],
            "environment": {"LAKEFRONT309_CONFIG": str(config_path), "LAKEFRONT309_BRIDGE_POLICY": str(policy_path),
                            "LAKEFRONT309_BRIDGE_POLICY_SHA256": policy_binding["sha256"],
                            "LEAN_PATH": str(sysroot / "lib/lean"), "JSP309_SETUP_CAPTURE": str(config_path),
                            "JSP309_SETUP_CAPTURE_SHA256": config_binding["sha256"]},
            "record_path": directory / "SETUP_CAPTURE.json"}


def validate_capture_argv(config: dict, argv: list[str]) -> None:
    if len(argv) != 12 or argv[:2] != ["-DElab.async=false", "-j1"]:
        raise RuntimeError("Setup capture requires the exact twelve-token stock Heavy call")
    if argv[3::2] != ["-o", "-i", "-c", "--setup", "--json"]:
        raise RuntimeError("Setup capture flag order differs from the stock Heavy call")
    expected = {2: config["source"]["path"], 4: config["artifacts"]["olean"],
                6: config["artifacts"]["ilean"], 8: config["artifacts"]["c"], 10: config["setup"]}
    for index, path in expected.items():
        if not Path(argv[index]).is_absolute() or Path(argv[index]).resolve() != Path(path).resolve():
            raise RuntimeError("Setup capture source/setup/artifact path mismatch")


def capture_payload(config: dict, argv: list[str]) -> dict:
    """Inspect the stock-written setup; never compile/export/create artifacts."""
    validate_capture_argv(config, argv)
    source = Path(config["source"]["path"])
    if (file_binding(source) != config["source"] or config["source"]["sha256"] != HEAVY["source_sha256"]
            or source.stat().st_size != HEAVY["source_bytes"]):
        raise RuntimeError("Setup capture source changed")
    setup_path = Path(config["setup"])
    check_setup(setup_path)
    for path in config["artifacts"].values():
        artifact = Path(path)
        if artifact.exists() or artifact.with_name(artifact.name + ".publish-pending").exists():
            raise RuntimeError("Stock facet must have cleared final Heavy outputs before capture")
    return {"schema": "jsp309.stock-setup-capture-record.v1", "status": "stock_setup_captured_expected_stop",
            "incoming_argv": argv, "stock_setup": {**file_binding(setup_path), "bytes": setup_path.stat().st_size},
            "source": config["source"], "expected_child_exit": 86,
            "proof_outputs_written": False, "not_a_proof_acceptance": True}
