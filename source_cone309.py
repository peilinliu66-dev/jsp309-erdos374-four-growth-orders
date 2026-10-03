#!/usr/bin/env python3
"""Read-only, pure-Python normalized JSP309 source-cone support.

No CLI/main, subprocess, Git, Lean, Lake, network or result-file writes.
make_manifest returns an UNVERIFIED snapshot. A final auditor may freeze its
exact bytes only after the final sources/pins have actually been verified.
This is a lexical source graph, never a proof, build or runtime-import check.
"""
from __future__ import annotations

import hashlib
import copy
import json
import os
from pathlib import Path, PurePosixPath
import re

SCHEMA = "jsp309.source-cone.v1"
ROOT = "Erdos374Research"
COUNTS = {ROOT: 66, "Tao2026": 287, "GafniTao": 964,
          "RiemannZeta": 291, "PrimeNumberTheoremAnd": 83}
AUDITS = ("Erdos374Audit.lean", "ExpandedAxiomAudit.lean")
PACKAGE_SCOPE = "Direct source import boundary only; no transitive package cone or package kernel replay claimed."
IDENT = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
CORE_NAMESPACES = {"Init", "Lean", "Std", "Lake"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def valid_sha(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def valid_module(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(IDENT, value) is not None


def local(root: Path, relative: str) -> Path:
    part = PurePosixPath(relative)
    require(bool(relative) and not part.is_absolute() and ".." not in part.parts and
            "\\" not in relative and ":" not in relative and str(part) == relative,
            "Noncanonical relative source path")
    path = root.joinpath(*part.parts).resolve()
    require(path.is_relative_to(root.resolve()), "Source path leaves its bound root")
    return path


def parse_imports(raw: bytes) -> tuple[list[str], list[dict]]:
    """Consume only header tokens; body strings/chars cannot create imports.

    Supports the frozen ASCII module-name subset, nested comments, arbitrary
    whitespace, module/prelude and multiple same-line directives. Conservative
    multi-name inventory is separate from the stock Lean syntax/build gate.
    """
    text = raw.decode("utf-8").removeprefix("\ufeff")
    position, size = 0, len(text)
    identifier = re.compile(IDENT)

    def next_token() -> tuple[str, int, int] | None:
        nonlocal position
        while position < size:
            if text[position].isspace():
                position += 1
            elif text.startswith("--", position):
                stop = text.find("\n", position)
                position = size if stop < 0 else stop
            elif text.startswith("/-", position):
                depth, position = 1, position + 2
                while position < size and depth:
                    if text.startswith("/-", position):
                        depth, position = depth + 1, position + 2
                    elif text.startswith("-/", position):
                        depth, position = depth - 1, position + 2
                    else:
                        position += 1
                require(depth == 0, "Unclosed nested Lean header comment")
            else:
                start = position
                match = identifier.match(text, position)
                position = match.end() if match else position + 1
                return text[start:position], start, position
        return None

    token = next_token()
    if token and token[0] == "module":
        token = next_token()
    if token and token[0] == "prelude":
        token = next_token()
    reserved = {"module", "prelude", "import", "all", "public", "private", "meta", "section", "namespace",
                "def", "theorem", "lemma", "example", "opaque", "axiom", "constant", "inductive", "structure",
                "class", "instance", "open", "export", "set_option", "variable", "variables", "noncomputable", "end",
                "abbrev", "syntax", "macro", "elab", "macro_rules", "elab_rules", "attribute", "local", "scoped",
                "notation", "declare_syntax_cat", "infix", "infixl", "infixr", "prefix", "postfix", "initialize",
                "unsafe", "partial", "protected", "mutual", "deriving", "universe", "universes", "include", "omit"}
    directives = []
    while token:
        modifiers = []
        while token and token[0] in {"public", "private", "meta"}:
            modifiers.append(token[0])
            token = next_token()
        if not token or token[0] != "import":
            break  # The first body command, including public section.
        require(len(modifiers) == len(set(modifiers)), "Duplicate import modifier")
        require(not ("public" in modifiers and "private" in modifiers), "Contradictory import visibility")
        token = next_token()
        all_import = token is not None and token[0] == "all"
        if all_import:
            token = next_token()
        require(token is not None and valid_module(token[0]) and token[0] not in reserved,
                "Unsupported or malformed header module import")
        while token:
            name, _, last_end = token
            directives.append({"module": name, "public": "public" in modifiers,
                               "private": "private" in modifiers, "meta": "meta" in modifiers,
                               "all": all_import})
            token = next_token()
            if not token or "\n" in text[last_end:token[1]] or "\r" in text[last_end:token[1]]:
                break
            require(bool(text[last_end:token[1]]) and token[0] not in {"«", "»"} and token[0].isascii(),
                    "Unsupported adjacent/Unicode/quoted header token")
            require(token[0] not in {",", ".", "/", "\\"}, "Unsupported header import punctuation")
            if not valid_module(token[0]) or token[0] in reserved:
                break
    return sorted({row["module"] for row in directives}), directives


def source_record(module: str, namespace: str, root: Path, relative: str) -> dict:
    raw = local(root, relative).read_bytes()
    imports, directives = parse_imports(raw)
    return {"module": module, "scope": namespace, "path": relative,
            "bytes": len(raw), "sha256": sha(raw), "imports": imports,
            "import_directives": directives}


def index_namespace(root: Path, namespace: str) -> dict[str, str]:
    root = root.resolve()
    index = {}
    candidates = [root / (namespace + ".lean")]
    directory = root / namespace
    if directory.exists():
        for folder, directories, files in os.walk(directory, followlinks=False):
            directories[:] = sorted(name for name in directories if name not in {".git", ".lake", "__pycache__"})
            candidates.extend(Path(folder, name) for name in sorted(files) if name.endswith(".lean"))
    for path in candidates:
        if not path.is_file():
            continue
        relative = path.relative_to(root).as_posix()
        local(root, relative)
        module = relative[:-5].replace("/", ".")
        require(valid_module(module) and module.split(".")[0] == namespace,
                "Unsupported source module filename")
        require(module not in index, "Duplicate indexed source module")
        index[module] = relative
    return index


def compute_source_cone(roots: dict[str, Path], packages: dict[str, Path], *, require_audits: bool = True) -> dict:
    require(set(roots) == set(COUNTS), "Exactly five mathematical source roots are required")
    require("LeanArchitect" in packages, "Pinned LeanArchitect package root is required")
    index, providers = {}, {}
    for namespace, root in roots.items():
        for module, relative in index_namespace(root, namespace).items():
            require(module not in index, "Ambiguous mathematical module provider")
            index[module], providers[module] = relative, namespace
    pending, records, external = [ROOT], {}, set()
    while pending:
        module = pending.pop()
        if module in records:
            continue
        namespace = module.split(".")[0]
        if namespace not in roots:
            external.add(module)
            continue
        require(module in index, "Missing mathematical import source: " + module)
        record = source_record(module, providers[module], roots[namespace], index[module])
        records[module] = record
        pending.extend(record["imports"])
    own_index = index_namespace(roots[ROOT], ROOT)
    require({module for module in records if providers[module] == ROOT} == set(own_index),
            "Root cone does not cover every own source module")
    architecture = packages["LeanArchitect"]
    architect_index = index_namespace(architecture, "Architect")
    architect = [source_record(module, "Architect", architecture, relative)
                 for module, relative in sorted(architect_index.items())]
    for row in architect:
        external.update(row["imports"])
    audits = []
    for relative in AUDITS:
        path = local(roots[ROOT], relative)
        if not path.is_file():
            require(not require_audits, "Missing final own audit source: " + relative)
            continue
        raw = path.read_bytes()
        imports, directives = parse_imports(raw)
        # Audits must not expand the frozen mathematical graph beyond its root.
        require(all(name.split(".")[0] not in roots or name in records for name in imports),
                "Audit imports a mathematical module outside the original root cone")
        external.update(imports)
        audits.append({"path": relative, "bytes": len(raw), "sha256": sha(raw),
                       "imports": imports, "import_directives": directives})
    package_rows, core = [], []
    for module in sorted(external - set(records) - set(architect_index)):
        relative = module.replace(".", "/") + ".lean"
        matches = [(name, folder) for name, folder in packages.items() if local(folder, relative).is_file()]
        if matches:
            require(len(matches) == 1, "Ambiguous package provider: " + module)
            package, folder = matches[0]
            raw = local(folder, relative).read_bytes()
            package_rows.append({"module": module, "package": package, "path": relative,
                                 "bytes": len(raw), "sha256": sha(raw)})
        else:
            require(module.split(".")[0] in CORE_NAMESPACES, "Unresolved non-core package import: " + module)
            core.append(module)
    counts = {namespace: sum(row["scope"] == namespace for row in records.values()) for namespace in COUNTS}
    return {"roots": [ROOT], "math_module_count": len(records), "scope_counts": counts,
            "math_modules": [records[name] for name in sorted(records)],
            "own_audit_files": sorted(audits, key=lambda row: row["path"]),
            "architect_module_count": len(architect), "architect_modules": architect,
            "package_boundary": package_rows, "core_boundary": core,
            "package_scope": PACKAGE_SCOPE}


def proof_inventory_sha256(proof: dict) -> str:
    # PROOF_INPUTS binds SOURCE_CONE's file SHA. Hash only its final source
    # inventory here, avoiding an impossible bidirectional manifest hash cycle.
    files, modules = proof.get("files"), proof.get("own_modules")
    require(isinstance(files, dict) and isinstance(modules, list) and all(valid_module(name) for name in modules) and
            len(modules) == len(set(modules)), "Invalid final proof source inventory")
    for path, item in files.items():
        require(isinstance(path, str) and isinstance(item, dict) and set(item) == {"bytes", "sha256"} and
                type(item["bytes"]) is int and item["bytes"] >= 0 and valid_sha(item["sha256"]),
                "Invalid final proof source bytes/SHA256 metadata")
    raw = json.dumps({"files": files, "own_modules": sorted(modules)},
                     ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")
    return sha(raw)


def make_manifest(snapshot: dict, proof: dict, pins: dict) -> dict:
    return dict(copy.deepcopy(snapshot), schema=SCHEMA, status="unverified_source_snapshot",
                proof_source_inventory_sha256=proof_inventory_sha256(proof), pins=copy.deepcopy(pins))


def read_manifest(path: Path) -> dict:
    def unique(pairs: list[tuple[str, object]]) -> dict:
        result = {}
        for key, value in pairs:
            require(key not in result, "Duplicate SOURCE_CONE JSON field")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise RuntimeError("Non-JSON numeric constant in SOURCE_CONE: " + value)

    value = json.loads(path.read_bytes().decode("utf-8"), object_pairs_hook=unique, parse_constant=reject_constant)
    require(isinstance(value, dict), "SOURCE_CONE must be a JSON object")
    return value


def validate_manifest(value: dict, proof: dict, pins: dict,
                      snapshot: dict | None = None) -> None:
    fields = {"schema", "status", "proof_source_inventory_sha256", "pins", "roots", "math_module_count",
              "scope_counts", "math_modules", "own_audit_files", "architect_module_count",
              "architect_modules", "package_boundary", "core_boundary", "package_scope"}
    require(set(value) == fields and value["schema"] == SCHEMA and value["status"] == "verified",
            "SOURCE_CONE schema/verified status/fields mismatch")
    require(valid_sha(value["proof_source_inventory_sha256"]) and
            value["proof_source_inventory_sha256"] == proof_inventory_sha256(proof) and value["pins"] == pins,
            "SOURCE_CONE final proof manifest or fixed dependency pins mismatch")
    require(value["roots"] == [ROOT] and value["package_scope"] == PACKAGE_SCOPE,
            "SOURCE_CONE root or package coverage claim mismatch")
    require(type(value["math_module_count"]) is int and value["math_module_count"] == 1691 and
            isinstance(value["scope_counts"], dict) and set(value["scope_counts"]) == set(COUNTS) and
            all(type(count) is int for count in value["scope_counts"].values()) and value["scope_counts"] == COUNTS,
            "SOURCE_CONE must contain exact 1691 mathematical modules and five frozen scopes")

    def rows(items: object, scopes: set[str], is_audit: bool = False, is_package: bool = False) -> dict:
        require(isinstance(items, list), "SOURCE_CONE inventory must be an array")
        identities, parsed = [], {}
        for item in items:
            required = {"path", "bytes", "sha256"}
            if not is_package:
                required |= {"imports", "import_directives"}
            if not is_audit:
                required |= {"module", "package" if is_package else "scope"}
            require(isinstance(item, dict) and set(item) == required, "SOURCE_CONE source row fields mismatch")
            require(type(item["bytes"]) is int and item["bytes"] >= 0 and valid_sha(item["sha256"]),
                    "SOURCE_CONE source byte count/SHA256 mismatch")
            path = item["path"]
            require(isinstance(path, str) and path.endswith(".lean"), "Invalid SOURCE_CONE source path")
            part = PurePosixPath(path)
            require(not part.is_absolute() and ".." not in part.parts and ":" not in path and
                    "\\" not in path and str(part) == path, "Noncanonical SOURCE_CONE relative path")
            identity = path if is_audit else item["module"]
            if not is_audit:
                require(valid_module(identity) and path == identity.replace(".", "/") + ".lean",
                        "SOURCE_CONE module/path identity mismatch")
                owner = item["package" if is_package else "scope"]
                require(isinstance(owner, str) and owner in scopes, "SOURCE_CONE source ownership mismatch")
                if not is_package:
                    require(identity.split(".")[0] == owner, "SOURCE_CONE module namespace/scope mismatch")
            require(identity not in parsed, "Duplicate SOURCE_CONE source identity")
            if not is_package:
                imports, directives = item["imports"], item["import_directives"]
                require(isinstance(imports, list) and all(valid_module(name) for name in imports) and
                        imports == sorted(set(imports)) and isinstance(directives, list),
                        "SOURCE_CONE imports must be canonical unique module names")
                for directive in directives:
                    require(isinstance(directive, dict) and set(directive) == {"module", "public", "private", "meta", "all"} and
                            valid_module(directive["module"]) and
                            all(type(directive[key]) is bool for key in ("public", "private", "meta", "all")) and
                            not (directive["public"] and directive["private"]), "SOURCE_CONE import directive mismatch")
                require(imports == sorted({row["module"] for row in directives}),
                        "SOURCE_CONE imports disagree with directive inventory")
            identities.append(identity)
            parsed[identity] = item
        require(identities == sorted(identities), "SOURCE_CONE inventory is not sorted canonically")
        return parsed

    math = rows(value["math_modules"], set(COUNTS))
    require(len(math) == 1691 and {ns: sum(row["scope"] == ns for row in math.values()) for ns in COUNTS} == COUNTS,
            "SOURCE_CONE row count/scope distribution mismatch")
    architect = rows(value["architect_modules"], {"Architect"})
    require(type(value["architect_module_count"]) is int and value["architect_module_count"] == len(architect) == 9,
            "Architect metadata inventory must contain nine modules outside mathematical1691")
    audits = rows(value["own_audit_files"], set(), is_audit=True)
    require(set(audits) == set(AUDITS), "SOURCE_CONE must bind both own audit sources")
    packages = rows(value["package_boundary"], set(pins["git_dependencies"]), is_package=True)
    core = value["core_boundary"]
    require(isinstance(core, list) and all(valid_module(name) and name.split(".")[0] in CORE_NAMESPACES for name in core) and
            core == sorted(set(core)), "SOURCE_CONE core import boundary mismatch")
    sets = [set(math), set(architect), set(packages), set(core)]
    require(sum(map(len, sets)) == len(set().union(*sets)), "SOURCE_CONE inventories overlap")
    imported = {name for row in list(math.values()) + list(architect.values()) + list(audits.values()) for name in row["imports"]}
    require(imported - set(math) - set(architect) == set(packages) | set(core),
            "SOURCE_CONE external direct-import boundary is incomplete or has extras")
    reached, pending = set(), [ROOT]
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        require(module in math, "SOURCE_CONE mathematical import has no source row")
        reached.add(module)
        for imported_name in math[module]["imports"]:
            if imported_name.split(".")[0] in COUNTS:
                pending.append(imported_name)
    require(reached == set(math), "SOURCE_CONE contains unreachable or missing mathematical modules")
    own = {module for module, row in math.items() if row["scope"] == ROOT}
    files, modules = proof.get("files"), proof.get("own_modules")
    require(isinstance(files, dict) and len(files) == 68 and isinstance(modules, list) and
            len(modules) == len(set(modules)) == 66 and own == set(modules),
            "SOURCE_CONE differs from final 66 modules/68 source inputs")
    expected_paths = {math[module]["path"] for module in own} | set(AUDITS)
    require(set(files) == expected_paths, "SOURCE_CONE own source/audit file inventory mismatch")
    for row in [math[module] for module in own] + list(audits.values()):
        require(files[row["path"]] == {"bytes": row["bytes"], "sha256": row["sha256"]},
                "SOURCE_CONE contains stale own source/audit bytes: " + row["path"])
    if snapshot is not None:
        for key in fields - {"schema", "status", "proof_source_inventory_sha256", "pins"}:
            require(value[key] == snapshot.get(key), "Recomputed SOURCE_CONE differs from final frozen " + key)
