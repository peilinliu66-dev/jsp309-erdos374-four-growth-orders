#!/usr/bin/env python3
"""Fetch separate pinned dependencies and reproduce the JSP309 source overlay.

DRAFT, NOT EXECUTION-TESTED. A release must place this script beside the final
Erdos374Research sources, both audit files, and verified PROOF_INPUTS.json.
Requires Python 3.11+, Git, and the pinned elan/Lake toolchain on PATH.
The frozen compiler adaptation currently supports Windows x64 only.
Any upstream proof-body overlay is explicitly recorded; theorem statements,
assumptions, dependency revisions and the Lean version remain unchanged.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import time
import tomllib

UPSTREAM_URL = "https://github.com/smccolm/Lean.git"
UPSTREAM_COMMIT = "91604dfc9733555f0b762594cd434450728d3d8c"
MATHLIB_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
TOOLCHAIN = "leanprover/lean4:v4.30.0"
COMPILER_COMMIT = "d024af099ca4bf2c86f649261ebf59565dc8c622"
SCOPE = PurePosixPath("Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/73 Tao, 2026")
PROJECT_REL = SCOPE / "Extension"
FROZEN_REL = SCOPE / "Dependencies/GafniTaoFrozen"
ROOT = "Erdos374Research"
ENDPOINT = ROOT + ".erdos_374_original_growth"
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COMPILED_OWN_MARKER = "JSP309_OWN_DECLARATIONS_JSON="
CONSTANT_KINDS = {"axiom", "definition", "theorem", "opaque", "quotient", "inductive", "constructor", "recursor"}
RIEMANN_WEAK_ARGS = ["-DElab.async=false", "-j1"]
TAO_WEAK_ARGS = ["-DElab.async=false", "-j1"]
TAO_SCHEDULING_ANCHOR = b'[[lean_lib]]\nname = "Tao2026"\n'
TAO_SCHEDULING_LINE = b'weakLeanArgs = ["-DElab.async=false", "-j1"]\n'
UPSTREAM_PROOF_OVERLAY = {
    "schema": "jsp309.upstream-proof-overlay.v1", "pinned_commit": UPSTREAM_COMMIT,
    "module": "Tao2026.SylvesterSchurHundred", "relative_path": "Tao2026/SylvesterSchurHundred.lean",
    "before_sha256": "8a01f7ca2f7d91053315b8e565d504d2d5d394673c976240b5fc8c2a6185461a", "before_bytes": 2424,
    "after_sha256": "1ce786579dda6b1487de56d80bb4577839630a4e8a2240426810fe44e5367d27", "after_bytes": 3755,
    "replacement_before": "  decide", "replacement_after": "first factorial closed certificate; second explicit five-prime construction", "replacement_count": 2,
    "statement_or_assumption_changes": False, "dependency_version_changes": False,
    "native_decide": False, "new_axioms": False,
}
HANSON_PROOF_OVERLAY = {
    "schema": "jsp309.upstream-proof-overlay.v1", "pinned_commit": UPSTREAM_COMMIT,
    "module": "Tao2026.ErdosSelfridgeHanson", "relative_path": "Tao2026/ErdosSelfridgeHanson.lean",
    "before_sha256": "8a02d5cbb402fcd213a9528c3d6ca9274a1deee545ffa4e5dad4f94a83f2f082", "before_bytes": 35862,
    "after_sha256": "9ee2d58fbd0d5ae374ce8130872a583d220bc3b22f74b1d133868a67946cfcee", "after_bytes": 179493,
    "replacement_before": "initial absorption decide; 25 numerical certificates (by decide)",
    "replacement_after": "initial absorption norm_num; 25 shared prefix certificates; 112 short blocks, 113 prefixes and two generic private proved helpers; Mathlib.Tactic.NormNum.Prime and BigOperators imports", "replacement_count": 26,
    "statement_or_assumption_changes": False, "dependency_version_changes": False,
    "native_decide": False, "new_axioms": False,
}
PRIME_COUNT_SIXA_PROOF_OVERLAY = {
    "schema": "jsp309.upstream-proof-overlay.v1", "pinned_commit": UPSTREAM_COMMIT,
    "module": "Tao2026.SylvesterSchurPrimeCountCertificatesSixA",
    "relative_path": "Tao2026/SylvesterSchurPrimeCountCertificatesSixA.lean",
    "before_sha256": "e06e31a9e6999b61774ca7047d1e8838b1218d6694690aca5caa81451fc83180", "before_bytes": 642,
    "after_sha256": "b9dfd0d50f45624eb16eef5b87290f2c33189dcdff115b86de4a4c45ffa20552", "after_bytes": 14671,
    "replacement_before": "by decide", "replacement_after": "short count increments from pi_1133", "replacement_count": 8,
    "statement_or_assumption_changes": False, "dependency_version_changes": False,
    "native_decide": False, "new_axioms": False,
}
PRIME_COUNT_SIXB_PROOF_OVERLAY = {
    "schema": "jsp309.upstream-proof-overlay.v1", "pinned_commit": UPSTREAM_COMMIT,
    "module": "Tao2026.SylvesterSchurPrimeCountCertificatesSixB",
    "relative_path": "Tao2026/SylvesterSchurPrimeCountCertificatesSixB.lean",
    "before_sha256": "9527c7d6d238d2a3cf21d4013a795ce4e788862016295dbffc21409c13dec9c3", "before_bytes": 458,
    "after_sha256": "f723be59ebd0f97677d2b16eb0c2bd84ff3cc860ae01fb6fbf719a5b6bfb7666", "after_bytes": 22713,
    "replacement_before": "by decide", "replacement_after": "short count increments from pi_1320", "replacement_count": 5,
    "statement_or_assumption_changes": False, "dependency_version_changes": False,
    "native_decide": False, "new_axioms": False,
}
PRIME_COUNT_SIXC_PROOF_OVERLAY = {
    "schema": "jsp309.upstream-proof-overlay.v1", "pinned_commit": UPSTREAM_COMMIT,
    "module": "Tao2026.SylvesterSchurPrimeCountCertificatesSixC",
    "relative_path": "Tao2026/SylvesterSchurPrimeCountCertificatesSixC.lean",
    "before_sha256": "88835a7aee7758e9e1a5c5284d77c28e552129ac4e99bb263cc1a8e638e058bf", "before_bytes": 214,
    "after_sha256": "9505a73faa89ad99dbf82cc93169240e016ce8677072c6c86baa73bc749d8420", "after_bytes": 7907,
    "replacement_before": "by decide", "replacement_after": "short count increments from pi_1746", "replacement_count": 1,
    "statement_or_assumption_changes": False, "dependency_version_changes": False,
    "native_decide": False, "new_axioms": False,
}
SYLVESTER_FACTORIAL_BODY = """  have certificate :
      ∀ H : Fin 101, 49 ≤ H.1 →
        (3 * H.1) ^ (H.1 + 1).primesBelow.card <
          (3 * H.1).factorial /
            (H.1.factorial * (3 * H.1 - H.1).factorial) := by
    decide +kernel
  intro H hH
  rw [Nat.choose_eq_factorial_div_factorial (by omega : H.1 ≤ 3 * H.1)]
  exact certificate H hH
"""
SYLVESTER_FIVE_PRIME_BODY = """  intro H N hH hHN hbelow
  have hHupper : H.1 < 101 := H.isLt
  have hNupper : N.1 < 200 := by omega
  have certificate (p : ℕ) (hp : p.Prime) (hNp : N.1 < p)
      (hpUpper : p ≤ N.1 + H.1) (hpBound : p < 301) :
      ∃ p : Fin 301, p.1.Prime ∧ H.1 < p.1 ∧
        p.1 ∣ consecutiveProduct N.1 H.1 := by
    refine ⟨⟨p, hpBound⟩, hp, by change H.1 < p; omega, ?_⟩
    change p ∣ (Finset.Ioc N.1 (N.1 + H.1)).prod (fun k : ℕ => k)
    exact Finset.dvd_prod_of_mem (fun k : ℕ => k)
      (Finset.mem_Ioc.mpr ⟨hNp, hpUpper⟩)
  by_cases h53 : N.1 < 53
  · exact certificate 53 (by norm_num) h53 (by omega) (by norm_num)
  by_cases h97 : N.1 < 97
  · exact certificate 97 (by norm_num) h97 (by omega) (by norm_num)
  by_cases h139 : N.1 < 139
  · exact certificate 139 (by norm_num) h139 (by omega) (by norm_num)
  by_cases h181 : N.1 < 181
  · exact certificate 181 (by norm_num) h181 (by omega) (by norm_num)
  exact certificate 223 (by norm_num) (by omega) (by omega) (by norm_num)
"""
BUILT_SUCCESS_LINE_RE = re.compile(
    r"^[✔ℹ][ \t]+(?:\[[0-9]+/[0-9]+\][ \t]+)?Built[ \t]+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*)[ \t]+"
    r"\([0-9]+(?:\.[0-9]+)?(?:ms|s)\)[ \t]*\r?$", re.M)
OVERLAY_TRAILER = b'\n# Original E374 source-only overlay.\n[[lean_lib]]\nname = "Erdos374Research"\n'
GIT_PINS = {
    "mathlib": ("https://github.com/leanprover-community/mathlib4.git", MATHLIB_COMMIT),
    "plausible": ("https://github.com/leanprover-community/plausible", "a456461b368b71d2accd95234832cd9c174b5437"),
    "LeanSearchClient": ("https://github.com/leanprover-community/LeanSearchClient", "c5d5b8fe6e5158def25cd28eb94e4141ad97c843"),
    "importGraph": ("https://github.com/leanprover-community/import-graph", "515cf9d0c00ece5e661f6de4326a53dedc1e8ea1"),
    "proofwidgets": ("https://github.com/leanprover-community/ProofWidgets4", "a84b3e2475d5c5ab979567b1ad8aea21b764bcf8"),
    "aesop": ("https://github.com/leanprover-community/aesop", "558915ae105bfd8074e22d597613d1961822adc2"),
    "Qq": ("https://github.com/leanprover-community/quote4", "a6e6c34c4ef182f83b219a3a5a385f51f44bdc4c"),
    "batteries": ("https://github.com/leanprover-community/batteries", "32dc18cde3684679f3c003de608743b57498c56f"),
    "Cli": ("https://github.com/leanprover/lean4-cli", "6b907cf12b2e445ccb7c24bc208ef04a1f39e84c"),
    "LeanArchitect": ("https://github.com/hanwenzhu/LeanArchitect.git", "b72ae37b08d264cf371f164f4ba60c5257c17727"),
}


def utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(part)
    return digest.hexdigest()


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def riemann_scheduling_config(config: bytes) -> bytes:
    """Append only the validated RiemannZeta library scheduling arguments."""
    anchor = b'[[lean_lib]]\nname = "RiemannZeta"\nsrcDir = "FrozenFoundation"\n'
    parsed = tomllib.loads(config.decode("utf-8"))
    libraries = [item for item in parsed.get("lean_lib", []) if item.get("name") == "RiemannZeta"]
    if (len(libraries) != 1 or libraries[0].get("srcDir") != "FrozenFoundation"
            or "weakLeanArgs" in libraries[0] or config.count(anchor) != 1):
        raise RuntimeError("Pinned RiemannZeta library configuration differs from the scheduling contract")
    line = b'weakLeanArgs = ["-DElab.async=false", "-j1"]\n'
    return config.replace(anchor, anchor + line)


def tao_scheduling_config(config: bytes) -> bytes:
    """Insert only Tao2026's validated sequential elaboration arguments."""
    parsed = tomllib.loads(config.decode("utf-8"))
    libraries = [item for item in parsed.get("lean_lib", []) if item.get("name") == "Tao2026"]
    if (len(libraries) != 1 or "weakLeanArgs" in libraries[0]
            or config.count(TAO_SCHEDULING_ANCHOR) != 1):
        raise RuntimeError("Pinned Tao2026 library configuration differs from the scheduling contract")
    return config.replace(TAO_SCHEDULING_ANCHOR, TAO_SCHEDULING_ANCHOR + TAO_SCHEDULING_LINE)


def load_upstream_proof_overlay(proof: dict, own: Path, cone_manifest: dict, cone, *,
                                expected: dict = UPSTREAM_PROOF_OVERLAY,
                                reference_key: str = "upstream_proof_overlay",
                                manifest_name: str = "UPSTREAM_PROOF_OVERLAY.json") -> dict | None:
    """Bind an explicitly hard-coded proof overlay without any source wildcard."""
    rows = [row for row in cone_manifest["math_modules"] if row["module"] == expected["module"]]
    if len(rows) != 1:
        raise RuntimeError("SOURCE_CONE omits or duplicates the exact upstream proof-overlay module")
    reference = proof.get(reference_key)
    if reference is None:
        if rows[0]["sha256"] != expected["before_sha256"] or rows[0]["bytes"] != expected["before_bytes"]:
            raise RuntimeError("Modified upstream proof source has no explicit frozen overlay binding")
        return None
    if (not isinstance(reference, dict) or set(reference) != {"path", "sha256"}
            or reference["path"] != manifest_name
            or not isinstance(reference["sha256"], str) or re.fullmatch(r"[0-9a-f]{64}", reference["sha256"]) is None):
        raise RuntimeError("Upstream proof overlay must bind its exact portable public manifest")
    path = local_path(own, reference["path"])
    if sha256(path) != reference["sha256"]:
        raise RuntimeError("Published upstream proof-overlay manifest SHA differs")
    value = cone.read_manifest(path)
    optional = {"utc", "exact_diff_sha256", "actual_compilation_verified"}
    if (not set(expected) <= set(value) <= set(expected) | optional
            or any(type(value[key]) is not type(frozen_value) or value[key] != frozen_value
                   for key, frozen_value in expected.items())):
        raise RuntimeError("Upstream proof overlay differs from its exact allowed module/patch binding")
    if (("utc" in value and not isinstance(value["utc"], str))
            or ("exact_diff_sha256" in value and (not isinstance(value["exact_diff_sha256"], str)
                or re.fullmatch(r"[0-9a-f]{64}", value["exact_diff_sha256"]) is None))
            or ("actual_compilation_verified" in value and type(value["actual_compilation_verified"]) is not bool)):
        raise RuntimeError("Upstream proof-overlay provenance fields have invalid types")
    if rows[0]["path"] != value["relative_path"] or rows[0]["sha256"] != value["after_sha256"] or rows[0]["bytes"] != value["after_bytes"]:
        raise RuntimeError("SOURCE_CONE does not bind the exact final upstream proof-overlay source")
    # Owner's historical actual_compilation_verified is metadata, never proof acceptance.
    return {"manifest_path": str(path), "manifest_sha256": reference["sha256"], "source_manifest": value}


def patched_upstream_proof_source(original: bytes) -> bytes:
    before = b"\n  decide\n"
    if (len(original) != UPSTREAM_PROOF_OVERLAY["before_bytes"]
            or hashlib.sha256(original).hexdigest() != UPSTREAM_PROOF_OVERLAY["before_sha256"]
            or original.count(before) != 2):
        raise RuntimeError("Upstream proof-overlay original is not the exact pinned Git source")
    parts = original.split(before)
    patched = (parts[0] + b"\n" + SYLVESTER_FACTORIAL_BODY.encode("utf-8") + parts[1]
               + b"\n" + SYLVESTER_FIVE_PRIME_BODY.encode("utf-8") + parts[2])
    if len(patched) != UPSTREAM_PROOF_OVERLAY["after_bytes"] or hashlib.sha256(patched).hexdigest() != UPSTREAM_PROOF_OVERLAY["after_sha256"]:
        raise RuntimeError("Derived upstream proof overlay differs from the exact frozen final source")
    return patched


def patched_hanson_proof_source(original: bytes) -> bytes:
    """Reconstruct the exact bounded proof overlay; Lean proves generated numerals."""
    absorption = (b"theorem hansonFour_exact_initial_absorption :\n"
                  b"    3 ^ 7225 * hansonFourFloorLoss < hansonFourRatio ^ 1400 := by\n  decide")
    import_anchor = b"import Mathlib.Data.Nat.Choose.Multinomial\n"
    if (len(original) != HANSON_PROOF_OVERLAY["before_bytes"]
            or hashlib.sha256(original).hexdigest() != HANSON_PROOF_OVERLAY["before_sha256"]
            or original.count(absorption) != 1 or original.count(b"(by decide)") != 25
            or original.count(import_anchor) != 1):
        raise RuntimeError("Hanson proof-overlay original/literal counts differ from the exact pinned source")
    source = original.decode("utf-8")
    if "\r" in source:
        raise RuntimeError("Hanson pinned source must retain its exact LF bytes")
    source = source.replace(import_anchor.decode("utf-8"),
                            import_anchor.decode("utf-8")
                            + "import Mathlib.Tactic.NormNum.Prime\n"
                            + "import Mathlib.Tactic.NormNum.BigOperators\n", 1)
    source = source.replace(absorption.decode("utf-8"),
                            absorption[:-len(b"decide")].decode("utf-8")
                            + "norm_num [hansonFourFloorLoss, hansonFourRatio]", 1)
    marker = "theorem erdosSelfridgePrimeProduct_le_three_pow_below_1400"
    begin = source.index(marker)
    end = source.index("/-- Hanson's elementary theorem", begin)
    theorem = source[begin:end]
    pairs = list(re.finditer(r"\(L := (\d+)\) \(U := (\d+)\)", theorem))
    if len(pairs) != 25:
        raise RuntimeError("Hanson fixed finite certificate count differs")
    bounds = [(int(m.group(1)), int(m.group(2))) for m in pairs]
    checkpoints = sorted(set(range(0, 1400, 16)) | {u for _, u in bounds})
    if (checkpoints[0] != 0 or checkpoints[-1] != 1399
            or max(b - a for a, b in zip(checkpoints, checkpoints[1:])) > 16):
        raise RuntimeError("Hanson fixed short-block boundaries differ")
    helpers = """/-- A symbolic range identity for the bounded finite certificates below. -/
private theorem hansonCertificate_primeProduct_range (H : ℕ) :
    erdosSelfridgePrimeProduct H =
      (Finset.range H).prod (fun p => if p.Prime then p else 1) := by
  rw [erdosSelfridgePrimeProduct, Nat.primesBelow, Finset.prod_filter]

private theorem hansonCertificate_primeProduct_add (n m : ℕ) :
    erdosSelfridgePrimeProduct (n + m) =
      erdosSelfridgePrimeProduct n *
        (Finset.range m).prod (fun i => if (n + i).Prime then n + i else 1) := by
  rewrite [hansonCertificate_primeProduct_range, Finset.prod_range_add]
  rewrite [← hansonCertificate_primeProduct_range]
  rfl

private theorem hansonCertificate_prefix_0 : erdosSelfridgePrimeProduct 0 = 1 := by
  rfl

"""

    def prime(n: int) -> bool:
        return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))

    prefix = 1
    prefix_values = {0: 1}
    for start, finish in zip(checkpoints, checkpoints[1:]):
        length = finish - start
        value = 1
        for n in range(start, finish):
            if prime(n):
                value *= n
        helpers += f"""private theorem hansonCertificate_block_{start} :
    (Finset.range {length}).prod
      (fun i => if ({start} + i).Prime then {start} + i else 1) = {value} := by
  norm_num [Finset.prod_range_succ]

private theorem hansonCertificate_prefix_{finish} :
    erdosSelfridgePrimeProduct {finish} = {prefix * value} := by
  calc
    erdosSelfridgePrimeProduct {finish} =
        erdosSelfridgePrimeProduct {start} *
          (Finset.range {length}).prod
            (fun i => if ({start} + i).Prime then {start} + i else 1) :=
      hansonCertificate_primeProduct_add {start} {length}
    _ = erdosSelfridgePrimeProduct {start} * {value} :=
      congrArg (fun z : ℕ => erdosSelfridgePrimeProduct {start} * z)
        hansonCertificate_block_{start}
    _ = {prefix * value} := by
      rewrite [hansonCertificate_prefix_{start}]
      norm_num1

"""
        prefix *= value
        prefix_values[finish] = prefix
    for lower, upper in bounds:
        if prefix_values[upper] > 3 ** lower:
            raise RuntimeError("Hanson generated finite certificate numeral differs")
    for i in reversed(range(len(pairs))):
        start = pairs[i].start()
        finish = pairs[i + 1].start() if i + 1 < len(pairs) else len(theorem)
        segment = theorem[start:finish]
        if segment.count("(by decide)") != 1:
            raise RuntimeError("Hanson fixed certificate proof literal differs")
        replacement = f"""(by
        rewrite [hansonCertificate_prefix_{bounds[i][1]}]
        norm_num1)"""
        segment = segment.replace("(by decide)", replacement, 1)
        theorem = theorem[:start] + segment + theorem[finish:]
    source = source[:begin] + helpers + theorem + source[end:]
    patched = source.encode("utf-8")
    if len(patched) != HANSON_PROOF_OVERLAY["after_bytes"] or hashlib.sha256(patched).hexdigest() != HANSON_PROOF_OVERLAY["after_sha256"]:
        raise RuntimeError("Derived Hanson proof overlay differs from its exact frozen final source")
    return patched


def patched_prime_count_sixa_proof_source(original: bytes) -> bytes:
    """Reconstruct 19 proved short count blocks from pi_1133, preserving eight types."""
    return patched_prime_count_block_source(original, PRIME_COUNT_SIXA_PROOF_OVERLAY,
        "sixA", 1133, 1320, 189, "FiveC", "pi_1150")


def patched_prime_count_sixb_proof_source(original: bytes) -> bytes:
    return patched_prime_count_block_source(original, PRIME_COUNT_SIXB_PROOF_OVERLAY,
        "sixB", 1320, 1746, 215, "SixA", "pi_1380")


def patched_prime_count_sixc_proof_source(original: bytes) -> bytes:
    return patched_prime_count_block_source(original, PRIME_COUNT_SIXC_PROOF_OVERLAY,
        "sixC", 1746, 1906, 271, "SixB", "pi_1906")


def patched_prime_count_block_source(original: bytes, expected: dict, label: str,
                                     base: int, last: int, base_count: int,
                                     base_module: str, first_name: str) -> bytes:
    """Generate only the three explicit, SHA-bound prime-count overlays above."""
    if (len(original) != expected["before_bytes"]
            or hashlib.sha256(original).hexdigest() != expected["before_sha256"]
            or original.count(b"by decide") != expected["replacement_count"]):
        raise RuntimeError(label + " proof-overlay original/literal count differs from the exact pinned source")
    source = original.decode("utf-8")
    import_anchor = f"import Tao2026.SylvesterSchurPrimeCountCertificates{base_module}\n"
    if "\r" in source or source.count(import_anchor) != 1:
        raise RuntimeError(label + " pinned LF source/import anchor differs")
    targets = list(re.finditer(r"theorem (pi_\d+) : Nat\.primeCounting ([\d_]+) = (\d+) := by decide", source))
    if len(targets) != expected["replacement_count"]:
        raise RuntimeError(label + " fixed theorem count differs")
    bounds = [(m.group(1), int(m.group(2).replace("_", "")), int(m.group(3))) for m in targets]
    checkpoints = sorted(set(range(base, last + 1, 16)) | {n for _, n, _ in bounds})
    if (checkpoints[0] != base or checkpoints[-1] != last
            or (label == "sixA" and len(checkpoints) != 20)):
        raise RuntimeError(label + " fixed short-block endpoints differ")
    helpers = f"""/-- Count only the short increment after an already proved prime-count prefix. -/
private theorem {label}_certificate_count_add (n m : ℕ) :
    Nat.primeCounting (n + m) = Nat.primeCounting n +
      (Finset.range m).sum (fun i => if (n + 1 + i).Prime then 1 else 0) := by
  change Nat.count Nat.Prime (n + m + 1) = Nat.count Nat.Prime (n + 1) + _
  rewrite [show n + m + 1 = (n + 1) + m by omega, Nat.count_add]
  exact congrArg (fun z : ℕ => Nat.count Nat.Prime (n + 1) + z) (by
    rw [Nat.count_eq_card_filter_range, Finset.card_filter])

private theorem {label}_certificate_prefix_{base} : Nat.primeCounting {base} = {base_count} :=
  pi_{base}

"""

    def prime(n: int) -> bool:
        return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))

    count = base_count
    for start, finish in zip(checkpoints, checkpoints[1:]):
        length = finish - start
        if not 1 <= length <= 16:
            raise RuntimeError(label + " bounded increment length differs")
        increment = sum(prime(n) for n in range(start + 1, finish + 1))
        helpers += f"""private theorem {label}_certificate_block_{start} :
    (Finset.range {length}).sum
      (fun i => if ({start} + 1 + i).Prime then 1 else 0) = {increment} := by
  norm_num only [Finset.sum_range_succ, if_true, if_false]

private theorem {label}_certificate_prefix_{finish} :
    Nat.primeCounting {finish} = {count + increment} := by
  calc
    Nat.primeCounting {finish} = Nat.primeCounting {start} +
        (Finset.range {length}).sum
          (fun i => if ({start} + 1 + i).Prime then 1 else 0) :=
      {label}_certificate_count_add {start} {length}
    _ = Nat.primeCounting {start} + {increment} :=
      congrArg (fun z : ℕ => Nat.primeCounting {start} + z)
        {label}_certificate_block_{start}
    _ = {count + increment} := by
      rewrite [{label}_certificate_prefix_{start}]
      norm_num1

"""
        count += increment
        for _, endpoint, theorem_count in bounds:
            if endpoint == finish and count != theorem_count:
                raise RuntimeError(label + " generated finite count numeral differs")
    for match in reversed(targets):
        endpoint = int(match.group(2).replace("_", ""))
        declaration = match.group(0).split(" := by decide", 1)[0]
        source = (source[:match.start()] + declaration
                  + f" :=\n  {label}_certificate_prefix_{endpoint}" + source[match.end():])
    source = source.replace(import_anchor, import_anchor
                            + "import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise\n"
                            + "import Mathlib.Tactic.NormNum.Prime\n"
                            + "import Mathlib.Tactic.NormNum.BigOperators\n", 1)
    source = source.replace("theorem " + first_name, helpers + "theorem " + first_name, 1)
    patched = source.encode("utf-8")
    if len(patched) != expected["after_bytes"] or hashlib.sha256(patched).hexdigest() != expected["after_sha256"]:
        raise RuntimeError("Derived " + label + " proof overlay differs from its exact frozen final source")
    return patched


def durable_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("wb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def durable_json(path: Path, value: object) -> None:
    durable_bytes(path, (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))


def contained(path: Path, root: Path) -> Path:
    result = path.resolve()
    if not result.is_relative_to(root.resolve()):
        raise RuntimeError(f"Path leaves its intended directory: {path}")
    return result


def local_path(root: Path, relative: str) -> Path:
    part = PurePosixPath(relative)
    if part.is_absolute() or ".." in part.parts or "\\" in relative or ":" in relative:
        raise RuntimeError(f"Invalid relative input path: {relative}")
    return contained(root.joinpath(*part.parts), root)


def load_source_cone_helper(path: Path):
    spec = importlib.util.spec_from_file_location("jsp309_frozen_source_cone_helper", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load the frozen source-cone helper")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_engine_inputs_helper(path: Path):
    spec = importlib.util.spec_from_file_location("jsp309_frozen_engine_inputs_helper", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load the frozen engine-inputs helper")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_engine_calls(engine, runtime: dict, before: set[Path]) -> dict:
    """Recheck genuine dispatcher files; prototype status alone cannot pass."""
    records = sorted(set(runtime["calls_root"].glob("*/call.json")) - before)
    if len(records) > 1:
        raise RuntimeError("More than one new exact-heavy dispatcher call occurred in one public build")
    outputs = runtime["config"]["target"]["artifacts"]
    if not records:
        artifacts = {key: engine.file_binding(Path(path)) for key, path in outputs.items()}
        return {"new_call_count": 0, "calls": [], "artifacts": artifacts,
                "scope": "No new heavy child; existing exact-pinned heavy outputs were reused by the genuine stock facet."}
    dispatcher = load_engine_inputs_helper(runtime["engine"]["dispatcher_python"])
    _, reference = dispatcher.baseline_payloads(runtime["engine"]["baseline_report_inventory"].read_bytes(),
                                                runtime["engine"]["baseline_request_inventory"].read_bytes())
    accepted = []
    for path in records:
        record_sha = sha256(path)
        record = engine.read_json(path)
        if (not isinstance(record, dict) or record.get("schema") != "lakefront309.real-heavy.call.v1"
                or record.get("status") != "completed" or record.get("route") != "frozen_cached_sequential_frontend"
                or type(record.get("natural_exit_code")) is not int or record["natural_exit_code"] != 0
                or type(record.get("dispatch_return_code")) is not int or record["dispatch_return_code"] != 0
                or record.get("stream_errors") != [] or record.get("validation_errors") != []
                or record.get("bound_inputs_changed") is not False
                or record.get("bound_inputs_before") != record.get("bound_inputs_after")):
            raise RuntimeError("Dispatcher did not finish with genuine clean exit/bindings: " + str(path))
        config_path = runtime["writes"][0][0]
        if (record.get("config_path") != str(config_path) or record.get("config_sha256") != sha256(config_path)
                or record.get("selected_driver_path") != str(runtime["engine"]["cached_frontend_lean"])):
            raise RuntimeError("Dispatcher call is not bound to this public config/driver")
        call_dir = path.parent.resolve()
        request_path, report_path = call_dir / "frontend.request.json", call_dir / "frontend.report.json"
        request = engine.read_json(request_path)
        expected_request = dict(runtime["config"]["request_template"], report=str(report_path),
                                provisionalOlean=str(call_dir / "heavy.provisional.olean"))
        if request != expected_request or record.get("frontend_request_body") != expected_request:
            raise RuntimeError("Actual heavy Request differs from all seventeen frozen public fields")
        request_snapshot = record.get("frontend_request", {})
        if (request_snapshot.get("path") != str(request_path) or request_snapshot.get("sha256") != sha256(request_path)
                or request_snapshot.get("bytes") != request_path.stat().st_size):
            raise RuntimeError("Actual heavy Request bytes/hash differ from dispatcher metadata")
        expected_command = [runtime["config"]["stock_lean"], "-t0", "-j1", "-DElab.async=false", "--run",
                            str(runtime["engine"]["cached_frontend_lean"]), str(request_path)]
        if record.get("child_command") != expected_command:
            raise RuntimeError("Heavy child command differs; the Lake DLL belongs only to the launcher")
        raw_logs = record.get("raw_logs", {})
        for channel, filename in (("stdout", "stdout.raw.log"), ("stderr", "stderr.raw.log"),
                                  ("merged", "child.raw.log"), ("segments", "raw_segments.jsonl")):
            item = raw_logs.get(channel, {})
            actual = call_dir / filename
            if (item.get("path") != str(actual) or item.get("exists") is not True
                    or item.get("sha256") != sha256(actual) or item.get("bytes") != actual.stat().st_size):
                raise RuntimeError("Dispatcher raw log bytes/hash differ: " + channel)
            if channel != "segments":
                clean_raw_proof_output(actual.read_bytes(), "heavy_child_" + channel)
        rescanned = dispatcher.scan_raw_logs(raw_logs)
        if rescanned.get("passed") is not True or rescanned != record.get("raw_log_gate"):
            raise RuntimeError("Complete independent raw scan differs or rejects the heavy child")
        report = engine.read_json(report_path)
        declarations = dispatcher.validate_report_payload(report, cached=True, reference=reference)
        if not set(runtime["config"]["request_template"]["expectedNames"]).issubset(declarations):
            raise RuntimeError("Heavy report omits original named declarations")
        frontend_result = record.get("frontend_result", {})
        if (frontend_result.get("path") != str(report_path) or frontend_result.get("sha256") != sha256(report_path)
                or frontend_result.get("report") != report):
            raise RuntimeError("Heavy report bytes/contents differ from genuine dispatcher evidence")
        provisional_names = {"olean": "heavy.provisional.olean", "ilean": "heavy.provisional.olean.ilean", "c": "heavy.provisional.olean.c"}
        artifacts = {}
        for key, name in provisional_names.items():
            final, provisional = Path(outputs[key]), call_dir / name
            final_binding, provisional_binding = engine.file_binding(final), engine.file_binding(provisional)
            if final_binding["sha256"] != provisional_binding["sha256"] or final.stat().st_size != provisional.stat().st_size:
                raise RuntimeError("Final artifact is not byte-identical to its genuine provisional: " + key)
            for group, actual in (("output_artifacts", final), ("genuine_provisional_artifacts", provisional)):
                item = record.get(group, {}).get(key, {})
                if (item.get("path") != str(actual) or item.get("exists") is not True
                        or item.get("sha256") != sha256(actual) or item.get("bytes") != actual.stat().st_size):
                    raise RuntimeError("Genuine artifact metadata differs: " + group + "/" + key)
            artifacts[key] = {"final": final_binding, "provisional": provisional_binding, "bytes": final.stat().st_size}
        if sha256(path) != record_sha:
            raise RuntimeError("Dispatcher call metadata changed during verification")
        accepted.append({"path": str(path), "sha256": record_sha, "request": engine.file_binding(request_path),
                         "report": engine.file_binding(report_path), "raw_logs": raw_logs, "artifacts": artifacts,
                         "kernel_declaration_count": len(declarations), "natural_child_exit": 0, "dispatcher_exit": 0})
    return {"new_call_count": len(accepted), "calls": accepted,
            "scope": "Fresh genuine heavy child with complete raw/report/request/provisional/final bindings; no stock-ilean equivalence claim."}


def fixed_source_pins() -> dict:
    return {"upstream_commit": UPSTREAM_COMMIT, "mathlib_commit": MATHLIB_COMMIT,
            "toolchain": TOOLCHAIN, "actual_compiler_commit": COMPILER_COMMIT,
            "git_dependencies": {name: {"url": url, "rev": revision} for name, (url, revision) in sorted(GIT_PINS.items())}}


def check_setup_capture_result(engine, capture: dict, raw: bytes, natural_exit_code: int) -> dict:
    """Accept preparation only with Lake 1, stock-observed compiler 86 and real setup."""
    if type(natural_exit_code) is not int or natural_exit_code != 1:
        raise RuntimeError("Cold setup preparation must have its genuine expected Lake exit 1")
    dispatcher = load_engine_inputs_helper(capture["engine"]["dispatcher_python"])
    raw_scan = dispatcher.scan_raw_stream(io.BytesIO(raw))
    if raw_scan["fatal_matches"] or raw_scan["reached_eof"] is not True:
        raise RuntimeError("Stock setup preparation contains fatal raw diagnostics")
    normalized = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", raw.decode("utf-8"))
    compiler_codes = re.findall(r"^error:\s*Lean exited with code ([0-9]+)\s*$", normalized, re.M)
    if compiler_codes != ["86"]:
        raise RuntimeError("Stock facet did not report exactly one genuine capture compiler exit 86")
    capture_record_sha = sha256(capture["record_path"])
    captured = engine.read_json(capture["record_path"])
    if (not isinstance(captured, dict) or captured.get("schema") != "jsp309.stock-setup-capture-record.v1"
            or captured.get("status") != "stock_setup_captured_expected_stop"
            or type(captured.get("expected_child_exit")) is not int or captured["expected_child_exit"] != 86
            or captured.get("proof_outputs_written") is not False or captured.get("not_a_proof_acceptance") is not True
            or captured.get("config_sha256") != sha256(capture["writes"][0][0])
            or captured.get("source") != capture["config"]["source"]):
        raise RuntimeError("Natural Lake 1 is not the exact expected stock setup capture stop")
    engine.validate_capture_argv(capture["config"], captured["incoming_argv"])
    actual_setup = Path(capture["config"]["setup"])
    setup_binding = engine.file_binding(actual_setup)
    if captured.get("stock_setup") != {**setup_binding, "bytes": actual_setup.stat().st_size}:
        raise RuntimeError("Captured stock setup bytes/hash changed before strict real configuration")
    engine.check_setup(actual_setup)
    engine.verify_runtime(capture)
    if sha256(capture["record_path"]) != capture_record_sha:
        raise RuntimeError("Stock setup capture record changed during verification")
    return {"mode": "official_stock_facet_capture", "natural_launcher_exit": 1,
            "expected_capture_child_exit": 86, "observed_stock_facet_compiler_exit": 86,
            "record": engine.file_binding(capture["record_path"]), "setup": setup_binding,
            "raw_scan": raw_scan, "proof_acceptance_claimed": False}


def capture_setup_child(argv: list[str], environment: dict | None = None) -> int:
    """Hidden bridge child: capture stock-written setup and stop before Heavy.

    This path never calls runner.main, Lean, Lake, a subprocess or an exporter.
    Its fixed nonzero result is preparation evidence, not proof acceptance.
    """
    env = os.environ if environment is None else environment
    configured, expected = env.get("JSP309_SETUP_CAPTURE"), env.get("JSP309_SETUP_CAPTURE_SHA256")
    if not isinstance(configured, str) or not Path(configured).is_absolute() or not isinstance(expected, str) or re.fullmatch(r"[0-9a-f]{64}", expected) is None:
        raise RuntimeError("Setup capture requires its exact absolute policy and SHA256")
    config_path = Path(configured).resolve(strict=True)
    if sha256(config_path) != expected:
        raise RuntimeError("Setup capture policy SHA differs")
    # Resolve the helper beside this running source; no policy-selected code is loaded.
    helper_path = Path(__file__).resolve().with_name("engine_inputs309.py")
    raw_config = json.loads(config_path.read_bytes().decode("utf-8"))
    if not isinstance(raw_config, dict) or raw_config.get("helper") != {"path": str(helper_path), "sha256": sha256(helper_path)}:
        raise RuntimeError("Capture policy does not bind this runner's exact sibling helper")
    engine = load_engine_inputs_helper(helper_path)
    config = engine.read_json(config_path)
    expected_fields = {"schema", "release_root", "pins", "runner", "helper", "proof", "engine_manifest", "source", "source_bytes",
                       "sysroot", "tools", "workspace", "build_root", "setup", "artifacts", "expected_child_exit"}
    if (set(config) != expected_fields or config["schema"] != "jsp309.stock-setup-capture.v1"
            or config["pins"] != fixed_source_pins() or type(config["expected_child_exit"]) is not int or config["expected_child_exit"] != 86):
        raise RuntimeError("Setup capture policy schema/pins/expected-stop differs")
    root = Path(config["release_root"]).resolve(strict=True)
    capture_root = (root / "verification/lakefront309/capture_public").resolve()
    if not config_path.is_relative_to(capture_root) or config_path.name != "setup_capture309.json":
        raise RuntimeError("Setup capture policy is outside its exact public engineering directory")
    runner_binding = engine.file_binding(Path(__file__))
    if config["runner"] != runner_binding or config["proof"]["path"] != str(root / "PROOF_INPUTS.json") or config["engine_manifest"]["path"] != str(root / "ENGINE_INPUTS.json"):
        raise RuntimeError("Setup capture runner/proof/engine manifest path binding differs")
    for binding in (config["runner"], config["helper"], config["proof"], config["engine_manifest"], *config["tools"].values()):
        if engine.file_binding(Path(binding["path"])) != binding:
            raise RuntimeError("Bound setup capture input bytes changed")
    proof = engine.read_json(root / "PROOF_INPUTS.json")
    if (proof.get("status") != "verified" or proof.get("schema") != "jsp309-proof-inputs-v1"
            or proof.get("engine_inputs_helper_sha256") != config["helper"]["sha256"]
            or proof.get("engine_inputs_manifest_sha256") != config["engine_manifest"]["sha256"]):
        raise RuntimeError("Capture helper/engine bytes are not bound by the verified public proof inputs")
    engine.validate_manifest(engine.read_manifest(root / "ENGINE_INPUTS.json"), fixed_source_pins(), root)
    engine.check_lean_inventory(root, proof["files"])
    sysroot = Path(config["sysroot"]).resolve(strict=True)
    if config["tools"] != {role: engine.file_binding(sysroot / row["path"]) for role, row in engine.TOOLCHAIN_RUNTIME.items()}:
        raise RuntimeError("Capture toolchain paths differ")
    if any(config["tools"][role]["sha256"] != row["sha256"] for role, row in engine.TOOLCHAIN_RUNTIME.items()):
        raise RuntimeError("Capture original Lean/Lake DLL SHA differs")
    module_path = Path(*engine.HEAVY["module"].split("."))
    build_root = Path(config["build_root"]).resolve()
    expected_setup = build_root / "ir" / module_path.with_suffix(".setup.json")
    expected_artifacts = {"olean": build_root / "lib/lean" / module_path.with_suffix(".olean"),
                          "ilean": build_root / "lib/lean" / module_path.with_suffix(".ilean"),
                          "c": build_root / "ir" / module_path.with_suffix(".c")}
    if config["setup"] != str(expected_setup) or config["artifacts"] != {key: str(path) for key, path in expected_artifacts.items()}:
        raise RuntimeError("Capture setup/artifacts differ from stock module paths")
    if (config["source"]["sha256"] != engine.HEAVY["source_sha256"] or type(config["source_bytes"]) is not int
            or config["source_bytes"] != engine.HEAVY["source_bytes"] or Path.cwd().resolve() != Path(config["workspace"]).resolve(strict=True)):
        raise RuntimeError("Capture original source/workspace differs")
    source_relative = Path("FrozenFoundation") / module_path.with_suffix(".lean")
    source_path = Path(config["source"]["path"])
    if Path(*source_path.parts[-len(source_relative.parts):]) != source_relative:
        raise RuntimeError("Capture original source module suffix differs")
    record = engine.capture_payload(config, argv)
    record.update(config_sha256=expected, runner=runner_binding, helper=config["helper"],
                  original_toolchain=config["tools"], pid=os.getpid(), captured_utc=utc())
    record_path = config_path.parent / "SETUP_CAPTURE.json"
    if record_path.exists():
        raise RuntimeError("Refusing to overwrite earlier stock setup capture evidence")
    durable_json(record_path, record)
    if engine.file_binding(Path(config["setup"])) != {key: record["stock_setup"][key] for key in ("path", "sha256")} or sha256(config_path) != expected:
        raise RuntimeError("Stock setup/capture policy changed during capture")
    print("JSP309 stock setup captured; expected preparation stop (86).", file=sys.stderr, flush=True)
    return 86


def audit_targets(path: Path) -> list[str]:
    names = re.findall(r"^#print\s+axioms\s+(.+?)\s*$", path.read_text(encoding="utf-8"), re.M)
    if not names or len(names) != len(set(names)):
        raise RuntimeError(f"Empty or duplicate axiom target inventory: {path}")
    return names


def check_axioms(output: str, expected: list[str]) -> dict[str, list[str]]:
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    rows += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    actual: dict[str, list[str]] = {}
    for name, text in rows:
        if name in actual:
            raise RuntimeError(f"Duplicate printed axiom closure: {name}")
        closure = {item.strip() for item in text.split(",") if item.strip()}
        if not closure <= STD_AXIOMS:
            raise RuntimeError(f"Unexpected trust dependency for {name}: {sorted(closure)}")
        actual[name] = sorted(closure)
    if set(actual) != set(expected):
        raise RuntimeError(f"Axiom targets mismatch; missing={sorted(set(expected)-set(actual))}, extra={sorted(set(actual)-set(expected))}")
    return actual


def canonical_name_ast(value: object) -> str:
    """Validate the lossless Lean Name constructors, then encode their identity."""
    def validate(node: object) -> None:
        if node is None:
            return
        if not isinstance(node, dict) or len(node) != 1:
            raise RuntimeError("A canonical Name AST must be null or exactly one str/num constructor")
        kind, parts = next(iter(node.items()))
        if kind not in {"str", "num"} or not isinstance(parts, list) or len(parts) != 2:
            raise RuntimeError("Malformed canonical Name constructor")
        validate(parts[0])
        if kind == "str" and not isinstance(parts[1], str):
            raise RuntimeError("A Name.str component must be a string")
        if kind == "num" and (type(parts[1]) is not int or parts[1] < 0):
            raise RuntimeError("A Name.num component must be a natural number, not a boolean/string")
    validate(value)
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False)


def check_compiled_own_inventory(output: str, modules: list[str], named: list[str]) -> dict:
    # Display strings need not identify private/numeric Names injectively.
    # The existing #print gate remains separate; this inventory excludes no
    # kernel constant based on name flags, kind, visibility or zero axioms.
    lines = [line.rstrip("\r") for line in output.split("\n") if line.startswith(COMPILED_OWN_MARKER)]
    if len(lines) != 1:
        raise RuntimeError("Exactly one whole-line compiled-own JSON marker is required")

    def unique_object(pairs: list[tuple[str, object]]) -> dict:
        result = {}
        for key, value in pairs:
            if key in result:
                raise RuntimeError(f"Duplicate compiled-inventory JSON object field: {key}")
            result[key] = value
        return result

    def reject_non_json_constant(value: str) -> None:
        raise RuntimeError(f"Non-JSON numeric constant in compiled inventory: {value}")

    try:
        payload = json.loads(lines[0][len(COMPILED_OWN_MARKER):], object_pairs_hook=unique_object,
                             parse_constant=reject_non_json_constant)
    except (ValueError, TypeError) as error:
        raise RuntimeError("Malformed compiled-own JSON marker payload") from error
    if not isinstance(payload, dict) or payload.get("schema") != "jsp309.own-declarations.v1":
        raise RuntimeError("Compiled-own inventory schema mismatch")
    listed = payload.get("own_modules")
    if (len(modules) != 66 or len(modules) != len(set(modules)) or not isinstance(listed, list)
            or any(not isinstance(module, str) for module in listed) or len(listed) != len(set(listed))
            or set(listed) != set(modules) or type(payload.get("own_module_count")) is not int
            or payload["own_module_count"] != len(modules)):
        raise RuntimeError("Compiled-own module list/count differs from the complete frozen own inventory")
    rows = payload.get("declarations")
    if (not isinstance(rows, list) or not rows or type(payload.get("declaration_count")) is not int
            or payload["declaration_count"] != len(rows)):
        raise RuntimeError("Compiled-own declaration count is empty or inconsistent")

    # Only the three fixed accepted axiom Names are encoded from their known
    # ordinary components. Actual declaration Names are never rebuilt from text.
    standard_asts = {}
    for axiom in STD_AXIOMS:
        value = None
        for part in axiom.split("."):
            value = {"str": [value, part]}
        standard_asts[axiom] = canonical_name_ast(value)
    identities, display_names = set(), set()
    module_indices, index_modules = {}, {}
    flags = ("is_private_name", "is_internal_name", "is_internal_detail_name",
             "has_numeric_name_part", "is_unsafe", "is_partial")
    for row in rows:
        if not isinstance(row, dict) or "name_ast" not in row:
            raise RuntimeError("Compiled-own declaration row or canonical name is missing")
        identity = canonical_name_ast(row["name_ast"])
        if identity in identities:
            raise RuntimeError("Duplicate canonical Name AST in compiled-own inventory")
        identities.add(identity)
        name = row.get("name_text")
        module, index = row.get("module"), row.get("module_index")
        if not isinstance(name, str) or not isinstance(module, str) or module not in modules:
            raise RuntimeError("Compiled declaration display name/module ownership is invalid")
        if type(index) is not int or index < 0 or not isinstance(row.get("kind"), str) or row["kind"] not in CONSTANT_KINDS:
            raise RuntimeError("Compiled declaration module index or ConstantInfo kind is invalid")
        if any(type(row.get(flag)) is not bool for flag in flags):
            raise RuntimeError("Compiled declaration Name/safety flags must all be booleans")
        has_num, part = False, row["name_ast"]
        while part is not None:
            kind, values = next(iter(part.items()))
            has_num |= kind == "num"
            part = values[0]
        if row["has_numeric_name_part"] != has_num:
            raise RuntimeError("Numeric-name flag disagrees with the lossless Name AST")
        if module in module_indices and module_indices[module] != index:
            raise RuntimeError("One own module is assigned inconsistent imported-module indices")
        if index in index_modules and index_modules[index] != module:
            raise RuntimeError("One imported-module index is assigned different own modules")
        module_indices[module], index_modules[index] = index, module
        display_names.add(name)
        axioms, axiom_asts = row.get("axioms"), row.get("axiom_name_asts")
        if (not isinstance(axioms, list) or any(not isinstance(axiom, str) for axiom in axioms)
                or len(axioms) != len(set(axioms)) or not set(axioms) <= STD_AXIOMS
                or not isinstance(axiom_asts, list) or len(axiom_asts) != len(axioms)):
            raise RuntimeError(f"Unexpected or malformed compiled axiom closure for {name}")
        if any(canonical_name_ast(ast) != standard_asts[axiom] for axiom, ast in zip(axioms, axiom_asts)):
            raise RuntimeError(f"Compiled axiom text/canonical Name mismatch for {name}")
    missing = set(named) - display_names
    if missing:
        raise RuntimeError(f"Source-named own audits absent from compiled inventory: {sorted(missing)}")
    # An import-only own module may have zero rows. Presence in own_modules,
    # rather than a positive per-module count, is the required module gate.
    return payload


def check_replay(output: str, modules: list[str]) -> list[str]:
    # Lean 4.30 supports --verbose and --fresh; --help is not a help command.
    # A prefix target replays every matching module, so verify the whole set.
    replayed = re.findall(r"^replaying ([^\r\n]+)\s*$", output, re.M)
    if len(replayed) != len(set(replayed)) or set(replayed) != set(modules):
        raise RuntimeError(f"Kernel markers mismatch; expected {len(modules)} distinct modules, got {replayed}")
    return replayed


def check_no_diagnostics(output: str, label: str) -> None:
    # Inspect the rendered signal while preserving the exact log/marker bytes.
    # A natural zero exit can still contain failed metadata export or rendering.
    diagnostic_text = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", output)
    if re.search(r"\b(?:warning|error)\s*:", diagnostic_text, re.I):
        raise RuntimeError(f"Lean warning/error diagnostic in proof gate: {label}")
    if re.search(r"\bPANIC\b|\(deterministic\)\s+timeout\b|\binvalid\s+MessageData\b",
                 diagnostic_text, re.I):
        raise RuntimeError(f"Lean panic/timeout/message failure in proof gate: {label}")


def clean_raw_proof_output(raw: bytes, label: str) -> str:
    # Lossy decoding could conceal a damaged raw-success log. General Git/cache
    # output is separate; every successful proof stage uses this strict gate.
    output = raw.decode("utf-8")
    check_no_diagnostics(output, label)
    return output


def check_fresh_build(output: str, modules: list[str]) -> list[str]:
    built = [name for name in BUILT_SUCCESS_LINE_RE.findall(output) if name == ROOT or name.startswith(ROOT + ".")]
    if len(built) != len(modules) or len(built) != len(set(built)) or set(built) != set(modules):
        raise RuntimeError(f"Fresh-build markers mismatch; expected every owned module exactly once, got {built}")
    return built


class Evidence:
    def __init__(self, directory: Path, threads: int):
        self.directory = directory
        self.directory.mkdir(parents=True, exist_ok=False)
        self.env = dict(os.environ, LEAN_NUM_THREADS=str(threads), LAKE_ARTIFACT_CACHE="false")
        for key in ("LEAN_PATH", "LEAN_SRC_PATH", "ELAN_TOOLCHAIN", "LAKEFRONT309_CONFIG", "LAKEFRONT309_BRIDGE_POLICY",
                    "LAKEFRONT309_BRIDGE_POLICY_SHA256", "JSP309_SETUP_CAPTURE", "JSP309_SETUP_CAPTURE_SHA256"):
            self.env.pop(key, None)
        self.state: dict = {"status": "running", "started_utc": utc(), "runs": [], "version_adjustments": []}
        self.save()

    def save(self) -> None:
        durable_json(self.directory / "SUMMARY.json", self.state)

    def run(self, command: list[str], cwd: Path, label: str, *, env_overrides: dict | None = None,
            expected_exit_codes: tuple[int, ...] = (0,)) -> bytes:
        number = len(self.state["runs"])
        stem = self.directory / f"{number:03d}_{label}"
        log = stem.with_suffix(".log")
        command_env = dict(self.env)
        command_env.update(env_overrides or {})
        record = {"command": command, "cwd": str(cwd), "started_utc": utc(),
                  "status": "running", "log": str(log),
                  "environment": {key: command_env[key] for key in ("LEAN_NUM_THREADS", "LAKE_ARTIFACT_CACHE", "MATHLIB_CACHE_DIR",
                      "LAKEFRONT309_CONFIG", "LAKEFRONT309_BRIDGE_POLICY", "LAKEFRONT309_BRIDGE_POLICY_SHA256", "LEAN_PATH",
                      "JSP309_SETUP_CAPTURE", "JSP309_SETUP_CAPTURE_SHA256") if key in command_env}}
        if expected_exit_codes != (0,):
            record.update(stage_role="stock_setup_preparation", expected_exit_codes=list(expected_exit_codes))
        self.state["runs"].append(record)
        durable_json(stem.with_suffix(".json"), record)
        self.save()
        print(f"[{number:03d}] {label}: {command}", flush=True)
        started = time.monotonic()
        process = None
        try:
            with log.open("wb") as output:
                process = subprocess.Popen(command, cwd=cwd, env=command_env, stdout=output, stderr=subprocess.STDOUT)
                record["pid"] = process.pid
                durable_json(stem.with_suffix(".json"), record)
                self.save()
                while True:
                    try:
                        code = process.wait(timeout=5)
                        break
                    except subprocess.TimeoutExpired:
                        output.flush()
                        os.fsync(output.fileno())
                output.flush()
                os.fsync(output.fileno())
            record.update(status="completed", natural_exit_code=code, ended_utc=utc(),
                          elapsed_seconds=time.monotonic()-started, log_sha256=sha256(log))
        except BaseException as error:
            record.update(status="interrupted_or_failed_to_start", ended_utc=utc(), error=repr(error))
            # No successful natural exit is assigned to an interrupted command.
            if process is not None and process.poll() is None:
                process.terminate()
                record["forced_termination_exit_code"] = process.wait()
            durable_json(stem.with_suffix(".json"), record)
            self.save()
            raise
        durable_json(stem.with_suffix(".json"), record)
        self.save()
        if code not in expected_exit_codes:
            raise RuntimeError(f"Natural exit {code}; complete output: {log}")
        return log.read_bytes()

    def run_proof(self, command: list[str], cwd: Path, label: str, *, env_overrides: dict | None = None) -> str:
        raw = (self.run(command, cwd, label) if env_overrides is None
               else self.run(command, cwd, label, env_overrides=env_overrides))
        record = self.state["runs"][-1]
        try:
            output = clean_raw_proof_output(raw, label)
        except (UnicodeError, RuntimeError) as error:
            record["proof_raw_log_gate"] = {"status": "rejected", "error": repr(error)}
            durable_json(Path(record["log"]).with_suffix(".json"), record)
            self.save()
            raise
        # This certifies only this raw diagnostic gate, never the whole proof.
        record["proof_raw_log_gate"] = {"status": "clean"}
        durable_json(Path(record["log"]).with_suffix(".json"), record)
        self.save()
        return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--work-dir", type=Path, help="Separate physical checkout/output directory. On Windows use a short path such as D:/J309; required on Windows")
    parser.add_argument("--upstream-dir", type=Path, help="Optional existing exact pinned checkout; unexpected tracked/source changes are refused")
    parser.add_argument("--reuse-bound-output-root", type=Path, help="Explicit existing absolute output root; its gafnitao/pnt subdirectories retain verified warm external artifacts")
    parser.add_argument("--threads", type=int, default=3)
    parser.add_argument("--no-cache", action="store_true", help="Compile Mathlib imports instead of fetching the matching official Mathlib cache")
    parser.add_argument("--no-kernel-replay", action="store_true", help="Explicitly omit kernel replay; the resulting evidence records that omission")
    parser.add_argument("--external-kernel-replay", action="store_true", help="Also replay the selected external modules listed in PROOF_INPUTS.json")
    args = parser.parse_args()
    if os.name != "nt":
        parser.error("The frozen native compiler adaptation currently requires Windows x64")
    if args.threads < 1:
        parser.error("--threads must be positive")
    if args.external_kernel_replay and args.no_kernel_replay:
        parser.error("--external-kernel-replay cannot be combined with --no-kernel-replay")
    if os.name == "nt" and args.work_dir is None:
        parser.error("On Windows give --work-dir a short physical directory, for example D:/J309. A junction to a long checkout does not shorten Lake's resolved paths.")
    own = args.source_dir.expanduser().resolve()
    work = args.work_dir.expanduser().resolve() if args.work_dir else own / ".external-work"
    repo = args.upstream_dir.expanduser().resolve() if args.upstream_dir else work / "u"
    if work.is_relative_to(own) or repo.is_relative_to(own):
        parser.error("The checkout/output work directories must be outside the public source directory")
    project = repo.joinpath(*PROJECT_REL.parts)
    proof_path = own / "PROOF_INPUTS.json"
    proof = json.loads(proof_path.read_text(encoding="utf-8"))
    for key, expected in (("schema", "jsp309-proof-inputs-v1"), ("status", "verified"),
                          ("upstream_commit", UPSTREAM_COMMIT), ("mathlib_commit", MATHLIB_COMMIT),
                          ("toolchain", TOOLCHAIN), ("actual_compiler_commit", COMPILER_COMMIT)):
        if proof.get(key) != expected:
            raise RuntimeError(f"Published proof manifest does not match {key}={expected}")
    files = proof["files"]
    live_files = {ROOT + ".lean", "Erdos374Audit.lean", "ExpandedAxiomAudit.lean"}
    live_files.update(path.relative_to(own).as_posix() for path in (own / ROOT).rglob("*.lean"))
    if set(files) != live_files:
        raise RuntimeError("The manifest must bind every own Lean module and both complete audit entrypoints")
    for relative, expected in files.items():
        path = local_path(own, relative)
        if sha256(path) != expected["sha256"] or path.stat().st_size != expected["bytes"]:
            raise RuntimeError(f"Source does not match its published SHA-256 and byte count: {relative}")
    modules = sorted(relative[:-5].replace("/", ".") for relative in files if relative == ROOT + ".lean" or relative.startswith(ROOT + "/"))
    if modules != sorted(proof["own_modules"]) or len(modules) < 66:
        raise RuntimeError("Published own-module inventory is incomplete or differs from the actual source tree")
    endpoint_targets = audit_targets(own / "Erdos374Audit.lean")
    expanded_targets = audit_targets(own / "ExpandedAxiomAudit.lean")
    if sorted(endpoint_targets) != sorted(proof["endpoint_axiom_declarations"]) or ENDPOINT not in endpoint_targets:
        raise RuntimeError("Endpoint audit does not match the final manifest or omits the original-scope theorem")
    if sorted(expanded_targets) != sorted(proof["all_own_axiom_declarations"]):
        raise RuntimeError("All-own audit target inventory differs from the final manifest")
    if any(not name.startswith(ROOT + ".") and not name.startswith("_private.") for name in expanded_targets):
        raise RuntimeError("All-own axiom audit contains an unexpected namespace")
    if (own / "lean-toolchain").exists() and (own / "lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
        raise RuntimeError("The published source toolchain differs from the fixed compiler")
    proof_sha = sha256(proof_path)
    cone_path = own / "SOURCE_CONE.json"
    cone_helper_path = Path(__file__).resolve().with_name("source_cone309.py")
    for path, field in ((cone_path, "source_cone_manifest_sha256"),
                        (cone_helper_path, "source_cone_helper_sha256")):
        expected = proof.get(field)
        if not isinstance(expected, str) or re.fullmatch(r"[0-9a-f]{64}", expected) is None:
            raise RuntimeError(f"Published proof manifest omits the exact final {field}")
        if sha256(path) != expected:
            raise RuntimeError(f"Published source-cone input does not match its final SHA256: {path}")
    cone_sha = sha256(cone_path)
    cone_helper_sha = sha256(cone_helper_path)
    cone = load_source_cone_helper(cone_helper_path)
    cone_manifest = cone.read_manifest(cone_path)
    cone_pins = fixed_source_pins()
    cone.validate_manifest(cone_manifest, proof, cone_pins)
    proof_overlay = load_upstream_proof_overlay(proof, own, cone_manifest, cone)
    hanson_overlay = load_upstream_proof_overlay(proof, own, cone_manifest, cone,
        expected=HANSON_PROOF_OVERLAY, reference_key="hanson_proof_overlay", manifest_name="HANSON_PROOF_OVERLAY.json")
    prime_count_sixa_overlay = load_upstream_proof_overlay(proof, own, cone_manifest, cone,
        expected=PRIME_COUNT_SIXA_PROOF_OVERLAY, reference_key="prime_count_sixa_proof_overlay",
        manifest_name="PRIME_COUNT_SIXA_PROOF_OVERLAY.json")
    prime_count_sixb_overlay = load_upstream_proof_overlay(proof, own, cone_manifest, cone,
        expected=PRIME_COUNT_SIXB_PROOF_OVERLAY, reference_key="prime_count_sixb_proof_overlay",
        manifest_name="PRIME_COUNT_SIXB_PROOF_OVERLAY.json")
    prime_count_sixc_overlay = load_upstream_proof_overlay(proof, own, cone_manifest, cone,
        expected=PRIME_COUNT_SIXC_PROOF_OVERLAY, reference_key="prime_count_sixc_proof_overlay",
        manifest_name="PRIME_COUNT_SIXC_PROOF_OVERLAY.json")
    engine_path = own / "ENGINE_INPUTS.json"
    engine_helper_path = Path(__file__).resolve().with_name("engine_inputs309.py")
    for path, field in ((engine_path, "engine_inputs_manifest_sha256"), (engine_helper_path, "engine_inputs_helper_sha256")):
        expected = proof.get(field)
        if not isinstance(expected, str) or re.fullmatch(r"[0-9a-f]{64}", expected) is None or sha256(path) != expected:
            raise RuntimeError(f"Published proof manifest omits or differs from the exact {field}")
    engine_sha, engine_helper_sha = sha256(engine_path), sha256(engine_helper_path)
    engine = load_engine_inputs_helper(engine_helper_path)
    engine_manifest = engine.read_manifest(engine_path)
    engine.validate_manifest(engine_manifest, cone_pins, own)
    engine.check_lean_inventory(own, files)
    external_output_root = engine.output_root(work, args.reuse_bound_output_root.expanduser() if args.reuse_bound_output_root else None)
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    evidence = Evidence(own / "build-logs" / stamp, args.threads)
    evidence.state.update(proof_inputs_manifest_sha256=proof_sha, user_sources=files, own_modules=modules,
                          upstream_commit=UPSTREAM_COMMIT, mathlib_commit=MATHLIB_COMMIT,
                          toolchain=TOOLCHAIN, compiler_commit=COMPILER_COMMIT,
                          reproduction_script_sha256=sha256(Path(__file__)),
                          source_cone_manifest_sha256=cone_sha, source_cone_helper_sha256=cone_helper_sha,
                          engine_inputs_manifest_sha256=engine_sha, engine_inputs_helper_sha256=engine_helper_sha,
                          external_output_root=str(external_output_root), warm_external_output_root_requested=args.reuse_bound_output_root is not None,
                          runner_invocation={"executable": str(Path(sys.executable).resolve()), "argv": [str(Path(__file__).resolve()), *sys.argv[1:]]},
                          source_directory=str(own), work_directory=str(work), upstream_directory=str(repo),
                          mathlib_cache_requested=not args.no_cache, kernel_replay_requested=not args.no_kernel_replay)
    if proof_overlay is not None:
        evidence.state["upstream_proof_overlay_manifest_sha256"] = proof_overlay["manifest_sha256"]
    if hanson_overlay is not None:
        evidence.state["hanson_proof_overlay_manifest_sha256"] = hanson_overlay["manifest_sha256"]
    if prime_count_sixa_overlay is not None:
        evidence.state["prime_count_sixa_proof_overlay_manifest_sha256"] = prime_count_sixa_overlay["manifest_sha256"]
    if prime_count_sixb_overlay is not None:
        evidence.state["prime_count_sixb_proof_overlay_manifest_sha256"] = prime_count_sixb_overlay["manifest_sha256"]
    if prime_count_sixc_overlay is not None:
        evidence.state["prime_count_sixc_proof_overlay_manifest_sha256"] = prime_count_sixc_overlay["manifest_sha256"]
    evidence.save()
    durable_json(evidence.directory / "USER_SOURCES_AT_START.json", files)

    def run(command: list[str], cwd: Path, label: str) -> str:
        return evidence.run(command, cwd, label).decode("utf-8", errors="replace")

    def run_proof(command: list[str], cwd: Path, label: str, *, env_overrides: dict | None = None) -> str:
        return evidence.run_proof(command, cwd, label, env_overrides=env_overrides)

    def git_checkout(url: str, target: Path, revision: str, sparse: bool = False) -> None:
        def windows_path_check() -> None:
            if os.name != "nt":
                return
            command = ["git", "-c", "core.quotepath=false", "ls-tree", "-r", "--name-only", revision]
            if sparse:
                command += ["--", SCOPE.as_posix()]
            paths = run(command, target, "windows_physical_path_inventory").splitlines()
            too_long = []
            for relative in paths:
                if not relative.endswith(".lean"):
                    continue
                source = target.resolve().joinpath(*PurePosixPath(relative).parts)
                candidates = [source]
                relative_path = PurePosixPath(relative)
                if sparse and relative_path.is_relative_to(PROJECT_REL):
                    module = relative_path.relative_to(PROJECT_REL).with_suffix(".olean.private")
                    candidates.append(target.resolve().joinpath(*PROJECT_REL.parts) / ".lake/build/lib/lean" / str(module))
                elif sparse and relative_path.is_relative_to(FROZEN_REL / "PrimeNumberTheoremAndClean"):
                    module = relative_path.relative_to(FROZEN_REL / "PrimeNumberTheoremAndClean").with_suffix(".olean.private")
                    candidates.append(work / "output/pnt/lib/lean" / str(module))
                elif sparse and relative_path.is_relative_to(FROZEN_REL):
                    module = relative_path.relative_to(FROZEN_REL)
                    if module.is_relative_to("FrozenFoundation"):
                        module = module.relative_to("FrozenFoundation")
                    candidates.append(work / "output/gafnitao/lib/lean" / str(module.with_suffix(".olean.private")))
                elif not sparse:
                    # Package modules use the conventional output directory.
                    # Include private OLean suffixes when reserving path space.
                    candidates.append(target.resolve() / ".lake/build/lib/lean" / str(PurePosixPath(relative).with_suffix(".olean.private")))
                candidates = [path.resolve() for path in candidates]
                if any(len(str(path)) > 250 for path in candidates):
                    too_long.extend(str(path) for path in candidates if len(str(path)) > 250)
            if too_long:
                raise RuntimeError("Windows Lean paths exceed the 250-character margin. Use a shorter physical --work-dir/--upstream-dir, not a junction. Examples: " + repr(too_long[:3]))
        fresh = not target.exists()
        if fresh:
            target.parent.mkdir(parents=True, exist_ok=True)
            run(["git", "clone", "--no-checkout", "--filter=blob:none", url, str(target)], own, "clone_" + target.name)
            run(["git", "config", "core.longpaths", "true"], target, "longpaths_" + target.name)
            run(["git", "config", "core.autocrlf", "false"], target, "autocrlf_" + target.name)
            windows_path_check()
            if sparse:
                run(["git", "sparse-checkout", "init", "--cone"], target, "sparse_init")
                run(["git", "sparse-checkout", "set", SCOPE.as_posix()], target, "sparse_scope_with_sibling_dependencies")
            run(["git", "checkout", "--detach", revision], target, "checkout_" + target.name)
        actual = run(["git", "rev-parse", "HEAD"], target, "head_" + target.name).strip()
        if actual != revision:
            raise RuntimeError(f"Existing checkout {target} is at {actual}, required {revision}; use a separate checkout")
        if not fresh:
            windows_path_check()

    def verify_git_source_bytes(target: Path, revision: str, label: str,
                                scope: PurePosixPath | None = None,
                                permitted: dict[str, list[bytes]] | None = None,
                                allowed_extra: set[str] | None = None) -> dict[str, dict]:
        command = ["git", "ls-tree", "-r", "--full-tree", "-z", revision]
        if scope is not None:
            command += ["--", scope.as_posix()]
        raw = evidence.run(command, target, label + "_git_tree")
        tracked: dict[str, dict] = {}
        expected_sources = set()
        configurations = {"lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"}
        for entry in raw.split(b"\0"):
            if not entry:
                continue
            header, name = entry.split(b"\t", 1)
            mode, kind, blob = header.decode("ascii").split()
            relative = name.decode("utf-8")
            if not (relative.endswith(".lean") or PurePosixPath(relative).name in configurations):
                continue
            if kind != "blob" or mode not in ("100644", "100755"):
                raise RuntimeError(f"Relevant dependency source is not a regular pinned Git blob: {relative}")
            path = local_path(target, relative)
            if not path.is_file():
                raise RuntimeError(f"Relevant pinned dependency source is missing: {path}")
            actual = path.read_bytes()
            original_hash = blob.decode("ascii")
            permitted_bytes = (permitted or {}).get(relative, [])
            if git_blob_sha1(actual) != original_hash and actual not in permitted_bytes:
                raise RuntimeError(f"Dependency source bytes differ from the pinned Git blob (including hidden index edits): {path}")
            tracked[relative] = {"pinned_git_blob": original_hash, "actual_git_blob": git_blob_sha1(actual),
                                 "sha256": hashlib.sha256(actual).hexdigest(), "bytes": len(actual)}
            if relative.endswith(".lean"):
                expected_sources.add(relative)
        search_root = target.joinpath(*scope.parts) if scope is not None else target
        actual_sources = set()
        for folder, directories, names in os.walk(search_root, followlinks=False):
            directories[:] = [name for name in directories if name not in {".git", ".lake", "__pycache__", "node_modules"}]
            for name in names:
                if name.endswith(".lean"):
                    actual_sources.add(Path(folder, name).relative_to(target).as_posix())
        unexpected = actual_sources - expected_sources - (allowed_extra or set())
        if unexpected:
            raise RuntimeError(f"Unexpected untracked dependency Lean sources: {sorted(unexpected)[:5]}")
        durable_json(evidence.directory / (label + "_TRACKED_SOURCE_BYTES.json"), tracked)
        return tracked

    try:
        git_checkout(UPSTREAM_URL, repo, UPSTREAM_COMMIT, sparse=True)
        if (project / "lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
            raise RuntimeError("The pinned upstream toolchain is different")
        original_cfg: dict[str, bytes] = {}
        for relative in (PROJECT_REL / "lakefile.toml", FROZEN_REL / "lakefile.toml",
                         FROZEN_REL / "PrimeNumberTheoremAndClean/lakefile.toml", PROJECT_REL / "lake-manifest.json"):
            original_cfg[relative.as_posix()] = evidence.run(["git", "show", UPSTREAM_COMMIT + ":" + relative.as_posix()], repo, "pinned_configuration")
        manifest_bytes = original_cfg[(PROJECT_REL / "lake-manifest.json").as_posix()]
        if (project / "lake-manifest.json").read_bytes() != manifest_bytes:
            raise RuntimeError("Existing upstream manifest differs from the pinned Git blob")
        manifest = json.loads(manifest_bytes.decode("utf-8"))
        found_git_pins = {item["name"]: (item["url"], item["rev"]) for item in manifest["packages"] if item["type"] == "git"}
        if found_git_pins != GIT_PINS or len([item for item in manifest["packages"] if item["type"] == "git"]) != len(GIT_PINS):
            raise RuntimeError("The ten Git dependency pins differ from the recorded fixed environment")
        packages = (project / manifest["packagesDir"]).resolve()
        contained(packages, repo)
        for package in manifest["packages"]:
            if package["type"] == "git":
                target = packages / package["name"]
                git_checkout(package["url"], target, package["rev"])
                if run(["git", "diff", "--name-only", "HEAD", "--"], target, "tracked_dependency_changes").strip():
                    raise RuntimeError(f"Tracked dependency source was modified: {target}")
                verify_git_source_bytes(target, package["rev"], "initial_" + package["name"])
        frozen = repo.joinpath(*FROZEN_REL.parts)
        if not (frozen / "GafniTao/AllIntervals.lean").is_file() or not (frozen / "PrimeNumberTheoremAndClean/lake-manifest.json").is_file():
            raise RuntimeError("The pinned sibling GafniTaoFrozen/PNT+ trees are incomplete")
        project_config_rel = (PROJECT_REL / "lakefile.toml").as_posix()
        original = original_cfg[project_config_rel]
        config = tomllib.loads(original.decode("utf-8"))
        if any(item.get("name") == ROOT for item in config.get("lean_lib", [])):
            raise RuntimeError("Pinned upstream unexpectedly already defines the original-source overlay")
        scheduled = tao_scheduling_config(original)
        plain_overlay = original + OVERLAY_TRAILER
        integrated = scheduled + OVERLAY_TRAILER
        allowed_changes = {project_config_rel}
        adaptations = []
        execution_adaptations = [{"path": project_config_rel, "kind": "Lean elaboration scheduling only",
            "library": "Tao2026", "weakLeanArgs": TAO_WEAK_ARGS,
            "global_lean_num_threads": str(args.threads), "scope": "Only Tao2026 module child processes; other libraries retain their original arguments",
            "before_sha256": hashlib.sha256(original).hexdigest(), "after_sha256": hashlib.sha256(scheduled).hexdigest(),
            "proof_sources_changed": False, "version_adjustments": []}]
        permitted_output_configs = {}
        prepared_configs = []
        prepared_proof_overlays = []
        for overlay, expected, patcher, label in (
                (proof_overlay, UPSTREAM_PROOF_OVERLAY, patched_upstream_proof_source, "upstream"),
                (hanson_overlay, HANSON_PROOF_OVERLAY, patched_hanson_proof_source, "hanson"),
                (prime_count_sixa_overlay, PRIME_COUNT_SIXA_PROOF_OVERLAY, patched_prime_count_sixa_proof_source, "prime_count_sixa"),
                (prime_count_sixb_overlay, PRIME_COUNT_SIXB_PROOF_OVERLAY, patched_prime_count_sixb_proof_source, "prime_count_sixb"),
                (prime_count_sixc_overlay, PRIME_COUNT_SIXC_PROOF_OVERLAY, patched_prime_count_sixc_proof_source, "prime_count_sixc")):
            if overlay is None:
                continue
            relative = (PROJECT_REL / expected["relative_path"]).as_posix()
            original_source = evidence.run(["git", "show", UPSTREAM_COMMIT + ":" + relative], repo, "pinned_" + label + "_proof_overlay_source")
            patched_source = patcher(original_source)
            source_path = local_path(project, expected["relative_path"])
            if source_path.read_bytes() not in (original_source, patched_source):
                raise RuntimeError("Existing upstream proof source differs from its exact original/allowed patch: " + relative)
            allowed_changes.add(relative)
            prepared_proof_overlays.append((overlay, relative, original_source, patched_source, source_path, label))
        for relative, before, subdir in ((FROZEN_REL / "lakefile.toml", "E:/Lean/.lake/tao73-gafnitao-build", "gafnitao"),
                                        (FROZEN_REL / "PrimeNumberTheoremAndClean/lakefile.toml", "E:/Lean/.lake/tao73-pnt-build", "pnt")):
            key = relative.as_posix()
            old = original_cfg[key]
            needle = ("buildDir = " + json.dumps(before)).encode("utf-8")
            after = (external_output_root / subdir).resolve().as_posix()
            if old.count(needle) != 1:
                raise RuntimeError(f"Unexpected pinned buildDir field: {key}")
            portable = old.replace(needle, ("buildDir = " + json.dumps(after)).encode("utf-8"))
            changed = portable
            if subdir == "gafnitao":
                changed = riemann_scheduling_config(portable)
                execution_adaptations.append({"path": key, "kind": "Lean elaboration scheduling only",
                    "library": "RiemannZeta", "srcDir": "FrozenFoundation", "weakLeanArgs": RIEMANN_WEAK_ARGS,
                    "global_lean_num_threads": str(args.threads), "scope": "Only RiemannZeta module child processes; other libraries retain their original arguments",
                    "before_sha256": hashlib.sha256(portable).hexdigest(), "after_sha256": hashlib.sha256(changed).hexdigest(),
                    "proof_sources_changed": False, "version_adjustments": []})
            current = repo.joinpath(*relative.parts)
            if current.read_bytes() not in (old, portable, changed):
                raise RuntimeError(f"Unexpected tracked output/scheduling configuration edits: {current}")
            permitted_output_configs[key] = [old, portable, changed]
            prepared_configs.append((current, old, changed, subdir))
            allowed_changes.add(key)
            adaptations.append({"path": key, "kind": "output directory portability; any library scheduling is separately recorded", "before": before, "after": after,
                                "original_sha256": hashlib.sha256(old).hexdigest(), "portability_only_sha256": hashlib.sha256(portable).hexdigest(),
                                "modified_sha256": hashlib.sha256(changed).hexdigest()})
        if (project / "lakefile.toml").read_bytes() not in (original, plain_overlay, scheduled, integrated):
            raise RuntimeError("Unexpected existing lakefile overlay; use a fresh separate checkout")
        existing_sources = []
        for relative in files:
            source = local_path(own, relative)
            destination = local_path(project, relative)
            if destination.exists() and destination.read_bytes() != source.read_bytes():
                raise RuntimeError(f"Refusing to overwrite different own source: {destination}")
            existing_sources.append((source, destination))
        already_staged = {path.relative_to(project).as_posix() for path in (project / ROOT).rglob("*.lean")}
        if not already_staged <= {relative for relative in files if relative.startswith(ROOT + "/")}:
            raise RuntimeError("Unexpected extra own source exists in the external checkout")
        changes = set(run(["git", "diff", "--name-only", "HEAD", "--"], repo, "existing_tracked_upstream_changes").splitlines())
        if not changes <= allowed_changes:
            raise RuntimeError(f"Tracked upstream edits are outside the exact configuration/proof-overlay allowlist: {changes}")
        permitted_initial = {project_config_rel: [original, plain_overlay, scheduled, integrated]}
        permitted_initial.update(permitted_output_configs)
        for _overlay, relative, original_source, patched_source, _source_path, _label in prepared_proof_overlays:
            permitted_initial[relative] = [original_source, patched_source]
        overlay_paths = {(PROJECT_REL / relative).as_posix() for relative in files}
        verify_git_source_bytes(repo, UPSTREAM_COMMIT, "initial_upstream", SCOPE, permitted_initial, overlay_paths)
        if os.name == "nt":
            for relative in files:
                source_path = local_path(project, relative)
                output_path = (project / ".lake/build/lib/lean" / str(PurePosixPath(relative).with_suffix(".olean.private"))).resolve()
                if len(str(source_path)) > 250 or len(str(output_path)) > 250:
                    raise RuntimeError(f"An own source/output path exceeds the Windows 250-character margin: {relative}. Use a shorter physical work directory.")
        # Validate every known collision/configuration before the first write.
        for current, old, changed, subdir in prepared_configs:
            durable_bytes(evidence.directory / "original-configurations" / subdir / "lakefile.toml", old)
            durable_bytes(current, changed)
        durable_bytes(evidence.directory / "original-configurations" / "extension" / "lakefile.toml", original)
        durable_bytes(evidence.directory / "modified-configurations" / "extension" / "lakefile.toml", integrated)
        durable_bytes(project / "lakefile.toml", integrated)
        for overlay, relative, original_source, patched_source, source_path, label in prepared_proof_overlays:
            durable_bytes(evidence.directory / (label + "-proof-overlay") / "original.source.txt", original_source)
            durable_bytes(evidence.directory / (label + "-proof-overlay") / "patched.source.txt", patched_source)
            durable_bytes(source_path, patched_source)
            applied = dict(overlay, relative_path=relative, actual_source_path=str(source_path),
                           original_sha256=hashlib.sha256(original_source).hexdigest(),
                           patched_sha256=hashlib.sha256(patched_source).hexdigest(), proof_acceptance_claimed=False)
            durable_json(evidence.directory / (label.upper() + "_PROOF_OVERLAY_APPLIED.json"), applied)
            evidence.state[label + "_proof_overlay"] = applied
        for source, destination in existing_sources:
            if not destination.exists():
                durable_bytes(destination, source.read_bytes())
        staged = {path.relative_to(project).as_posix() for path in (project / ROOT).rglob("*.lean")}
        if staged != {relative for relative in files if relative.startswith(ROOT + "/")}:
            raise RuntimeError("Unexpected extra or missing own module in the external checkout")
        changes = set(run(["git", "diff", "--name-only", "HEAD", "--"], repo, "tracked_upstream_changes_after_overlay").splitlines())
        if changes != allowed_changes:
            raise RuntimeError("Actual tracked changes differ from the exact configuration/proof-overlay transformations")
        durable_json(evidence.directory / "PORTABILITY_AND_OVERLAY.json", {"version_adjustments": [], "output_directory_adaptations": adaptations,
                     "execution_option_adaptations": execution_adaptations,
                     "extension_lakefile_byte_patch": {
                         "offset_basis": "Original pinned Git bytes; apply inserts in descending offset order",
                         "original_configuration": "original-configurations/extension/lakefile.toml",
                         "modified_configuration": "modified-configurations/extension/lakefile.toml",
                         "original_sha256": hashlib.sha256(original).hexdigest(),
                         "scheduling_only_sha256": hashlib.sha256(scheduled).hexdigest(),
                         "modified_sha256": hashlib.sha256(integrated).hexdigest(),
                         "edits": [{"offset": original.index(TAO_SCHEDULING_ANCHOR) + len(TAO_SCHEDULING_ANCHOR),
                                    "delete_bytes": 0, "insert_utf8": TAO_SCHEDULING_LINE.decode("utf-8")},
                                   {"offset": len(original), "delete_bytes": 0, "insert_utf8": OVERLAY_TRAILER.decode("utf-8")}]},
                     "upstream_lakefile_sha256": hashlib.sha256(original).hexdigest(), "overlay_lakefile_sha256": sha256(project / "lakefile.toml")})
        evidence.state["output_directory_adaptations"] = adaptations
        evidence.state["execution_option_adaptations"] = execution_adaptations
        evidence.save()

        def check_static_source_cone(label: str) -> dict:
            if sha256(cone_path) != cone_sha or sha256(cone_helper_path) != cone_helper_sha:
                raise RuntimeError("Frozen SOURCE_CONE manifest or public helper changed during reproduction")
            roots = {ROOT: project, "Tao2026": project, "GafniTao": frozen,
                     "RiemannZeta": frozen / "FrozenFoundation",
                     "PrimeNumberTheoremAnd": frozen / "PrimeNumberTheoremAndClean"}
            actual = cone.compute_source_cone(roots, {name: packages / name for name in GIT_PINS})
            cone.validate_manifest(cone_manifest, proof, cone_pins, actual)
            path = evidence.directory / (label + ".json")
            durable_json(path, actual)
            return {"path": str(path), "sha256": sha256(path), "math_module_count": actual["math_module_count"],
                    "scope_counts": actual["scope_counts"], "architect_module_count": actual["architect_module_count"],
                    "package_boundary_count": len(actual["package_boundary"]), "package_scope": actual["package_scope"]}

        evidence.state["static_source_cone_before"] = check_static_source_cone("SOURCE_CONE_AT_START")
        evidence.save()
        # Resolve Lake only after replacing the two host-specific E:/ outputs.
        version = run(["lake", "env", "lean", "--version"], project, "actual_compiler_version")
        if re.search(r"version 4\.30\.0,", version) is None or COMPILER_COMMIT not in version:
            raise RuntimeError("Actual Lean compiler version or commit differs from the pin")
        run(["lake", "--version"], project, "actual_lake_version")
        sysroot_text = run(["lake", "env", "lean", "--print-prefix"], project, "actual_compiler_sysroot").strip()
        if not Path(sysroot_text).is_absolute():
            raise RuntimeError("Actual Lean installation prefix must be an explicit absolute path")
        sysroot = Path(sysroot_text).resolve(strict=True)
        if not args.no_cache:
            run(["lake", "exe", "cache", "get"], project, "matching_official_mathlib_cache")

        # The cold preparation uses the same genuine stock facet to write setup.
        # Its bridge child captures those bytes and deliberately stops before Heavy.
        # This preparation's natural nonzero exit is separate from proof success.
        try:
            runtime = engine.plan_runtime(engine_manifest, own, cone_pins, files,
                                          sysroot, Path(sys.executable), project, frozen, external_output_root)
            evidence.state["stock_setup_preparation"] = {"mode": "existing_stock_setup",
                "setup": runtime["setup_binding"], "capture_stage_executed": False}
        except engine.MissingStockSetup:
            capture = engine.plan_capture(engine_manifest, own, cone_pins, files, sysroot,
                Path(sys.executable), project, frozen, external_output_root, Path(__file__).resolve(), engine_helper_path, stamp)
            for path, raw in capture["writes"]:
                if path.exists():
                    raise RuntimeError(f"Fresh cold capture input already exists: {path}")
                durable_bytes(path, raw)
            if capture["record_path"].exists():
                raise RuntimeError("Fresh stock setup capture evidence already exists")
            engine.verify_runtime(capture)
            raw = evidence.run(capture["command"], project, "prepare_stock_setup_expected_stop",
                               env_overrides=capture["environment"], expected_exit_codes=(1,))
            evidence.state["stock_setup_preparation"] = check_setup_capture_result(engine, capture, raw,
                evidence.state["runs"][-1]["natural_exit_code"])
            runtime = engine.plan_runtime(engine_manifest, own, cone_pins, files,
                                          sysroot, Path(sys.executable), project, frozen, external_output_root)
        evidence.save()
        for path, raw in runtime["writes"]:
            if path.exists() and path.read_bytes() != raw:
                raise RuntimeError(f"Refusing to overwrite differing generated engine input: {path}")
            if not path.exists():
                durable_bytes(path, raw)
        engine.verify_runtime(runtime)
        calls_before = set(runtime["calls_root"].glob("*/call.json"))
        durable_json(evidence.directory / "ENGINE_RUNTIME_AT_START.json", {
            "engine_manifest_sha256": engine_sha, "engine_helper_sha256": engine_helper_sha,
            "bindings": runtime["bindings"], "command": runtime["command"],
            "environment": runtime["environment"], "request": runtime["request"],
            "config": runtime["config"], "policy": runtime["policy"], "stock_setup": runtime["setup_binding"],
            "stock_setup_preparation": evidence.state["stock_setup_preparation"]})

        # Force every own library module to elaborate afresh. Preserve old
        # artifacts rather than deleting them. Dependencies may retain their
        # matching build outputs; their actual reuse scope is recorded below.
        relocated = []
        build_root = contained(project / ".lake/build", project)
        for module in modules:
            path_parts = module.split(".")
            for folder in ("lib/lean", "ir"):
                prefix = build_root / folder
                prefix = prefix.joinpath(*path_parts)
                if prefix.parent.exists():
                    for artifact in sorted(prefix.parent.glob(prefix.name + ".*")):
                        if artifact.is_file():
                            checked = contained(artifact, build_root)
                            target = evidence.directory / "previous_own_outputs" / checked.relative_to(build_root)
                            target.parent.mkdir(parents=True, exist_ok=True)
                            item = {"original": str(checked), "preserved": str(target), "sha256": sha256(checked), "bytes": checked.stat().st_size}
                            shutil.move(str(checked), str(target))
                            relocated.append(item)
        durable_json(evidence.directory / "PRESERVED_OWN_OUTPUTS.json", relocated)
        # Existing exact-pinned dependency OLeans may be reused. The disabled
        # artifact cache and exact Built inventory ensure absent own outputs
        # cannot be silently restored from Lake's local artifact cache.
        freshly_built = check_fresh_build(run_proof(runtime["command"], project,
            "fresh_own_library_and_required_imports", env_overrides=runtime["environment"]), modules)
        engine.verify_runtime(runtime)
        evidence.state["stock_setup_sha256_unchanged_by_official_final_facet"] = True
        engine_calls = check_engine_calls(engine, runtime, calls_before)
        durable_json(evidence.directory / "ENGINE_DISPATCHER_CALLS.json", engine_calls)
        evidence.state["engine_dispatcher_calls"] = engine_calls
        evidence.save()
        endpoint_axioms = check_axioms(run_proof(["lake", "env", "lean", "-DautoImplicit=false", "Erdos374Audit.lean"], project, "endpoint_axiom_audit"), endpoint_targets)
        expanded_output = run_proof(["lake", "env", "lean", "-DautoImplicit=false", "ExpandedAxiomAudit.lean"], project, "all_own_axiom_audit")
        expanded_axioms = check_axioms(expanded_output, expanded_targets)
        compiled_own = check_compiled_own_inventory(expanded_output, modules, proof["all_own_axiom_declarations"])
        compiled_path = evidence.directory / "COMPILED_OWN_DECLARATIONS.json"
        durable_json(compiled_path, compiled_own)
        audit_record = evidence.state["runs"][-1]
        evidence.state.update(source_named_own_axiom_count=len(expanded_targets),
                              compiled_own_declaration_count=compiled_own["declaration_count"],
                              compiled_own_inventory_evidence={"path": str(compiled_path), "sha256": sha256(compiled_path),
                                  "schema": compiled_own["schema"], "own_module_count": compiled_own["own_module_count"],
                                  "proof_inputs_manifest_sha256": proof_sha, "audit_log": audit_record["log"],
                                  "audit_log_sha256": audit_record["log_sha256"], "audit_command_number": len(evidence.state["runs"])-1},
                              compiled_own_axiom_scope="All imported own kernel declarations, all ConstantInfo kinds and canonical Names; no filtering by private/internal/numeric flags.")
        evidence.save()
        replayed = []
        if not args.no_kernel_replay:
            replayed = check_replay(run_proof(["lake", "env", "leanchecker", "--verbose", ROOT], project, "all_own_kernel_replay"), modules)
        external_replays = []
        if args.external_kernel_replay:
            if args.no_kernel_replay:
                raise RuntimeError("--external-kernel-replay cannot be combined with --no-kernel-replay")
            selected = proof.get("external_kernel_replay_modules", [])
            if not selected or len(selected) != len(set(selected)):
                raise RuntimeError("The published selected external replay inventory is missing or duplicate")
            for module in selected:
                if not isinstance(module, str) or re.fullmatch(r"[A-Za-z0-9_.]+", module) is None or module == ROOT or module.startswith(ROOT + "."):
                    raise RuntimeError(f"Invalid selected external module name: {module}")
                actual = run_proof(["lake", "env", "leanchecker", "--verbose", module], project, "selected_external_kernel_replay")
                rows = re.findall(r"^replaying ([^\r\n]+)\s*$", actual, re.M)
                if module not in rows or len(rows) != len(set(rows)):
                    raise RuntimeError(f"Exact selected external module replay marker absent/duplicate: {module}")
                external_replays.append({"requested": module, "replayed": rows})
        for relative, expected in files.items():
            for path in (local_path(own, relative), local_path(project, relative)):
                if sha256(path) != expected["sha256"] or path.stat().st_size != expected["bytes"]:
                    raise RuntimeError(f"Source changed during reproduction: {path}")
        if sha256(proof_path) != proof_sha:
            raise RuntimeError("Published proof-input manifest changed during reproduction")
        for name, (_url, revision) in GIT_PINS.items():
            target = packages / name
            if run(["git", "rev-parse", "HEAD"], target, "final_dependency_head").strip() != revision:
                raise RuntimeError(f"Dependency HEAD changed during reproduction: {target}")
            if run(["git", "diff", "--name-only", "HEAD", "--"], target, "final_dependency_source_changes").strip():
                raise RuntimeError(f"Dependency tracked source changed during reproduction: {target}")
            verify_git_source_bytes(target, revision, "final_" + name)
        if run(["git", "rev-parse", "HEAD"], repo, "final_upstream_head").strip() != UPSTREAM_COMMIT:
            raise RuntimeError("Upstream HEAD changed during reproduction")
        final_changes = set(run(["git", "diff", "--name-only", "HEAD", "--"], repo, "final_upstream_changes").splitlines())
        if final_changes != allowed_changes:
            raise RuntimeError("Additional upstream tracked files changed during reproduction")
        if (project / "lake-manifest.json").read_bytes() != manifest_bytes or (project / "lakefile.toml").read_bytes() != integrated:
            raise RuntimeError("Pinned manifest or library-overlay configuration changed during reproduction")
        for item in adaptations:
            if sha256(repo.joinpath(*PurePosixPath(item["path"]).parts)) != item["modified_sha256"]:
                raise RuntimeError("A portability-only output configuration changed during reproduction")
        permitted_final = {project_config_rel: [integrated]}
        permitted_final.update({item["path"]: [changed] for item, (_current, _old, changed, _subdir) in zip(adaptations, prepared_configs)})
        for overlay, relative, _original_source, patched_source, source_path, _label in prepared_proof_overlays:
            if sha256(Path(overlay["manifest_path"])) != overlay["manifest_sha256"] or source_path.read_bytes() != patched_source:
                raise RuntimeError("Frozen upstream proof-overlay manifest/source changed during reproduction")
            permitted_final[relative] = [patched_source]
        verify_git_source_bytes(repo, UPSTREAM_COMMIT, "final_upstream", SCOPE, permitted_final, overlay_paths)
        for directory in (own, project):
            if {path.relative_to(directory).as_posix() for path in (directory / ROOT).rglob("*.lean")} != {relative for relative in files if relative.startswith(ROOT + "/")}:
                raise RuntimeError("The own-source inventory changed during reproduction")
        evidence.state["static_source_cone_after"] = check_static_source_cone("SOURCE_CONE_AT_END")
        if sha256(engine_path) != engine_sha or sha256(engine_helper_path) != engine_helper_sha:
            raise RuntimeError("Frozen engine manifest/helper changed during reproduction")
        engine.validate_manifest(engine_manifest, cone_pins, own)
        engine.check_lean_inventory(own, files)
        engine.verify_runtime(runtime)
        durable_json(evidence.directory / "ENGINE_RUNTIME_AT_END.json", {"bindings": runtime["bindings"], "before_after_sha256_equal": True})
        evidence.state.update(status="passed", ended_utc=utc(), endpoint_axioms=endpoint_axioms,
                              all_own_axioms=expanded_axioms, freshly_built_own_modules=freshly_built, replayed_own_modules=replayed,
                              selected_external_replays=external_replays,
                              kernel_replay_scope="Omitted by --no-kernel-replay." if args.no_kernel_replay else "Own module declarations against imported environments; --fresh is not used.",
                              build_scope="All own library modules elaborate afresh; required import cone built by Lake. Unrelated upstream All is not a target.",
                              dependency_cache_scope="Matching official Mathlib cache if requested; existing exact-pinned dependency outputs may be reused. Own outputs were preserved outside the build directory before build; LAKE_ARTIFACT_CACHE=false and exact Built markers require actual own compilation.")
        evidence.save()
        print(f"Build and named axiom audits passed. Kernel replay enabled: {not args.no_kernel_replay}. Evidence: {evidence.directory}", flush=True)
    except BaseException as error:
        evidence.state.update(status="failed_or_interrupted", ended_utc=utc(), error=repr(error))
        evidence.save()
        raise


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    if os.environ.get("JSP309_SETUP_CAPTURE") is not None:
        try:
            raise SystemExit(capture_setup_child(sys.argv[1:]))
        except Exception as error:
            print("JSP309 stock setup capture refused: " + repr(error), file=sys.stderr, flush=True)
            raise SystemExit(87)
    main()
