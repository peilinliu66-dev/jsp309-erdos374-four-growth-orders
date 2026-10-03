# JSP309 / Erdős 374 audit report — actual release evidence

Release contract updated on 2026-10-04 for the four-order formalization. The integrated main build and one subsequent final-theorem endpoint axiom command using the existing audit entrypoint both completed with natural exit 0. Their actual process records and complete raw logs are linked below, with metadata taken directly from those records and the observed final-theorem axiom output quoted from the endpoint log. The immutable proof URL in the official submission identifies the submitted source commit.

## Statement and mathematical review

The endpoint is `Erdos374Research.erdos_374_original_growth : OriginalGrowthConclusion`. The reviewed definitions require positive distinct factorial indices, largest index `n`, and minimal representation size among all `k ≥ 2`. The original growth question is for `3 ≤ k ≤ 6`. The conclusion has precisely those four constant-factor clauses: `D₃(X) ≍ √X` and `D₄(X),D₅(X),D₆(X) ≍ X`, with positive real upper and lower constants and an eventual threshold. Its declaration has no additional mathematical premises.

Independent static reviews covered the D3/D4 sieve and summable-weight argument, ordered long-block weights and phase adapters, admissible and even-cofactor density, candidate supply, singleton cancellation, all-parameter exceptional-set counting, and D5/D6 minimality. No fatal mathematical gap was identified in those reviews. That is a source-review finding; compilation and imported trust closure require their actual outputs.

The mathematics follows Fedir Yudin's [arXiv:2610.01899v1](https://arxiv.org/html/2610.01899v1), dated 1 October 2026, Theorems 1.1 and 1.2 and Corollary 1.3. The repository's Lean formalization contribution is attributed to `peilinliu66-dev`, with the formal analytic dependencies and AI assistance credited in [SOURCE_ATTRIBUTION.md](SOURCE_ATTRIBUTION.md).

## Fixed inputs and configuration

| Input | Exact value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.30.0` |
| Actual compiler commit | `d024af099ca4bf2c86f649261ebf59565dc8c622` |
| Mathlib commit | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| Analytic source commit | `smccolm/Lean@91604dfc9733555f0b762594cd434450728d3d8c` |
| Version adjustments | None |

The analytic scope retains the full `73 Tao, 2026` project folder, including its sibling frozen dependency and nested PNT+ tree. The ten Git dependencies remain fixed at their original manifest revisions.

The two original `E:/Lean/.lake/...` dependency output directories are changed to task-local output directories. The Extension configuration adds the `Erdos374Research` library target. Original bytes, changed bytes and their hashes are retained; these are configuration changes for assembling and locating build outputs. A short physical Windows checkout is used because Lean cannot open some paths from the longer original location. Junction aliases alone do not shorten Lake's resolved paths.

The Tao2026 library uses `-DElab.async=false` and `-j1` to limit concurrent elaboration. The `Tao2026/SylvesterSchurHundred.lean` proof-body overlay uses a factorial closed certificate and an explicit five-prime construction. Its record identifies the pinned original bytes, exact patch and final source hash. Its theorem statements and dependency versions remain unchanged. All five selected proof-overlay records accompany the main-build evidence.

The final Hanson proof-body overlay uses 112 short blocks and 113 shared prefix certificates for the 25 finite bounds, with two ordinary proved helper lemmas for generic product identities. The remaining changed proof is the exact floor-loss absorption via `norm_num`. It imports `Mathlib.Tactic.NormNum.Prime` and `Mathlib.Tactic.NormNum.BigOperators` from the same pinned Mathlib. The selected source has SHA256 `9ee2d58fbd0d5ae374ce8130872a583d220bc3b22f74b1d133868a67946cfcee` and 179,493 bytes. A recorded main log contains `Built Tao2026.ErdosSelfridgeHanson (250s)`, and its compiled output is reused in the current main; this establishes that module's historical compilation. The completed integrated main process and final-target axiom command are recorded separately below.

The prime-count A/B/C overlays use shared short count increments closed with `norm_num only [sum_range_succ, if_true, if_false]`, retaining their original eight/five/one theorem types, assumptions and dependency pins. A starts from the already compiled `primeCounting 1133 = 189` certificate and covers the next 187 integers in 19 blocks of at most 16 integers each; its selected source is SHA256 `b9dfd0d50f45624eb16eef5b87290f2c33189dcdff115b86de4a4c45ffa20552`, 14,671 bytes. B uses the `primeCounting 1320 = 215` baseline and 31 blocks for 426 subsequent integers; its selected source is SHA256 `f723be59ebd0f97677d2b16eb0c2bd84ff3cc860ae01fb6fbf719a5b6bfb7666`, 22,713 bytes. C uses the `primeCounting 1746 = 271` baseline and 10 blocks for 160 subsequent integers; its selected source is SHA256 `9505a73faa89ad99dbf82cc93169240e016ce8677072c6c86baa73bc749d8420`, 7,907 bytes. Their portable records are `PRIME_COUNT_SIXA_PROOF_OVERLAY.json`, `PRIME_COUNT_SIXB_PROOF_OVERLAY.json` and `PRIME_COUNT_SIXC_PROOF_OVERLAY.json`; the selected modules were actually Built in 77, 262 and 138 seconds, respectively, in the main run started at 2026-10-03T19:48:50Z. All 1,625 external analytic modules had actually compiled before the final main command. Their fixed-pin outputs were reused by the final main, which built the owned proof library incrementally; the completed main and endpoint results are recorded below.

The prepared heavy-module execution integration uses a Lake launcher, cached frontend driver, Python dispatcher and Windows native bridge. Its two engine Lean files are outside the 66-module owned proof library. The launcher uses the fixed toolchain's official `libLake_shared.dll`. The actual main command, recorded working directory and complete log below describe the execution. It reuses the declared output root at the fixed pins, including previously compiled external analytic outputs and completed owned outputs, and incrementally builds the current owned source changes.

The reconstructed mathematical source cone has 1,691 modules: 66 owned library modules and 1,625 external analytic modules, comprising Tao 287, Gafni 964, frozen Riemann 291 and PNT 83. Nine Architect metadata/tool modules are inventoried separately. This inventory includes ordinary and `public import` edges. These are static source-inventory facts, not runtime or completed-build results.

## Observed release evidence

| Evidence | Current state |
|---|---|
| Original definition and four-clause scope correspondence | Independently reviewed in source |
| D3/D4, long-block, density and D5/D6 proof structure | Independently reviewed in source |
| Integrated main build | Completed; natural exit 0; [20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.json](evidence/main/20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.json) and [20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.log](evidence/main/20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.log) |
| Final-theorem endpoint axiom command | Completed after the main; natural exit 0; [20261003T213000253508Z_FINAL_TARGET_AXIOMS.json](evidence/endpoint/20261003T213000253508Z_FINAL_TARGET_AXIOMS.json) and [20261003T213000253508Z_FINAL_TARGET_AXIOMS.log](evidence/endpoint/20261003T213000253508Z_FINAL_TARGET_AXIOMS.log) |
| Independent heavy-module compile and kernel replay | Previously successful; historical evidence for that external module only |
| Expanded axiom inventory | Optional; not run for this release |
| Public reproduction runner | Optional; not run for this release |
| Submitted proof commit | Identified by the immutable proof URL in the official submission; evidence links are relative to that source snapshot |

The historical heavy-module records are `verification/build309/REAL_HEAVY_COMPILE_RESULT.json` and `verification/build309/REAL_CLEAN_HEAVY_KERNEL_RESULT.json`, with the independent review in `verification/ROOT_REAL_CLEAN_KERNEL_REVIEW.json`. The observed heavy OLean SHA256 is `a48abb2c7747ff57eaa891d2cee634bdd2c13b2a70f056b405569fd110bbc52b`. The compile had clean natural-zero output and an official Lake `Built` marker; the selected official kernel replay had natural exit 0 and the exact module marker. These historical results cover that external module; the completed integrated main build has its separate process record and complete raw log below.

The immutable proof URL supplied in the official submission identifies the actual submitted source and configuration commit. The relative links under `evidence/main/` and `evidence/endpoint/` preserve the original record and log filenames and refer to evidence in that same snapshot.

## Actual main and endpoint evidence

The final main uses the fixed Lean toolchain and the documented Windows execution integration. Its dependency outputs are reused from the declared task-local root at the fixed pins. All 1,625 external analytic modules had actually compiled before this final process; the 66-module owned proof library is built incrementally, with previously completed outputs reused. All five selected proof-body overlays have actual module compilation evidence: SylvesterSchurHundred was actually built, Hanson has the recorded 250-second `Built` marker, and prime-count A/B/C have the recorded 77/262/138-second `Built` markers. The independent heavy-module compile and official kernel replay remain separate historical evidence as recorded above.

The release contract requires complete raw output free of warning/error diagnostics, `PANIC`, `(deterministic) timeout` and invalid `MessageData`; natural exit zero alone does not establish that output condition. The links below retain the complete original raw output. This document fill reports the existing process metadata and endpoint printout; it does not execute another build, audit or reproduction command.

### Integrated main build

Process record: [20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.json](evidence/main/20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.json). Complete original raw log: [20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.log](evidence/main/20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.log).

The exact command arguments, as JSON from the process record, are:

```json
[
  "lake",
  "env",
  "lean",
  "-t0",
  "-j3",
  "-DElab.async=false",
  "--load-dynlib=C:\\Users\\28983\\.elan\\toolchains\\leanprover--lean4---v4.30.0\\bin\\libLake_shared.dll",
  "--run",
  "C:\\Users\\28983\\Documents\\ChatGPT\\孙宇晨奖\\JSP000309_audit_20261003\\verification\\lakefront309\\LakeFrontend309.lean",
  "C:\\Users\\28983\\Documents\\ChatGPT\\孙宇晨奖\\JSP000309_audit_20261003\\verification\\lakefront309\\LauncherReal.native.request.json"
]
```

| Recorded process field | Actual value |
|---|---|
| Working directory | `D:\L309\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\73 Tao, 2026\Extension` |
| Started UTC | `2026-10-03T21:28:01.478407+00:00` |
| Ended UTC | `2026-10-03T21:29:12.828344+00:00` |
| Status | `completed` |
| Natural exit code | `0` |
| Complete raw-log SHA-256 | `b0549bca6a8cc62750db87c6cf8e2759ac2b6f415bfab334e923d333b8a85e1f` |

### One final-theorem endpoint axiom command

Process record: [20261003T213000253508Z_FINAL_TARGET_AXIOMS.json](evidence/endpoint/20261003T213000253508Z_FINAL_TARGET_AXIOMS.json). Complete original raw log: [20261003T213000253508Z_FINAL_TARGET_AXIOMS.log](evidence/endpoint/20261003T213000253508Z_FINAL_TARGET_AXIOMS.log).

The exact command arguments, as JSON from the process record, are:

```json
[
  "lake",
  "env",
  "C:\\Users\\28983\\.elan\\toolchains\\leanprover--lean4---v4.30.0\\bin\\lean.exe",
  "-t0",
  "-j1",
  "-DElab.async=false",
  "-DautoImplicit=false",
  "D:\\L309\\Riemann Zeta\\9. Zero Density, Large Values and Prime Transfer\\73 Tao, 2026\\Extension\\Erdos374Audit.lean"
]
```

| Recorded process field | Actual value |
|---|---|
| Working directory | `D:\L309\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\73 Tao, 2026\Extension` |
| Started UTC | `2026-10-03T21:30:00.253731+00:00` |
| Ended UTC | `2026-10-03T21:30:24.137598+00:00` |
| Status | `completed` |
| Natural exit code | `0` |
| Complete raw-log SHA-256 | `1a60c7974c21b507083b24ad46bc7ed7a40de003164ecfb716763ef1fd9c3242` |

The following is the actual target axiom output extracted from the complete endpoint raw log (ANSI display escapes are omitted in this quotation; the linked raw bytes are unchanged):

```text
'Erdos374Research.erdos_374_original_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only this observed final-target output is reported here. The optional expanded inventory and public reproduction runner retain their unexecuted status below.

## Optional verification

Expanded declaration/runtime inventories, additional kernel replay, fresh owned-library rebuilds, standalone public reproduction and independent final seals are optional and are not publication prerequisites for this release. Expanded and public-runner execution have not been performed for this release. No successful reproduction or all-owned-module kernel replay is claimed here.

Historical failed or controlled-termination logs may be retained with their actual status.

