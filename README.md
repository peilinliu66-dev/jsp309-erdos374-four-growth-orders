# JSP309 / Erdős 374: four orders of factorial-square growth

This project formalizes the order-of-growth question for square products of distinct factorials. Its endpoint is

```lean
theorem Erdos374Research.erdos_374_original_growth :
    Erdos374Research.OriginalGrowthConclusion
```

The original question asks for the growth orders for `3 ≤ k ≤ 6`. The endpoint has exactly those four clauses: `D₃(X) ≍ √X` and `D₄(X), D₅(X), D₆(X) ≍ X`.

**Completed release verification.** The integrated main project build and the subsequent final-target axiom command both completed with natural exit 0. Their exact commands, working directories, UTC times, recorded log hashes and observed axiom output are recorded in [AUDIT_REPORT.md](AUDIT_REPORT.md). The original process records and complete raw logs are linked below.

## Exact problem statement

For `n ≥ 2`, let `F(n)` be the least `k ≥ 2` for which there are positive distinct indices

$$1\le a_1<a_2<\cdots<a_k=n$$

such that $\prod_{i=1}^{k}a_i!$ is a square. Following the mathematical source, put `F(n) = ∞` if no representation exists. Write

$$\mathcal D_k=\{n\ge2:F(n)=k\},\qquad D_k(X)=\#(\mathcal D_k\cap[1,X]).$$

[Definitions.lean](Erdos374Research/Definitions.lean) implements this directly through `HasRepresentation`, `IsInD`, and `countD`. A `Finset` enforces distinctness; every index is positive and at most `n`, and `n` belongs to the set. `IsInD k n` explicitly excludes every smaller representation size `j` with `2 ≤ j < k`. The equivalence with increasing tuples is proved in [OrderedRepresentations.lean](Erdos374Research/OrderedRepresentations.lean).

`HasOrder f g` means that there are **fixed positive real constants** `c, C` and a threshold after which

$$c\,g(X)\le f(X)\le C\,g(X).$$

Thus the final theorem proves the actual constant-factor orders requested in the [original problem](https://www.erdosproblems.com/374) and [JSP-000309 catalogue entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000309). Its statement has no additional mathematical premises. This scope does not include a leading asymptotic constant for `D₃`, limiting densities for `D₄,D₅,D₆`, or the paper's higher-power appendix.

## Mathematical source and formalization

The mathematical solution is Fedir Yudin's [*Square products of factorials and a conjecture of Erdős and Graham*, arXiv:2610.01899v1, 1 October 2026](https://arxiv.org/html/2610.01899v1), Theorems 1.1 and 1.2 and Corollary 1.3. The Lean formalization contribution is attributed to `peilinliu66-dev`, with AI assistance. It includes problem-specific representation interfaces, arithmetic cancellation, detecting-weight adapters, density and counting arguments, and the final assembly. [MATHEMATICS.md](MATHEMATICS.md) describes that chain. [SOURCE_ATTRIBUTION.md](SOURCE_ATTRIBUTION.md) distinguishes the mathematical source, classical constructions, imported analytic proofs and AI assistance.

## Fixed environment

| Component | Exact pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.30.0` |
| Actual Lean compiler commit | `d024af099ca4bf2c86f649261ebf59565dc8c622` |
| Mathlib | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| Analytic source repository | [`smccolm/Lean`](https://github.com/smccolm/Lean) |
| Analytic source commit | `91604dfc9733555f0b762594cd434450728d3d8c` |

These are the supplied project's versions; there is no version adjustment. The source overlay is assembled into the pinned upstream project

```text
Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/73 Tao, 2026/Extension
```

The sibling `Dependencies/GafniTaoFrozen` directory and its `PrimeNumberTheoremAndClean` subtree are retained. The ten Git packages remain at their original manifest revisions. Two upstream `buildDir` values referring to `E:/Lean/.lake/...` are adapted to a separate task-local output directory. The Extension adds the owned proof library, and Tao2026 uses `-DElab.async=false` and `-j1` for elaboration scheduling. The `Tao2026/SylvesterSchurHundred.lean` proof-body overlay uses a factorial closed certificate and an explicit five-prime construction; its theorem statements and dependency versions are unchanged.

The selected `Tao2026/ErdosSelfridgeHanson.lean` proof-body overlay has SHA-256 `9ee2d58fbd0d5ae374ce8130872a583d220bc3b22f74b1d133868a67946cfcee` and 179,493 bytes. It uses 112 short blocks, 113 shared prefixes and two ordinary proved helper lemmas, plus the exact floor-loss absorption proof, with `Mathlib.Tactic.NormNum.Prime` and `Mathlib.Tactic.NormNum.BigOperators` imported from the same pinned Mathlib. A recorded main log contains `Built Tao2026.ErdosSelfridgeHanson (250s)`; its compiled output is reused in the current main. This is a historical completed module result; the completed integrated main process and final-target axiom command are recorded below.

The prime-count proof-body overlays use shared count increments closed with `norm_num only [sum_range_succ, if_true, if_false]`, preserving their original theorem types, assumptions and dependency pins. `Tao2026/SylvesterSchurPrimeCountCertificatesSixA.lean`, SHA-256 `b9dfd0d50f45624eb16eef5b87290f2c33189dcdff115b86de4a4c45ffa20552`, 14,671 bytes, starts from the already compiled `primeCounting 1133 = 189` certificate and divides the next 187 integers into 19 short blocks of at most 16 integers each, retaining its eight target theorem types.

`Tao2026/SylvesterSchurPrimeCountCertificatesSixB.lean`, SHA-256 `f723be59ebd0f97677d2b16eb0c2bd84ff3cc860ae01fb6fbf719a5b6bfb7666`, 22,713 bytes, uses the `primeCounting 1320 = 215` baseline and 31 blocks for the next 426 integers, retaining five target theorem types. `Tao2026/SylvesterSchurPrimeCountCertificatesSixC.lean`, SHA-256 `9505a73faa89ad99dbf82cc93169240e016ce8677072c6c86baa73bc749d8420`, 7,907 bytes, uses the `primeCounting 1746 = 271` baseline and 10 blocks for the next 160 integers, retaining its one target theorem type. These three selected modules were actually Built in 77, 262 and 138 seconds, respectively, in the recorded main run started at 2026-10-03T19:48:50Z. All 1,625 external analytic modules had actually compiled before the final main command. The final main reused their fixed-pin outputs and built the owned proof library incrementally. The completed main result and endpoint output are recorded below.

The Windows integration uses a Lake launcher, a cached frontend driver, a Python dispatcher and a native bridge for the heavy source module. `ENGINE_INPUTS.json` records those execution inputs separately from the mathematical sources. The launcher loads the official `libLake_shared.dll` from the fixed Lean toolchain; that toolchain binary is not distributed as a project file. Previously compiled dependency outputs are reused from the declared output root at the fixed pins. The actual command, output root and reuse scope belong in the main-build evidence.

## Build and release evidence

The release contains the project-specific Lean sources, mathematical exposition, attribution and complete actual build evidence. Its final target is the declaration above, assembled by [FinalTheorem.lean](Erdos374Research/FinalTheorem.lean). Third-party analytic sources are obtained from the pinned repositories, with the documented proof-body overlay.

The integrated main build uses the fixed Lean toolchain and the documented Windows execution integration. Use a short **physical** work directory; a junction to a longer checkout does not shorten Lake's resolved paths. The release report provides the exact actual command and its recorded working directory, complete output, natural exit code, UTC times and log SHA-256 values. The final main used the declared fixed-pin output root, reusing the previously compiled 1,625 external analytic modules and completed owned outputs while incrementally building the owned source changes. Accepted build output must be free of warning/error diagnostics, `PANIC`, `(deterministic) timeout` and invalid `MessageData`; natural exit zero alone does not establish a clean build.

After the main build succeeded, one existing endpoint entrypoint obtained the actual axiom output for `Erdos374Research.erdos_374_original_growth`, with natural exit 0. Its exact command and complete raw output are included as evidence; [AUDIT_REPORT.md](AUDIT_REPORT.md) quotes the observed target axiom output directly from that log.

| Actual evidence | Process record | Complete raw log |
|---|---|---|
| Integrated main build | [20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.json](evidence/main/20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.json) | [20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.log](evidence/main/20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.log) |
| Final-theorem endpoint | [20261003T213000253508Z_FINAL_TARGET_AXIOMS.json](evidence/endpoint/20261003T213000253508Z_FINAL_TARGET_AXIOMS.json) | [20261003T213000253508Z_FINAL_TARGET_AXIOMS.log](evidence/endpoint/20261003T213000253508Z_FINAL_TARGET_AXIOMS.log) |

`PROOF_INPUTS.json`, `SOURCE_CONE.json`, `ENGINE_INPUTS.json` and the explicit upstream proof-overlay records describe source and execution inputs. The five overlay filenames are `UPSTREAM_PROOF_OVERLAY.json`, `HANSON_PROOF_OVERLAY.json`, `PRIME_COUNT_SIXA_PROOF_OVERLAY.json`, `PRIME_COUNT_SIXB_PROOF_OVERLAY.json` and `PRIME_COUNT_SIXC_PROOF_OVERLAY.json`; their records identify the selected sources above. Their hashes identify the distributed bytes; input metadata does not substitute for an actual successful process log. [AUDIT_REPORT.md](AUDIT_REPORT.md) records the two actual evidence processes. The immutable proof URL in the official submission is the identifier for the submitted source commit; these relative evidence links refer to files in that source snapshot.

## Optional reproduction and expanded audit tools

The prepared `reproduce.py` interface uses Python 3.11+, Git and the pinned elan/Lake toolchain, together with the Windows native bridge. Its default command is:

```powershell
python .\reproduce.py --work-dir D:/J309 --threads 3
```

`Erdos374Audit.lean` and `ExpandedAxiomAudit.lean` are available audit sources. The expanded entrypoint and optional runner support broader declaration inventories and official checker replay. The optional public runner and expanded audit have not been executed for this release; no public reproduction or expanded-audit PASS is claimed. They are available for reviewers and future use and are not additional release gates.

The separately completed heavy-module compile and official kernel replay are historical results for that module, documented in [AUDIT_REPORT.md](AUDIT_REPORT.md). The integrated main build and one final-target axiom command have their separate completed natural-zero records and complete raw logs above.

