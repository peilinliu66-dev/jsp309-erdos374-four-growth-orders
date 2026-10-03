# Sources and attribution

## Mathematical result

Fedir Yudin, [*Square products of factorials and a conjecture of Erdős and Graham*, arXiv:2610.01899v1](https://arxiv.org/html/2610.01899v1), 1 October 2026, supplies the mathematical solution followed by this formalization, through Theorems 1.1 and 1.2 and Corollary 1.3. Section 1 identifies the growth question for `3 ≤ k ≤ 6` as [Erdős problem 374](https://www.erdosproblems.com/374), identified in the prize catalogue as [JSP-000309](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000309). The formal endpoint has the four constant-factor conclusions `D₃(X) ≍ √X` and `D₄(X), D₅(X), D₆(X) ≍ X`.

The four- and six-factor constructions are the classical Erdős–Graham identities recalled in that paper. The five-factor construction is attributed there to Straus. The owned Lean modules verify positivity, distinctness and the required minimality separately from constructing a square product.

The Lean formalization contribution is attributed to `peilinliu66-dev`, with AI assistance. It formalizes these four order-of-growth conclusions. The mathematical solution and imported analytic theorems retain their authorship.

## Formal analytic dependencies

S. McColm's [`smccolm/Lean`](https://github.com/smccolm/Lean/tree/91604dfc9733555f0b762594cd434450728d3d8c) repository is fixed at commit `91604dfc9733555f0b762594cd434450728d3d8c`. The formalization uses its `73 Tao, 2026/Extension` project, the sibling `GafniTaoFrozen` project, frozen Riemann-zeta material and the nested PNT+ source tree.

This credits the reused Lean implementation separately from its underlying mathematical sources. Those sources retain the individual authorship documented in the pinned upstream source ledgers and theorem crosswalks, including Terence Tao's *Products of consecutive integers with unusual anatomy*, arXiv:2603.27990v2, and the analytic sources cited there.

The project records five explicit proof-body adaptations: `Tao2026/SylvesterSchurHundred.lean`, `Tao2026/ErdosSelfridgeHanson.lean`, `Tao2026/SylvesterSchurPrimeCountCertificatesSixA.lean`, `Tao2026/SylvesterSchurPrimeCountCertificatesSixB.lean` and `Tao2026/SylvesterSchurPrimeCountCertificatesSixC.lean`. The prime-count proofs retain their original eight/five/one theorem types and fixed pins, using shared short count increments closed with `norm_num only [sum_range_succ, if_true, if_false]`. The selected Hanson source is 179,493 bytes with SHA-256 `9ee2d58fbd0d5ae374ce8130872a583d220bc3b22f74b1d133868a67946cfcee`; its numerical proofs use 112 short blocks, 113 shared prefixes and two ordinary proved helper lemmas, with the two `NormNum.Prime` and `NormNum.BigOperators` imports from the same pinned Mathlib. Its recorded main-build marker is `Built Tao2026.ErdosSelfridgeHanson (250s)`. These proof-strategy adaptations retain the imported mathematical authorship. Their historical module compilation records are preserved separately from the completed integrated main build and final-target axiom command recorded in [AUDIT_REPORT.md](AUDIT_REPORT.md).

Those projects supply reciprocal exponential-sum estimates, all-interval short-prime results, character-sum bounds, uniform Pell estimates, factorial squarefree-part estimates, finite large-sieve results and the Erdős–Selfridge theorem. The source audits include the directly consumed analytic endpoints, such as:

- `Tao2026.vinogradovExponentialSumEstimate_unconditional`;
- `GafniTao.gafniTaoTheorem11_allIntervals_guthMaynard_native`;
- `Tao2026.erdosSelfridgeSquare`;
- `Tao2026.norm_primePolynomialCharacterCorrelation_le_of_monic_split_simple_root`.

Their names identify the imported theorem APIs. The actual final-target axiom output and integrated compilation result are recorded in [AUDIT_REPORT.md](AUDIT_REPORT.md). Labels within theorem names identify APIs; the observed endpoint printout supplies the reported final-target axiom closure. The optional expanded axiom inventory has not been executed for this release.

The owned `Erdos374Research` modules provide the literal original-problem interface, the ordered-representation correspondence, real-phase/Fourier adapters, long-block weights and mass estimates, arithmetic cancellation, cofactor and candidate-density arguments, short-block counting, minimality exclusions and the four-clause endpoint. The exposition in `MATHEMATICS.md` identifies the sufficient bounds used by this implementation.

Lean and Mathlib are credited to their respective contributors. The fixed toolchain is Lean 4.30.0, compiler commit `d024af099ca4bf2c86f649261ebf59565dc8c622`; Mathlib is fixed at `c5ea00351c28e24afc9f0f84379aa41082b1188f`. All other Git package revisions remain those in the original pinned manifest.

Blueprint metadata tooling comes from [`hanwenzhu/LeanArchitect`](https://github.com/hanwenzhu/LeanArchitect/tree/b72ae37b08d264cf371f164f4ba60c5257c17727) at commit `b72ae37b08d264cf371f164f4ba60c5257c17727`. Its nine imported tool modules are inventoried separately from the 1,691-module mathematical source cone.

## Source distribution

The release contains only the project-specific sources, documentation, reproduction tools and selected verification evidence. The analytic dependency is fetched separately from its pinned repository. Upstream papers, books, datasets and broad source snapshots are not bundled.

The upstream repository's [MIT-0 license](https://github.com/smccolm/Lean/blob/91604dfc9733555f0b762594cd434450728d3d8c/LICENSE) applies to its original repository material. Its [third-party notices](https://github.com/smccolm/Lean/blob/91604dfc9733555f0b762594cd434450728d3d8c/THIRD_PARTY_NOTICES.md) preserve the licensing of third-party material, including Apache-2.0 notices for adapted [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) source. Obtaining the pinned dependency retains those notices and the package licenses.

## AI assistance

ChatGPT and Codex assisted in preparing, reviewing and repairing the Lean formalization, writing reproduction tools and documentation, and analyzing compiler output. Mathematical authorship is credited above. Verification results in the report are tied to the actual main-build and final-target axiom-command records and complete original logs for the released source. The immutable proof URL in the official submission identifies the submitted source commit.

The integrated main build and the subsequent final-target axiom command both completed with natural exit 0. Their original evidence is [20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.json](evidence/main/20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.json), [20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.log](evidence/main/20261003T212801478173Z_full_cone_stock_lake_with_cached_frontend_native_lake.log), [20261003T213000253508Z_FINAL_TARGET_AXIOMS.json](evidence/endpoint/20261003T213000253508Z_FINAL_TARGET_AXIOMS.json) and [20261003T213000253508Z_FINAL_TARGET_AXIOMS.log](evidence/endpoint/20261003T213000253508Z_FINAL_TARGET_AXIOMS.log). The main reused previously compiled fixed-pin outputs and incrementally built the owned proof library. The optional public runner and expanded audit have not been executed for this release; exact process metadata and the observed endpoint axiom output are recorded in [AUDIT_REPORT.md](AUDIT_REPORT.md).
