import Erdos374Research.RationalPhaseGeometry
import Erdos374Research.PrimeParameterRanges
import Erdos374Research.PrimeLogBudget

/-!
UNCOMPILED application-specific prime comparison for Yudin's separable weight.

Lean 4.30.0; Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
Tao2026 dependency: smccolm/Lean @ 91604dfc9733555f0b762594cd434450728d3d8c.
The analytic estimates and Fourier reconstruction are public source work of
S. McColm and their cited mathematical authors. The rational separation and
paired two-dimensional assembly adapt these inputs to Yudin's argument.

The final estimate has explicit numerical separation/size conditions, smooth
periodic weights, and supremum bounds. It does not assume a prime discrepancy
estimate, Vinogradov estimate, PNT, or Fourier approximation as a hypothesis.
The later application substitutes R=ceil(log^40 n), a<n^alpha and
P comparable with L log^2 n. Every declaration below has a proof body, but none
has been compiled in this task.
-/

namespace Erdos374Research

open Tao2026 Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology

noncomputable section

/-- Uniform rational two-coefficient comparison for two smooth periodic
weights. The threshold is independent of the weights and all listed data.
The displayed separation and stretched-exponential conditions are numerical.
-/
theorem eventually_rational_product_prime_comparison (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (l u a t R : ℕ) (N M : ℝ)
      (H G : ℝ × ℝ → ℂ),
      P ≤ l → l < u → u ≤ 2 * P → 0 < a → t < a →
      0 < N → |M| ≤ N → 4 * (a : ℝ) * R ≤ P →
      2 * (R : ℝ) * N ≤ Real.exp ((Real.log P) ^ (5 / 4 : ℝ)) →
      ContDiff ℝ ∞ H → ContDiff ℝ ∞ G →
      IsZ2Periodic H → IsZ2Periodic G →
      (∀ x, ‖H x‖ ≤ 1) → (∀ x, ‖G x‖ ≤ 1) →
      let δ := smoothTruncationError H R + smoothTruncationError G R +
        smoothTruncationError H R * smoothTruncationError G R
      ‖primeEquidistributionSum (P : ℝ) (Ico (l : ℝ) (u : ℝ))
          (pairedWeight H G ((t : ℝ) / a)) N M 2 -
        primeEquidistributionIntegral (Ico (l : ℝ) (u : ℝ))
          (pairedWeight H G ((t : ℝ) / a)) N M 2‖ ≤
        (2 * (P : ℝ) + 1) * δ +
          smoothCoefficientMass H * smoothCoefficientMass G *
            ((P : ℝ) / (Real.log P) ^ S) +
          (δ / Real.log P) * P := by
  filter_upwards [eventually_rational_modes S,
    eventually_ge_atTop (2 : ℕ)] with P hmodes hP
  intro l u a t R N M H G hPl hlu huP ha ht hN hM hgeom hsize
    hH hG hperH hperG hHone hGone
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hI : Ico (l : ℝ) (u : ℝ) ⊆ Icc (P : ℝ) (2 * (P : ℝ)) := by
    intro x hx
    constructor
    · exact (show (P : ℝ) ≤ l by exact_mod_cast hPl).trans hx.1
    · exact hx.2.le.trans (show (u : ℝ) ≤ 2 * (P : ℝ) by exact_mod_cast huP)
  exact pairedSmooth_discrepancy hPR measurableSet_Ico hI
    H G hH hG hperH hperG hHone hGone R ((t : ℝ) / a) N M
    (by positivity) (hmodes l u a t R N M hPl hlu huP ha ht hN hM hgeom hsize)

/-- The factor in the existing inverse-square-root Fourier tail gives the
needed inverse logarithm at the chosen radius. -/
lemma logarithmic_radiusFactor {n : ℕ} (hn : 2 ≤ n) (T : ℕ) :
    (((specializedFourierRadius (2 * T) n : ℕ) : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤
      (Real.log n) ^ (-(T : ℝ)) := by
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlower : (Real.log (n : ℝ)) ^ (2 * T) ≤
      (specializedFourierRadius (2 * T) n : ℝ) + 1 :=
    (log_pow_le_specializedFourierRadius (2 * T) n).trans (by linarith)
  have hmono := Real.rpow_le_rpow_of_nonpos
    (pow_pos hlog (2 * T)) hlower (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  refine hmono.trans_eq ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul hlog.le]
  congr 1
  push_cast
  ring

lemma smoothTruncationError_logarithmicRadius
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (hper : IsZ2Periodic H)
    {n : ℕ} (hn : 2 ≤ n) (T : ℕ) :
    smoothTruncationError H (specializedFourierRadius (2 * T) n) ≤
      27 * taoC3Norm H * ((Real.log n) ^ (-(T : ℝ)) * fourierTailConstant) := by
  have hC := taoC3Norm_nonneg_of_smooth H hH hper
  have hT : 0 ≤ fourierTailConstant := tsum_nonneg fourierDecayWeightFiveHalves_nonneg
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (logarithmic_radiusFactor hn T) hT) (by positivity)

/-- A logarithmic-radius form exposing only the C³ norms. With C³(H)=O(log⁶ n)
and C³(G)=O(1), T=20 and S=20 give the required O(P/log¹⁴ n) after the explicit
numerical parameter conditions and log P comparable with log n are inserted.
-/
theorem eventually_rational_product_logarithmic_comparison (S T : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (l u a t n : ℕ) (M : ℝ)
      (H G : ℝ × ℝ → ℂ),
      P ≤ l → l < u → u ≤ 2 * P → 0 < a → t < a → 2 ≤ n →
      |M| ≤ n →
      4 * (a : ℝ) * specializedFourierRadius (2 * T) n ≤ P →
      2 * (specializedFourierRadius (2 * T) n : ℝ) * n ≤
        Real.exp ((Real.log P) ^ (5 / 4 : ℝ)) →
      ContDiff ℝ ∞ H → ContDiff ℝ ∞ G →
      IsZ2Periodic H → IsZ2Periodic G →
      (∀ x, ‖H x‖ ≤ 1) → (∀ x, ‖G x‖ ≤ 1) →
      let dH := 27 * taoC3Norm H *
        ((Real.log n) ^ (-(T : ℝ)) * fourierTailConstant)
      let dG := 27 * taoC3Norm G *
        ((Real.log n) ^ (-(T : ℝ)) * fourierTailConstant)
      let δ := dH + dG + dH * dG
      ‖primeEquidistributionSum (P : ℝ) (Ico (l : ℝ) (u : ℝ))
          (pairedWeight H G ((t : ℝ) / a)) n M 2 -
        primeEquidistributionIntegral (Ico (l : ℝ) (u : ℝ))
          (pairedWeight H G ((t : ℝ) / a)) n M 2‖ ≤
        (2 * (P : ℝ) + 1) * δ +
          smoothCoefficientMass H * smoothCoefficientMass G *
            ((P : ℝ) / (Real.log P) ^ S) +
          (δ / Real.log P) * P := by
  filter_upwards [eventually_rational_product_prime_comparison S,
    eventually_ge_atTop (2 : ℕ)] with P hmain hP
  intro l u a t n M H G hPl hlu huP ha ht hn hM hgeom hsize
    hH hG hperH hperG hHone hGone
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hraw := hmain l u a t (specializedFourierRadius (2 * T) n)
    (n : ℝ) M H G hPl hlu huP ha ht hnpos hM hgeom hsize
    hH hG hperH hperG hHone hGone
  have hHtail := smoothTruncationError_logarithmicRadius H hH hperH hn T
  have hGtail := smoothTruncationError_logarithmicRadius G hG hperG hn T
  have hH0 := smoothTruncationError_nonneg H hH hperH
    (specializedFourierRadius (2 * T) n)
  have hG0 := smoothTruncationError_nonneg G hG hperG
    (specializedFourierRadius (2 * T) n)
  have hδ := add_le_add (add_le_add hHtail hGtail)
    (mul_le_mul hHtail hGtail hG0 (hH0.trans hHtail))
  have hlog : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  dsimp only at hraw ⊢
  refine hraw.trans ?_
  exact add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hδ (by positivity)) le_rfl)
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hδ hlog.le) (Nat.cast_nonneg P))

/-- All numerical mode restrictions are automatic in the original rational
parameter range. The dyadic scale is a natural number, allowing the application
to choose a rounded value of L log² n directly. There is no upper restriction
on P in this comparison. -/
theorem eventually_yudin_dyadic_comparison {α ε : ℝ}
    (hαε : α < ε) (hε : 0 < ε) (S T : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P a t : ℕ) (M : ℝ) (H G : ℝ × ℝ → ℂ),
      (n : ℝ) ^ ε ≤ P → 0 < a → t < a → (a : ℝ) ≤ (n : ℝ) ^ α →
      |M| ≤ n → ContDiff ℝ ∞ H → ContDiff ℝ ∞ G →
      IsZ2Periodic H → IsZ2Periodic G →
      (∀ x, ‖H x‖ ≤ 1) → (∀ x, ‖G x‖ ≤ 1) →
      let dH := 27 * taoC3Norm H *
        ((Real.log n) ^ (-(T : ℝ)) * fourierTailConstant)
      let dG := 27 * taoC3Norm G *
        ((Real.log n) ^ (-(T : ℝ)) * fourierTailConstant)
      let δ := dH + dG + dH * dG
      ‖primeEquidistributionSum (P : ℝ) (Ico (P : ℝ) (2 * (P : ℝ)))
          (pairedWeight H G ((t : ℝ) / a)) n M 2 -
        primeEquidistributionIntegral (Ico (P : ℝ) (2 * (P : ℝ)))
          (pairedWeight H G ((t : ℝ) / a)) n M 2‖ ≤
        (2 * (P : ℝ) + 1) * δ +
          smoothCoefficientMass H * smoothCoefficientMass G *
            ((P : ℝ) / (Real.log P) ^ S) +
          (δ / Real.log P) * P := by
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (eventually_rational_product_logarithmic_comparison S T)
  have hlarge : ∀ᶠ n : ℕ in atTop, (K : ℝ) ≤ (n : ℝ) ^ ε :=
    ((_root_.tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (K : ℝ))
  filter_upwards [eventually_rationalParameterRanges hαε hε (2 * T), hlarge]
    with n hparams hlargeN
  intro P a t M H G hP ha ht haN hM hH hG hperH hperG hHone hGone
  have hn := hparams.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hPpos : 0 < P := by
    exact_mod_cast (Real.rpow_pos_of_pos hnpos ε).trans_le hP
  have hKP : K ≤ P := by exact_mod_cast hlargeN.trans hP
  have hpar := hparams.2 a P haN hP
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    hK P hKP P (2 * P) a t n M H G le_rfl (by omega) le_rfl ha ht hn hM
      hpar.1 hpar.2.1 hH hG hperH hperG hHone hGone

/-- Uniform quantitative form after inserting the actual C³ growth bounds.
All phase-size and stationary-point restrictions have been proved from
a≤n^alpha and P≥n^epsilon. -/
theorem eventually_yudin_prime_comparison_fourteen {α ε C_H C_G : ℝ}
    (hαε : α < ε) (hε : 0 < ε) (hCH : 0 < C_H) (hCG : 0 < C_G) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (P a t : ℕ) (M : ℝ) (H G : ℝ × ℝ → ℂ),
      (n : ℝ) ^ ε ≤ P → 0 < a → t < a → (a : ℝ) ≤ (n : ℝ) ^ α →
      |M| ≤ n → ContDiff ℝ ∞ H → ContDiff ℝ ∞ G →
      IsZ2Periodic H → IsZ2Periodic G →
      (∀ x, ‖H x‖ ≤ 1) → (∀ x, ‖G x‖ ≤ 1) →
      taoC3Norm H ≤ C_H * (Real.log n) ^ K → taoC3Norm G ≤ C_G →
      ‖primeEquidistributionSum (P : ℝ) (Ico (P : ℝ) (2 * (P : ℝ)))
          (pairedWeight H G ((t : ℝ) / a)) n M 2 -
        primeEquidistributionIntegral (Ico (P : ℝ) (2 * (P : ℝ)))
          (pairedWeight H G ((t : ℝ) / a)) n M 2‖ ≤
        C * ((P : ℝ) / (Real.log n) ^ 14) := by
  let C := primeComparisonConstant K ε C_H C_G + 1
  have hC : 0 < C := by
    have h := primeComparisonConstant_nonneg K hε hCH.le hCG.le
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hscaled : ∀ᶠ n : ℕ in atTop, 1 ≤ ε * Real.log (n : ℝ) :=
    ((tendsto_const_mul_atTop_of_pos hε).mpr
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_yudin_dyadic_comparison hαε hε (K + 14) (K + 14),
    eventually_rationalParameterRanges hαε hε (2 * (K + 14)), hlog, hscaled]
    with n hmain hparams hlogn hscaledN
  intro P a t M H G hP ha ht haN hM hH hG hperH hperG hHone hGone hHnorm hGnorm
  have hlogScale := (hparams.2 a P haN hP).2.2
  have hn := hparams.1
  have hlogP : 1 ≤ Real.log (P : ℝ) := hscaledN.trans hlogScale
  have hPpos : 0 < P := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact_mod_cast (Real.rpow_pos_of_pos hnpos ε).trans_le hP
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  have hraw := hmain P a t M H G hP ha ht haN hM hH hG hperH hperG hHone hGone
  have hbudget := primeComparison_scalar_budget K hε hCH.le hCG.le
    (taoC3Norm_nonneg_of_smooth H hH hperH)
    (taoC3Norm_nonneg_of_smooth G hG hperG)
    hlogn hlogP hPR hlogScale hHnorm hGnorm
  have hbound : ‖primeEquidistributionSum (P : ℝ)
      (Ico (P : ℝ) (2 * (P : ℝ))) (pairedWeight H G ((t : ℝ) / a)) n M 2 -
      primeEquidistributionIntegral (Ico (P : ℝ) (2 * (P : ℝ)))
        (pairedWeight H G ((t : ℝ) / a)) n M 2‖ ≤
      primeComparisonConstant K ε C_H C_G * ((P : ℝ) / (Real.log n) ^ 14) := by
    exact hraw.trans (by simpa only [smoothCoefficientMass] using hbudget)
  refine hbound.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  dsimp only [C]
  linarith

/-- Application endpoint: the logarithmic saving requested in Yudin's
positive-weight contradiction, with no additional analytic hypotheses.
It uses the natural dyadic prime interval [P,2P); the mathematical application
can select P=ceil(L log² n). -/
theorem eventually_yudin_prime_comparison {α ε C_H C_G : ℝ}
    (hαε : α < ε) (hε : 0 < ε) (hCH : 0 < C_H) (hCG : 0 < C_G) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (P a t : ℕ) (M : ℝ) (H G : ℝ × ℝ → ℂ),
      (n : ℝ) ^ ε ≤ P → 0 < a → t < a → (a : ℝ) ≤ (n : ℝ) ^ α →
      |M| ≤ n → ContDiff ℝ ∞ H → ContDiff ℝ ∞ G →
      IsZ2Periodic H → IsZ2Periodic G →
      (∀ x, ‖H x‖ ≤ 1) → (∀ x, ‖G x‖ ≤ 1) →
      taoC3Norm H ≤ C_H * (Real.log n) ^ K → taoC3Norm G ≤ C_G →
      ‖primeEquidistributionSum (P : ℝ) (Ico (P : ℝ) (2 * (P : ℝ)))
          (pairedWeight H G ((t : ℝ) / a)) n M 2 -
        primeEquidistributionIntegral (Ico (P : ℝ) (2 * (P : ℝ)))
          (pairedWeight H G ((t : ℝ) / a)) n M 2‖ ≤
        C * ((P : ℝ) / (Real.log n) ^ 5) := by
  obtain ⟨C, hC, hmain⟩ :=
    eventually_yudin_prime_comparison_fourteen hαε hε hCH hCG K
  refine ⟨C, hC, ?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hmain, hlog] with n hmainN hlogn
  intro P a t M H G hP ha ht haN hM hH hG hperH hperG hHone hGone hHnorm hGnorm
  have hbound := hmainN P a t M H G hP ha ht haN hM hH hG hperH hperG
    hHone hGone hHnorm hGnorm
  have hpowers : (Real.log (n : ℝ)) ^ 5 ≤ (Real.log (n : ℝ)) ^ 14 := by
    calc
      (Real.log (n : ℝ)) ^ 5 = (Real.log (n : ℝ)) ^ 5 * 1 := by ring
      _ ≤ (Real.log (n : ℝ)) ^ 5 * (Real.log (n : ℝ)) ^ 9 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 9) hlogn) (by positivity)
      _ = (Real.log (n : ℝ)) ^ 14 := by ring
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (Nat.cast_nonneg P)
      (pow_pos (by linarith : 0 < Real.log (n : ℝ)) 5) hpowers) hC.le)

end
end Erdos374Research
