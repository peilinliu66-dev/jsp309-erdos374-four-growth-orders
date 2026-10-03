import Erdos374Research.PrimeModes

/-!
UNCOMPILED. Finite product assembly using two existing two-dimensional Fourier
expansions. The Fourier reconstruction and decay results are S. McColm's public
Tao2026 modules at 91604dfc9733555f0b762594cd434450728d3d8c (MIT-0 for original
repository source). This adapter implements the separable weight in Yudin's
factorial argument; it introduces no Fourier reconstruction hypothesis.
-/

namespace Erdos374Research

open Tao2026 Complex Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology

noncomputable section

def pairedWeight (H G : ℝ × ℝ → ℂ) (θ : ℝ) (x : ℝ × ℝ) : ℂ :=
  H (x.1, θ * x.1) * G (0, x.2)

lemma continuous_pairedWeight {H G : ℝ × ℝ → ℂ}
    (hH : Continuous H) (hG : Continuous G) (θ : ℝ) :
    Continuous (pairedWeight H G θ) := by
  unfold pairedWeight
  fun_prop

def pairedLinear (q : ℤ × ℤ) (θ N : ℝ) : ℝ :=
  ((q.1 : ℝ) + (q.2 : ℝ) * θ) * N

def pairedQuadratic (r : ℤ × ℤ) (M : ℝ) : ℝ := (r.2 : ℝ) * M

lemma pairedMode_eval (q r : ℤ × ℤ) (θ N M t : ℝ) :
    fourierMode2D q (N / t, θ * (N / t)) *
        fourierMode2D r (0, M / t ^ 2) =
      standardAdditiveCharacter
        (reciprocalPhase (pairedLinear q θ N) (pairedQuadratic r M) 2 t) := by
  unfold fourierMode2D
  rw [← standardAdditiveCharacter_add, reciprocalPhase_eq_div]
  congr 1
  unfold pairedLinear pairedQuadratic
  ring

lemma pairedPolynomial_eval
    (s u : Finset (ℤ × ℤ)) (c d : ℤ × ℤ → ℂ) (θ N M t : ℝ) :
    pairedWeight (finiteFourierPolynomial s c) (finiteFourierPolynomial u d)
        θ (N / t, M / t ^ 2) =
      ∑ q ∈ s, ∑ r ∈ u, (c q * d r) *
        standardAdditiveCharacter
          (reciprocalPhase (pairedLinear q θ N) (pairedQuadratic r M) 2 t) := by
  unfold pairedWeight finiteFourierPolynomial
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  calc
    (c q * fourierMode2D q (N / t, θ * (N / t))) *
        (d r * fourierMode2D r (0, M / t ^ 2)) =
      (c q * d r) * (fourierMode2D q (N / t, θ * (N / t)) *
        fourierMode2D r (0, M / t ^ 2)) := by ring
    _ = _ := by rw [pairedMode_eval]

lemma pairedPolynomial_primeSum
    (P : ℝ) (I : Set ℝ) (s u : Finset (ℤ × ℤ))
    (c d : ℤ × ℤ → ℂ) (θ N M : ℝ) :
    primeEquidistributionSum P I
        (pairedWeight (finiteFourierPolynomial s c)
          (finiteFourierPolynomial u d) θ) N M 2 =
      ∑ q ∈ s, ∑ r ∈ u, (c q * d r) *
        primeFourierModeSum P I (1, 1)
          (pairedLinear q θ N) (pairedQuadratic r M) 2 := by
  unfold primeEquidistributionSum
  simp_rw [pairedPolynomial_eval]
  simp only [primeFourierModeSum, Int.cast_one, one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.mul_sum]

lemma pairedPolynomial_integral
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hI : I ⊆ Icc P (2 * P))
    (s u : Finset (ℤ × ℤ)) (c d : ℤ × ℤ → ℂ) (θ N M : ℝ) :
    primeEquidistributionIntegral I
        (pairedWeight (finiteFourierPolynomial s c)
          (finiteFourierPolynomial u d) θ) N M 2 =
      ∑ q ∈ s, ∑ r ∈ u, (c q * d r) *
        fourierModeIntegral I (1, 1)
          (pairedLinear q θ N) (pairedQuadratic r M) 2 := by
  have hint (q r : ℤ × ℤ) : IntegrableOn
      (fun t => (c q * d r) *
        (standardAdditiveCharacter
          (reciprocalPhase (pairedLinear q θ N) (pairedQuadratic r M) 2 t) /
            Real.log t)) I := by
    have h := integrableOn_fourierModeIntegrand hP hI
      ((1, 1) : ℤ × ℤ) (pairedLinear q θ N) (pairedQuadratic r M) 2
    simpa only [Int.cast_one, one_mul] using h.const_mul (c q * d r)
  unfold primeEquidistributionIntegral
  simp_rw [pairedPolynomial_eval, Finset.sum_div, mul_div_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q _hq
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro r _hr
      rw [MeasureTheory.integral_const_mul]
      simp only [fourierModeIntegral, Int.cast_one, one_mul]
    · intro r _hr
      exact hint q r
  · intro q _hq
    exact integrable_finsetSum u (fun r _ => hint q r)

lemma pairedPolynomial_discrepancy
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hI : I ⊆ Icc P (2 * P))
    (s u : Finset (ℤ × ℤ)) (c d : ℤ × ℤ → ℂ) (θ N M : ℝ)
    {E : ℝ}
    (hmode : ∀ q ∈ s, ∀ r ∈ u,
      ‖primeFourierModeSum P I (1, 1)
          (pairedLinear q θ N) (pairedQuadratic r M) 2 -
        fourierModeIntegral I (1, 1)
          (pairedLinear q θ N) (pairedQuadratic r M) 2‖ ≤ E) :
    ‖primeEquidistributionSum P I
        (pairedWeight (finiteFourierPolynomial s c)
          (finiteFourierPolynomial u d) θ) N M 2 -
      primeEquidistributionIntegral I
        (pairedWeight (finiteFourierPolynomial s c)
          (finiteFourierPolynomial u d) θ) N M 2‖ ≤
      (∑ q ∈ s, ‖c q‖) * (∑ r ∈ u, ‖d r‖) * E := by
  rw [pairedPolynomial_primeSum,
    pairedPolynomial_integral hP hI s u c d θ N M,
    ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    ‖∑ q ∈ s, ∑ r ∈ u, (c q * d r) *
        (primeFourierModeSum P I (1, 1)
            (pairedLinear q θ N) (pairedQuadratic r M) 2 -
          fourierModeIntegral I (1, 1)
            (pairedLinear q θ N) (pairedQuadratic r M) 2)‖ ≤
        ∑ q ∈ s, ∑ r ∈ u, ‖c q‖ * ‖d r‖ * E := by
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro q hq
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hmode q hq r hr) (by positivity)
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]

lemma norm_product_sub_product_le
    {a b c d : ℂ} {δ ε : ℝ}
    (hδ : 0 ≤ δ) (_hε : 0 ≤ ε)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hac : ‖a - c‖ ≤ δ) (hbd : ‖b - d‖ ≤ ε) :
    ‖a * b - c * d‖ ≤ δ + ε + δ * ε := by
  have hc : ‖c‖ ≤ 1 + δ := by
    calc
      ‖c‖ = ‖a - (a - c)‖ := by congr 1; ring
      _ ≤ ‖a‖ + ‖a - c‖ := norm_sub_le _ _
      _ ≤ 1 + δ := add_le_add ha hac
  calc
    ‖a * b - c * d‖ = ‖(a - c) * b + c * (b - d)‖ := by congr 1; ring
    _ ≤ ‖(a - c) * b‖ + ‖c * (b - d)‖ := norm_add_le _ _
    _ = ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by rw [norm_mul, norm_mul]
    _ ≤ δ * 1 + (1 + δ) * ε := by gcongr
    _ = δ + ε + δ * ε := by ring

def fourierTailConstant : ℝ :=
  ∑' q : ℤ × ℤ, fourierDecayWeightFiveHalves q

def fourierMassConstant : ℝ :=
  ∑' q : ℤ × ℤ, fourierDecayWeight q

def smoothTruncationError (H : ℝ × ℝ → ℂ) (R : ℕ) : ℝ :=
  27 * taoC3Norm H * (((R : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * fourierTailConstant)

def smoothCoefficientMass (H : ℝ × ℝ → ℂ) : ℝ :=
  27 * taoC3Norm H * fourierMassConstant

lemma smoothTruncationError_nonneg (H : ℝ × ℝ → ℂ)
    (hH : ContDiff ℝ ∞ H) (hper : IsZ2Periodic H) (R : ℕ) :
    0 ≤ smoothTruncationError H R := by
  have hC := taoC3Norm_nonneg_of_smooth H hH hper
  have hT : 0 ≤ fourierTailConstant := tsum_nonneg fourierDecayWeightFiveHalves_nonneg
  unfold smoothTruncationError
  positivity

lemma smoothCoefficientMass_nonneg (H : ℝ × ℝ → ℂ)
    (hH : ContDiff ℝ ∞ H) (hper : IsZ2Periodic H) :
    0 ≤ smoothCoefficientMass H := by
  have hC := taoC3Norm_nonneg_of_smooth H hH hper
  have hM : 0 ≤ fourierMassConstant := tsum_nonneg fourierDecayWeight_nonneg
  unfold smoothCoefficientMass
  positivity

lemma smoothTruncation_bound (H : ℝ × ℝ → ℂ)
    (hH : ContDiff ℝ ∞ H) (hper : IsZ2Periodic H) (R : ℕ) (x : ℝ × ℝ) :
    ‖H x - finiteFourierPolynomial (fourierFrequencyBox R)
        (taoFourierCoeff H hper hH.continuous) x‖ ≤ smoothTruncationError H R := by
  have hC := taoC3Norm_nonneg_of_smooth H hH hper
  exact (norm_taoFourierPolynomial_sub_le_coefficientTail hper hH.continuous
    (norm_taoFourierCoeff_le_taoC3Norm_mul_fourierDecayWeight_of_smooth H hH hper)
    R x).trans ((taoFourierCoefficientTail_le_taoC3Norm_mul_decayTail H hH hper R).trans
      (mul_le_mul_of_nonneg_left (fourierDecayTail_le_invSqrt R) (by positivity)))

lemma pairedSmooth_discrepancy
    {P : ℝ} (hP : 2 ≤ P) {I : Set ℝ} (hImeas : MeasurableSet I)
    (hI : I ⊆ Icc P (2 * P))
    (H G : ℝ × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hperH : IsZ2Periodic H) (hperG : IsZ2Periodic G)
    (hHone : ∀ x, ‖H x‖ ≤ 1) (hGone : ∀ x, ‖G x‖ ≤ 1)
    (R : ℕ) (θ N M : ℝ) {E : ℝ} (hE : 0 ≤ E)
    (hmode : ∀ q ∈ fourierFrequencyBox R, ∀ r ∈ fourierFrequencyBox R,
      ‖primeFourierModeSum P I (1, 1)
          (pairedLinear q θ N) (pairedQuadratic r M) 2 -
        fourierModeIntegral I (1, 1)
          (pairedLinear q θ N) (pairedQuadratic r M) 2‖ ≤ E) :
    let δ := smoothTruncationError H R + smoothTruncationError G R +
      smoothTruncationError H R * smoothTruncationError G R
    ‖primeEquidistributionSum P I (pairedWeight H G θ) N M 2 -
      primeEquidistributionIntegral I (pairedWeight H G θ) N M 2‖ ≤
      (2 * P + 1) * δ + smoothCoefficientMass H * smoothCoefficientMass G * E +
        (δ / Real.log P) * P := by
  let c := taoFourierCoeff H hperH hH.continuous
  let d := taoFourierCoeff G hperG hG.continuous
  let F := pairedWeight (finiteFourierPolynomial (fourierFrequencyBox R) c)
    (finiteFourierPolynomial (fourierFrequencyBox R) d) θ
  have hδH := smoothTruncationError_nonneg H hH hperH R
  have hδG := smoothTruncationError_nonneg G hG hperG R
  have hmassH := sum_norm_taoFourierCoeff_le_taoC3Norm_mul_decayMass H hH hperH
    (fourierFrequencyBox R)
  have hmassG := sum_norm_taoFourierCoeff_le_taoC3Norm_mul_decayMass G hG hperG
    (fourierFrequencyBox R)
  have hmassH0 := smoothCoefficientMass_nonneg H hH hperH
  have hmassG0 := smoothCoefficientMass_nonneg G hG hperG
  have hpoly : ‖primeEquidistributionSum P I F N M 2 -
      primeEquidistributionIntegral I F N M 2‖ ≤
      smoothCoefficientMass H * smoothCoefficientMass G * E := by
    refine (pairedPolynomial_discrepancy hP hI
      (fourierFrequencyBox R) (fourierFrequencyBox R) c d θ N M hmode).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hmassH hmassG (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        hmassH0) hE
  apply norm_primeEquidistributionDiscrepancy_le_of_approx hP hImeas hI
    (pairedWeight H G θ) F (continuous_pairedWeight hH.continuous hG.continuous θ)
    (continuous_pairedWeight (continuous_finiteFourierPolynomial _ _)
      (continuous_finiteFourierPolynomial _ _) θ) N M 2 (by positivity) _ hpoly
  intro x
  exact norm_product_sub_product_le hδH hδG (hHone _) (hGone _)
    (smoothTruncation_bound H hH hperH R _) (smoothTruncation_bound G hG hperG R _)

end
end Erdos374Research
