import Erdos374Research.LongBlockRanges

/-!
# The analytic long-block contradiction

UNCOMPILED original adapter of Yudin, Section 5. The detecting functions,
their positive period mass, the square-divisibility exclusion, and every
C³ and rounding budget are supplied by preceding modules. The comparison
estimate is the actual two-Fourier adapter to the pinned public theorem.
The preliminary reduction from arbitrary representations is separate.
-/

namespace Erdos374Research

open Filter Tao2026 Set
open scoped Topology

theorem eventually_no_long_two_blocks_with_relation {α ε γ D : ℝ}
    (hα : 0 ≤ α) (hαε : α < ε) (hgap : α + γ < 1) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, ∀ m l₁ l₂ c a t j : ℕ,
      1 ≤ l₁ → 1 ≤ l₂ → l₁ ≤ n → l₂ ≤ m → m < n →
      j < l₂ → 1 ≤ t → t < a → (a : ℝ) ≤ (n : ℝ) ^ α →
      ((m - j : ℕ) : ℝ) = (t : ℝ) / a * n →
      (n : ℝ) ^ ε ≤ (max l₁ l₂ : ℕ) →
      (max l₁ l₂ : ℕ) ≤ (n : ℝ) ^ γ →
      (c : ℝ) ≤ D * ((max l₁ l₂ : ℕ) * Real.log n + 1) →
      ¬IsSquare (falling n l₁ * falling m l₂ * c.factorial) := by
  obtain ⟨N, hN, hd⟩ := exists_fixed_integerAvoidingWeight
  obtain ⟨C_H, hCH, hHbound⟩ := exists_blockSeparator_C3_bound N
  obtain ⟨C_G, hCG, hGbound⟩ := exists_longBlockSquareWeight_C3_bound N
  obtain ⟨C, hC, hcomparison⟩ := eventually_yudin_prime_comparison
    hαε (lt_of_le_of_lt hα hαε) hCH hCG 24
  have hlog : ∀ᶠ n : ℕ in atTop,
      57600000 * C + 2 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hcomparison, hlog, eventually_longBlockScale_ranges hα hαε hgap hD hN]
    with n hcomp hlarge hscales
  intro m l₁ l₂ c a t j hl₁ hl₂ hl₁n hl₂m hmn hj ht hta haN hrel hLlow hLhigh hc hsq
  have ha : 0 < a := by omega
  have htpos : 0 < t := by omega
  let L := max l₁ l₂
  let P := longBlockPrimeScale n L
  let M := selectedBlockCenter n m l₁ l₂ j
  have hranges := hscales.2.2.2 L a c ha haN hLlow hLhigh hc
  obtain ⟨hP, hLP, hcp, hPn, hPε, hslow, hboundary, hsmall, hsquare⟩ := hranges
  have hn := hscales.1
  have hlog2 := hscales.2.1
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hM := selectedBlockCenter_pos_le (l₁ := l₁) hn hmn hl₂m hj
  have hMabs : |(M : ℝ)| ≤ n := by
    rw [abs_of_nonneg (Nat.cast_nonneg M)]
    exact_mod_cast hM.2
  have hbound := hcomp P a t M
    (blockSeparator n N P l₁ l₂ j)
    (secondWeightLift (longBlockSquareWeight N M P))
    hPε ha hta haN hMabs
    (blockSeparator_contDiff _ _ _ _ _ _)
    (secondWeightLift_contDiff (longBlockSquareWeight_contDiff _ _ _))
    (blockSeparator_periodic _ _ _ _ _ _)
    (secondWeightLift_periodic (longBlockSquareWeight_periodic _ _ _))
    (blockSeparator_norm_le_one _ _ _ _ _ _)
    (secondWeightLift_norm_le_one (longBlockSquareWeight_nonneg _ _ _)
      (longBlockSquareWeight_le_one _ _ _))
    (hHbound n P l₁ l₂ j (by linarith)) (hGbound M P)
  have hzero := blockDetectingWeight_primeSum_zero hn hlog2 hN hl₁ hl₂ hl₁n hl₂m
    hj ha hrel hscales.2.2.1 hLP hcp hsmall hsquare hsq
  change primeEquidistributionSum (P : ℝ) (Ico (P : ℝ) (2 * P))
    (blockDetectingWeight n m N P l₁ l₂ j a t) n M 2 = 0 at hzero
  change ‖primeEquidistributionSum (P : ℝ) (Ico (P : ℝ) (2 * P))
      (blockDetectingWeight n m N P l₁ l₂ j a t) n M 2 -
    primeEquidistributionIntegral (Ico (P : ℝ) (2 * P))
      (blockDetectingWeight n m N P l₁ l₂ j a t) n M 2‖ ≤ _ at hbound
  rw [hzero, zero_sub, norm_neg] at hbound
  have hlower := blockDetectingWeight_integral_lower (l₁ := l₁) hn hmn hl₂m hj
    (by linarith : 1 < Real.log (n : ℝ)) hN hd htpos hta hP hPn hslow hboundary
  have hPR : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hsmallC : C / Real.log (n : ℝ) ^ 2 < 1 / 57600000 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hlogpos)).mpr
    nlinarith
  have hstrict : C * ((P : ℝ) / Real.log n ^ 5) <
      (P : ℝ) / (57600000 * Real.log n ^ 3) := by
    calc
      C * ((P : ℝ) / Real.log n ^ 5) =
          ((P : ℝ) / Real.log n ^ 3) * (C / Real.log n ^ 2) := by field_simp
      _ < ((P : ℝ) / Real.log n ^ 3) * (1 / 57600000) :=
        mul_lt_mul_of_pos_left hsmallC (by positivity)
      _ = (P : ℝ) / (57600000 * Real.log n ^ 3) := by ring
  exact (not_lt_of_ge (hlower.trans hbound)) hstrict

end Erdos374Research
