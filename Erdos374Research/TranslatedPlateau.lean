import Tao2026.FactorialEquidistribution

/-!
# Translated normalized periodic plateaus

UNCOMPILED. This adapter reuses the actual public normalized cutoff and
derivative bounds in Tao2026, credited to the pinned upstream formalization.
The later two-block construction uses different translations and powers
of the outer parameter while retaining one uniform derivative constant.
-/

namespace Erdos374Research

open Tao2026 MeasureTheory
open scoped BigOperators ContDiff

noncomputable def shiftedPlateau (N : ℕ) (c x : ℝ) : ℝ :=
  factorialNormalizedPlateauWeight N (x - c)

theorem shiftedPlateau_contDiff (N : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (shiftedPlateau N c) :=
  (factorialNormalizedPlateauWeight_contDiff N).comp (contDiff_id.sub contDiff_const)

theorem shiftedPlateau_periodic (N : ℕ) (c : ℝ) :
    Function.Periodic (shiftedPlateau N c) 1 := by
  intro x
  have h := factorialNormalizedPlateauWeight_periodic N (x - c)
  simpa only [shiftedPlateau, add_sub_right_comm] using h

theorem shiftedPlateau_nonneg (N : ℕ) (c x : ℝ) : 0 ≤ shiftedPlateau N c x :=
  factorialNormalizedPlateauWeight_nonneg N (x - c)

theorem shiftedPlateau_le_one (N : ℕ) (c x : ℝ) : shiftedPlateau N c x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem shiftedPlateau_supported {N : ℕ} (hN : 1 < Real.log (N : ℝ))
    {c x : ℝ} (hx : shiftedPlateau N c x ≠ 0) :
    1 - 1 / (10 * (Real.log N) ^ 2) ≤ Int.fract (x - c) :=
  factorialNormalizedPlateauWeight_supported hN hx

theorem shiftedPlateau_eq_one {N : ℕ} (hN : 1 < Real.log (N : ℝ))
    {c x : ℝ}
    (hleft : factorialPlateauArcLeft N ≤ Int.fract (x - c))
    (hright : Int.fract (x - c) ≤ factorialPlateauArcRight N) :
    shiftedPlateau N c x = 1 :=
  factorialNormalizedPlateauWeight_eq_one_of_innerFractionalArc hN hleft hright

theorem shiftedPlateau_period_mass {N : ℕ} (hN : 1 < Real.log (N : ℝ))
    (c a : ℝ) :
    1 / (60 * (Real.log N) ^ 2) ≤ ∫ x in a..a + 1, shiftedPlateau N c x := by
  unfold shiftedPlateau
  rw [intervalIntegral.integral_comp_sub_right]
  have h := one_div_sixty_log_sq_le_intervalIntegral_factorialPlateauWeight_unit
    hN (factorialNormalizedPlateauWeight_spec hN) (a - c)
  convert h using 1
  congr 1
  ring

theorem norm_iteratedFDeriv_shiftedPlateau_le
    {B : ℝ} (hB : 1 ≤ B)
    (htransition : ∀ i < 4, ∀ x : ℝ,
      ‖iteratedFDeriv ℝ i Real.smoothTransition x‖ ≤ B)
    {N i : ℕ} (hN : 1 ≤ Real.log (N : ℝ)) (hi : i < 4) (c x : ℝ) :
    ‖iteratedFDeriv ℝ i (shiftedPlateau N c) x‖ ≤
      6 * B * (1200 * (Real.log N) ^ 4) ^ 3 := by
  unfold shiftedPlateau
  rw [iteratedFDeriv_comp_sub]
  exact norm_iteratedFDeriv_factorialNormalizedPlateauWeight_le hB htransition hN hi (x - c)

theorem shiftedPlateau_lift_periodic (N : ℕ) (c : ℝ) :
    IsZ2Periodic (factorialPlateauWeightLift (shiftedPlateau N c)) := by
  intro x y m n
  change ((shiftedPlateau N c (x + (m : ℝ)) : ℝ) : ℂ) =
    ((shiftedPlateau N c x : ℝ) : ℂ)
  rw [show x + (m : ℝ) = x + (m : ℝ) * 1 by ring,
    (shiftedPlateau_periodic N c).int_mul m]

theorem shiftedPlateau_lift_contDiff (N : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (factorialPlateauWeightLift (shiftedPlateau N c)) := by
  unfold factorialPlateauWeightLift
  exact Complex.ofRealCLM.contDiff.comp ((shiftedPlateau_contDiff N c).comp contDiff_fst)

theorem shiftedPlateau_lift_norm_le_one (N : ℕ) (c : ℝ) (z : ℝ × ℝ) :
    ‖factorialPlateauWeightLift (shiftedPlateau N c) z‖ ≤ 1 := by
  change ‖((shiftedPlateau N c z.1 : ℝ) : ℂ)‖ ≤ 1
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (shiftedPlateau_nonneg _ _ _)]
  exact shiftedPlateau_le_one _ _ _

theorem exists_shiftedPlateau_lift_C3_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (c : ℝ),
      1 ≤ Real.log (N : ℝ) →
      taoC3Norm (factorialPlateauWeightLift (shiftedPlateau N c)) ≤
        C * (Real.log N) ^ 12 := by
  obtain ⟨B, hB, htransition⟩ := exists_smoothTransition_C3_bound
  refine ⟨24 * B * 1200 ^ (3 : ℕ), by positivity, ?_⟩
  intro N c hN
  have hpoint : ∀ i < 4, ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ i (factorialPlateauWeightLift (shiftedPlateau N c)) z‖ ≤
        6 * B * (1200 * (Real.log N) ^ 4) ^ 3 := by
    intro i hi z
    exact (norm_iteratedFDeriv_factorialPlateauWeightLift_le
      (shiftedPlateau_contDiff N c) i z).trans
      (norm_iteratedFDeriv_shiftedPlateau_le hB htransition hN hi c z.1)
  calc
    taoC3Norm (factorialPlateauWeightLift (shiftedPlateau N c)) ≤
        4 * (6 * B * (1200 * (Real.log N) ^ 4) ^ 3) :=
      taoC3Norm_le_four_mul_of_iteratedFDeriv_le (by positivity) hpoint
    _ = (24 * B * 1200 ^ (3 : ℕ)) * (Real.log N) ^ 12 := by ring

theorem exists_shiftedPlateau_power_lift_C3_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (c : ℝ),
      1 ≤ Real.log (n : ℝ) →
      taoC3Norm (factorialPlateauWeightLift (shiftedPlateau (n ^ m) c)) ≤
        C * (Real.log n) ^ 12 := by
  obtain ⟨C, hC, hbound⟩ := exists_shiftedPlateau_lift_C3_bound
  refine ⟨C * (m : ℝ) ^ 12, by positivity, ?_⟩
  intro n c hn
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : Real.log ((n ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log (n : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hnlog : 1 ≤ Real.log ((n ^ m : ℕ) : ℝ) := by rw [hlog]; nlinarith
  have h := hbound (n ^ m) c hnlog
  rw [hlog] at h
  convert h using 1
  ring

end Erdos374Research
