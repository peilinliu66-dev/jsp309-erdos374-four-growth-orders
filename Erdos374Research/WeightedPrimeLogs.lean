import Tao2026.CoefficientBounds
import Tao2026.FactorialCoefficientBounds

/-!
UNCOMPILED. The lower weighted prime-log estimate needed by Gallagher's sieve.
This is an Abel-summation consequence of the already imported Chebyshev PNT;
it does not depend on a new external Mertens module or toolchain.
-/

namespace Erdos374Research

open Tao2026 Filter Finset
open scoped BigOperators Topology

noncomputable section

lemma abel_linear_model (c B : ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ)⁻¹ * (c * ((k + 1 : ℕ) : ℝ) - B) +
      ∑ i ∈ Finset.Ioc 0 k, (c * i - B) / ((i : ℝ) * (i + 1)) =
        c * (harmonic (k + 1) : ℝ) - B := by
  induction k with
  | zero => norm_num [harmonic_succ]
  | succ k ih =>
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), harmonic_succ (k + 1)]
      push_cast at ih ⊢
      have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
      have hstep :
          ((k : ℝ) + 1 + 1)⁻¹ * (c * ((k : ℝ) + 1 + 1) - B) +
            (c * ((k : ℝ) + 1) - B) / (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1)) =
          ((k : ℝ) + 1)⁻¹ * (c * ((k : ℝ) + 1) - B) +
            c * ((k : ℝ) + 1 + 1)⁻¹ := by
        field_simp [h1, h2]
        ring
      linarith

lemma weightedPrimeLogSum_ge_of_theta_lower {c B : ℝ} (hc : 0 ≤ c)
    (hθ : ∀ i : ℕ, 1 ≤ i → c * i - B ≤ Chebyshev.theta i)
    {H : ℕ} (hH : 1 ≤ H) :
    c * Real.log (H : ℝ) - B ≤ weightedPrimeLogSum H := by
  have hHpos : 0 < H := by omega
  have hHR : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hmodel := abel_linear_model c B (H - 1)
  rw [Nat.sub_add_cancel hH] at hmodel
  have hlower : c * (harmonic H : ℝ) - B ≤ weightedPrimeLogSum H := by
    rw [← hmodel, weightedPrimeLogSum_abel H hHpos]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (hθ H hH) (inv_nonneg.mpr hHR.le)
    · apply Finset.sum_le_sum
      intro i hi
      have hi1 : 1 ≤ i := by have := (Finset.mem_Ioc.mp hi).1; omega
      exact div_le_div_of_nonneg_right (hθ i hi1) (by positivity)
  have hlog : Real.log (H : ℝ) ≤ (harmonic H : ℝ) := by
    simpa only [Nat.floor_natCast] using log_le_harmonic_floor (H : ℝ) (Nat.cast_nonneg H)
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hlog hc) B).trans hlower

lemma exists_chebyshev_theta_uniform_lower {η : ℝ} (hη : 0 < η) (_hη1 : η < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : ℕ, 1 ≤ i →
      (1 - η) * i - B ≤ Chebyshev.theta i := by
  have hevent := tendsto_natCast_atTop_atTop.eventually
    (eventually_abs_chebyshev_theta_error_le η hη)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  refine ⟨(K : ℝ), Nat.cast_nonneg K, ?_⟩
  intro i hi
  by_cases hKi : K ≤ i
  · have h := (abs_le.mp (hK i hKi)).1
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  · have hiK : (i : ℝ) ≤ K := by exact_mod_cast (show i ≤ K by omega)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hθ := Chebyshev.theta_nonneg (i : ℝ)
    nlinarith [mul_nonneg hη.le hi0]

/-- Uniform pointwise weighted Mertens lower bound with any coefficient
strictly below one. The constant absorbs the finite initial PNT range. -/
theorem exists_weightedPrimeLogSum_lower {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ H : ℕ, 1 ≤ H →
      (1 - η) * Real.log (H : ℝ) - B ≤ weightedPrimeLogSum H := by
  obtain ⟨B, hB, hθ⟩ := exists_chebyshev_theta_uniform_lower hη hη1
  exact ⟨B, hB, fun H hH => weightedPrimeLogSum_ge_of_theta_lower
    (by linarith : 0 ≤ 1 - η) hθ hH⟩

/-- The exact two-cutoff form used by the hard D3 fibres. The upper bound at
the smaller cutoff is already present in the fixed Tao2026 dependency. -/
theorem exists_weightedPrimeLogSum_difference_lower {η : ℝ}
    (hη : 0 < η) (hη1 : η < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Q Y : ℕ, 1 ≤ Q → 1 ≤ Y →
      (1 - η) * Real.log (Q : ℝ) -
        Real.log 4 * (2 + Real.log Y) - B ≤
      weightedPrimeLogSum Q - weightedPrimeLogSum Y := by
  obtain ⟨B, hB, hlarge⟩ := exists_weightedPrimeLogSum_lower hη hη1
  refine ⟨B, hB, ?_⟩
  intro Q Y hQ hY
  have hlo := hlarge Q hQ
  have hhi := weightedPrimeLogSum_le Y (by omega)
  linarith

end
end Erdos374Research
