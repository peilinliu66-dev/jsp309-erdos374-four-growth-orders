import Erdos374Research.ConsecutiveCount
import Erdos374Research.NonconsecutiveCount
import Erdos374Research.ThreeLower
import Erdos374Research.FourFactors

/-!
# The original D3 and D4 orders of growth

UNCOMPILED. These two clauses have full source bodies and no assumed
growth estimate. They are only part of the original E374 question; D5 and
D6 must also be completed before this project is a full handoff.
-/

namespace Erdos374Research

open Filter Finset
open scoped Topology

theorem countD_three_le_factorialThreeCount (X : ℕ) :
    countD 3 X ≤ Tao2026.factorialThreeCount X := by
  classical
  change (numbersInDUpTo 3 X).card ≤ (Tao2026.factorialThreeNumbersUpTo X).card
  apply Finset.card_le_card
  intro n hn
  have hd := mem_numbersInDUpTo.mp hn
  apply Tao2026.mem_factorialThreeNumbersUpTo.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨hd.1, hd.2.1⟩,
    (hasRepresentation_three_iff_upstream n).mp hd.2.2.2.1⟩

theorem eventually_countD_three_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      (countD 3 X : ℝ) ≤ C * Real.sqrt X := by
  obtain ⟨C₀, hC₀, hnon⟩ := eventually_nontrivialFactorialThreeCount_le
  let C := C₀ + factorialRootWeightSum + 1
  have hC : 0 < C := by dsimp [C]; linarith [factorialRootWeightSum_nonneg]
  refine ⟨C, hC, ?_⟩
  filter_upwards [hnon, eventually_ge_atTop (1 : ℕ)] with X hX hX1
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hpow : (X : ℝ) ^ d3HardExponent ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hXR d3HardExponent_lt_half.le
  have hsplit : (Tao2026.factorialThreeCount X : ℝ) =
      Tao2026.nontrivialFactorialThreeCount X + Tao2026.factorialThreeOneTermCount X := by
    exact_mod_cast (Tao2026.nontrivialFactorialThreeCount_add_factorialThreeOneTermCount X).symm
  calc
    (countD 3 X : ℝ) ≤ Tao2026.factorialThreeCount X := by
      exact_mod_cast countD_three_le_factorialThreeCount X
    _ = Tao2026.nontrivialFactorialThreeCount X + Tao2026.factorialThreeOneTermCount X := hsplit
    _ ≤ C₀ * (X : ℝ) ^ d3HardExponent + factorialRootWeightSum * Real.sqrt X :=
      add_le_add hX (factorialThreeOneTermCount_le_sqrt X)
    _ ≤ C₀ * Real.sqrt X + factorialRootWeightSum * Real.sqrt X := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpow hC₀.le) le_rfl
    _ ≤ C * Real.sqrt X := by dsimp [C]; nlinarith [Real.sqrt_nonneg (X : ℝ)]

theorem growth_three : HasOrder (countD 3) (fun X => Real.sqrt X) := by
  obtain ⟨C, hC, hupper⟩ := eventually_countD_three_upper
  refine ⟨1 / 4, C, by norm_num, hC, ?_⟩
  filter_upwards [eventually_countD_three_lower, hupper] with X hl hu
  exact ⟨by simpa only [one_div_mul_eq_div] using hl, hu⟩

theorem growth_four : HasOrder (countD 4) (fun X => X) := by
  obtain ⟨C, hC, hupper⟩ := eventually_countD_three_upper
  exact growth_four_of_three_upper hC hupper

theorem growth_three_and_four :
    HasOrder (countD 3) (fun X => Real.sqrt X) ∧
      HasOrder (countD 4) (fun X => X) := ⟨growth_three, growth_four⟩

end Erdos374Research
