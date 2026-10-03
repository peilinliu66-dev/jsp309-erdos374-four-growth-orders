import Erdos374Research.TwoFactors

/-!
# A positive-density supply of at-most-four-factor representations

UNCOMPILED. Multiples of four give a sufficient family. After removing the
two- and three-factor sets, the finite inequality below yields D4 of order X.
No assertion about the exact density of nonsquarefree integers is needed.
-/

namespace Erdos374Research

open Finset Filter
open scoped BigOperators Topology

theorem hasRepresentation_four_of_four_mul {u : ℕ} (hu : 2 ≤ u) :
    HasRepresentation 4 (4 * u) := by
  apply hasRepresentation_four (a := u - 1) (b := u) (c := 4 * u - 1)
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨2 * u * (4 * u - 1).factorial * (u - 1).factorial, ?_⟩
  have hid : (4 * u).factorial * (4 * u - 1).factorial *
      u.factorial * (u - 1).factorial =
      (2 * u * (4 * u - 1).factorial * (u - 1).factorial) ^ 2 := by
    simpa using four_factorial_identity (u := u) (v := 2) (by omega) (by decide)
  calc
    (u - 1).factorial * u.factorial * (4 * u - 1).factorial * (4 * u).factorial =
        (4 * u).factorial * (4 * u - 1).factorial * u.factorial * (u - 1).factorial := by ring
    _ = _ := by simpa only [pow_two] using hid

def fourMultipleFamily (X : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (X / 4)).image (fun u => 4 * u)

theorem card_fourMultipleFamily (X : ℕ) :
    (fourMultipleFamily X).card = X / 4 - 1 := by
  unfold fourMultipleFamily
  rw [Finset.card_image_of_injective _
    (fun a b h => Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h)]
  simp

theorem fourMultipleFamily_subset (X : ℕ) :
    fourMultipleFamily X ⊆
      numbersInDUpTo 2 X ∪ numbersInDUpTo 3 X ∪ numbersInDUpTo 4 X := by
  classical
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨u, hu, rfl⟩
  have huData := Finset.mem_Icc.mp hu
  have hnX : 4 * u ≤ X :=
    (Nat.mul_le_mul_left 4 huData.2).trans (Nat.mul_div_le X 4)
  have hn1 : 1 ≤ 4 * u := by omega
  obtain ⟨j, hj4, hj⟩ := exists_isInD_of_representation (by decide : 2 ≤ 4)
    (hasRepresentation_four_of_four_mul huData.1)
  have hcases : j = 2 ∨ j = 3 ∨ j = 4 := by have := hj.1; omega
  rcases hcases with rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (mem_numbersInDUpTo.mpr ⟨hn1, hnX, hj⟩))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (mem_numbersInDUpTo.mpr ⟨hn1, hnX, hj⟩))
  · exact Finset.mem_union_right _ (mem_numbersInDUpTo.mpr ⟨hn1, hnX, hj⟩)

theorem floor_quarter_le_sum_counts (X : ℕ) :
    X / 4 - 1 ≤ countD 2 X + countD 3 X + countD 4 X := by
  rw [← card_fourMultipleFamily]
  calc
    (fourMultipleFamily X).card ≤
        (numbersInDUpTo 2 X ∪ numbersInDUpTo 3 X ∪ numbersInDUpTo 4 X).card :=
      Finset.card_le_card (fourMultipleFamily_subset X)
    _ ≤ (numbersInDUpTo 2 X ∪ numbersInDUpTo 3 X).card + (numbersInDUpTo 4 X).card :=
      Finset.card_union_le _ _
    _ ≤ countD 2 X + countD 3 X + countD 4 X :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _

theorem growth_four_of_three_upper {C : ℝ} (hC : 0 < C)
    (hthree : ∀ᶠ X : ℕ in atTop, (countD 3 X : ℝ) ≤ C * Real.sqrt X) :
    HasOrder (countD 4) (fun X => X) := by
  apply hasOrder_linear_of_lower
  refine ⟨1 / 8, by norm_num, ?_⟩
  have hlarge : ∀ᶠ X : ℕ in atTop,
      max 32 ((16 * (C + 1)) ^ 2) ≤ (X : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hthree, hlarge, eventually_ge_atTop (4 : ℕ)] with X h3 hX hX4
  have hX32 : (32 : ℝ) ≤ X := (le_max_left _ _).trans hX
  have hXsquared : (16 * (C + 1)) ^ 2 ≤ (X : ℝ) := (le_max_right _ _).trans hX
  have hsquare : (Real.sqrt (X : ℝ)) ^ 2 = X := Real.sq_sqrt (Nat.cast_nonneg _)
  have hroot : 16 * (C + 1) ≤ Real.sqrt (X : ℝ) := by
    nlinarith [Real.sqrt_nonneg (X : ℝ)]
  have hlinear : (C + 1) * Real.sqrt (X : ℝ) ≤ (X : ℝ) / 16 := by
    have hm := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (X : ℝ))
    nlinarith
  have htwo : (countD 2 X : ℝ) ≤ Real.sqrt X := by
    rw [countD_two]
    exact (show ((Nat.sqrt X - 1 : ℕ) : ℝ) ≤ Nat.sqrt X by
      exact_mod_cast Nat.sub_le (Nat.sqrt X) 1).trans Real.nat_sqrt_le_real_sqrt
  have hdiv1 : 1 ≤ X / 4 := by omega
  have hcount : ((X / 4 - 1 : ℕ) : ℝ) ≤
      (countD 2 X : ℝ) + countD 3 X + countD 4 X := by
    exact_mod_cast floor_quarter_le_sum_counts X
  rw [Nat.cast_sub hdiv1, Nat.cast_one] at hcount
  have hmod : X % 4 < 4 := Nat.mod_lt X (by decide)
  have hdivision : (X : ℝ) = (X / 4 : ℕ) * 4 + (X % 4 : ℕ) := by
    exact_mod_cast (show X = (X / 4) * 4 + X % 4 by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod X 4).symm)
  have hmodreal : ((X % 4 : ℕ) : ℝ) < 4 := by exact_mod_cast hmod
  nlinarith

end Erdos374Research
