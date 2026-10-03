import Erdos374Research.TwoFactors

/-!
# The nonsquare family 2q² lies in D3

UNCOMPILED. Unlike the square family in the upstream F3 endpoint, these
integers have minimal factor count exactly three, so they give the required
original D3 lower bound.
-/

namespace Erdos374Research

open Filter Finset
open scoped BigOperators Topology

theorem not_isSquare_two : ¬ IsSquare (2 : ℕ) := by
  rintro ⟨r, hr⟩
  have hrlt : r < 2 := by nlinarith
  interval_cases r <;> norm_num at hr

theorem two_mul_square_mem_D3 {q : ℕ} (hq : 2 ≤ q) : IsInD 3 (2 * q ^ 2) := by
  have hn : 1 ≤ 2 * q ^ 2 := by nlinarith
  have hqSq : 4 ≤ q ^ 2 := by nlinarith
  have hrep : HasRepresentation 3 (2 * q ^ 2) := by
    rw [hasRepresentation_three_iff]
    refine ⟨2, 2 * q ^ 2 - 1, by decide, by omega, by omega,
      2 * q * (2 * q ^ 2 - 1).factorial, ?_⟩
    have hp := paired_factorials hn
    norm_num only [Nat.factorial_succ, Nat.factorial_zero] at hp ⊢
    nlinarith [hp]
  apply isInD_three_of_representation_of_not_square hrep
  intro hsq
  have hsq' : IsSquare (q ^ 2 * 2) := by simpa only [mul_comm] using hsq
  exact not_isSquare_two ((square_mul_iff (by omega : q ≠ 0) (by decide : 2 ≠ 0)).mp hsq')

def twiceSquareFamily (X : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (Nat.sqrt (X / 2))).image (fun q => 2 * q ^ 2)

theorem card_twiceSquareFamily (X : ℕ) :
    (twiceSquareFamily X).card = Nat.sqrt (X / 2) - 1 := by
  unfold twiceSquareFamily
  rw [Finset.card_image_of_injective _ (fun a b hab => ?_)]
  · simp
  · have hs : a ^ 2 = b ^ 2 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hab
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) hs

theorem twiceSquareFamily_subset (X : ℕ) : twiceSquareFamily X ⊆ numbersInDUpTo 3 X := by
  classical
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
  have hqd := Finset.mem_Icc.mp hq
  have hqSq : q ^ 2 ≤ X / 2 :=
    (Nat.pow_le_pow_left hqd.2 2).trans (Nat.sqrt_le' (X / 2))
  have hnX : 2 * q ^ 2 ≤ X :=
    (Nat.mul_le_mul_left 2 hqSq).trans (Nat.mul_div_le X 2)
  exact mem_numbersInDUpTo.mpr ⟨by nlinarith [hqd.1], hnX, two_mul_square_mem_D3 hqd.1⟩

theorem sqrt_half_sub_one_le_countD_three (X : ℕ) :
    Nat.sqrt (X / 2) - 1 ≤ countD 3 X := by
  rw [← card_twiceSquareFamily]
  exact Finset.card_le_card (twiceSquareFamily_subset X)

theorem eventually_countD_three_lower :
    ∀ᶠ X : ℕ in atTop, Real.sqrt (X : ℝ) / 4 ≤ countD 3 X := by
  filter_upwards [eventually_ge_atTop (64 : ℕ)] with X hX
  let q := Nat.sqrt (X / 2)
  have hq1 : 1 ≤ q := by
    apply Nat.le_sqrt.mpr
    omega
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hqroot := Real.real_sqrt_lt_nat_sqrt_succ (a := X / 2)
  have hySq := Real.sq_sqrt (Nat.cast_nonneg (X / 2))
  have hxSq := Real.sq_sqrt (Nat.cast_nonneg X)
  have hxroot := Real.sqrt_nonneg (X : ℝ)
  have hqroot' : Real.sqrt (X / 2 : ℕ) < (q : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hqroot
  have hdiv : X ≤ 2 * (X / 2) + 1 := by omega
  have hdivR : (X : ℝ) ≤ 2 * ((X / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hdiv
  have hX64 : (64 : ℝ) ≤ X := by exact_mod_cast hX
  have hroot8 : 8 ≤ Real.sqrt (X : ℝ) := by nlinarith
  have hrootQ : Real.sqrt (X : ℝ) < 2 * ((q : ℝ) + 1) := by
    nlinarith [Real.sqrt_nonneg ((X / 2 : ℕ) : ℝ)]
  have hcount : ((q - 1 : ℕ) : ℝ) ≤ countD 3 X := by
    exact_mod_cast sqrt_half_sub_one_le_countD_three X
  rw [Nat.cast_sub hq1, Nat.cast_one] at hcount
  linarith

end Erdos374Research
