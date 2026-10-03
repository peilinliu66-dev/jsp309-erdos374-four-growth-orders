import Mathlib

/-!
# An elementary square-divisor tail bound

UNCOMPILED. Counting all large integer squares, rather than only prime
squares, gives the uniform X/Z error needed after a finite CRT sieve.
-/

namespace Erdos374Research

open Finset
open scoped BigOperators

theorem sum_reciprocal_differences (Z H : ℕ) (hZ : 1 ≤ Z) (hZH : Z ≤ H) :
    (∑ d ∈ Finset.Icc (Z + 1) H, ((1 : ℝ) / ((d : ℝ) - 1) - 1 / d)) =
      (1 : ℝ) / Z - 1 / H := by
  induction H, hZH using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self Z), Finset.sum_empty]
      ring
  | succ H hZH ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
      have hZ0 : (Z : ℝ) ≠ 0 := by exact_mod_cast (show Z ≠ 0 by omega)
      have hH1 : (H : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hH0, hZ0, hH1]
      ring

theorem inverse_square_le_reciprocal_difference {d : ℕ} (hd : 2 ≤ d) :
    (1 : ℝ) / (d : ℝ) ^ 2 ≤ 1 / ((d : ℝ) - 1) - 1 / d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hid : (1 : ℝ) / ((d : ℝ) - 1) - 1 / d = 1 / ((d : ℝ) * ((d : ℝ) - 1)) := by
    field_simp [hd0.ne', hd1.ne']
    ring
  rw [hid]
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hd0 hd1) (by nlinarith)

theorem sum_inverse_squares_tail_le (Z H : ℕ) (hZ : 1 ≤ Z) :
    (∑ d ∈ Finset.Icc (Z + 1) H, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 1 / Z := by
  by_cases hZH : Z ≤ H
  · calc
      (∑ d ∈ Finset.Icc (Z + 1) H, (1 : ℝ) / (d : ℝ) ^ 2) ≤
          ∑ d ∈ Finset.Icc (Z + 1) H, ((1 : ℝ) / ((d : ℝ) - 1) - 1 / d) := by
        apply Finset.sum_le_sum
        intro d hd
        exact inverse_square_le_reciprocal_difference (by have := (Finset.mem_Icc.mp hd).1; omega)
      _ = (1 : ℝ) / Z - 1 / H := sum_reciprocal_differences Z H hZ hZH
      _ ≤ (1 : ℝ) / Z := sub_le_self _ (by positivity)
  · have hempty : Finset.Icc (Z + 1) H = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hempty, Finset.sum_empty]
    positivity

def largeSquareMultiples (X Z : ℕ) : Finset ℕ :=
  (Finset.Icc (Z + 1) (Nat.sqrt X)).biUnion fun d =>
    (Finset.Ioc 0 X).filter (fun n => d ^ 2 ∣ n)

theorem card_largeSquareMultiples_le (X Z : ℕ) (hZ : 1 ≤ Z) :
    ((largeSquareMultiples X Z).card : ℝ) ≤ (X : ℝ) / Z := by
  have hcard : (largeSquareMultiples X Z).card ≤
      ∑ d ∈ Finset.Icc (Z + 1) (Nat.sqrt X),
        ((Finset.Ioc 0 X).filter (fun n => d ^ 2 ∣ n)).card := Finset.card_biUnion_le
  have hterm : ∀ d ∈ Finset.Icc (Z + 1) (Nat.sqrt X),
      (((Finset.Ioc 0 X).filter (fun n => d ^ 2 ∣ n)).card : ℝ) ≤
        (X : ℝ) / (d : ℝ) ^ 2 := by
    intro d hd
    have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    apply (le_div_iff₀ (sq_pos_of_pos hdR)).mpr
    exact_mod_cast Nat.div_mul_le_self X (d ^ 2)
  calc
    ((largeSquareMultiples X Z).card : ℝ) ≤
        ∑ d ∈ Finset.Icc (Z + 1) (Nat.sqrt X),
          (((Finset.Ioc 0 X).filter (fun n => d ^ 2 ∣ n)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ d ∈ Finset.Icc (Z + 1) (Nat.sqrt X), (X : ℝ) / (d : ℝ) ^ 2 :=
      Finset.sum_le_sum hterm
    _ = (X : ℝ) * ∑ d ∈ Finset.Icc (Z + 1) (Nat.sqrt X), (1 : ℝ) / (d : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (X : ℝ) * (1 / Z) :=
      mul_le_mul_of_nonneg_left (sum_inverse_squares_tail_le Z (Nat.sqrt X) hZ) (Nat.cast_nonneg X)
    _ = (X : ℝ) / Z := by ring

end Erdos374Research
