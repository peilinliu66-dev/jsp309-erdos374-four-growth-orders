import Mathlib

/-!
# Crude finite Euler products with polynomial loss

UNCOMPILED. These elementary telescoping products are sufficient for the
positive density of rough squarefree cofactors; no Mertens asymptotic or
exact squarefree density is assumed.
-/

namespace Erdos374Research

open Finset
open scoped BigOperators

theorem prod_le_prod_subset_unit {α : Type*} [DecidableEq α]
    (s t : Finset α) (f : α → ℝ) (hsub : s ⊆ t)
    (hnonneg : ∀ x ∈ t, 0 ≤ f x) (hone : ∀ x ∈ t, f x ≤ 1) :
    (∏ x ∈ t, f x) ≤ ∏ x ∈ s, f x := by
  have hfilter : t.filter (fun x => x ∈ s) = s := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  calc
    (∏ x ∈ t, f x) ≤ ∏ x ∈ t, (if x ∈ s then f x else 1) := by
      apply Finset.prod_le_prod hnonneg
      intro x hx
      split_ifs with hs
      · exact le_rfl
      · exact hone x hx
    _ = ∏ x ∈ s, f x := by rw [← Finset.prod_filter, hfilter]

theorem prod_one_sub_reciprocal (B : ℕ) (hB : 1 ≤ B) :
    (∏ d ∈ Finset.Icc 2 B, (1 - (1 : ℝ) / d)) = 1 / B := by
  induction B, hB using Nat.le_induction with
  | base => norm_num
  | succ B hB ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      push_cast
      have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
      have hB1 : (B : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hB0, hB1]
      ring

theorem prod_one_sub_reciprocal_square (Z : ℕ) (hZ : 1 ≤ Z) :
    (∏ d ∈ Finset.Icc 2 Z, (1 - (1 : ℝ) / (d : ℝ) ^ 2)) =
      ((Z : ℝ) + 1) / (2 * Z) := by
  induction Z, hZ using Nat.le_induction with
  | base => norm_num
  | succ Z hZ ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      push_cast
      have hZ0 : (Z : ℝ) ≠ 0 := by exact_mod_cast (show Z ≠ 0 by omega)
      have hZ1 : (Z : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hZ0, hZ1]
      ring

theorem prime_product_lower (B : ℕ) (hB : 1 ≤ B) :
    (1 : ℝ) / B ≤ ∏ p ∈ (Finset.Icc 2 B).filter Nat.Prime, (1 - (1 : ℝ) / p) := by
  rw [← prod_one_sub_reciprocal B hB]
  apply prod_le_prod_subset_unit _ _ _ (Finset.filter_subset _ _)
  · intro d hd
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by have := (Finset.mem_Icc.mp hd).1; omega)
    have hinv : (1 : ℝ) / d ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < d)).mpr hdR
    linarith
  · intro d hd
    have hnon : (0 : ℝ) ≤ 1 / d := by positivity
    linarith

theorem prime_square_product_lower (B Z : ℕ) (hB : 1 ≤ B) (hZ : 1 ≤ Z) :
    (1 / 2 : ℝ) ≤
      ∏ p ∈ (Finset.Icc (B + 1) Z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ) ^ 2) := by
  have hsub : (Finset.Icc (B + 1) Z).filter Nat.Prime ⊆ Finset.Icc 2 Z := by
    intro p hp
    have hpd := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Icc.mpr ⟨by omega, hpd.2⟩
  have hprod := prod_le_prod_subset_unit _ _
    (fun d : ℕ => 1 - (1 : ℝ) / (d : ℝ) ^ 2) hsub
    (by
      intro d hd
      have hdR : (2 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hden : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
      have hfrac : (1 : ℝ) / (d : ℝ) ^ 2 ≤ 1 := (div_le_one hden).mpr (by nlinarith)
      linarith)
    (by
      intro d hd
      have hfrac : (0 : ℝ) ≤ 1 / (d : ℝ) ^ 2 := by positivity
      linarith)
  rw [prod_one_sub_reciprocal_square Z hZ] at hprod
  apply le_trans _ hprod
  have hZR : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Z)).mpr
  linarith

end Erdos374Research
