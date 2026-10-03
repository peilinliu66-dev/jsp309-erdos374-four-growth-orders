import Mathlib

/-!
# Literal factorial-square representations for Erdős problem 374

Original statements for the order-of-growth formalization of Yudin (2026).
This file is an uncompiled research draft. The mathematical source is
https://arxiv.org/html/2610.01899v1 .

A finite set records distinct positive factorial indices. Its largest index
is explicitly `n`; no multiset, repeated factorial, or finite sample is used
in the original-problem endpoint.
-/

namespace Erdos374Research

open Filter Finset
open scoped BigOperators Topology

/-- A product of `k` distinct positive-index factorials, with largest index
`n`, is a square in the natural numbers. -/
def HasRepresentation (k n : ℕ) : Prop :=
  ∃ s : Finset ℕ, s.card = k ∧ n ∈ s ∧
    (∀ a ∈ s, 1 ≤ a ∧ a ≤ n) ∧ IsSquare (∏ a ∈ s, a.factorial)

/-- Literal membership in `D_k`: the least admissible number of factorials,
among numbers at least two, is exactly `k`. -/
def IsInD (k n : ℕ) : Prop :=
  2 ≤ k ∧ HasRepresentation k n ∧
    ∀ j : ℕ, 2 ≤ j → j < k → ¬ HasRepresentation j n

noncomputable def numbersInDUpTo (k X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (IsInD k)

noncomputable def countD (k X : ℕ) : ℕ := (numbersInDUpTo k X).card

@[simp] theorem mem_numbersInDUpTo {k X n : ℕ} :
    n ∈ numbersInDUpTo k X ↔ 1 ≤ n ∧ n ≤ X ∧ IsInD k n := by
  classical
  simp [numbersInDUpTo, and_assoc]

theorem representation_card_le {k n : ℕ} (h : HasRepresentation k n) : k ≤ n := by
  classical
  rcases h with ⟨s, hcard, hn, hs, hsq⟩
  have hsub : s ⊆ Finset.Icc 1 n := by
    intro a ha
    exact Finset.mem_Icc.mpr (hs a ha)
  have hc := Finset.card_le_card hsub
  simpa [hcard] using hc

theorem IsInD.two_le_endpoint {k n : ℕ} (h : IsInD k n) : 2 ≤ n :=
  h.1.trans (representation_card_le h.2.1)

theorem isInD_unique {k j n : ℕ} (hk : IsInD k n) (hj : IsInD j n) : k = j := by
  rcases lt_trichotomy k j with h | h | h
  · exact False.elim (hj.2.2 k hk.1 h hk.2.1)
  · exact h
  · exact False.elim (hk.2.2 j hj.1 h hj.2.1)

theorem isInD_iff_minimal {k n : ℕ} :
    IsInD k n ↔ 2 ≤ k ∧ HasRepresentation k n ∧
      ∀ j, 2 ≤ j → HasRepresentation j n → k ≤ j := by
  constructor
  · rintro ⟨hk, hrep, hmin⟩
    refine ⟨hk, hrep, ?_⟩
    intro j hj hjrep
    by_contra hnot
    exact hmin j hj (Nat.lt_of_not_ge hnot) hjrep
  · rintro ⟨hk, hrep, hmin⟩
    refine ⟨hk, hrep, ?_⟩
    intro j hj hjk hjrep
    exact (Nat.not_lt_of_ge (hmin j hj hjrep)) hjk

theorem exists_isInD_of_representation {k n : ℕ}
    (hk : 2 ≤ k) (hrep : HasRepresentation k n) :
    ∃ j, j ≤ k ∧ IsInD j n := by
  classical
  have hex : ∃ j, 2 ≤ j ∧ HasRepresentation j n := ⟨k, hk, hrep⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  refine ⟨j, Nat.find_min' hex ⟨hk, hrep⟩, hj.1, hj.2, ?_⟩
  intro i hi hij hirep
  exact Nat.find_min hex hij ⟨hi, hirep⟩

theorem countD_le (k X : ℕ) : countD k X ≤ X := by
  classical
  unfold countD numbersInDUpTo
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem countD_mono (k : ℕ) : Monotone (countD k) := by
  classical
  intro X Y hXY
  apply Finset.card_le_card
  intro n hn
  rw [mem_numbersInDUpTo] at hn ⊢
  exact ⟨hn.1, hn.2.1.trans hXY, hn.2.2⟩

/-- Order of growth with both positive constant factors and one eventual
threshold. This is stronger than merely an exponent `r+o(1)`. -/
def HasOrder (f : ℕ → ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ X : ℕ in atTop, c * g X ≤ f X ∧ (f X : ℝ) ≤ C * g X

/-- Full order-of-growth scope asked for in the original problem. -/
def OriginalGrowthConclusion : Prop :=
  HasOrder (countD 3) (fun X => Real.sqrt X) ∧
  HasOrder (countD 4) (fun X => X) ∧
  HasOrder (countD 5) (fun X => X) ∧
  HasOrder (countD 6) (fun X => X)

theorem hasOrder_linear_of_lower (k : ℕ)
    (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ countD k X) :
    HasOrder (countD k) (fun X => X) := by
  rcases h with ⟨c, hc, h⟩
  refine ⟨c, 1, hc, zero_lt_one, ?_⟩
  filter_upwards [h] with X hX
  refine ⟨hX, ?_⟩
  simpa using (show (countD k X : ℝ) ≤ X by exact_mod_cast countD_le k X)

end Erdos374Research
