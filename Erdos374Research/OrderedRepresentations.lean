import Erdos374Research.FactorialIdentities

/-!
# Ordered tuples and literal distinct-index representations

UNCOMPILED. This interface proves that the finset definition used at the
final endpoint agrees with strictly increasing factorial indices. In
particular, the upstream three-factor theorem will be used on the actual
original representations rather than a weakened proxy.
-/

namespace Erdos374Research

open Finset
open scoped BigOperators

theorem hasRepresentation_succ_iff (k n : ℕ) :
    HasRepresentation (k + 1) n ↔
      ∃ f : Fin (k + 1) → ℕ, StrictMono f ∧ 1 ≤ f 0 ∧
        f (Fin.last k) = n ∧ IsSquare (∏ i, (f i).factorial) := by
  classical
  constructor
  · rintro ⟨s, hcard, hn, hs, hsq⟩
    let f : Fin (k + 1) ↪o ℕ := s.orderEmbOfFin hcard
    have hmem : ∀ i, f i ∈ s := fun i => s.orderEmbOfFin_mem hcard i
    have hlast : f (Fin.last k) = n := by
      apply le_antisymm (hs _ (hmem _)).2
      have hnrange : n ∈ Set.range f := by
        simpa only [f, s.range_orderEmbOfFin hcard] using hn
      rcases hnrange with ⟨i, hi⟩
      have hiLast := f.monotone (Fin.le_last i)
      simpa only [hi] using hiLast
    refine ⟨f, f.strictMono, (hs _ (hmem 0)).1, hlast, ?_⟩
    have himage : (Finset.univ : Finset (Fin (k + 1))).image f = s :=
      s.image_orderEmbOfFin_univ hcard
    have hprod : (∏ i : Fin (k + 1), (f i).factorial) = ∏ a ∈ s, a.factorial := by
      rw [← himage, Finset.prod_image]
      exact fun a ha b hb hab => f.injective hab
    rwa [hprod]
  · rintro ⟨f, hf, hpos, hlast, hsq⟩
    let s := (Finset.univ : Finset (Fin (k + 1))).image f
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · simpa [s] using Finset.card_image_of_injective
        (Finset.univ : Finset (Fin (k + 1))) hf.injective
    · exact Finset.mem_image.mpr ⟨Fin.last k, Finset.mem_univ _, hlast⟩
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
      refine ⟨hpos.trans (hf.monotone (Fin.zero_le i)), ?_⟩
      simpa only [hlast] using hf.monotone (Fin.le_last i)
    · dsimp [s]
      rw [Finset.prod_image]
      · exact hsq
      · exact fun a ha b hb hab => hf.injective hab

theorem hasRepresentation_two_iff (n : ℕ) :
    HasRepresentation 2 n ↔
      ∃ a : ℕ, 1 ≤ a ∧ a < n ∧ IsSquare (a.factorial * n.factorial) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, hasRepresentation_succ_iff]
  constructor
  · rintro ⟨f, hf, ha, hlast, hsq⟩
    have hlt := hf (show (0 : Fin 2) < 1 by decide)
    have hn : f 1 = n := hlast
    refine ⟨f 0, ha, by simpa only [hn] using hlt, ?_⟩
    simpa [Fin.prod_univ_succ, hn] using hsq
  · rintro ⟨a, ha, han, hsq⟩
    refine ⟨![a, n], ?_, ha, by simp, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · simpa [Fin.prod_univ_succ] using hsq

theorem hasRepresentation_three_iff (n : ℕ) :
    HasRepresentation 3 n ↔
      ∃ a b : ℕ, Tao2026.IsFactorialSquareTriple a b n := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, hasRepresentation_succ_iff]
  constructor
  · rintro ⟨f, hf, ha, hlast, hsq⟩
    have hab := hf (show (0 : Fin 3) < 1 by decide)
    have hbn := hf (show (1 : Fin 3) < 2 by decide)
    have hn : f 2 = n := hlast
    rcases hsq with ⟨r, hr⟩
    refine ⟨f 0, f 1, ha, hab, by simpa only [hn] using hbn, r, ?_⟩
    simpa [Fin.prod_univ_succ, hn, pow_two, mul_assoc] using hr
  · rintro ⟨a, b, ha, hab, hbn, r, hr⟩
    refine ⟨![a, b, n], ?_, ha, by simp, r, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
      all_goals omega
    · simpa [Fin.prod_univ_succ, pow_two, mul_assoc] using hr

theorem hasRepresentation_three_iff_upstream (n : ℕ) :
    HasRepresentation 3 n ↔ n ∈ Tao2026.factorialThreeSet := by
  rw [hasRepresentation_three_iff,
    Tao2026.mem_factorialThreeSet_iff_exists_triple]

theorem hasRepresentation_four {a b c n : ℕ}
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcn : c < n)
    (hsq : IsSquare (a.factorial * b.factorial * c.factorial * n.factorial)) :
    HasRepresentation 4 n := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, hasRepresentation_succ_iff]
  refine ⟨![a, b, c, n], ?_, ha, by simp, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  · simpa [Fin.prod_univ_succ, mul_assoc] using hsq

theorem hasRepresentation_five {a b c d n : ℕ}
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hdn : d < n)
    (hsq : IsSquare (a.factorial * b.factorial * c.factorial * d.factorial * n.factorial)) :
    HasRepresentation 5 n := by
  rw [show (5 : ℕ) = 4 + 1 by rfl, hasRepresentation_succ_iff]
  refine ⟨![a, b, c, d, n], ?_, ha, by simp, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  · simpa [Fin.prod_univ_succ, mul_assoc] using hsq

theorem hasRepresentation_six {a b c d e n : ℕ}
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) (hen : e < n)
    (hsq : IsSquare (a.factorial * b.factorial * c.factorial *
      d.factorial * e.factorial * n.factorial)) :
    HasRepresentation 6 n := by
  rw [show (6 : ℕ) = 5 + 1 by rfl, hasRepresentation_succ_iff]
  refine ⟨![a, b, c, d, e, n], ?_, ha, by simp, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  · simpa [Fin.prod_univ_succ, mul_assoc] using hsq

end Erdos374Research
