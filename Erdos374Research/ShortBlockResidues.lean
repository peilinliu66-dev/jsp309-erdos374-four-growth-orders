import Erdos374Research.RepresentationBlocks
import Erdos374Research.WeilResidues
import Erdos374Research.ShortBlockSieve

/-!
# The square-value residues of a punctured short block

UNCOMPILED. Removing the unique multiple of the large prime leaves a
nonconstant split polynomial. Its remaining roots are distinct modulo each
sieve prime, and the actual Weil bound excludes a fixed fraction of residues.
-/

namespace Erdos374Research

open Finset Tao2026
open scoped BigOperators

noncomputable section

def puncturedRoots (q l j : ℕ) : Finset (ZMod q) :=
  ((Finset.range l).erase j).image (fun i : ℕ => (i : ZMod q))

def puncturedSquareResidues (q a t c l j : ℕ) [NeZero q] : Finset (ZMod q) :=
  splitSquareResidues q ((a * t * c.factorial : ℕ) : ZMod q) (puncturedRoots q l j)

lemma puncturedRoots_nonempty (q : ℕ) {l j : ℕ} (hl : 2 ≤ l) :
    (puncturedRoots q l j).Nonempty := by
  have hne : ((Finset.range l).erase j).Nonempty := by
    by_cases hj : j = 0
    · exact ⟨1, Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩
    · exact ⟨0, Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_range.mpr (by omega)⟩⟩
  exact hne.image _

lemma puncturedSquareResidues_nonempty (q a t c : ℕ) [NeZero q]
    {l j : ℕ} (hl : 2 ≤ l) : (puncturedSquareResidues q a t c l j).Nonempty := by
  obtain ⟨r, hr⟩ := puncturedRoots_nonempty q (j := j) hl
  refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  have hz : splitValue ((a * t * c.factorial : ℕ) : ZMod q) (puncturedRoots q l j) r = 0 := by
    unfold splitValue
    rw [Finset.prod_eq_zero hr (sub_self r), mul_zero]
  rw [hz]
  exact IsSquare.zero

lemma natCast_injective_on_short_range {q l j : ℕ} [NeZero q] (hlq : l ≤ q) :
    Set.InjOn (fun i : ℕ => (i : ZMod q)) ((Finset.range l).erase j) := by
  intro i hi k hk heq
  have hiq : i < q := (Finset.mem_range.mp (Finset.mem_erase.mp hi).2).trans_le hlq
  have hkq : k < q := (Finset.mem_range.mp (Finset.mem_erase.mp hk).2).trans_le hlq
  have hv := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hiq, Nat.mod_eq_of_lt hkq] using hv

lemma puncturedRoots_card_le (q l j : ℕ) : (puncturedRoots q l j).card ≤ l := by
  exact (Finset.card_image_le).trans ((Finset.card_erase_le).trans (by simp))

lemma puncturedSquareResidues_mem {q a t c m l j : ℕ} [NeZero q]
    (hlm : l ≤ m) (hlq : l ≤ q)
    (hsq : IsSquare (a * t * c.factorial * puncturedFalling m l j)) :
    (m : ZMod q) ∈ puncturedSquareResidues q a t c l j := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hprod : (puncturedFalling m l j : ZMod q) =
      ∏ r ∈ puncturedRoots q l j, ((m : ZMod q) - r) := by
    unfold puncturedRoots puncturedFalling
    rw [Finset.prod_image (natCast_injective_on_short_range hlq), Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have him : i ≤ m := (Finset.mem_range.mp (Finset.mem_erase.mp hi).2).le.trans hlm
    exact Nat.cast_sub him
  rcases hsq with ⟨r, hr⟩
  refine ⟨(r : ZMod q), ?_⟩
  have hcast := congrArg (fun n : ℕ => (n : ZMod q)) hr
  simpa only [splitValue, Nat.cast_mul, hprod] using hcast

lemma puncturedScalar_ne_zero {q a t c : ℕ} [NeZero q] [Fact q.Prime]
    (ha : 1 ≤ a) (ht : 1 ≤ t) (haq : a < q) (htq : t < q) (hcq : c < q) :
    ((a * t * c.factorial : ℕ) : ZMod q) ≠ 0 := by
  have hq : q.Prime := Fact.out
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hd
  rcases hq.dvd_mul.mp hd with hat | hfact
  · rcases hq.dvd_mul.mp hat with had | htd
    · exact (not_le_of_gt haq) (Nat.le_of_dvd ha had)
    · exact (not_le_of_gt htq) (Nat.le_of_dvd ht htd)
  · exact (not_le_of_gt hcq) (hq.dvd_factorial.mp hfact)

theorem puncturedSquareResidues_card_le_three_quarters
    {q a t c l j : ℕ} [NeZero q] [Fact q.Prime]
    (hq2 : q ≠ 2) (ha : 1 ≤ a) (ht : 1 ≤ t)
    (haq : a < q) (htq : t < q) (hcq : c < q)
    (hl : 2 ≤ l) (hlsmall : 8 * (l : ℝ) ≤ Real.sqrt q) :
    ((puncturedSquareResidues q a t c l j).card : ℝ) ≤ 3 / 4 * q := by
  have hweil := card_splitSquareResidues_le q hq2
    (puncturedScalar_ne_zero ha ht haq htq hcq) (puncturedRoots q l j)
    (puncturedRoots_nonempty q hl)
  have hrootcard : ((puncturedRoots q l j).card : ℝ) ≤ l := by
    exact_mod_cast puncturedRoots_card_le q l j
  have hrootpred : ((puncturedRoots q l j).card - 1 : ℕ) ≤ l :=
    (Nat.sub_le _ _).trans (puncturedRoots_card_le q l j)
  have hrootpredR : (((puncturedRoots q l j).card - 1 : ℕ) : ℝ) ≤ l := by
    exact_mod_cast hrootpred
  have hqnon := Real.sqrt_nonneg (q : ℝ)
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg q)
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hmul := mul_le_mul_of_nonneg_right hrootpredR hqnon
  have hlroot := mul_le_mul_of_nonneg_right hlsmall hqnon
  have hqroot : Real.sqrt (q : ℝ) ≤ q := by nlinarith
  change ((puncturedSquareResidues q a t c l j).card : ℝ) ≤ _
  dsimp [puncturedSquareResidues] at *
  nlinarith

end
end Erdos374Research
