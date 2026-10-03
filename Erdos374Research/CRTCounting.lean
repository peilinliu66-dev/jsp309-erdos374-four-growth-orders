import Erdos374Research.PeriodicCounting
import Mathlib.Data.ZMod.QuotientRing

/-!
# Exact finite CRT count for avoiding zero residue classes

UNCOMPILED. Small primes will use modulus p, and the remaining finitely
many primes will use p². The independent nonzero-coordinate count is an
application of Mathlib's Chinese remainder equivalence, not a density axiom.
-/

namespace Erdos374Research

open Finset
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (q : ι → ℕ) [∀ i, NeZero (q i)]
variable (hcop : Pairwise (Function.onFun Nat.Coprime q))

def crtNonzeroClasses : Finset (ZMod (∏ i, q i)) :=
  (Fintype.piFinset (fun i => (Finset.univ : Finset (ZMod (q i))).erase 0)).image
    (ZMod.prodEquivPi q hcop).symm

theorem card_crtNonzeroClasses :
    (crtNonzeroClasses q hcop).card = ∏ i, (q i - 1) := by
  unfold crtNonzeroClasses
  rw [Finset.card_image_of_injective _ (ZMod.prodEquivPi q hcop).symm.injective,
    Fintype.card_piFinset]
  simp

theorem mem_crtNonzeroClasses_natCast (n : ℕ) :
    (n : ZMod (∏ i, q i)) ∈ crtNonzeroClasses q hcop ↔
      ∀ i, ¬ q i ∣ n := by
  let e := ZMod.prodEquivPi q hcop
  have hcast : ∀ i, e (n : ZMod (∏ i, q i)) i = (n : ZMod (q i)) := by
    intro i
    have h := congrArg (fun f : (i : ι) → ZMod (q i) => f i) (map_natCast e n)
    exact h
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨y, hy, heq⟩
    have hyEq : y = e (n : ZMod (∏ i, q i)) := by
      have h := congrArg e heq
      simpa only [e, RingEquiv.apply_symm_apply] using h
    rw [hyEq] at hy
    intro i
    have hi := Fintype.mem_piFinset.mp hy i
    have hne : e (n : ZMod (∏ i, q i)) i ≠ 0 := (Finset.mem_erase.mp hi).1
    rw [hcast] at hne
    exact fun hd => hne ((ZMod.natCast_eq_zero_iff n (q i)).mpr hd)
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨e (n : ZMod (∏ i, q i)), ?_, e.symm_apply_apply _⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rw [hcast]
    exact fun hz => hn i ((ZMod.natCast_eq_zero_iff n (q i)).mp hz)

def crtNatResidues : Finset ℕ := (crtNonzeroClasses q hcop).image ZMod.val

theorem crtNatResidues_subset_range [NeZero (∏ i, q i)] :
    crtNatResidues q hcop ⊆ Finset.range (∏ i, q i) := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
  exact Finset.mem_range.mpr (ZMod.val_lt z)

theorem card_crtNatResidues [NeZero (∏ i, q i)] :
    (crtNatResidues q hcop).card = ∏ i, (q i - 1) := by
  unfold crtNatResidues
  rw [Finset.card_image_of_injective _ (ZMod.val_injective _), card_crtNonzeroClasses]

theorem mod_mem_crtNatResidues [NeZero (∏ i, q i)] (n : ℕ) :
    n % (∏ i, q i) ∈ crtNatResidues q hcop ↔ ∀ i, ¬ q i ∣ n := by
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, hval⟩
    have heq : z = (n : ZMod (∏ i, q i)) := by
      apply ZMod.val_injective _
      simpa only [ZMod.val_natCast] using hval
    rw [heq] at hz
    exact (mem_crtNonzeroClasses_natCast q hcop n).mp hz
  · intro hn
    exact Finset.mem_image.mpr ⟨(n : ZMod (∏ i, q i)),
      (mem_crtNonzeroClasses_natCast q hcop n).mpr hn, ZMod.val_natCast _ n⟩

include hcop in
theorem crt_avoidance_prefix_lower (X : ℕ) (hM : 0 < ∏ i, q i) :
    ((∏ i, (q i - 1) : ℕ) : ℝ) / (∏ i, q i : ℕ) * X - (∏ i, q i : ℕ) ≤
      (((Finset.range X).filter (fun n => ∀ i, ¬ q i ∣ n)).card : ℝ) := by
  letI : NeZero (∏ i, q i) := ⟨hM.ne'⟩
  have h := residuePrefix_card_lower_real X hM (crtNatResidues q hcop)
    (crtNatResidues_subset_range q hcop)
  rw [card_crtNatResidues] at h
  simpa only [residuePrefix, mod_mem_crtNatResidues] using h

end
end Erdos374Research
