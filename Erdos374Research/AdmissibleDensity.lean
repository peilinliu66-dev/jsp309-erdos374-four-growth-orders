import Erdos374Research.CofactorTail
import Erdos374Research.RoughSquarefreeDensity

/-!
# Positive lower density of admissible squarefree cofactors

UNCOMPILED. The finite witness-selection argument uses the same cofactor
set as Yudin's Lemma 7.1. Every small factorial is handled by coprimality;
the remaining finite selected witnesses are bounded by the exponential tail.
-/

namespace Erdos374Research

open Finset Filter
open scoped BigOperators Topology

noncomputable section

theorem rough_small_factorial_component {B a c : ℕ}
    (ha : IsRoughSquarefree B a) (hc : c ≤ B) :
    a ≤ Tao2026.squarefreeComponent (a * c.factorial) := by
  have hcop : Nat.Coprime a c.factorial := by
    apply Nat.coprime_of_dvd
    intro p hp hpa hpf
    have hpc : p ≤ c := hp.dvd_factorial.mp hpf
    exact ha.2.2 p hp (hpc.trans hc) hpa
  have hcop' : Nat.Coprime a (Tao2026.squarefreeComponent c.factorial) :=
    hcop.of_dvd_right (Tao2026.squarefreeComponent_dvd c.factorial)
  rw [squarefreeComponent_mul_factorial ha.2.1, hcop'.gcd_eq_one, Nat.div_one, Nat.div_one]
  have hpos : 1 ≤ Tao2026.squarefreeComponent c.factorial := factorialComponent_pos c
  simpa only [mul_one] using Nat.mul_le_mul_left a hpos

def admissibleCofactorsUpTo (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 0 X).filter AdmissibleCofactor

def excludedRoughCofactors (B X : ℕ) : Finset ℕ := by
  classical
  exact (roughSquarefreeUpTo B X).filter (fun a => ¬ AdmissibleCofactor a)

theorem excludedRoughCofactor_has_witness (B X : ℕ)
    (a : ↥(excludedRoughCofactors B X)) :
    ∃ c : ℕ, B < c ∧ a.1 ∈ badCofactorsFor X c := by
  classical
  have ha := Finset.mem_filter.mp a.2
  have haRough := Finset.mem_filter.mp ha.1
  have hex : ∃ c : ℕ, Tao2026.squarefreeComponent (a.1 * c.factorial) < a.1 := by
    by_contra hnot
    apply ha.2
    refine ⟨haRough.2.1, haRough.2.2.1, ?_⟩
    intro c
    by_contra hnotle
    exact hnot ⟨c, Nat.lt_of_not_ge hnotle⟩
  obtain ⟨c, hc⟩ := hex
  have hBc : B < c := by
    by_contra hnot
    exact (not_lt_of_ge (rough_small_factorial_component haRough.2 (Nat.le_of_not_gt hnot))) hc
  exact ⟨c, hBc, Finset.mem_filter.mpr ⟨haRough.1, haRough.2.2.1, hc⟩⟩

theorem card_excludedRoughCofactors_le {B X : ℕ}
    (htail : ∀ S : Finset ℕ, (∀ c ∈ S, B < c) →
      (∑ c ∈ S, badFactorialWeight c) ≤ (1 : ℝ) / (8 * B)) :
    ((excludedRoughCofactors B X).card : ℝ) ≤ (X : ℝ) / (8 * B) := by
  classical
  let f : ↥(excludedRoughCofactors B X) → ℕ := fun a =>
    Classical.choose (excludedRoughCofactor_has_witness B X a)
  have hf : ∀ a, B < f a ∧ a.1 ∈ badCofactorsFor X (f a) := fun a =>
    Classical.choose_spec (excludedRoughCofactor_has_witness B X a)
  let S := (Finset.univ : Finset ↥(excludedRoughCofactors B X)).image f
  have hS : ∀ c ∈ S, B < c := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨a, ha, rfl⟩
    exact (hf a).1
  have hsub : excludedRoughCofactors B X ⊆ S.biUnion (badCofactorsFor X) := by
    intro a ha
    let z : ↥(excludedRoughCofactors B X) := ⟨a, ha⟩
    exact Finset.mem_biUnion.mpr ⟨f z,
      Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩, (hf z).2⟩
  have hcard : (excludedRoughCofactors B X).card ≤
      ∑ c ∈ S, (badCofactorsFor X c).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    ((excludedRoughCofactors B X).card : ℝ) ≤ ∑ c ∈ S, ((badCofactorsFor X c).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ c ∈ S, (X : ℝ) * badFactorialWeight c :=
      Finset.sum_le_sum (fun c hc => card_badCofactorsFor_le X c)
    _ = (X : ℝ) * ∑ c ∈ S, badFactorialWeight c := by rw [Finset.mul_sum]
    _ ≤ (X : ℝ) * (1 / (8 * B)) :=
      mul_le_mul_of_nonneg_left (htail S hS) (Nat.cast_nonneg X)
    _ = (X : ℝ) / (8 * B) := by ring

theorem rough_card_le_admissible_add_excluded (B X : ℕ) :
    (roughSquarefreeUpTo B X).card ≤
      (admissibleCofactorsUpTo X).card + (excludedRoughCofactors B X).card := by
  classical
  have hsub : roughSquarefreeUpTo B X ⊆ admissibleCofactorsUpTo X ∪ excludedRoughCofactors B X := by
    intro a ha
    by_cases hadm : AdmissibleCofactor a
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp ha).1, hadm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha, hadm⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem admissibleCofactors_positive_lower_density :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ X : ℕ in atTop,
      κ * X ≤ (admissibleCofactorsUpTo X).card := by
  obtain ⟨B, hB, htail⟩ := exists_badFactorialWeight_tail_small
  have hBR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  refine ⟨1 / (8 * B), by positivity, ?_⟩
  filter_upwards [eventually_roughSquarefree_positive_density hB] with X hX
  have hbad := card_excludedRoughCofactors_le (X := X) htail
  have hsplit : ((roughSquarefreeUpTo B X).card : ℝ) ≤
      (admissibleCofactorsUpTo X).card + (excludedRoughCofactors B X).card := by
    exact_mod_cast rough_card_le_admissible_add_excluded B X
  have hid : (X : ℝ) / (4 * B) - (X : ℝ) / (8 * B) = (1 / (8 * B)) * X := by
    field_simp [hBR.ne']
    ring
  linarith

end
end Erdos374Research
