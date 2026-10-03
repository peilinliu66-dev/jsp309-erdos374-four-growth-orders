import Erdos374Research.PrimeCofactorCounting

/-! UNCOMPILED. Even squarefree cofactors have positive lower density. -/

namespace Erdos374Research

open Finset Filter
open scoped BigOperators Topology

def EvenSquarefreeCofactor (a : ℕ) : Prop := 1 ≤ a ∧ Squarefree a ∧ Even a

theorem rough_two_mul_evenSquarefree {b : ℕ} (hb : IsRoughSquarefree 2 b) :
    EvenSquarefreeCofactor (2 * b) := by
  have hb1 : 1 ≤ b := hb.1
  have hcop : Nat.Coprime 2 b := Nat.prime_two.coprime_iff_not_dvd.mpr
    (hb.2.2 2 Nat.prime_two le_rfl)
  exact ⟨by omega, (Nat.squarefree_mul hcop).mpr ⟨Nat.prime_two.squarefree, hb.2.1⟩,
    ⟨b, by omega⟩⟩

theorem card_evenSquarefree_lower (X : ℕ) :
    (roughSquarefreeUpTo 2 (X / 2)).card ≤
      (predicatePrefix EvenSquarefreeCofactor X).card := by
  classical
  let S := roughSquarefreeUpTo 2 (X / 2)
  have hinj : Function.Injective (fun b : ℕ => 2 * b) := by
    intro b c h
    change 2 * b = 2 * c at h
    omega
  have hsub : S.image (fun b => 2 * b) ⊆ predicatePrefix EvenSquarefreeCofactor X := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
    have hb' := Finset.mem_filter.mp hb
    have hbound := Finset.mem_Ioc.mp hb'.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, ?_⟩,
      rough_two_mul_evenSquarefree hb'.2⟩
    exact (Nat.mul_le_mul_left 2 hbound.2).trans (by
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self X 2)
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hinj] at hcard

theorem evenSquarefree_positive_lower_density :
    ∀ᶠ X : ℕ in atTop, (1 / 24 : ℝ) * X ≤
      (predicatePrefix EvenSquarefreeCofactor X).card := by
  have hrough := (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).eventually
    (eventually_roughSquarefree_positive_density (by norm_num : 2 ≤ 2))
  filter_upwards [hrough, eventually_ge_atTop (2 : ℕ)] with X hr hX
  have hdiv : X ≤ 3 * (X / 2) := by omega
  have hdivR : (X : ℝ) ≤ 3 * (X / 2 : ℕ) := by exact_mod_cast hdiv
  have hc : ((roughSquarefreeUpTo 2 (X / 2)).card : ℝ) ≤
      (predicatePrefix EvenSquarefreeCofactor X).card := by
    exact_mod_cast card_evenSquarefree_lower X
  norm_num at hr
  linarith

theorem admissible_prime_candidates_linear {α : ℝ} (hα : 0 < α) (hαhalf : α < 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop, δ * X ≤
      (primeCofactorProducts (cofactorPowerWindow AdmissibleCofactor α X) X).card := by
  obtain ⟨κ, hκ, hd⟩ := admissibleCofactors_positive_lower_density
  refine ⟨κ * α / 32, by positivity, ?_⟩
  exact positive_density_primeCofactorProducts AdmissibleCofactor hκ hα hαhalf hd

theorem evenSquarefree_prime_candidates_linear {α : ℝ}
    (hα : 0 < α) (hαhalf : α < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, (α / 768) * X ≤
      (primeCofactorProducts (cofactorPowerWindow EvenSquarefreeCofactor α X) X).card := by
  have hcoef : (1 / 24 : ℝ) * α / 32 = α / 768 := by ring
  simpa only [hcoef] using positive_density_primeCofactorProducts EvenSquarefreeCofactor
    (by norm_num : (0 : ℝ) < 1 / 24) hα hαhalf evenSquarefree_positive_lower_density

end Erdos374Research
