import Erdos374Research.TwoFactors
import Tao2026.FactorialOneTermAsymptotics

/-!
# A constant-times-square-root bound for consecutive representations

UNCOMPILED. The logarithmic index budget alone loses a factor log X.
Here the exponential growth of the squarefree component of a! supplies a
summable weight, retaining the full O(sqrt X) order needed by the problem.
-/

namespace Erdos374Research

open Filter Finset
open scoped BigOperators Topology

noncomputable def factorialRootWeight (a : ℕ) : ℝ :=
  1 / Real.sqrt (Tao2026.squarefreeComponent a.factorial)

theorem factorialRootWeight_nonneg (a : ℕ) : 0 ≤ factorialRootWeight a := by
  unfold factorialRootWeight
  positivity

theorem factorialComponent_pos (a : ℕ) :
    0 < Tao2026.squarefreeComponent a.factorial :=
  Tao2026.squarefreeComponent_pos_of_positive ⟨a.factorial, Nat.factorial_pos a⟩

theorem eventually_factorialRootWeight_le_exp :
    ∀ᶠ a : ℕ in atTop, factorialRootWeight a ≤ Real.exp (-(a : ℝ) / 8) := by
  filter_upwards [Tao2026.eventually_log_squarefreeComponent_factorial_lower] with a ha
  let d : ℝ := Tao2026.squarefreeComponent a.factorial
  have hd : 0 < d := by
    change (0 : ℝ) < (Tao2026.squarefreeComponent a.factorial : ℝ)
    exact_mod_cast factorialComponent_pos a
  have hexp : Real.exp ((a : ℝ) / 4) ≤ d := by
    calc
      Real.exp ((a : ℝ) / 4) ≤ Real.exp (Real.log d) := Real.exp_le_exp.mpr ha
      _ = d := Real.exp_log hd
  have hsq : Real.exp ((a : ℝ) / 8) ^ 2 = Real.exp ((a : ℝ) / 4) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsqrt : Real.exp ((a : ℝ) / 8) ≤ Real.sqrt d := by
    have hs := Real.sq_sqrt hd.le
    have hn := Real.sqrt_nonneg d
    have he := Real.exp_pos ((a : ℝ) / 8)
    nlinarith
  calc
    factorialRootWeight a = 1 / Real.sqrt d := rfl
    _ ≤ 1 / Real.exp ((a : ℝ) / 8) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hsqrt
    _ = Real.exp (-(a : ℝ) / 8) := by
      rw [show -(a : ℝ) / 8 = -((a : ℝ) / 8) by ring, Real.exp_neg, one_div]

theorem summable_factorialRootWeight : Summable factorialRootWeight := by
  have hgeo : Summable (fun a : ℕ => Real.exp (-(a : ℝ) / 8)) := by
    have h := Real.summable_exp_nat_mul_iff.mpr (show (-1 / 8 : ℝ) < 0 by norm_num)
    convert h using 1
    ext a
    congr 1
    ring
  apply hgeo.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_factorialRootWeight_le_exp] with a ha
  simpa only [Real.norm_of_nonneg (factorialRootWeight_nonneg a)] using ha

noncomputable def factorialRootWeightSum : ℝ := ∑' a, factorialRootWeight a

theorem factorialRootWeightSum_nonneg : 0 ≤ factorialRootWeightSum :=
  tsum_nonneg factorialRootWeight_nonneg

noncomputable def oneTermFamily (a X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.sqrt (X / Tao2026.squarefreeComponent a.factorial))).image
    (fun r => r ^ 2 * Tao2026.squarefreeComponent a.factorial)

theorem card_oneTermFamily_le (a X : ℕ) :
    ((oneTermFamily a X).card : ℝ) ≤ Real.sqrt X * factorialRootWeight a := by
  let d := Tao2026.squarefreeComponent a.factorial
  let q := Nat.sqrt (X / d)
  have hd : 0 < d := factorialComponent_pos a
  have hcard : (oneTermFamily a X).card ≤ q := by
    calc
      (oneTermFamily a X).card ≤ (Finset.Icc 1 q).card := Finset.card_image_le
      _ = q := by simp
  have hq : q ^ 2 * d ≤ X :=
    (Nat.mul_le_mul_right d (Nat.sqrt_le' (X / d))).trans (Nat.div_mul_le_self X d)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hqreal : (q : ℝ) ^ 2 * d ≤ X := by exact_mod_cast hq
  have hsqD := Real.sq_sqrt hdreal.le
  have hsqX := Real.sq_sqrt (Nat.cast_nonneg X)
  have hsqrtD : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdreal
  have hprodsq : ((q : ℝ) * Real.sqrt (d : ℝ)) ^ 2 ≤ (X : ℝ) := by
    calc
      ((q : ℝ) * Real.sqrt (d : ℝ)) ^ 2 = (q : ℝ) ^ 2 * (d : ℝ) := by
        rw [mul_pow, Real.sq_sqrt hdreal.le]
      _ ≤ (X : ℝ) := hqreal
  have hprod : (q : ℝ) * Real.sqrt d ≤ Real.sqrt X := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hx0 := Real.sqrt_nonneg (X : ℝ)
    nlinarith
  have hqbound : (q : ℝ) ≤ Real.sqrt X / Real.sqrt d :=
    (le_div_iff₀ hsqrtD).mpr hprod
  calc
    ((oneTermFamily a X).card : ℝ) ≤ q := by exact_mod_cast hcard
    _ ≤ Real.sqrt X / Real.sqrt d := hqbound
    _ = Real.sqrt X * factorialRootWeight a := by
      dsimp [factorialRootWeight, d]
      ring

theorem oneTermNumbers_subset_families (X : ℕ) :
    Tao2026.factorialThreeOneTermNumbersUpTo X ⊆
      (Finset.Icc 1 (Tao2026.factorialOneTermIndexBudget X)).biUnion
        (fun a => oneTermFamily a X) := by
  classical
  intro n hn
  have hd := Finset.mem_filter.mp hn
  have hnRange : 1 ≤ n ∧ n ≤ X := Finset.mem_Icc.mp hd.1
  obtain ⟨a, r, ha, han, heq⟩ :=
    Tao2026.mem_factorialThreeOneTermSet_iff_exists_sq_mul.mp hd.2
  have habudget := Tao2026.factorialOneTerm_index_le_budget hnRange.2 hnRange.1 heq
  have hr : 1 ≤ r := by
    by_contra hnot
    have hr0 : r = 0 := by omega
    simp [hr0] at heq
    omega
  have hmult : r ^ 2 * Tao2026.squarefreeComponent a.factorial ≤ X := by
    simpa only [← heq] using hnRange.2
  have hdiv : r ^ 2 ≤ X / Tao2026.squarefreeComponent a.factorial :=
    (Nat.le_div_iff_mul_le (factorialComponent_pos a)).mpr hmult
  have hsqrt : r ≤ Nat.sqrt (X / Tao2026.squarefreeComponent a.factorial) := by
    rw [Nat.le_sqrt]
    simpa only [pow_two] using hdiv
  exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_Icc.mpr ⟨ha, habudget⟩,
    Finset.mem_image.mpr ⟨r, Finset.mem_Icc.mpr ⟨hr, hsqrt⟩, heq.symm⟩⟩

theorem factorialThreeOneTermCount_le_sqrt (X : ℕ) :
    (Tao2026.factorialThreeOneTermCount X : ℝ) ≤
      factorialRootWeightSum * Real.sqrt X := by
  classical
  let s := Finset.Icc 1 (Tao2026.factorialOneTermIndexBudget X)
  have hc : Tao2026.factorialThreeOneTermCount X ≤ ∑ a ∈ s, (oneTermFamily a X).card := by
    change (Tao2026.factorialThreeOneTermNumbersUpTo X).card ≤ _
    exact (Finset.card_le_card (oneTermNumbers_subset_families X)).trans Finset.card_biUnion_le
  have hs : (∑ a ∈ s, factorialRootWeight a) ≤ factorialRootWeightSum :=
    summable_factorialRootWeight.sum_le_tsum s (fun a ha => factorialRootWeight_nonneg a)
  calc
    (Tao2026.factorialThreeOneTermCount X : ℝ) ≤ ∑ a ∈ s, ((oneTermFamily a X).card : ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ a ∈ s, Real.sqrt X * factorialRootWeight a :=
      Finset.sum_le_sum (fun a ha => card_oneTermFamily_le a X)
    _ = Real.sqrt X * ∑ a ∈ s, factorialRootWeight a := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt X * factorialRootWeightSum :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ = factorialRootWeightSum * Real.sqrt X := mul_comm _ _

end Erdos374Research
