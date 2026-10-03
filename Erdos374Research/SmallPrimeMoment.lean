import Erdos374Research.WeightedPrimeLogs
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# An elementary small-prime moment bound

UNCOMPILED. This is the finite Euler-product/Markov argument used to discard
integers with a large squarefree component supported on very small primes.
No smooth-number asymptotic or Dickman theorem is assumed.
-/

namespace Erdos374Research

open Finset
open scoped BigOperators

noncomputable section

lemma prod_primes_dvd_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    · have hsub : S ⊆ n.primeFactors := fun p hp =>
        (hS p hp).mem_primeFactors (h p hp) hn
      exact (Finset.prod_dvd_prod_of_subset S n.primeFactors id hsub).trans
        (Nat.prod_primeFactors_dvd n)

lemma divisor_product_expansion (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∏ p ∈ P, (1 + if p ∣ n then w p else 0)) =
      ∑ S ∈ P.powerset, if (∏ p ∈ S, p) ∣ n then ∏ p ∈ S, w p else 0 := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S hSP
  have hsub := Finset.mem_powerset.mp hSP
  by_cases hall : ∀ p ∈ S, p ∣ n
  · rw [if_pos ((prod_primes_dvd_iff (fun p hp => hP p (hsub hp)) n).mpr hall)]
    apply Finset.prod_congr rfl
    intro p hp
    rw [if_pos (hall p hp)]
  · rw [if_neg (mt (prod_primes_dvd_iff (fun p hp => hP p (hsub hp)) n).mp hall)]
    push Not at hall
    obtain ⟨p, hp, hpnot⟩ := hall
    exact Finset.prod_eq_zero hp (if_neg hpnot)

theorem sum_divisor_products_le (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, 0 ≤ w p) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, ∏ p ∈ P, (1 + if p ∣ n then w p else 0)) ≤
      (X : ℝ) * ∏ p ∈ P, (1 + w p / p) := by
  simp_rw [divisor_product_expansion P w hP]
  rw [Finset.sum_comm, Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hSP
  have hsub := Finset.mem_powerset.mp hSP
  let d : ℕ := ∏ p ∈ S, p
  let W : ℝ := ∏ p ∈ S, w p
  have hd : 0 < d := Finset.prod_pos (fun p hp => (hP p (hsub hp)).pos)
  have hW : 0 ≤ W := Finset.prod_nonneg (fun p hp => hw p (hsub hp))
  have hsum : (∑ n ∈ Ioc 0 X, if d ∣ n then W else 0) =
      ((X / d : ℕ) : ℝ) * W := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
  change (∑ n ∈ Ioc 0 X, if d ∣ n then W else 0) ≤ _
  rw [hsum]
  have hratio : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := Nat.cast_div_le
  calc
    ((X / d : ℕ) : ℝ) * W ≤ ((X : ℝ) / d) * W :=
      mul_le_mul_of_nonneg_right hratio hW
    _ = (X : ℝ) * ∏ p ∈ S, w p / p := by
      rw [Finset.prod_div_distrib, ← Nat.cast_prod]
      change (X : ℝ) / d * W = X * (W / d)
      ring

lemma exp_sub_one_le_exp_one_mul {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u - 1 ≤ Real.exp 1 * u := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 0 ≤ 1 - u by linarith) hu (show (1 - u) + u = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  linarith

def smallPrimeSet (y : ℝ) : Finset ℕ := (Icc 2 ⌊y⌋₊).filter Nat.Prime

def smallPrimeMoment (y : ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ smallPrimeSet y, if p ∣ n then (p : ℝ) ^ (1 / Real.log y) else 1

def smallPrimeMomentConstant : ℝ := Real.exp (3 * Real.exp 1 * Real.log 4)

lemma smallPrimeMomentConstant_pos : 0 < smallPrimeMomentConstant := Real.exp_pos _

theorem sum_smallPrimeMoment_le {y : ℝ} (hypos : 0 < y) (hy : 1 ≤ Real.log y) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, smallPrimeMoment y n) ≤ smallPrimeMomentConstant * X := by
  have hlogpos : 0 < Real.log y := by linarith
  have hyone : 1 < y := (Real.log_pos_iff hypos.le).mp hlogpos
  let P := smallPrimeSet y
  let w : ℕ → ℝ := fun p => (p : ℝ) ^ (1 / Real.log y) - 1
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hpy : ∀ p ∈ P, (p : ℝ) ≤ y := by
    intro p hp
    have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    exact (by exact_mod_cast h : (p : ℝ) ≤ ⌊y⌋₊).trans (Nat.floor_le hypos.le)
  have hw : ∀ p ∈ P, 0 ≤ w p := by
    intro p hp
    have hpone : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
    have h := Real.one_le_rpow hpone (by positivity : 0 ≤ 1 / Real.log y)
    dsimp [w]
    linarith
  have hwbound : ∀ p ∈ P,
      w p ≤ Real.exp 1 / Real.log y * Real.log p := by
    intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg
      (by exact_mod_cast (hP p hp).one_lt.le)
    have hlogpy := Real.log_le_log hpR (hpy p hp)
    have hu : 0 ≤ Real.log p / Real.log y := by positivity
    have hu1 : Real.log p / Real.log y ≤ 1 := (div_le_one hlogpos).mpr hlogpy
    have h := exp_sub_one_le_exp_one_mul hu hu1
    dsimp [w]
    rw [Real.rpow_def_of_pos hpR]
    have hexponent : Real.log (p : ℝ) * (1 / Real.log y) =
        Real.log p / Real.log y := by ring
    rw [hexponent]
    calc
      Real.exp (Real.log p / Real.log y) - 1 ≤
          Real.exp 1 * (Real.log p / Real.log y) := h
      _ = Real.exp 1 / Real.log y * Real.log p := by ring
  have hsumlog : (∑ p ∈ P, Real.log p / p) ≤ Real.log 4 * (2 + Real.log y) := by
    have hfloor1 : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff y).mpr hyone.le
    have hupper := Tao2026.weightedPrimeLogSum_le ⌊y⌋₊ (by omega)
    have heq : (∑ p ∈ P, Real.log p / p) = Tao2026.weightedPrimeLogSum ⌊y⌋₊ := by
      rfl
    rw [heq]
    have hlogfloor := Real.log_le_log (by exact_mod_cast (show 0 < ⌊y⌋₊ by omega))
      (Nat.floor_le hypos.le)
    have h4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    exact hupper.trans (by gcongr)
  have hsum : (∑ p ∈ P, w p / p) ≤ 3 * Real.exp 1 * Real.log 4 := by
    calc
      (∑ p ∈ P, w p / p) ≤
          ∑ p ∈ P, (Real.exp 1 / Real.log y) * (Real.log p / p) := by
        apply Finset.sum_le_sum
        intro p hp
        convert div_le_div_of_nonneg_right (hwbound p hp) (Nat.cast_nonneg p) using 1
        ring
      _ = (Real.exp 1 / Real.log y) * ∑ p ∈ P, Real.log p / p := by rw [Finset.mul_sum]
      _ ≤ (Real.exp 1 / Real.log y) * (Real.log 4 * (2 + Real.log y)) := by gcongr
      _ ≤ 3 * Real.exp 1 * Real.log 4 := by
        have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        have hbound : (2 + Real.log y) / Real.log y ≤ 3 :=
          (div_le_iff₀ hlogpos).mpr (by linarith)
        have hscaled := mul_le_mul_of_nonneg_left hbound
          (show 0 ≤ Real.exp 1 * Real.log 4 by positivity)
        convert hscaled using 1 <;> ring
  have hprod : (∏ p ∈ P, (1 + w p / p)) ≤ smallPrimeMomentConstant := by
    calc
      (∏ p ∈ P, (1 + w p / p)) ≤ ∏ p ∈ P, Real.exp (w p / p) := by
        apply Finset.prod_le_prod
        · intro p hp; have := hw p hp; positivity
        · intro p hp; linarith [Real.add_one_le_exp (w p / p)]
      _ = Real.exp (∑ p ∈ P, w p / p) := by rw [Real.exp_sum]
      _ ≤ smallPrimeMomentConstant := Real.exp_le_exp.mpr hsum
  have hmoment := sum_divisor_products_le P w hP hw X
  have heq : ∀ n, (∏ p ∈ P, (1 + if p ∣ n then w p else 0)) =
      smallPrimeMoment y n := by
    intro n
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [w]
    split_ifs <;> ring
  simp_rw [heq] at hmoment
  exact hmoment.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg X))

end
end Erdos374Research
