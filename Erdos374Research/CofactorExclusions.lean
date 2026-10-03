import Erdos374Research.ConsecutiveCount
import Tao2026.QuadraticSolutionCount

/-!
# The bad cofactor sets have an exponentially decaying density bound

UNCOMPILED. These are the squarefree-component and finite divisibility
estimates in Yudin's Lemma 7.1, with its classical divisor bound supplied
by the actual pinned upstream theorem.
-/

namespace Erdos374Research

open Finset Filter
open scoped BigOperators Topology

def AdmissibleCofactor (a : ℕ) : Prop :=
  1 ≤ a ∧ Squarefree a ∧ ∀ c : ℕ, a ≤ Tao2026.squarefreeComponent (a * c.factorial)

theorem AdmissibleCofactor.not_small_factorial_square {a t c : ℕ}
    (ha : AdmissibleCofactor a) (ht : 1 ≤ t) (hta : t < a) :
    ¬ IsSquare (a * t * c.factorial) := by
  rintro ⟨r, hr⟩
  have hac : a * c.factorial ≠ 0 :=
    Nat.mul_ne_zero (by omega) (Nat.factorial_ne_zero c)
  have heq : Tao2026.squarefreeComponent t =
      Tao2026.squarefreeComponent (a * c.factorial) := by
    apply (Tao2026.squarefreeComponent_eq_iff_mul_eq_sq (by omega) hac).mpr
    refine ⟨r, ?_⟩
    calc
      t * (a * c.factorial) = a * t * c.factorial := by ring
      _ = r ^ 2 := by simpa only [pow_two] using hr
  have hsmall : Tao2026.squarefreeComponent t ≤ t :=
    Nat.le_of_dvd ht (Tao2026.squarefreeComponent_dvd t)
  have hlarge := ha.2.2 c
  rw [← heq] at hlarge
  omega

theorem not_isSquare_mul_of_squarefree_left {n m : ℕ}
    (hn : Squarefree n) (hm : 1 ≤ m) (hmn : m < n) : ¬ IsSquare (n * m) := by
  rintro ⟨r, hr⟩
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  have hnComp : Tao2026.squarefreeComponent n = n := by
    exact (Tao2026.eq_squarefreeComponent_of_sq_mul hn0 hn
      (show 1 ^ 2 * n = n by simp)).symm
  have heq : Tao2026.squarefreeComponent n = Tao2026.squarefreeComponent m :=
    (Tao2026.squarefreeComponent_eq_iff_mul_eq_sq hn.ne_zero (by omega)).mpr
      ⟨r, by simpa only [pow_two] using hr⟩
  have hdvd := Tao2026.squarefreeComponent_dvd m
  rw [← heq, hnComp] at hdvd
  exact (not_le_of_gt hmn) (Nat.le_of_dvd hm hdvd)

theorem squarefreeComponent_mul_factorial {a c : ℕ} (ha : Squarefree a) :
    Tao2026.squarefreeComponent (a * c.factorial) =
      (a / Nat.gcd a (Tao2026.squarefreeComponent c.factorial)) *
        (Tao2026.squarefreeComponent c.factorial /
          Nat.gcd a (Tao2026.squarefreeComponent c.factorial)) := by
  let b := Tao2026.squarefreeComponent c.factorial
  let g := Nat.gcd a b
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hb0 : 0 < b := factorialComponent_pos c
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha0
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have haq : a / g * g = a := Nat.div_mul_cancel hga
  have hbq : b / g * g = b := Nat.div_mul_cancel hgb
  have haDvd : a / g ∣ a := ⟨g, haq.symm⟩
  have hbDvd : b / g ∣ b := ⟨g, hbq.symm⟩
  have hsqa : Squarefree (a / g) := ha.squarefree_of_dvd haDvd
  have hsqb : Squarefree (b / g) :=
    (Tao2026.squarefree_squarefreeComponent c.factorial).squarefree_of_dvd hbDvd
  have hcop : Nat.Coprime (a / g) (b / g) :=
    Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hg0
  have hsq : Squarefree (a / g * (b / g)) := (Nat.squarefree_mul hcop).mpr ⟨hsqa, hsqb⟩
  have hid : g ^ 2 * (a / g * (b / g)) = a * b := by
    calc
      _ = (a / g * g) * (b / g * g) := by ring
      _ = a * b := by rw [haq, hbq]
  obtain ⟨q, hq⟩ := Tao2026.exists_sq_mul_squarefreeComponent (Nat.factorial_pos c)
  have htotal : (q * g) ^ 2 * (a / g * (b / g)) = a * c.factorial := by
    calc
      _ = q ^ 2 * (g ^ 2 * (a / g * (b / g))) := by ring
      _ = q ^ 2 * (a * b) := by rw [hid]
      _ = a * (q ^ 2 * b) := by ring
      _ = a * c.factorial := by rw [hq]
  exact (Tao2026.eq_squarefreeComponent_of_sq_mul
    (Nat.mul_pos ha0 (Nat.factorial_pos c)) hsq htotal).symm

theorem bad_cofactor_has_large_common_divisor {a c : ℕ}
    (ha : Squarefree a) (hbad : Tao2026.squarefreeComponent (a * c.factorial) < a) :
    ∃ d ∈ (Tao2026.squarefreeComponent c.factorial).divisors,
      d ∣ a ∧ Tao2026.squarefreeComponent c.factorial < d ^ 2 := by
  let b := Tao2026.squarefreeComponent c.factorial
  let g := Nat.gcd a b
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hb0 : 0 < b := factorialComponent_pos c
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha0
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have haq : a / g * g = a := Nat.div_mul_cancel hga
  have hbq : b / g * g = b := Nat.div_mul_cancel hgb
  have hid : Tao2026.squarefreeComponent (a * c.factorial) * g ^ 2 = a * b := by
    rw [squarefreeComponent_mul_factorial ha]
    change (a / g * (b / g)) * g ^ 2 = a * b
    calc
      _ = (a / g * g) * (b / g * g) := by ring
      _ = a * b := by rw [haq, hbq]
  have hscaled := Nat.mul_lt_mul_of_pos_right hbad (pow_pos hg0 2)
  rw [hid] at hscaled
  have hgbig : b < g ^ 2 := (Nat.mul_lt_mul_left ha0).mp hscaled
  exact ⟨g, Nat.mem_divisors.mpr ⟨hgb, hb0.ne'⟩, hga, hgbig⟩

noncomputable def badCofactorsFor (X c : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 0 X).filter fun a =>
    Squarefree a ∧ Tao2026.squarefreeComponent (a * c.factorial) < a

noncomputable def badFactorialWeight (c : ℕ) : ℝ :=
  ((Tao2026.squarefreeComponent c.factorial).divisors.card : ℝ) /
    Real.sqrt (Tao2026.squarefreeComponent c.factorial)

theorem badFactorialWeight_nonneg (c : ℕ) : 0 ≤ badFactorialWeight c := by
  unfold badFactorialWeight
  positivity

theorem card_badCofactorsFor_le (X c : ℕ) :
    ((badCofactorsFor X c).card : ℝ) ≤ (X : ℝ) * badFactorialWeight c := by
  classical
  let b := Tao2026.squarefreeComponent c.factorial
  let D := b.divisors.filter (fun d => b < d ^ 2)
  let A := fun d => (Finset.Ioc 0 X).filter (fun a => d ∣ a)
  have hb0 : 0 < b := factorialComponent_pos c
  have hsub : badCofactorsFor X c ⊆ D.biUnion A := by
    intro a ha
    have hd := Finset.mem_filter.mp ha
    obtain ⟨d, hdDiv, hda, hdLarge⟩ := bad_cofactor_has_large_common_divisor hd.2.1 hd.2.2
    exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_filter.mpr ⟨hdDiv, hdLarge⟩,
      Finset.mem_filter.mpr ⟨hd.1, hda⟩⟩
  have hone : ∀ d ∈ D, ((A d).card : ℝ) ≤ (X : ℝ) / Real.sqrt b := by
    intro d hd
    have hdata := Finset.mem_filter.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hdata.1) hb0
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
    have hsqrt : Real.sqrt (b : ℝ) ≤ d := by
      have hpow : (b : ℝ) < (d : ℝ) ^ 2 := by exact_mod_cast hdata.2
      nlinarith [Real.sq_sqrt hbR.le, Real.sqrt_nonneg (b : ℝ)]
    have hdiv : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := by
      apply (le_div_iff₀ hdR).mpr
      exact_mod_cast Nat.div_mul_le_self X d
    calc
      ((A d).card : ℝ) = (X / d : ℕ) := by rw [Nat.Ioc_filter_dvd_card_eq_div]
      _ ≤ (X : ℝ) / d := hdiv
      _ ≤ (X : ℝ) / Real.sqrt b :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg X) (Real.sqrt_pos.mpr hbR) hsqrt
  have hcard : (badCofactorsFor X c).card ≤ ∑ d ∈ D, (A d).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hD : D.card ≤ b.divisors.card := Finset.card_filter_le _ _
  calc
    ((badCofactorsFor X c).card : ℝ) ≤ ∑ d ∈ D, ((A d).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _d ∈ D, (X : ℝ) / Real.sqrt b := Finset.sum_le_sum hone
    _ = (D.card : ℝ) * ((X : ℝ) / Real.sqrt b) := by simp
    _ ≤ (b.divisors.card : ℝ) * ((X : ℝ) / Real.sqrt b) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hD) (by positivity)
    _ = (X : ℝ) * badFactorialWeight c := by dsimp [badFactorialWeight, b]; ring

theorem eventually_badFactorialWeight_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c : ℕ in atTop,
      badFactorialWeight c ≤ C * Real.exp (-(c : ℝ) / 16) := by
  let C := RiemannZeta.GuthMaynard.divisorEpsilonConstant (1 / 4)
  have hC : 0 < C := RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos _
  refine ⟨C, hC, ?_⟩
  filter_upwards [Tao2026.eventually_log_squarefreeComponent_factorial_lower] with c hc
  let d := Tao2026.squarefreeComponent c.factorial
  have hd0 : 0 < d := factorialComponent_pos c
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdiv := RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow
    (by norm_num : (0 : ℝ) < 1 / 4) hd0.ne'
  have hrpow : (d : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt d = (d : ℝ) ^ (-1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hdR]
    norm_num
  have hdecay : (d : ℝ) ^ (-1 / 4 : ℝ) ≤ Real.exp (-(c : ℝ) / 16) := by
    rw [Real.rpow_def_of_pos hdR]
    apply Real.exp_le_exp.mpr
    change (c : ℝ) / 4 ≤ Real.log (d : ℝ) at hc
    linarith
  calc
    badFactorialWeight c ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) / Real.sqrt d :=
      div_le_div_of_nonneg_right hdiv (Real.sqrt_nonneg _)
    _ = C * (d : ℝ) ^ (-1 / 4 : ℝ) := by rw [mul_div_assoc, hrpow]
    _ ≤ C * Real.exp (-(c : ℝ) / 16) := mul_le_mul_of_nonneg_left hdecay hC.le

theorem summable_badFactorialWeight : Summable badFactorialWeight := by
  obtain ⟨C, hC, hbound⟩ := eventually_badFactorialWeight_le_exp
  have hgeo : Summable (fun c : ℕ => C * Real.exp (-(c : ℝ) / 16)) := by
    have h := (Real.summable_exp_nat_mul_iff.mpr (show (-1 / 16 : ℝ) < 0 by norm_num)).mul_left C
    convert h using 1
    ext c
    congr 2
    ring
  apply hgeo.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hbound] with c hc
  simpa only [Real.norm_of_nonneg (badFactorialWeight_nonneg c)] using hc

end Erdos374Research
