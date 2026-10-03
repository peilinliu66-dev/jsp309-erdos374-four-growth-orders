import Erdos374Research.FactorialIdentities
import Tao2026.FactorialShortIntervals

/-!
# Prime cancellation in two factorial blocks

UNCOMPILED. These are the elementary valuation and interval steps in
Yudin's Section 4. The large prime must occur in the second block as well;
no cancellation or existence condition is hidden in an analytic hypothesis.
-/

namespace Erdos374Research

open Finset
open scoped BigOperators

theorem falling_eq_prod_Ioc {n l : ℕ} (hl : l ≤ n) :
    falling n l = ∏ v ∈ Finset.Ioc (n - l) n, v := by
  simp only [falling, Tao2026.consecutiveProduct, Tao2026.consecutiveInterval,
    Nat.sub_add_cancel hl]

theorem prime_factorization_zero {p v : ℕ} (hp : p.Prime)
    (hv : v ≠ 0) (hnot : ¬ p ∣ v) : v.factorization p = 0 := by
  have h := hp.dvd_iff_one_le_factorization hv
  by_contra hne
  exact hnot (h.mpr (by omega))

theorem even_factorization_of_isSquare {v p : ℕ} (hv : IsSquare v) :
    Even (v.factorization p) := by
  rcases hv with ⟨r, rfl⟩
  rw [← pow_two, Nat.factorization_pow]
  change Even (2 * r.factorization p)
  exact ⟨r.factorization p, by omega⟩

theorem eq_of_prime_dvd_block_terms {n l p v w : ℕ}
    (hl : l ≤ n) (hlp : l < p)
    (hv : v ∈ Finset.Ioc (n - l) n) (hw : w ∈ Finset.Ioc (n - l) n)
    (hpv : p ∣ v) (hpw : p ∣ w) : v = w := by
  have hv' : v ∈ Tao2026.consecutiveInterval (n - l) l := by
    simpa only [Tao2026.consecutiveInterval, Nat.sub_add_cancel hl] using hv
  have hw' : w ∈ Tao2026.consecutiveInterval (n - l) l := by
    simpa only [Tao2026.consecutiveInterval, Nat.sub_add_cancel hl] using hw
  exact Tao2026.eq_of_mem_consecutiveInterval_of_prime_dvd hv' hw' hlp hpv hpw

theorem factorization_falling_eq_unique {n l p v : ℕ}
    (hl : l ≤ n) (hp : p.Prime) (hlp : l < p)
    (hv : v ∈ Finset.Ioc (n - l) n) (hpv : p ∣ v) :
    (falling n l).factorization p = v.factorization p := by
  rw [falling_eq_prod_Ioc hl, Nat.factorization_prod_apply]
  · apply Finset.sum_eq_single v
    · intro w hw hwv
      have hwpos : 0 < w := by have := (Finset.mem_Ioc.mp hw).1; omega
      apply prime_factorization_zero hp hwpos.ne'
      intro hpw
      exact hwv (eq_of_prime_dvd_block_terms hl hlp hw hv hpw hpv)
    · exact fun h => (h hv).elim
  · intro w hw
    have := (Finset.mem_Ioc.mp hw).1
    omega

theorem factorization_eq_one_of_prime_dvd_of_lt_sq {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hnsq : n < p ^ 2) :
    n.factorization p = 1 := by
  have hone : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn.ne').mp hpn
  have htwo : ¬ 2 ≤ n.factorization p := by
    intro h
    have hd := (hp.pow_dvd_iff_le_factorization hn.ne').mpr h
    exact (not_le_of_gt hnsq) (Nat.le_of_dvd hn hd)
  omega

theorem prime_dvd_lower_block {n m l₁ l₂ c p : ℕ}
    (hl₁pos : 0 < l₁) (hl₁ : l₁ ≤ n)
    (hp : p.Prime) (hl₁p : l₁ < p) (hcp : c < p)
    (hpn : p ∣ n) (hnsq : n < p ^ 2)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial)) :
    p ∣ falling m l₂ := by
  have hn : 0 < n := hl₁pos.trans_le hl₁
  have hnmem : n ∈ Finset.Ioc (n - l₁) n :=
    Finset.mem_Ioc.mpr ⟨Nat.sub_lt hn hl₁pos, le_rfl⟩
  have hupper : (falling n l₁).factorization p = 1 :=
    (factorization_falling_eq_unique hl₁ hp hl₁p hnmem hpn).trans
      (factorization_eq_one_of_prime_dvd_of_lt_sq hn hp hpn hnsq)
  have hcfact : c.factorial.factorization p = 0 := by
    apply prime_factorization_zero hp (Nat.factorial_ne_zero c)
    rw [hp.dvd_factorial, not_le]
    exact hcp
  by_contra hnot
  have hlower := prime_factorization_zero hp (falling_pos m l₂).ne' hnot
  have heven := even_factorization_of_isSquare (p := p) hsq
  rw [Nat.factorization_mul
    (mul_ne_zero (falling_pos n l₁).ne' (falling_pos m l₂).ne')
    (Nat.factorial_ne_zero c),
    Nat.factorization_mul (falling_pos n l₁).ne' (falling_pos m l₂).ne'] at heven
  have heven1 : Even (1 : ℕ) := by
    simpa only [Finsupp.add_apply, hupper, hlower, hcfact, add_zero] using heven
  exact (by decide : ¬ Even (1 : ℕ)) heven1

/-- The unique lower-block term divisible by the largest prime gives the
rational relation used in the smooth-weight argument. -/
theorem exists_lower_block_rational_relation {n m l₁ l₂ c p a : ℕ}
    (hl₁pos : 0 < l₁) (hl₁ : l₁ ≤ n) (hl₂ : l₂ ≤ m)
    (hmn : m < n) (hp : p.Prime) (hl₁p : l₁ < p) (hl₂p : l₂ < p)
    (hcp : c < p) (hnap : n = a * p) (hnsq : n < p ^ 2)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial)) :
    ∃ j t : ℕ, j < l₂ ∧ 1 ≤ t ∧ t < a ∧ m - j = t * p ∧
      ∀ i < l₂, p ∣ m - i → i = j := by
  have hpn : p ∣ n := by rw [hnap]; exact dvd_mul_left p a
  have hdvd := prime_dvd_lower_block hl₁pos hl₁ hp hl₁p hcp hpn hnsq hsq
  rw [falling_eq_prod_Ioc hl₂] at hdvd
  obtain ⟨v, hv, hpv⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdvd
  have hvData := Finset.mem_Ioc.mp hv
  have hvpos : 0 < v := by omega
  obtain ⟨t, ht⟩ := hpv
  change v = p * t at ht
  have htpos : 1 ≤ t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    simp [ht0] at ht
    omega
  have hta : t < a := by
    have hmul : t * p < a * p := by
      rw [mul_comm t p, ← ht, ← hnap]
      exact hvData.2.trans_lt hmn
    exact (Nat.mul_lt_mul_right hp.pos).mp hmul
  let j := m - v
  have hj : j < l₂ := by dsimp [j]; omega
  have hterm : m - j = t * p := by dsimp [j]; rw [Nat.sub_sub_self hvData.2, ht]; ring
  refine ⟨j, t, hj, htpos, hta, hterm, ?_⟩
  intro i hi hpi
  have hiMem : m - i ∈ Finset.Ioc (m - l₂) m := by
    apply Finset.mem_Ioc.mpr
    constructor <;> omega
  have heq := eq_of_prime_dvd_block_terms hl₂ hl₂p hiMem hv hpi
    (by rw [ht]; exact dvd_mul_right p t)
  dsimp [j]
  omega

/-- The rational relation prevents a sufficiently large divisor of n-1
from dividing any term of the lower block. The nonzero remainder t<a is
essential; omitting it would make this implication false. -/
theorem not_dvd_lower_term_of_dvd_n_sub_one {n m p a j t l q i : ℕ}
    (hn : 1 ≤ n) (hl : l ≤ m) (hj : j < l) (hi : i < l)
    (ht : 1 ≤ t) (hta : t < a)
    (hnap : n = a * p) (hmjp : m - j = t * p)
    (hqn : q ∣ n - 1) (hlarge : a * l < q) : ¬ q ∣ m - i := by
  intro hqmi
  have hjm : j ≤ m := by omega
  have him : i ≤ m := by omega
  have hm : m = t * p + j := by omega
  have hnZ : (n : ℤ) = (a : ℤ) * p := by exact_mod_cast hnap
  have hmZ : (m : ℤ) = (t : ℤ) * p + j := by exact_mod_cast hm
  have hqnZ : (q : ℤ) ∣ (n : ℤ) - 1 := by
    have h : (q : ℤ) ∣ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast hqn
    simpa only [Nat.cast_sub hn, Nat.cast_one] using h
  have hqmiZ : (q : ℤ) ∣ (m : ℤ) - i := by
    have h : (q : ℤ) ∣ ((m - i : ℕ) : ℤ) := by exact_mod_cast hqmi
    simpa only [Nat.cast_sub him] using h
  let z : ℤ := (a : ℤ) * ((j : ℤ) - i) + t
  have hid : (a : ℤ) * ((m : ℤ) - i) - (t : ℤ) * ((n : ℤ) - 1) = z := by
    dsimp [z]
    rw [hmZ, hnZ]
    ring
  have hqz : (q : ℤ) ∣ z := by
    rw [← hid]
    exact dvd_sub (dvd_mul_of_dvd_right hqmiZ a) (dvd_mul_of_dvd_right hqnZ t)
  have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have htaZ : (t : ℤ) < a := by exact_mod_cast hta
  have haZ : (0 : ℤ) ≤ a := Int.natCast_nonneg a
  have hji : -(l : ℤ) + 1 ≤ (j : ℤ) - i ∧ (j : ℤ) - i ≤ (l : ℤ) - 1 := by
    have hiZ : (i : ℤ) < l := by exact_mod_cast hi
    have hjZ : (j : ℤ) < l := by exact_mod_cast hj
    omega
  have hzbound : |z| < (a : ℤ) * l := by
    apply abs_lt.mpr
    have hlow := mul_le_mul_of_nonneg_left hji.1 haZ
    have hupp := mul_le_mul_of_nonneg_left hji.2 haZ
    dsimp [z]
    constructor <;> nlinarith
  have hz0 : z ≠ 0 := by
    intro hz
    have hat : (a : ℤ) ∣ t := by
      refine ⟨-((j : ℤ) - i), ?_⟩
      dsimp [z] at hz
      nlinarith
    have hatNat : a ∣ t := by exact_mod_cast hat
    exact (not_le_of_gt hta) (Nat.le_of_dvd ht hatNat)
  have hqZ : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have hlargeZ : (a : ℤ) * l < q := by exact_mod_cast hlarge
  obtain ⟨r, hr⟩ := hqz
  have hr0 : r ≠ 0 := by intro hr0; apply hz0; rw [hr, hr0, mul_zero]
  have hrabs : (1 : ℤ) ≤ |r| := by
    rcases lt_or_gt_of_ne hr0 with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have hmabs := mul_le_mul_of_nonneg_left hrabs hqZ
  rw [hr, abs_mul, abs_of_nonneg hqZ] at hzbound
  nlinarith

theorem odd_factorization_pred_imp_le {n m l₁ l₂ c p a q : ℕ}
    (hl₁two : 2 ≤ l₁) (hl₁ : l₁ ≤ n) (hl₂ : l₂ ≤ m) (hmn : m < n)
    (hp : p.Prime) (hl₁p : l₁ < p) (hl₂p : l₂ < p) (hcp : c < p)
    (hnap : n = a * p) (hnsq : n < p ^ 2)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial))
    (hq : q.Prime) (hodd : Odd ((n - 1).factorization q)) :
    q ≤ max l₁ (max c (a * l₂)) := by
  by_contra hnot
  have hbig : max l₁ (max c (a * l₂)) < q := Nat.lt_of_not_ge hnot
  have hlq : l₁ < q := (le_max_left _ _).trans_lt hbig
  have hcq : c < q := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hbig
  have halq : a * l₂ < q := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hbig
  have hn2 : 2 ≤ n := hl₁two.trans hl₁
  have hn1 : 0 < n - 1 := by omega
  have hqpred : q ∣ n - 1 :=
    (hq.dvd_iff_one_le_factorization hn1.ne').mpr (by rcases hodd with ⟨r, hr⟩; omega)
  obtain ⟨j, t, hj, ht, hta, hmjp, huniq⟩ :=
    exists_lower_block_rational_relation (by omega) hl₁ hl₂ hmn hp hl₁p hl₂p
      hcp hnap hnsq hsq
  have hqlower : ¬ q ∣ falling m l₂ := by
    rw [falling_eq_prod_Ioc hl₂]
    intro h
    obtain ⟨v, hv, hqv⟩ := (hq.prime.dvd_finsetProd_iff id).mp h
    have hvd := Finset.mem_Ioc.mp hv
    let i := m - v
    have hi : i < l₂ := by dsimp [i]; omega
    have hvEq : m - i = v := by dsimp [i]; omega
    exact not_dvd_lower_term_of_dvd_n_sub_one (by omega) hl₂ hj hi ht hta
      hnap hmjp hqpred halq (by simpa only [hvEq] using hqv)
  have hlowVal := prime_factorization_zero hq (falling_pos m l₂).ne' hqlower
  have hcfact : c.factorial.factorization q = 0 := by
    apply prime_factorization_zero hq (Nat.factorial_ne_zero c)
    rw [hq.dvd_factorial, not_le]
    exact hcq
  have hpredMem : n - 1 ∈ Finset.Ioc (n - l₁) n := by
    apply Finset.mem_Ioc.mpr
    constructor <;> omega
  have huppVal := factorization_falling_eq_unique hl₁ hq hlq hpredMem hqpred
  have heven := even_factorization_of_isSquare (p := q) hsq
  rw [Nat.factorization_mul
    (mul_ne_zero (falling_pos n l₁).ne' (falling_pos m l₂).ne')
    (Nat.factorial_ne_zero c),
    Nat.factorization_mul (falling_pos n l₁).ne' (falling_pos m l₂).ne'] at heven
  have hevenPred : Even ((n - 1).factorization q) := by
    simpa only [Finsupp.add_apply, huppVal, hlowVal, hcfact, add_zero] using heven
  exact (Nat.not_odd_iff_even.mpr hevenPred) hodd

end Erdos374Research
