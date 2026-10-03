import Erdos374Research.BlockWeightArithmetic
import Erdos374Research.ShortPrimes
import Erdos374Research.LargerSieve
import Tao2026.FactorialCoefficientBounds

/-! UNCOMPILED. The exact prime-parity and logarithmic-product inequalities
in Yudin's preliminary two-block reduction. Endpoint equality c=m-l₂ is
allowed, including the c=1 convention for four distinct factorials. -/

namespace Erdos374Research

open Tao2026 Finset Filter
open scoped BigOperators Topology

noncomputable section

lemma log_falling_le {n l : ℕ} (hl : l ≤ n) :
    Real.log (falling n l) ≤ (l : ℝ) * Real.log n := by
  rw [falling_eq_prod_Ioc hl, Nat.cast_prod, Real.log_prod]
  · calc
      (∑ v ∈ Finset.Ioc (n - l) n, Real.log (v : ℝ)) ≤
          ∑ _v ∈ Finset.Ioc (n - l) n, Real.log (n : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        have h := Finset.mem_Ioc.mp hv
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < v)) (by exact_mod_cast h.2)
      _ = (l : ℝ) * Real.log n := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_sub_self hl]
  · intro v hv
    have h := (Finset.mem_Ioc.mp hv).1
    exact_mod_cast (by omega : v ≠ 0)

lemma prime_dvd_eq_self_below_twice {p v : ℕ}
    (_hp : 0 < p) (hv : 0 < v) (hvlt : v < 2 * p) (hd : p ∣ v) : v = p := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k = 1 := by nlinarith
  simp only [hk, mul_one]

lemma upperHalfPrime_factorization_falling {n l p : ℕ}
    (hl : l ≤ n) (hp : p.Prime) (hhalf : n < 2 * p)
    (hmem : p ∈ Finset.Ioc (n - l) n) :
    (falling n l).factorization p = 1 := by
  rw [falling_eq_prod_Ioc hl, Nat.factorization_prod_apply]
  · rw [Finset.sum_eq_single p]
    · exact hp.factorization_self
    · intro v hv hvp
      apply prime_factorization_zero hp (by have := (Finset.mem_Ioc.mp hv).1; omega)
      intro hdiv
      exact hvp (prime_dvd_eq_self_below_twice hp.pos
        (by have := (Finset.mem_Ioc.mp hv).1; omega)
        ((Finset.mem_Ioc.mp hv).2.trans_lt hhalf) hdiv)
    · exact fun h => (h hmem).elim
  · intro v hv
    have := (Finset.mem_Ioc.mp hv).1
    omega

lemma prime_factorization_falling_zero_of_end_lt {m l p : ℕ}
    (hl : l ≤ m) (hp : p.Prime) (hmp : m < p) :
    (falling m l).factorization p = 0 := by
  apply prime_factorization_zero hp (falling_pos _ _).ne'
  intro hdiv
  rw [falling_eq_prod_Ioc hl] at hdiv
  obtain ⟨v, hv, hpv⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdiv
  have hvdata := Finset.mem_Ioc.mp hv
  exact Nat.not_dvd_of_pos_of_lt (by omega) (hvdata.2.trans_lt hmp) hpv

lemma upperHalfPrime_not_in_upper_block {n m l₁ l₂ c p : ℕ}
    (hl₁ : l₁ ≤ n) (hl₂ : l₂ ≤ m) (hm : m < n - l₁) (hc : c ≤ m - l₂)
    (hp : p.Prime) (hhalf : n < 2 * p)
    (hmem : p ∈ Finset.Ioc (n - l₁) n)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial)) : False := by
  have hmp : m < p := hm.trans (Finset.mem_Ioc.mp hmem).1
  have hcp : c < p := (hc.trans (Nat.sub_le _ _)).trans_lt hmp
  have hfirst := upperHalfPrime_factorization_falling hl₁ hp hhalf hmem
  have hsecond := prime_factorization_falling_zero_of_end_lt hl₂ hp hmp
  have hfact : c.factorial.factorization p = 0 := prime_factorization_zero hp
    (Nat.factorial_ne_zero c) (fun h => (not_le_of_gt hcp) (hp.dvd_factorial.mp h))
  have heven := even_factorization_of_isSquare (p := p) hsq
  rw [Nat.factorization_mul (mul_ne_zero (falling_pos _ _).ne' (falling_pos _ _).ne')
    (Nat.factorial_ne_zero c), Nat.factorization_mul (falling_pos _ _).ne' (falling_pos _ _).ne'] at heven
  have h : Even (1 : ℕ) := by simpa only [Finsupp.add_apply, hfirst, hsecond, hfact, add_zero] using heven
  exact (by decide : ¬Even (1 : ℕ)) h

lemma upperHalfPrime_in_lower_dvd_upper {n m l₁ l₂ c p : ℕ}
    (_hl₁ : l₁ ≤ n) (hl₂ : l₂ ≤ m) (hc : c ≤ m - l₂)
    (hp : p.Prime) (hhalf : m < 2 * p)
    (hmem : p ∈ Finset.Ioc (m - l₂) m)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial)) : p ∣ falling n l₁ := by
  have hcp : c < p := hc.trans_lt (Finset.mem_Ioc.mp hmem).1
  have hsecond := upperHalfPrime_factorization_falling hl₂ hp hhalf hmem
  have hfact : c.factorial.factorization p = 0 := prime_factorization_zero hp
    (Nat.factorial_ne_zero c) (fun h => (not_le_of_gt hcp) (hp.dvd_factorial.mp h))
  by_contra hnot
  have hfirst := prime_factorization_zero hp (falling_pos _ _).ne' hnot
  have heven := even_factorization_of_isSquare (p := p) hsq
  rw [Nat.factorization_mul (mul_ne_zero (falling_pos _ _).ne' (falling_pos _ _).ne')
    (Nat.factorial_ne_zero c), Nat.factorization_mul (falling_pos _ _).ne' (falling_pos _ _).ne'] at heven
  have h : Even (1 : ℕ) := by
    simpa only [Finsupp.add_apply, hfirst, hsecond, hfact, add_zero, zero_add] using heven
  exact (by decide : ¬Even (1 : ℕ)) h

lemma factorial_upperHalfPrime_dvd_two_blocks {n m l₁ l₂ c p : ℕ}
    (hp : p ∈ factorialUpperHalfPrimes c)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial)) :
    p ∣ falling n l₁ * falling m l₂ := by
  have hpd := Finset.mem_filter.mp hp
  have hbounds := Finset.mem_Ioc.mp hpd.1
  have hfact := factorization_factorial_eq_one_of_half_lt hpd.2 hbounds.1 hbounds.2
  by_contra hnot
  have hprod := prime_factorization_zero hpd.2
    (mul_ne_zero (falling_pos _ _).ne' (falling_pos _ _).ne') hnot
  have heven := even_factorization_of_isSquare (p := p) hsq
  rw [Nat.factorization_mul (mul_ne_zero (falling_pos _ _).ne' (falling_pos _ _).ne')
    (Nat.factorial_ne_zero c)] at heven
  have h : Even (1 : ℕ) := by simpa only [Finsupp.add_apply, hprod, hfact, zero_add] using heven
  exact (by decide : ¬Even (1 : ℕ)) h

theorem two_block_cofactor_theta_le {n m l₁ l₂ c : ℕ}
    (hl₁ : l₁ ≤ n) (hl₂ : l₂ ≤ m) (hmn : m ≤ n)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial)) :
    Chebyshev.theta c - Chebyshev.theta ((c / 2 : ℕ) : ℝ) ≤
      ((l₁ : ℝ) + l₂) * Real.log n := by
  rw [← sum_log_factorialUpperHalfPrimes_eq_theta_sub]
  have h := sum_log_prime_divisors_le (factorialUpperHalfPrimes c)
    (mul_pos (falling_pos _ _) (falling_pos _ _))
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => factorial_upperHalfPrime_dvd_two_blocks hp hsq)
  rw [Nat.cast_mul, Real.log_mul
    (by exact_mod_cast (falling_pos n l₁).ne') (by exact_mod_cast (falling_pos m l₂).ne')] at h
  have hfirst := log_falling_le hl₁
  have hsecond : Real.log (falling m l₂) ≤ (l₂ : ℝ) * Real.log n := by
    by_cases hm : m = 0
    · have hl : l₂ = 0 := by omega
      simp [hm, hl, falling, consecutiveProduct, consecutiveInterval]
    · exact (log_falling_le hl₂).trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hm)) (by exact_mod_cast hmn))
        (Nat.cast_nonneg l₂))
  nlinarith

theorem exists_two_block_cofactor_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ n m l₁ l₂ c : ℕ,
      2 ≤ n → l₁ ≤ n → l₂ ≤ m → m ≤ n →
      IsSquare (falling n l₁ * falling m l₂ * c.factorial) →
      (c : ℝ) ≤ D * ((max l₁ l₂ : ℕ) * Real.log n + 1) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp eventually_nat_factorialUpperHalfTheta_lower
  let D : ℝ := max 8 A + 1
  have hD : 0 < D := by dsimp only [D]; have := le_max_left (8 : ℝ) A; linarith
  refine ⟨D, hD, ?_⟩
  intro n m l₁ l₂ c hn hl₁ hl₂ hmn hsq
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hL0 : (0 : ℝ) ≤ (max l₁ l₂ : ℕ) := Nat.cast_nonneg _
  have hD8 : 8 ≤ D := by
    dsimp only [D]
    have hmax : (8 : ℝ) ≤ (max 8 A : ℕ) := by exact_mod_cast le_max_left (8 : ℕ) A
    linarith
  have hDA : (A : ℝ) ≤ D := by
    dsimp only [D]
    have hmax : (A : ℝ) ≤ (max 8 A : ℕ) := by exact_mod_cast le_max_right (8 : ℕ) A
    linarith
  by_cases hc : A ≤ c
  · have hlo := hA c hc
    have hhi := two_block_cofactor_theta_le hl₁ hl₂ hmn hsq
    have hl₁R : (l₁ : ℝ) ≤ (max l₁ l₂ : ℕ) := by exact_mod_cast le_max_left l₁ l₂
    have hl₂R : (l₂ : ℝ) ≤ (max l₁ l₂ : ℕ) := by exact_mod_cast le_max_right l₁ l₂
    have hsum := mul_le_mul_of_nonneg_right (add_le_add hl₁R hl₂R) hlog
    have hmul := mul_le_mul_of_nonneg_right hD8 (mul_nonneg hL0 hlog)
    nlinarith
  · have hcR : (c : ℝ) ≤ A := by exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    nlinarith [mul_nonneg hD.le (mul_nonneg hL0 hlog)]

def shortIntervalPrimes (m : ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊(m : ℝ) - y⌋₊ m).filter Nat.Prime

lemma mem_shortIntervalPrimes {m p : ℕ} {y : ℝ}
    (hy : y ≤ m) : p ∈ shortIntervalPrimes m y ↔ p.Prime ∧ (m : ℝ) - y < p ∧ p ≤ m := by
  unfold shortIntervalPrimes
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  have hfloor : ⌊(m : ℝ) - y⌋₊ < p ↔ (m : ℝ) - y < p :=
    Nat.floor_lt (by linarith : 0 ≤ (m : ℝ) - y)
  rw [hfloor]
  tauto

lemma sum_log_shortIntervalPrimes {m : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    ∑ p ∈ shortIntervalPrimes m y, Real.log (p : ℝ) =
      Chebyshev.theta m - Chebyshev.theta ((m : ℝ) - y) := by
  have h := primeMangoldtIntervalSum_eq_theta_sub ((m : ℝ) - y) hy
  rw [sub_add_cancel] at h
  rw [← h]
  unfold shortIntervalPrimes GafniTao.primeMangoldtIntervalSum
  simp only [sub_add_cancel, Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro p hp
  exact (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm

theorem upper_block_theta_difference_eq_zero {n m l₁ l₂ c : ℕ} {y : ℝ}
    (hy0 : 0 ≤ y) (hyl : y ≤ l₁) (hyn : y ≤ (n : ℝ) / 2)
    (hl₁ : l₁ ≤ n) (hl₂ : l₂ ≤ m) (hm : m < n - l₁) (hc : c ≤ m - l₂)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial)) :
    Chebyshev.theta n - Chebyshev.theta ((n : ℝ) - y) = 0 := by
  rw [← sum_log_shortIntervalPrimes hy0]
  apply Finset.sum_eq_zero
  intro p hp
  have hd := (mem_shortIntervalPrimes (by nlinarith : y ≤ n)).mp hp
  have hpHalf : n < 2 * p := by exact_mod_cast (by linarith : (n : ℝ) < 2 * p)
  have hpblock : p ∈ Finset.Ioc (n - l₁) n := by
    apply Finset.mem_Ioc.mpr
    refine ⟨?_, hd.2.2⟩
    have h : ((n - l₁ : ℕ) : ℝ) < p := by rw [Nat.cast_sub hl₁]; linarith
    exact_mod_cast h
  exact (upperHalfPrime_not_in_upper_block hl₁ hl₂ hm hc hd.1 hpHalf hpblock hsq).elim

theorem lower_block_theta_difference_le {n m l₁ l₂ c : ℕ} {y : ℝ}
    (hy0 : 0 ≤ y) (hyl : y ≤ l₂) (hym : y ≤ (m : ℝ) / 2)
    (hl₁ : l₁ ≤ n) (hl₂ : l₂ ≤ m) (hc : c ≤ m - l₂)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial)) :
    Chebyshev.theta m - Chebyshev.theta ((m : ℝ) - y) ≤ (l₁ : ℝ) * Real.log n := by
  rw [← sum_log_shortIntervalPrimes hy0]
  apply (sum_log_prime_divisors_le (shortIntervalPrimes m y) (falling_pos n l₁)
    (fun p hp => (Finset.mem_filter.mp hp).2) ?_).trans (log_falling_le hl₁)
  intro p hp
  have hd := (mem_shortIntervalPrimes (by nlinarith : y ≤ m)).mp hp
  have hpHalf : m < 2 * p := by exact_mod_cast (by linarith : (m : ℝ) < 2 * p)
  have hpblock : p ∈ Finset.Ioc (m - l₂) m := by
    apply Finset.mem_Ioc.mpr
    refine ⟨?_, hd.2.2⟩
    have h : ((m - l₂ : ℕ) : ℝ) < p := by rw [Nat.cast_sub hl₂]; linarith
    exact_mod_cast h
  exact upperHalfPrime_in_lower_dvd_upper hl₁ hl₂ hc hd.1 hpHalf hpblock hsq

end
end Erdos374Research
