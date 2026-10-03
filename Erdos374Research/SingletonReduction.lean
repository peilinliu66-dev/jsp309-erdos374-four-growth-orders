import Erdos374Research.CandidateGeometry
import Erdos374Research.ShortBlockAsymptotics

/-!
# Reduction to two singleton blocks

UNCOMPILED. Once the analytic shortness theorem has been applied, the large
odd-valuation prime in n−1 forces the first block to have length one. The
finite short-block exceptional set removes every second block of length≥2.
-/

namespace Erdos374Research

open Finset Tao2026
open scoped BigOperators

theorem cofactor_prime_gt_power {n a p : ℕ} {α β : ℝ}
    (hn : 1 < n) (hnap : n = a * p) (ha : (a : ℝ) ≤ (n : ℝ) ^ α)
    (hgap : α + β < 1) : (n : ℝ) ^ β < p := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  by_contra hnot
  have hp : (p : ℝ) ≤ (n : ℝ) ^ β := le_of_not_gt hnot
  have hprod := mul_le_mul ha hp (Nat.cast_nonneg p) (Real.rpow_nonneg hnpos.le α)
  rw [← Real.rpow_add hnpos] at hprod
  have hnEq : (n : ℝ) = a * p := by exact_mod_cast hnap
  have hlt := Real.rpow_lt_rpow_of_exponent_lt hnR hgap
  rw [Real.rpow_one] at hlt
  linarith

theorem first_block_singleton_of_large_squarefree_prime
    {n m l₁ l₂ c a p q : ℕ}
    (hb : OrderedTwoBlocks n m l₁ l₂ c) (hp : p.Prime)
    (hnap : n = a * p) (hap : a < p)
    (hl₁p : l₁ < p) (hl₂p : l₂ < p) (hcp : c < p)
    (hq : q.Prime) (hqd : q ∣ squarefreeComponent (n - 1))
    (hlq : l₁ < q) (hcq : c < q) (halq : a * l₂ < q) : l₁ = 1 := by
  have hodd : Odd ((n - 1).factorization q) := by
    have hmem := hq.mem_primeFactors hqd (squarefree_squarefreeComponent (n - 1)).ne_zero
    exact (mem_primeFactors_squarefreeComponent_iff.mp hmem).2
  by_contra hnot
  have hl₁two : 2 ≤ l₁ := by have := hb.first_pos; omega
  have hnsq : n < p ^ 2 := by rw [hnap, pow_two]; exact Nat.mul_lt_mul_of_pos_right hap hp.pos
  have hbound := odd_factorization_pred_imp_le hl₁two hb.first_lt.le hb.second_lt.le
    (hb.separated.trans_le (Nat.sub_le _ _)) hp hl₁p hl₂p hcp hnap hnsq hb.square hq hodd
  have hlt : max l₁ (max c (a * l₂)) < q := max_lt hlq (max_lt hcq halq)
  omega

theorem short_blocks_singletons_of_not_exceptional
    {X n m l₁ l₂ c a p : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 100000)
    (hn : 1 < n) (hnX : n ≤ X) (hb : OrderedTwoBlocks n m l₁ l₂ c)
    (hp : p.Prime) (ha : 1 ≤ a) (hap : a < p) (hnap : n = a * p)
    (haSmall : (a : ℝ) ≤ (n : ℝ) ^ (3 * ε / 4))
    (hlarge : HasLargeSquarefreePrime (3 * ε) X n)
    (hshort : (max l₁ l₂ : ℕ) < (n : ℝ) ^ ε)
    (hcSmall : (c : ℝ) ≤ (n : ℝ) ^ (2 * ε))
    (hnot : n ∉ shortBlockExceptional X (shortBlockCutoff ε X)) :
    l₁ = 1 ∧ l₂ = 1 := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNleX : (n : ℝ) ≤ X := by exact_mod_cast hnX
  have hpPower := cofactor_prime_gt_power hn hnap haSmall
    (show 3 * ε / 4 + 2 * ε < 1 by linarith)
  have hpow12 : (n : ℝ) ^ ε ≤ (n : ℝ) ^ (2 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR.le (by linarith)
  have hl₁small : (l₁ : ℝ) < (n : ℝ) ^ ε :=
    (by exact_mod_cast le_max_left l₁ l₂ : (l₁ : ℝ) ≤ max l₁ l₂).trans_lt hshort
  have hl₂small : (l₂ : ℝ) < (n : ℝ) ^ ε :=
    (by exact_mod_cast le_max_right l₁ l₂ : (l₂ : ℝ) ≤ max l₁ l₂).trans_lt hshort
  have hl₁p : l₁ < p := by exact_mod_cast (hl₁small.trans_le hpow12).trans hpPower
  have hl₂p : l₂ < p := by exact_mod_cast (hl₂small.trans_le hpow12).trans hpPower
  have hcp : c < p := by exact_mod_cast hcSmall.trans_lt hpPower
  obtain ⟨q, hq, hqd, hqbig⟩ := hlarge
  have hnq : (n : ℝ) ^ (3 * ε) < q :=
    (Real.rpow_le_rpow hnpos.le hNleX (by positivity)).trans_lt hqbig
  have hlq : l₁ < q := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hnR.le (show ε ≤ 3 * ε by linarith)
    exact_mod_cast (hl₁small.trans_le hpow).trans hnq
  have hcq : c < q := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hnR.le (show 2 * ε ≤ 3 * ε by linarith)
    exact_mod_cast (hcSmall.trans hpow).trans_lt hnq
  have halq : a * l₂ < q := by
    have hmul := mul_le_mul haSmall hl₂small.le (Nat.cast_nonneg l₂)
      (Real.rpow_nonneg hnpos.le (3 * ε / 4))
    rw [← Real.rpow_add hnpos] at hmul
    have hpw := Real.rpow_le_rpow_of_exponent_le hnR.le
      (show 3 * ε / 4 + ε ≤ 3 * ε by linarith)
    exact_mod_cast (hmul.trans hpw).trans_lt hnq
  have hl₁ := first_block_singleton_of_large_squarefree_prime hb hp hnap hap
    hl₁p hl₂p hcp hq hqd hlq hcq halq
  refine ⟨hl₁, ?_⟩
  by_contra hl₂not
  have hl₂two : 2 ≤ l₂ := by have := hb.second_pos; omega
  have hnsq : n < p ^ 2 := by rw [hnap, pow_two]; exact Nat.mul_lt_mul_of_pos_right hap hp.pos
  obtain ⟨j, t, hj, ht, hta, hmjp, huniq⟩ := exists_lower_block_rational_relation
    (by have := hb.first_pos; omega) hb.first_lt.le hb.second_lt.le
    (hb.separated.trans_le (Nat.sub_le _ _)) hp hl₁p hl₂p hcp hnap hnsq hb.square
  have hsq := first_singleton_punctured_square (by omega : 1 ≤ n) hb.second_lt.le hj
    hp.pos ha ht hnap hmjp (by simpa only [hl₁] using hb.square)
  have hBX : (n : ℝ) ^ (2 * ε) ≤ (shortBlockCutoff ε X : ℝ) :=
    (Real.rpow_le_rpow hnpos.le hNleX (by positivity)).trans (Nat.le_ceil _)
  have haB : a ≤ shortBlockCutoff ε X := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hnR.le
      (show 3 * ε / 4 ≤ 2 * ε by linarith)
    exact_mod_cast (haSmall.trans hpow).trans hBX
  have htB : t ≤ shortBlockCutoff ε X := hta.le.trans haB
  have hcB : c ≤ shortBlockCutoff ε X := by exact_mod_cast hcSmall.trans hBX
  have hlB : l₂ ≤ shortBlockCutoff ε X := by exact_mod_cast (hl₂small.le.trans hpow12).trans hBX
  have hrel : a * (m - j) = t * n := by rw [hmjp, hnap]; ring
  exact hnot (mem_shortBlockExceptional
    ((hb.separated.trans_le (Nat.sub_le _ _)).le.trans hnX)
    hb.second_lt.le ha ht hl₂two hj haB htB hcB hlB hrel hsq)

theorem singleton_blocks_not_square_for_admissible
    {n m c a p : ℕ} (hb : OrderedTwoBlocks n m 1 1 c)
    (ha : AdmissibleCofactor a) (hp : p.Prime) (hap : a < p)
    (hnap : n = a * p) (hcp : c < p) : False := by
  have hmn : m < n := hb.separated.trans_le (Nat.sub_le _ _)
  have hnsq : n < p ^ 2 := by rw [hnap, pow_two]; exact Nat.mul_lt_mul_of_pos_right hap hp.pos
  obtain ⟨j, t, hj, ht, hta, hmjp, huniq⟩ := exists_lower_block_rational_relation
    (by decide) hb.first_lt.le hb.second_lt.le hmn hp hp.one_lt hp.one_lt hcp hnap hnsq hb.square
  have hj0 : j = 0 := by omega
  have hsq := first_singleton_punctured_square (by have := hb.first_lt; omega)
    hb.second_lt.le hj hp.pos ha.1 ht hnap hmjp hb.square
  have hpunct : puncturedFalling m 1 j = 1 := by simp [puncturedFalling, hj0]
  rw [hpunct, mul_one] at hsq
  exact ha.not_small_factorial_square ht hta hsq

theorem singleton_blocks_not_square_for_squarefree
    {n m : ℕ} (hb : OrderedTwoBlocks n m 1 1 1) (hn : Squarefree n) : False := by
  have hfalln : falling n 1 = n := by rw [falling_eq_prod_range hb.first_lt.le]; simp
  have hfallm : falling m 1 = m := by rw [falling_eq_prod_range hb.second_lt.le]; simp
  have hsq : IsSquare (n * m) := by
    simpa only [hfalln, hfallm, Nat.factorial_one, mul_one] using hb.square
  exact not_isSquare_mul_of_squarefree_left hn (by have := hb.second_lt; omega)
    (hb.separated.trans_le (Nat.sub_le _ _)) hsq

end Erdos374Research
