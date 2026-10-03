import Erdos374Research.LongBlocks
import Erdos374Research.TwoBlockPreliminary
import Erdos374Research.RepresentationBlocks

/-!
UNCOMPILED. The original ordered two-block shortness conclusion. Prime-size,
cofactor and preliminary length estimates are consequences, not extra
inputs. Only the actual factorization n=a*p and small cofactor a remain.
-/

namespace Erdos374Research

open Filter Tao2026
open scoped Topology

theorem eventually_orderedTwoBlocks_short {α ε : ℝ}
    (hα : 0 ≤ α) (hαε : α < ε) (hαsmall : α < 1 / 3) :
    ∀ᶠ n : ℕ in atTop, ∀ a p m l₁ l₂ c : ℕ,
      p.Prime → n = a * p → (a : ℝ) ≤ (n : ℝ) ^ α →
      OrderedTwoBlocks n m l₁ l₂ c →
      (max l₁ l₂ : ℕ) < (n : ℝ) ^ ε := by
  obtain ⟨D₀, hD₀, hcofactor⟩ := exists_two_block_cofactor_bound
  let D := D₀ + 1
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  have hDpos : 0 < D := by linarith
  have hgap : α + (2 / 3 : ℝ) < 1 := by linarith
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    eventually_two_block_lengths_le_two_thirds,
    eventually_large_prime_dominates_blocks hα hαsmall hD,
    eventually_no_long_two_blocks_with_relation hα hαε hgap hDpos]
    with n hn hprelim hprime hlong
  intro a p m l₁ l₂ c hp hnap haN hblocks
  have ha : 0 < a := by
    by_contra hnot
    have hz : a = 0 := by omega
    simp only [hz, zero_mul] at hnap
    omega
  have hmn : m < n := hblocks.separated.trans_le (Nat.sub_le _ _)
  have hcofactorN := hcofactor n m l₁ l₂ c hn hblocks.first_lt.le
    hblocks.second_lt.le hmn.le hblocks.square
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hcD : (c : ℝ) ≤ D * ((max l₁ l₂ : ℕ) * Real.log n + 1) :=
    hcofactorN.trans (mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith)
      (by positivity))
  have hL := hprelim m l₁ l₂ c hblocks.first_lt.le hblocks.second_lt.le
    hblocks.separated hblocks.coefficient_le hblocks.square
  obtain ⟨hLp, hcp, hnsq⟩ := hprime a p (max l₁ l₂) c ha hp.pos hnap haN hL hcD
  obtain ⟨j, t, hj, ht, hta, hmj, hunique⟩ := exists_lower_block_rational_relation
    hblocks.first_pos hblocks.first_lt.le hblocks.second_lt.le hmn hp
    ((le_max_left _ _).trans_lt hLp) ((le_max_right _ _).trans_lt hLp)
    hcp hnap hnsq hblocks.square
  have hrel : ((m - j : ℕ) : ℝ) = (t : ℝ) / a * n := by
    rw [hmj, hnap]
    push_cast
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp [haR]
  by_contra hnot
  exact hlong m l₁ l₂ c a t j hblocks.first_pos hblocks.second_pos
    hblocks.first_lt.le hblocks.second_lt.le hmn hj ht hta haN hrel
    (le_of_not_gt hnot) hL hcD hblocks.square

theorem eventually_orderedTwoBlocks_small_parameters {α ε : ℝ}
    (hα : 0 ≤ α) (hαε : α < ε) (hαsmall : α < 1 / 3) :
    ∀ᶠ n : ℕ in atTop, ∀ a p m l₁ l₂ c : ℕ,
      p.Prime → n = a * p → (a : ℝ) ≤ (n : ℝ) ^ α →
      OrderedTwoBlocks n m l₁ l₂ c →
      (max l₁ l₂ : ℕ) < (n : ℝ) ^ ε ∧ (c : ℝ) < (n : ℝ) ^ (2 * ε) ∧
      ∃ j t : ℕ, j < l₂ ∧ 1 ≤ t ∧ t < a ∧ m - j = t * p := by
  obtain ⟨D₀, hD₀, hcofactor⟩ := exists_two_block_cofactor_bound
  let D := D₀ + 1
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  have hε : 0 < ε := lt_of_le_of_lt hα hαε
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [eventually_orderedTwoBlocks_short hα hαε hαsmall,
    eventually_two_block_lengths_le_two_thirds,
    eventually_large_prime_dominates_blocks hα hαsmall hD,
    eventually_logPow_le_small_rpow 1 (d := ε) (c := 1 / (4 * D)) hε (by positivity),
    hlog, eventually_ge_atTop (2 : ℕ)] with n hshort hprelim hprime hsmall hlogn hn
  intro a p m l₁ l₂ c hp hnap haN hblocks
  have ha : 0 < a := by
    by_contra hnot
    have hz : a = 0 := by omega
    simp only [hz, zero_mul] at hnap
    omega
  have hmn : m < n := hblocks.separated.trans_le (Nat.sub_le _ _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hεpow : 1 ≤ (n : ℝ) ^ ε := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hn1 hε.le
  have hL := hshort a p m l₁ l₂ c hp hnap haN hblocks
  have hc₀ := hcofactor n m l₁ l₂ c hn hblocks.first_lt.le
    hblocks.second_lt.le hmn.le hblocks.square
  have hcD : (c : ℝ) ≤ D * ((max l₁ l₂ : ℕ) * Real.log n + 1) :=
    hc₀.trans (mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith) (by positivity))
  have hcSmall : (c : ℝ) < (n : ℝ) ^ (2 * ε) := by
    have hcoef : (c : ℝ) ≤ 2 * D * (n : ℝ) ^ ε * Real.log n := by
      have hm := mul_le_mul_of_nonneg_right hL.le (by linarith : 0 ≤ Real.log (n : ℝ))
      have hbase : 1 ≤ (n : ℝ) ^ ε * Real.log n := by nlinarith
      have hscaled := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ D)
      have hone := mul_le_mul_of_nonneg_left hbase (by linarith : 0 ≤ D)
      nlinarith
    have hlogbound : 4 * D * Real.log (n : ℝ) ≤ (n : ℝ) ^ ε := by
      simp only [pow_one] at hsmall
      calc
        4 * D * Real.log (n : ℝ) ≤ 4 * D * ((1 / (4 * D)) * (n : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ = (n : ℝ) ^ ε := by field_simp
    have hmul := mul_le_mul_of_nonneg_right hlogbound (Real.rpow_nonneg hnR.le ε)
    have hid : (n : ℝ) ^ ε * (n : ℝ) ^ ε = (n : ℝ) ^ (2 * ε) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring
    have hpos := Real.rpow_pos_of_pos hnR (2 * ε)
    nlinarith
  have hLprelim := hprelim m l₁ l₂ c hblocks.first_lt.le hblocks.second_lt.le
    hblocks.separated hblocks.coefficient_le hblocks.square
  obtain ⟨hLp, hcp, hnsq⟩ := hprime a p (max l₁ l₂) c ha hp.pos hnap haN hLprelim hcD
  obtain ⟨j, t, hj, ht, hta, hmj, hunique⟩ := exists_lower_block_rational_relation
    hblocks.first_pos hblocks.first_lt.le hblocks.second_lt.le hmn hp
    ((le_max_left _ _).trans_lt hLp) ((le_max_right _ _).trans_lt hLp)
    hcp hnap hnsq hblocks.square
  exact ⟨hL, hcSmall, j, t, hj, ht, hta, hmj⟩

end Erdos374Research
