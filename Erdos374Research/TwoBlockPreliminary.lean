import Erdos374Research.TwoBlockPreliminaryArithmetic
import Erdos374Research.PrimeParameterRanges

/-! UNCOMPILED. Uniform preliminary length bounds, using the actual
all-short-interval Chebyshev theorem. A minimum with m/2 avoids a separate
Bertrand-postulate argument and retains all small lower endpoints. -/

namespace Erdos374Research

open Filter Tao2026
open scoped Topology

lemma eventually_three_fifths_le_half :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) / 2 := by
  filter_upwards [eventually_logPow_le_small_rpow 0
    (d := (2 / 5 : ℝ)) (c := 1 / 2) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hsmall hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hnR.le (3 / 5 : ℝ))
  have hid : (n : ℝ) ^ (3 / 5 : ℝ) * (n : ℝ) ^ (2 / 5 : ℝ) = n := by
    rw [← Real.rpow_add hnR]
    norm_num
  simp only [pow_zero, mul_one] at hmul
  nlinarith

theorem eventually_two_block_lengths_le_two_thirds :
    ∀ᶠ n : ℕ in atTop, ∀ m l₁ l₂ c : ℕ,
      l₁ ≤ n → l₂ ≤ m → m < n - l₁ → c ≤ m - l₂ →
      IsSquare (falling n l₁ * falling m l₂ * c.factorial) →
      (max l₁ l₂ : ℕ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hshort : ∀ᶠ m : ℕ in atTop, 2 ≤ m ∧
      (m : ℝ) ^ (3 / 5 : ℝ) ≤ (m : ℝ) / 2 ∧
      ∀ y : ℝ, (m : ℝ) ^ (3 / 5 : ℝ) ≤ y → y ≤ (m : ℝ) / 2 →
        y / 8 ≤ Chebyshev.theta m - Chebyshev.theta ((m : ℝ) - y) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_three_fifths_le_half,
      tendsto_natCast_atTop_atTop.eventually eventually_theta_backward_three_fifths]
      with m hm hhalf htheta
    exact ⟨hm, hhalf, htheta⟩
  obtain ⟨A, hA⟩ := eventually_atTop.mp hshort
  have hApower : ∀ᶠ n : ℕ in atTop, (A : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    ((_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop A, hApower, hlog,
    eventually_logPow_le_small_rpow 1 (d := (1 / 15 : ℝ)) (c := 1 / 16)
      (by norm_num) (by norm_num)] with n hnA hnPower hlogn hlogSmall
  intro m l₁ l₂ c hl₁ hl₂ hsep hc hsq
  have hnData := hA n hnA
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmn : m ≤ n := hsep.le.trans (Nat.sub_le _ _)
  have hfirst : (l₁ : ℝ) < (n : ℝ) ^ (3 / 5 : ℝ) := by
    by_contra hnot
    let y := min (l₁ : ℝ) ((n : ℝ) / 2)
    have hylow : (n : ℝ) ^ (3 / 5 : ℝ) ≤ y :=
      le_min (le_of_not_gt hnot) hnData.2.1
    have hypos : 0 < y := (Real.rpow_pos_of_pos hnR _).trans_le hylow
    have htheta := hnData.2.2 y hylow (min_le_right _ _)
    have hzero := upper_block_theta_difference_eq_zero hypos.le (min_le_left _ _)
      (min_le_right _ _) hl₁ hl₂ hsep hc hsq
    rw [hzero] at htheta
    linarith
  have hsecond : (l₂ : ℝ) ≤ 16 * (n : ℝ) ^ (3 / 5 : ℝ) * Real.log n := by
    by_cases hmA : A ≤ m
    · have hmData := hA m hmA
      by_cases hlshort : (l₂ : ℝ) < (m : ℝ) ^ (3 / 5 : ℝ)
      · have hpmon : (m : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmn) (by norm_num)
        have hp0 := Real.rpow_nonneg hnR.le (3 / 5 : ℝ)
        nlinarith [mul_le_mul_of_nonneg_left hlogn hp0]
      · let y := min (l₂ : ℝ) ((m : ℝ) / 2)
        have hylow : (m : ℝ) ^ (3 / 5 : ℝ) ≤ y :=
          le_min (le_of_not_gt hlshort) hmData.2.1
        have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
        have hypos : 0 < y := (Real.rpow_pos_of_pos hmR _).trans_le hylow
        have htheta := hmData.2.2 y hylow (min_le_right _ _)
        have hthetaUpper := lower_block_theta_difference_le hypos.le (min_le_left _ _)
          (min_le_right _ _) hl₁ hl₂ hc hsq
        have hl2y : (l₂ : ℝ) ≤ 2 * y := by
          have hl₂R : (l₂ : ℝ) ≤ m := by exact_mod_cast hl₂
          dsimp only [y]
          rcases le_total (l₂ : ℝ) ((m : ℝ) / 2) with h | h
          · rw [min_eq_left h]; nlinarith [Nat.cast_nonneg (α := ℝ) l₂]
          · rw [min_eq_right h]; linarith
        have hmul := mul_le_mul_of_nonneg_right hfirst.le (by linarith : 0 ≤ Real.log (n : ℝ))
        nlinarith
    · have hmR : (m : ℝ) ≤ A := by exact_mod_cast (le_of_lt (lt_of_not_ge hmA))
      have hl₂R : (l₂ : ℝ) ≤ m := by exact_mod_cast hl₂
      have hp0 := Real.rpow_nonneg hnR.le (3 / 5 : ℝ)
      nlinarith [mul_le_mul_of_nonneg_left hlogn hp0]
  have hfirstCoarse : (l₁ : ℝ) ≤ 16 * (n : ℝ) ^ (3 / 5 : ℝ) * Real.log n := by
    nlinarith [mul_le_mul_of_nonneg_left hlogn (Real.rpow_nonneg hnR.le (3 / 5 : ℝ))]
  have hmax : ((max l₁ l₂ : ℕ) : ℝ) ≤ 16 * (n : ℝ) ^ (3 / 5 : ℝ) * Real.log n := by
    rw [Nat.cast_max]
    exact max_le hfirstCoarse hsecond
  apply hmax.trans
  have hmul := mul_le_mul_of_nonneg_left hlogSmall (Real.rpow_nonneg hnR.le (3 / 5 : ℝ))
  have hid : (n : ℝ) ^ (3 / 5 : ℝ) * (n : ℝ) ^ (1 / 15 : ℝ) =
      (n : ℝ) ^ (2 / 3 : ℝ) := by rw [← Real.rpow_add hnR]; norm_num
  simp only [pow_one] at hmul
  nlinarith

theorem eventually_large_prime_dominates_blocks {α D : ℝ}
    (_hα : 0 ≤ α) (hαsmall : α < 1 / 3) (hD : 1 ≤ D) :
    ∀ᶠ n : ℕ in atTop, ∀ a p L c : ℕ,
      0 < a → 0 < p → n = a * p → (a : ℝ) ≤ (n : ℝ) ^ α →
      (L : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) →
      (c : ℝ) ≤ D * ((L : ℝ) * Real.log n + 1) →
      L < p ∧ c < p ∧ n < p ^ 2 := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hlog, eventually_ge_atTop (2 : ℕ),
    eventually_logPow_le_small_rpow 1 (d := 1 - α - 2 / 3) (c := 1 / (4 * D))
      (by linarith) (by positivity),
    eventually_logPow_le_small_rpow 0 (d := 1 - 2 * α) (c := 1 / 2)
      (by linarith) (by norm_num)] with n hlogn hn hsmall hsquare
  intro a p L c ha hp hnap haN hL hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hgamma1 : 1 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hbudget : 4 * D * ((n : ℝ) ^ α * (n : ℝ) ^ (2 / 3 : ℝ)) * Real.log n ≤ n := by
    have h := mul_le_mul_of_nonneg_left hsmall
      (Real.rpow_nonneg hnR.le (α + 2 / 3))
    have hid : (n : ℝ) ^ (α + 2 / 3) * (n : ℝ) ^ (1 - α - 2 / 3) = n := by
      rw [← Real.rpow_add hnR]
      convert Real.rpow_one (n : ℝ) using 1
      ring
    simp only [pow_one] at h
    have hnorm : (n : ℝ) ^ (α + 2 / 3) * Real.log n ≤ (n : ℝ) / (4 * D) := by
      calc
        (n : ℝ) ^ (α + 2 / 3) * Real.log n ≤
            (n : ℝ) ^ (α + 2 / 3) * ((1 / (4 * D)) * (n : ℝ) ^ (1 - α - 2 / 3)) := h
        _ = ((n : ℝ) ^ (α + 2 / 3) * (n : ℝ) ^ (1 - α - 2 / 3)) / (4 * D) := by ring
        _ = (n : ℝ) / (4 * D) := by rw [hid]
    have h' := (le_div_iff₀ (by positivity : 0 < 4 * D)).mp hnorm
    rw [Real.rpow_add hnR] at h'
    nlinarith
  have hLC : (a : ℝ) * L < n ∧ (a : ℝ) * c < n := by
    have hprod := mul_le_mul haN hL (Nat.cast_nonneg L) (Real.rpow_nonneg hnR.le α)
    have hcoef : (c : ℝ) ≤ 2 * D * (n : ℝ) ^ (2 / 3 : ℝ) * Real.log n := by
      have h := mul_le_mul_of_nonneg_right hL hlogpos.le
      have hbase : 1 ≤ (n : ℝ) ^ (2 / 3 : ℝ) * Real.log n := by nlinarith
      have hscaled := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ D)
      have hone := mul_le_mul_of_nonneg_left hbase (by linarith : 0 ≤ D)
      nlinarith
    have hprodC := mul_le_mul haN hcoef (Nat.cast_nonneg c) (Real.rpow_nonneg hnR.le α)
    have hbase := mul_le_mul_of_nonneg_left hlogn
      (mul_nonneg (Real.rpow_nonneg hnR.le α) (Real.rpow_nonneg hnR.le (2 / 3 : ℝ)))
    have hfactor : 1 ≤ 2 * D * Real.log (n : ℝ) := by nlinarith
    have hscale := mul_le_mul_of_nonneg_left hfactor
      (mul_nonneg (Real.rpow_nonneg hnR.le α) (Real.rpow_nonneg hnR.le (2 / 3 : ℝ)))
    constructor <;> nlinarith
  have haSq : (a : ℝ) ^ 2 < n := by
    have hpow : (a : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * α) := by
      calc
        (a : ℝ) ^ 2 ≤ ((n : ℝ) ^ α) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) a]
        _ = (n : ℝ) ^ (2 * α) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]; congr 1; ring
    have h := mul_le_mul_of_nonneg_left hsquare (Real.rpow_nonneg hnR.le (2 * α))
    have hid : (n : ℝ) ^ (2 * α) * (n : ℝ) ^ (1 - 2 * α) = n := by
      rw [← Real.rpow_add hnR]
      convert Real.rpow_one (n : ℝ) using 1
      ring
    simp only [pow_zero, mul_one] at h
    nlinarith
  have hLNat : a * L < n := by exact_mod_cast hLC.1
  have hcNat : a * c < n := by exact_mod_cast hLC.2
  have haNat : a * a < n := by
    have h : a ^ 2 < n := by exact_mod_cast haSq
    simpa only [pow_two] using h
  rw [hnap] at hLNat hcNat haNat
  have hap : a < p := (Nat.mul_lt_mul_left ha).mp haNat
  exact ⟨(Nat.mul_lt_mul_left ha).mp hLNat, (Nat.mul_lt_mul_left ha).mp hcNat,
    by rw [hnap, pow_two]; exact Nat.mul_lt_mul_of_pos_right hap hp⟩

end Erdos374Research
