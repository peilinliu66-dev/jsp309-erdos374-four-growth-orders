import Erdos374Research.PrimeComparison
import Erdos374Research.IntegerAvoidingWeight

/-! UNCOMPILED. Exact natural rounding and support scales for the long-block
argument. Constants use a block-ratio split of 2000. -/

namespace Erdos374Research

open Tao2026

noncomputable section

def longBlockSigma (n : ℕ) : ℝ := 1 / (Real.log n) ^ 2
def longBlockPrimeScale (n L : ℕ) : ℕ := ⌈(L : ℝ) * (Real.log n) ^ 2⌉₊

lemma longBlockPrimeScale_bounds {n L : ℕ}
    (hlog : 1 ≤ Real.log (n : ℝ)) (hL : 1 ≤ L) :
    (L : ℝ) * (Real.log n) ^ 2 ≤ longBlockPrimeScale n L ∧
      (longBlockPrimeScale n L : ℝ) ≤ 2 * (L : ℝ) * (Real.log n) ^ 2 := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogSq : 1 ≤ (Real.log (n : ℝ)) ^ 2 := one_le_pow₀ (n := 2) hlog
  have hbase : 1 ≤ (L : ℝ) * (Real.log n) ^ 2 := by nlinarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (L : ℝ) * (Real.log n) ^ 2 by positivity)
  exact ⟨Nat.le_ceil _, by change (longBlockPrimeScale n L : ℝ) < _ at hceil; linarith⟩

lemma longBlockPrimeScale_pos {n L : ℕ}
    (hlog : 1 ≤ Real.log (n : ℝ)) (hL : 1 ≤ L) : 0 < longBlockPrimeScale n L := by
  have h := (longBlockPrimeScale_bounds hlog hL).1
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hp : (0 : ℝ) < longBlockPrimeScale n L := (by positivity :
    0 < (L : ℝ) * (Real.log n) ^ 2).trans_le h
  exact_mod_cast hp

lemma longBlock_ratio_bounds {n L : ℕ}
    (hlog : 1 ≤ Real.log (n : ℝ)) (hL : 1 ≤ L) :
    longBlockSigma n / 2 ≤ (L : ℝ) / longBlockPrimeScale n L ∧
      (L : ℝ) / longBlockPrimeScale n L ≤ longBlockSigma n := by
  have hp : (0 : ℝ) < longBlockPrimeScale n L := by exact_mod_cast longBlockPrimeScale_pos hlog hL
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hb := longBlockPrimeScale_bounds hlog hL
  unfold longBlockSigma
  constructor
  · rw [show (1 / (Real.log (n : ℝ)) ^ 2) / 2 =
        1 / (2 * (Real.log (n : ℝ)) ^ 2) by ring]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (Real.log (n : ℝ)) ^ 2) hp).2
    nlinarith
  · apply (div_le_div_iff₀ hp (by positivity : 0 < (Real.log (n : ℝ)) ^ 2)).2
    nlinarith

lemma plateauWidth_natPower {n m : ℕ} (_hm : 1 ≤ m) :
    plateauWidth (n ^ m) = longBlockSigma n / (10 * (m : ℝ) ^ 2) := by
  unfold plateauWidth longBlockSigma
  rw [Nat.cast_pow, Real.log_pow, mul_pow, div_div]
  congr 1
  ring

lemma lower_dominant_avoided_width {n l₁ l₂ : ℕ}
    (hlog : 1 ≤ Real.log (n : ℝ)) (hl₂ : 1 ≤ l₂) (hdom : 2000 * l₁ < l₂) :
    (l₁ : ℝ) / longBlockPrimeScale n l₂ < plateauWidth (n ^ 3) / 12 := by
  have hp : (0 : ℝ) < longBlockPrimeScale n l₂ := by exact_mod_cast longBlockPrimeScale_pos hlog hl₂
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hsigma : 0 < longBlockSigma n := by unfold longBlockSigma; positivity
  have hdomR : 2000 * (l₁ : ℝ) < l₂ := by exact_mod_cast hdom
  have hratio := (longBlock_ratio_bounds hlog hl₂).2
  have hlratio : (l₁ : ℝ) / longBlockPrimeScale n l₂ < longBlockSigma n / 2000 := by
    have h := (div_lt_div_iff_of_pos_right hp).2 hdomR
    rw [mul_div_assoc] at h
    nlinarith
  rw [plateauWidth_natPower (by norm_num : 1 ≤ (3 : ℕ))]
  norm_num
  nlinarith

end
end Erdos374Research
