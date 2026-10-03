import Erdos374Research.LongBlockScale
import Erdos374Research.RationalWeightPeriods
import Erdos374Research.WeightC3
import Erdos374Research.QuadraticPeriodMass

/-!
UNCOMPILED. Explicit translated source plateaus for the two cases of Yudin's
long-block argument. The ratio split is 2000. The upper-case orbit estimate
is the additive-character minorant proved in RationalWeightPeriods.
-/

namespace Erdos374Research

open Tao2026 MeasureTheory
open scoped ContDiff

noncomputable section

def upperBlockSeparator (n N P l : ℕ) (z : ℝ × ℝ) : ℂ :=
  (shiftedPlateau (n ^ 100) ((l : ℝ) / (4 * P)) z.1 : ℂ) *
    (integerAvoidingWeight N z.2 : ℂ)

def lowerBlockSeparator (n P l j : ℕ) (z : ℝ × ℝ) : ℂ :=
  (integerAvoidingWeight (n ^ 3) z.1 : ℂ) *
    (shiftedPlateau n (((l : ℝ) - j) / (2 * P)) z.2 : ℂ)

def blockSeparator (n N P l₁ l₂ j : ℕ) : ℝ × ℝ → ℂ :=
  if l₂ ≤ 2000 * l₁ then upperBlockSeparator n N P l₁
  else lowerBlockSeparator n P l₂ j

def blockSeparatorReal (n N P l₁ l₂ j a t : ℕ) (u : ℝ) : ℝ :=
  if l₂ ≤ 2000 * l₁ then
    shiftedPlateau (n ^ 100) ((l₁ : ℝ) / (4 * P)) u *
      integerAvoidingWeight N ((t : ℝ) / a * u)
  else integerAvoidingWeight (n ^ 3) u *
    shiftedPlateau n (((l₂ : ℝ) - j) / (2 * P)) ((t : ℝ) / a * u)

def selectedBlockCenter (n m l₁ l₂ j : ℕ) : ℕ :=
  if l₂ ≤ 2000 * l₁ then n else m - j

lemma blockSeparatorReal_eval (n N P l₁ l₂ j a t : ℕ) (u : ℝ) :
    blockSeparator n N P l₁ l₂ j (u, (t : ℝ) / a * u) =
      (blockSeparatorReal n N P l₁ l₂ j a t u : ℂ) := by
  unfold blockSeparator blockSeparatorReal upperBlockSeparator lowerBlockSeparator
  split_ifs <;> simp only [Complex.ofReal_mul]

lemma blockSeparator_contDiff (n N P l₁ l₂ j : ℕ) :
    ContDiff ℝ ∞ (blockSeparator n N P l₁ l₂ j) := by
  unfold blockSeparator
  split_ifs
  · exact (shiftedPlateau_lift_contDiff _ _).mul
      (secondWeightLift_contDiff (integerAvoidingWeight_contDiff N))
  · exact (integerAvoidingWeight_first_lift_contDiff _).mul
      (secondWeightLift_contDiff (shiftedPlateau_contDiff _ _))

lemma blockSeparator_periodic (n N P l₁ l₂ j : ℕ) :
    IsZ2Periodic (blockSeparator n N P l₁ l₂ j) := by
  intro x y k l
  unfold blockSeparator upperBlockSeparator lowerBlockSeparator
  split_ifs
  · dsimp only
    rw [show x + (k : ℝ) = x + (k : ℝ) * 1 by ring,
      show y + (l : ℝ) = y + (l : ℝ) * 1 by ring,
      (shiftedPlateau_periodic _ _).int_mul k,
      (integerAvoidingWeight_periodic _).int_mul l]
  · dsimp only
    rw [show x + (k : ℝ) = x + (k : ℝ) * 1 by ring,
      show y + (l : ℝ) = y + (l : ℝ) * 1 by ring,
      (integerAvoidingWeight_periodic _).int_mul k,
      (shiftedPlateau_periodic _ _).int_mul l]

lemma blockSeparator_norm_le_one (n N P l₁ l₂ j : ℕ) (z : ℝ × ℝ) :
    ‖blockSeparator n N P l₁ l₂ j z‖ ≤ 1 := by
  unfold blockSeparator upperBlockSeparator lowerBlockSeparator
  split_ifs <;> rw [norm_mul] <;>
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (shiftedPlateau_nonneg _ _ _),
      abs_of_nonneg (integerAvoidingWeight_nonneg _ _)]
  · exact mul_le_one₀ (shiftedPlateau_le_one _ _ _) (integerAvoidingWeight_nonneg _ _)
      (integerAvoidingWeight_le_one _ _)
  · exact mul_le_one₀ (integerAvoidingWeight_le_one _ _) (shiftedPlateau_nonneg _ _ _)
      (shiftedPlateau_le_one _ _ _)

lemma blockSeparatorReal_continuous (n N P l₁ l₂ j a t : ℕ) :
    Continuous (blockSeparatorReal n N P l₁ l₂ j a t) := by
  unfold blockSeparatorReal
  split_ifs
  · exact (shiftedPlateau_contDiff _ _).continuous.mul
      ((integerAvoidingWeight_contDiff _).continuous.comp (continuous_const.mul continuous_id))
  · exact (integerAvoidingWeight_contDiff _).continuous.mul
      ((shiftedPlateau_contDiff _ _).continuous.comp (continuous_const.mul continuous_id))

lemma blockSeparatorReal_nonneg (n N P l₁ l₂ j a t : ℕ) (u : ℝ) :
    0 ≤ blockSeparatorReal n N P l₁ l₂ j a t u := by
  unfold blockSeparatorReal
  split_ifs
  · exact mul_nonneg (shiftedPlateau_nonneg _ _ _) (integerAvoidingWeight_nonneg _ _)
  · exact mul_nonneg (integerAvoidingWeight_nonneg _ _) (shiftedPlateau_nonneg _ _ _)

lemma blockSeparatorReal_periodic (n N P l₁ l₂ j : ℕ) {a t : ℕ} (ha : 0 < a) :
    Function.Periodic (blockSeparatorReal n N P l₁ l₂ j a t) (a : ℝ) := by
  unfold blockSeparatorReal
  split_ifs
  · exact rational_product_periodic (shiftedPlateau_periodic _ _)
      (integerAvoidingWeight_periodic _) ha
  · exact rational_product_periodic (integerAvoidingWeight_periodic _)
      (shiftedPlateau_periodic _ _) ha

theorem blockSeparatorReal_period_mass {n N a t : ℕ}
    (hn : 1 < Real.log (n : ℝ)) (hN : 1 < Real.log (N : ℝ))
    (hd : plateauWidth N ≤ 1 / 100) (ht : 0 < t) (hta : t < a)
    (P l₁ l₂ j : ℕ) :
    (a : ℝ) * (longBlockSigma n / 1800000) ≤
      ∫ u in (0 : ℝ)..a, blockSeparatorReal n N P l₁ l₂ j a t u := by
  have ha : 0 < a := lt_trans ht hta
  have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hl : Real.log (n : ℝ) ≠ 0 := by linarith
  have hsigma : 0 < longBlockSigma n := by unfold longBlockSigma; positivity
  have hlog100 : 1 < Real.log ((n ^ 100 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    linarith
  have hlog3 : 1 < Real.log ((n ^ 3 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    linarith
  unfold blockSeparatorReal
  split_ifs
  · have h := upper_weight_rational_period_mass hN hd ht hta
      (shiftedPlateau_contDiff (n ^ 100) ((l₁ : ℝ) / (4 * P))).continuous
      (shiftedPlateau_periodic _ _) (shiftedPlateau_nonneg _ _)
    have hm := shiftedPlateau_period_mass hlog100 ((l₁ : ℝ) / (4 * P)) 0
    simp only [zero_add] at hm
    have hvalue : 1 / (60 * Real.log ((n ^ 100 : ℕ) : ℝ) ^ 2) =
        longBlockSigma n / 600000 := by
      rw [Nat.cast_pow, Real.log_pow]
      unfold longBlockSigma
      norm_num
      ring
    rw [hvalue] at hm
    have hh := mul_le_mul_of_nonneg_left hm (div_nonneg haR (by norm_num : (0 : ℝ) ≤ 3))
    calc
      (a : ℝ) * (longBlockSigma n / 1800000) =
          ((a : ℝ) / 3) * (longBlockSigma n / 600000) := by ring
      _ ≤ _ := hh.trans h
  · have h := lower_weight_rational_period_mass hlog3 ha ht
      (shiftedPlateau_contDiff n (((l₂ : ℝ) - j) / (2 * P))).continuous
      (shiftedPlateau_periodic _ _) (shiftedPlateau_nonneg _ _) (shiftedPlateau_le_one _ _)
    have hm := shiftedPlateau_period_mass hn (((l₂ : ℝ) - j) / (2 * P)) 0
    simp only [zero_add] at hm
    have hvalue : 1 / (60 * Real.log (n : ℝ) ^ 2) = longBlockSigma n / 60 := by
      unfold longBlockSigma
      ring
    rw [hvalue] at hm
    rw [plateauWidth_natPower (by norm_num : 1 ≤ (3 : ℕ))] at h
    norm_num at h
    have hmul := mul_le_mul_of_nonneg_left hm haR
    nlinarith

theorem exists_blockSeparator_C3_bound (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n P l₁ l₂ j : ℕ, 1 ≤ Real.log (n : ℝ) →
      taoC3Norm (blockSeparator n N P l₁ l₂ j) ≤ C * (Real.log n) ^ 24 := by
  obtain ⟨C₁, hC₁, hfirst⟩ := exists_shiftedPlateau_power_lift_C3_bound 100 (by norm_num)
  obtain ⟨C₂, hC₂, hsecond⟩ := exists_integerAvoidingWeight_power_lift_C3_bound 3 (by norm_num)
  obtain ⟨C₃, hC₃, hthird⟩ := exists_shiftedPlateau_power_second_C3_bound 1 (by norm_num)
  let D := taoC3Norm (secondWeightLift (integerAvoidingWeight N))
  have hD : 0 ≤ D := taoC3Norm_nonneg_of_smooth _
    (secondWeightLift_contDiff (integerAvoidingWeight_contDiff N))
    (secondWeightLift_periodic (integerAvoidingWeight_periodic N))
  refine ⟨32 * C₁ * (1 + D) + 32 * C₂ * C₃ + 1, by positivity, ?_⟩
  intro n P l₁ l₂ j hn
  have hpow : (Real.log (n : ℝ)) ^ 12 ≤ (Real.log n) ^ 24 := by
    have h := one_le_pow₀ (n := 12) hn
    nlinarith
  unfold blockSeparator
  split_ifs
  · have h := taoC3Norm_mul_le
      (shiftedPlateau_lift_contDiff (n ^ 100) ((l₁ : ℝ) / (4 * P)))
      (secondWeightLift_contDiff (integerAvoidingWeight_contDiff N))
      (shiftedPlateau_lift_periodic (n ^ 100) ((l₁ : ℝ) / (4 * P)))
      (secondWeightLift_periodic (integerAvoidingWeight_periodic N))
    have hb := hfirst n ((l₁ : ℝ) / (4 * P)) hn
    change taoC3Norm (upperBlockSeparator n N P l₁) ≤ _ at h
    change taoC3Norm (upperBlockSeparator n N P l₁) ≤ _
    have hcoef : 32 * C₁ * D ≤ 32 * C₁ * (1 + D) + 32 * C₂ * C₃ + 1 := by
      nlinarith [show 0 ≤ C₂ * C₃ by positivity]
    calc
      taoC3Norm (upperBlockSeparator n N P l₁) ≤
          32 * taoC3Norm (factorialPlateauWeightLift
            (shiftedPlateau (n ^ 100) ((l₁ : ℝ) / (4 * P)))) * D := h
      _ ≤ 32 * (C₁ * (Real.log n) ^ 12) * D :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 32)) hD
      _ = (32 * C₁ * D) * (Real.log n) ^ 12 := by ring
      _ ≤ (32 * C₁ * D) * (Real.log n) ^ 24 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (32 * C₁ * (1 + D) + 32 * C₂ * C₃ + 1) * (Real.log n) ^ 24 :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
  · have h := taoC3Norm_mul_le (integerAvoidingWeight_first_lift_contDiff (n ^ 3))
      (secondWeightLift_contDiff (shiftedPlateau_contDiff n (((l₂ : ℝ) - j) / (2 * P))))
      (integerAvoidingWeight_first_lift_periodic (n ^ 3))
      (secondWeightLift_periodic (shiftedPlateau_periodic n (((l₂ : ℝ) - j) / (2 * P))))
    have hb := hsecond n hn
    have hc := hthird n (((l₂ : ℝ) - j) / (2 * P)) hn
    simp only [pow_one] at hc
    have hnonneg := taoC3Norm_nonneg_of_smooth _
      (secondWeightLift_contDiff (shiftedPlateau_contDiff n (((l₂ : ℝ) - j) / (2 * P))))
      (secondWeightLift_periodic (shiftedPlateau_periodic _ _))
    have hmul := mul_le_mul hb hc hnonneg (by positivity : 0 ≤ C₂ * (Real.log n) ^ 12)
    have hid : (Real.log (n : ℝ)) ^ 12 * (Real.log n) ^ 12 = (Real.log n) ^ 24 := by ring
    change taoC3Norm (lowerBlockSeparator n P l₂ j) ≤ _ at h
    change taoC3Norm (lowerBlockSeparator n P l₂ j) ≤ _
    have hcoef : 32 * C₂ * C₃ ≤ 32 * C₁ * (1 + D) + 32 * C₂ * C₃ + 1 := by
      linarith [show 0 ≤ 32 * C₁ * (1 + D) by positivity]
    calc
      taoC3Norm (lowerBlockSeparator n P l₂ j) ≤
          32 * taoC3Norm (factorialPlateauWeightLift (integerAvoidingWeight (n ^ 3))) *
            taoC3Norm (secondWeightLift (shiftedPlateau n (((l₂ : ℝ) - j) / (2 * P)))) := h
      _ = 32 * (taoC3Norm (factorialPlateauWeightLift (integerAvoidingWeight (n ^ 3))) *
          taoC3Norm (secondWeightLift (shiftedPlateau n (((l₂ : ℝ) - j) / (2 * P))))) := by ring
      _ ≤ 32 * (C₂ * (Real.log n) ^ 12 * (C₃ * (Real.log n) ^ 12)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 32)
      _ = (32 * C₂ * C₃) * ((Real.log n) ^ 12 * (Real.log n) ^ 12) := by ring
      _ = (32 * C₂ * C₃) * (Real.log n) ^ 24 := by rw [hid]
      _ ≤ (32 * C₁ * (1 + D) + 32 * C₂ * C₃ + 1) * (Real.log n) ^ 24 :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)

end
end Erdos374Research
