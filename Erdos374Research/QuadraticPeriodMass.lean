import Erdos374Research.GoodPeriodMass

/-! UNCOMPILED. The public quadratic-band measure theorem, a fixed smooth
integer-avoiding factor, and complete rational periods give a uniform
positive integral. The small quadratic coefficient case is explicit. -/

namespace Erdos374Research

open Tao2026 MeasureTheory Set
open scoped ContDiff

noncomputable section

lemma one_hundredth_le_dist_integer_of_innerBand {x : ℝ}
    (hx0 : (1 / 100 : ℝ) ≤ Int.fract x) (hx1 : Int.fract x ≤ 89 / 100)
    (k : ℤ) : (1 / 100 : ℝ) ≤ |x - (k : ℝ)| := by
  have hid := Int.fract_add_floor x
  by_cases hk : k ≤ ⌊x⌋
  · have hkR : (k : ℝ) ≤ ⌊x⌋ := by exact_mod_cast hk
    have h := le_abs_self (x - (k : ℝ))
    linarith
  · have hkR : (⌊x⌋ : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : ⌊x⌋ + 1 ≤ k)
    have h := neg_le_abs (x - (k : ℝ))
    linarith

lemma integerAvoidingWeight_eq_one_of_innerBand {N : ℕ}
    (hN : 1 < Real.log (N : ℝ)) (hd : plateauWidth N < 1 / 100)
    {x : ℝ} (hx0 : (1 / 100 : ℝ) ≤ Int.fract x) (hx1 : Int.fract x ≤ 89 / 100) :
    integerAvoidingWeight N x = 1 :=
  integerAvoidingWeight_eq_one_far hN
    (fun k => hd.trans_le (one_hundredth_le_dist_integer_of_innerBand hx0 hx1 k))

theorem quadratic_period_integral_lower
    {n M P N : ℕ} {a b : ℝ} {F : ℝ → ℝ}
    (hn : 0 < n) (hM : 0 < M) (hP : 0 < P) (hMn : M ≤ n)
    (hN : 1 < Real.log (N : ℝ)) (hd : plateauWidth N < 1 / 100)
    (ha : 0 < a) (hb : 0 ≤ b)
    (hslow : 200 * a ≤ P) (hboundary : a ≤ (n : ℝ) / (32 * P))
    (hscale : (1 / 2 : ℝ) ≤ (M : ℝ) / (P : ℝ) ^ 2)
    (hF : Continuous F) (hF0 : ∀ u, 0 ≤ F u) (hper : Function.Periodic F a)
    (hmass : a * b ≤ ∫ u in (0 : ℝ)..a, F u) :
    b * (n : ℝ) / (32 * P) ≤
      ∫ u in (n : ℝ) / (2 * P)..(n : ℝ) / P,
        F u * integerAvoidingWeight N ((M : ℝ) * u ^ 2 / (n : ℝ) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  let A := (n : ℝ) / (2 * P)
  let B := (n : ℝ) / P
  let W := fun u => F u * integerAvoidingWeight N ((M : ℝ) * u ^ 2 / (n : ℝ) ^ 2)
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact div_le_div_of_nonneg_left hnR.le hPR (by linarith)
  have hS : rationalQuadraticBand n M P ⊆ Ioo A B := by
    intro u hu
    exact ((mem_rationalQuadraticBand hn hM hP).mp hu).1
  have hW : Continuous W := hF.mul ((integerAvoidingWeight_contDiff N).continuous.comp
    ((continuous_const.mul (continuous_id.pow 2)).div_const _))
  have hnear : ∀ u ∈ rationalQuadraticBand n M P, ∀ v ∈ Icc A B,
      |v - u| ≤ a → W v = F v := by
    intro u hu v hv hdist
    obtain ⟨huI, hu0, hu1⟩ := (mem_rationalQuadraticBand hn hM hP).mp hu
    have hvariation := quadratic_phase_variation hn hP hMn hv ⟨huI.1.le, huI.2.le⟩ hdist
    have hsmall : 2 * a / (P : ℝ) ≤ 1 / 100 := (div_le_iff₀ hPR).mpr (by linarith)
    have hband := fract_mem_veryBad_innerBand_of_abs_sub_le (hvariation.trans hsmall) hu0 hu1
    dsimp only [W]
    rw [integerAvoidingWeight_eq_one_of_innerBand hN hd hband.1 hband.2, mul_one]
  have h := periodic_weight_integral_lower_from_band ha hAB (mul_nonneg ha.le hb)
    hF hW (fun u => mul_nonneg (hF0 u) (integerAvoidingWeight_nonneg _ _))
    hper hmass hS hnear
  have hmeasure := rationalQuadraticBand_measure_lower hn hM hP hscale
  have hcoef : (n : ℝ) / (32 * P) ≤ volume.real (rationalQuadraticBand n M P) - a := by
    have hid : (n : ℝ) / (16 * P) = 2 * ((n : ℝ) / (32 * P)) := by field_simp; ring
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hb
  have hid : (volume.real (rationalQuadraticBand n M P) - a) / a * (a * b) =
      (volume.real (rationalQuadraticBand n M P) - a) * b := by field_simp
  rw [hid] at h
  calc
    b * (n : ℝ) / (32 * P) = ((n : ℝ) / (32 * P)) * b := by ring
    _ ≤ (volume.real (rationalQuadraticBand n M P) - a) * b := hmul
    _ ≤ _ := h

theorem full_period_integral_lower
    {n P : ℕ} {a b : ℝ} {F : ℝ → ℝ}
    (hn : 0 < n) (hP : 0 < P) (ha : 0 < a) (hb : 0 ≤ b)
    (hboundary : a ≤ (n : ℝ) / (4 * P))
    (hF : Continuous F) (hF0 : ∀ u, 0 ≤ F u) (hper : Function.Periodic F a)
    (hmass : a * b ≤ ∫ u in (0 : ℝ)..a, F u) :
    b * (n : ℝ) / (4 * P) ≤ ∫ u in (n : ℝ) / (2 * P)..(n : ℝ) / P, F u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hAB : (n : ℝ) / (2 * P) ≤ (n : ℝ) / P :=
    div_le_div_of_nonneg_left hnR.le hPR (by linarith)
  have h := periodic_weight_integral_lower_from_band
    (S := Ioo ((n : ℝ) / (2 * P)) ((n : ℝ) / P)) ha hAB (mul_nonneg ha.le hb)
    hF hF hF0 hper hmass (fun _ h => h) (fun _ _ _ _ _ => rfl)
  have hm : volume.real (Ioo ((n : ℝ) / (2 * P)) ((n : ℝ) / P)) =
      (n : ℝ) / (2 * P) := by
    change (volume _).toReal = _
    rw [Real.volume_Ioo,
      show (n : ℝ) / P - (n : ℝ) / (2 * P) = (n : ℝ) / (2 * P) by field_simp; ring,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hm] at h
  have hid : ((n : ℝ) / (2 * P) - a) / a * (a * b) =
      ((n : ℝ) / (2 * P) - a) * b := by field_simp
  rw [hid] at h
  have hcoef : (n : ℝ) / (4 * P) ≤ (n : ℝ) / (2 * P) - a := by
    have hid : (n : ℝ) / (2 * P) = 2 * ((n : ℝ) / (4 * P)) := by field_simp; ring
    linarith
  calc
    b * (n : ℝ) / (4 * P) = ((n : ℝ) / (4 * P)) * b := by ring
    _ ≤ ((n : ℝ) / (2 * P) - a) * b := mul_le_mul_of_nonneg_right hcoef hb
    _ ≤ _ := h

def longBlockSquareWeight (N M P : ℕ) (x : ℝ) : ℝ :=
  if 2 * M < P ^ 2 then 1 else integerAvoidingWeight N x

theorem longBlockSquareWeight_contDiff (N M P : ℕ) :
    ContDiff ℝ ∞ (longBlockSquareWeight N M P) := by
  unfold longBlockSquareWeight
  split_ifs
  · exact contDiff_const
  · exact integerAvoidingWeight_contDiff N

theorem longBlockSquareWeight_nonneg (N M P : ℕ) (x : ℝ) :
    0 ≤ longBlockSquareWeight N M P x := by
  unfold longBlockSquareWeight
  split_ifs
  · norm_num
  · exact integerAvoidingWeight_nonneg N x

theorem longBlockSquareWeight_le_one (N M P : ℕ) (x : ℝ) :
    longBlockSquareWeight N M P x ≤ 1 := by
  unfold longBlockSquareWeight
  split_ifs
  · rfl
  · exact integerAvoidingWeight_le_one N x

theorem longBlockSquareWeight_periodic (N M P : ℕ) :
    Function.Periodic (longBlockSquareWeight N M P) 1 := by
  unfold longBlockSquareWeight
  split_ifs
  · exact fun _ => rfl
  · exact integerAvoidingWeight_periodic N

theorem longBlockSquareWeight_reciprocal_mass
    {n M P N : ℕ} {a b : ℝ} {F : ℝ → ℝ}
    (hn : 0 < n) (hM : 0 < M) (hP : 0 < P) (hMn : M ≤ n)
    (hN : 1 < Real.log (N : ℝ)) (hd : plateauWidth N < 1 / 100)
    (ha : 0 < a) (hb : 0 ≤ b)
    (hslow : 200 * a ≤ P) (hboundary : a ≤ (n : ℝ) / (32 * P))
    (hF : Continuous F) (hF0 : ∀ u, 0 ≤ F u) (hper : Function.Periodic F a)
    (hmass : a * b ≤ ∫ u in (0 : ℝ)..a, F u) :
    b * (n : ℝ) / (32 * P) ≤
      ∫ u in (n : ℝ) / (2 * P)..(n : ℝ) / P,
        F u * longBlockSquareWeight N M P ((M : ℝ) * u ^ 2 / (n : ℝ) ^ 2) := by
  unfold longBlockSquareWeight
  split_ifs with hsmall
  · simp only [mul_one]
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlarge : a ≤ (n : ℝ) / (4 * P) := hboundary.trans
      (div_le_div_of_nonneg_left hnR.le (by positivity) (by nlinarith))
    have h := full_period_integral_lower hn hP ha hb hlarge hF hF0 hper hmass
    exact (div_le_div_of_nonneg_left (mul_nonneg hb hnR.le)
      (by positivity) (by nlinarith)).trans h
  · apply quadratic_period_integral_lower hn hM hP hMn hN hd ha hb hslow hboundary
      _ hF hF0 hper hmass
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP
    have h' : (P : ℝ) ^ 2 ≤ 2 * M := by exact_mod_cast (le_of_not_gt hsmall)
    exact (le_div_iff₀ (sq_pos_of_pos hPR)).mpr (by linarith)

end
end Erdos374Research
