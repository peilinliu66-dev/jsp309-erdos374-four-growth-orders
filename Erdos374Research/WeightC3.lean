import Erdos374Research.TranslatedPlateau
import Erdos374Research.IntegerAvoidingWeight
import Tao2026.SpecializedGrowingFourier

/-!
UNCOMPILED. Coarse C³ calculus for the separable detecting weights. The
projection estimate and Leibniz bookkeeping adapt the actual MIT-0 Tao2026
FactorialEquidistribution implementation; all analytic inputs stay upstream.
-/

namespace Erdos374Research

open Tao2026
open scoped BigOperators ContDiff

noncomputable section

def secondWeightLift (w : ℝ → ℝ) (z : ℝ × ℝ) : ℂ := (w z.2 : ℂ)

lemma secondWeightLift_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (secondWeightLift w) :=
  Complex.ofRealCLM.contDiff.comp (hw.comp contDiff_snd)

lemma secondWeightLift_periodic {w : ℝ → ℝ} (hw : Function.Periodic w 1) :
    IsZ2Periodic (secondWeightLift w) := by
  intro x y m n
  change ((w (y + (n : ℝ)) : ℝ) : ℂ) = ((w y : ℝ) : ℂ)
  rw [show y + (n : ℝ) = y + (n : ℝ) * 1 by ring, hw.int_mul n]

lemma secondWeightLift_norm_le_one {w : ℝ → ℝ}
    (h0 : ∀ x, 0 ≤ w x) (h1 : ∀ x, w x ≤ 1) (z : ℝ × ℝ) :
    ‖secondWeightLift w z‖ ≤ 1 := by
  change ‖(w z.2 : ℂ)‖ ≤ 1
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 _)] using h1 z.2

lemma norm_iteratedFDeriv_secondWeightLift_le {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (i : ℕ) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (secondWeightLift w) z‖ ≤ ‖iteratedFDeriv ℝ i w z.2‖ := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let f : (ℝ × ℝ) → ℝ := w ∘ L
  have hf : ContDiff ℝ ∞ f := hw.comp_continuousLinearMap
  have hlift : secondWeightLift w = Complex.ofRealLI ∘ f := rfl
  rw [hlift, Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt (mod_cast le_top)]
  have heq := L.iteratedFDeriv_comp_right hw z (i := i) (mod_cast le_top)
  change ‖iteratedFDeriv ℝ i f z‖ ≤ _
  rw [show f = w ∘ L by rfl, heq]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ i w (L z)) (fun _ => L)).trans
  calc
    ‖iteratedFDeriv ℝ i w (L z)‖ * ∏ _j : Fin i, ‖L‖ ≤
        ‖iteratedFDeriv ℝ i w (L z)‖ * ∏ _j : Fin i, (1 : ℝ) := by
      gcongr with j
      exact ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
    _ = ‖iteratedFDeriv ℝ i w z.2‖ := by simp only [Finset.prod_const_one, mul_one, L]; rfl

lemma norm_iteratedFDeriv_le_C3 {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hper : IsZ2Periodic F) {i : ℕ} (hi : i < 4) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i F z‖ ≤ taoC3Norm F :=
  norm_iteratedFDeriv_le_taoC3Norm_of_bddAbove F
    (fun j _ => bddAbove_iteratedFDeriv_norm_range F hF hper j)
    (Finset.mem_range.mpr hi) z

lemma taoC3Norm_mul_le {F G : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hperF : IsZ2Periodic F) (hperG : IsZ2Periodic G) :
    taoC3Norm (fun z => F z * G z) ≤ 32 * taoC3Norm F * taoC3Norm G := by
  have hF0 := taoC3Norm_nonneg_of_smooth F hF hperF
  have hG0 := taoC3Norm_nonneg_of_smooth G hG hperG
  have hpoint : ∀ i < 4, ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ i (fun z => F z * G z) z‖ ≤
        8 * taoC3Norm F * taoC3Norm G := by
    intro i hi z
    have hproduct := norm_iteratedFDeriv_mul_le hF hG z (n := i) (mod_cast le_top)
    calc
      ‖iteratedFDeriv ℝ i (fun z => F z * G z) z‖ ≤
          ∑ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j F z‖ *
              ‖iteratedFDeriv ℝ (i - j) G z‖ := hproduct
      _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * taoC3Norm F * taoC3Norm G := by
        apply Finset.sum_le_sum
        intro j hj
        have hjle : j ≤ i := by have := Finset.mem_range.mp hj; omega
        gcongr
        · exact norm_iteratedFDeriv_le_C3 hF hperF (by omega) z
        · exact norm_iteratedFDeriv_le_C3 hG hperG (by omega) z
      _ = (2 : ℝ) ^ i * taoC3Norm F * taoC3Norm G := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum,
          Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ 8 * taoC3Norm F * taoC3Norm G := by
        have hpow : (2 : ℝ) ^ i ≤ 8 := by interval_cases i <;> norm_num
        gcongr
  have h := taoC3Norm_le_four_mul_of_iteratedFDeriv_le (by positivity) hpoint
  nlinarith

lemma taoC3Norm_one_sub_le {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (hperF : IsZ2Periodic F) :
    taoC3Norm (fun z => 1 - F z) ≤ 4 * (1 + taoC3Norm F) := by
  have hF0 := taoC3Norm_nonneg_of_smooth F hF hperF
  apply taoC3Norm_le_four_mul_of_iteratedFDeriv_le (by positivity)
  intro i hi z
  have hFi : ContDiff ℝ i F := hF.of_le (mod_cast le_top)
  have hconst : ContDiff ℝ i (fun _ : ℝ × ℝ => (1 : ℂ)) := contDiff_const
  change ‖iteratedFDeriv ℝ i ((fun _ : ℝ × ℝ => (1 : ℂ)) - F) z‖ ≤ _
  rw [iteratedFDeriv_sub_apply hconst.contDiffAt hFi.contDiffAt]
  have hc : ‖iteratedFDeriv ℝ i (fun _ : ℝ × ℝ => (1 : ℂ)) z‖ ≤ 1 := by
    by_cases hi0 : i = 0
    · subst i
      simp
    · rw [iteratedFDeriv_const_of_ne hi0]
      simp
  exact (norm_sub_le _ _).trans (add_le_add hc (norm_iteratedFDeriv_le_C3 hF hperF hi z))

lemma exists_shiftedPlateau_power_second_C3_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (c : ℝ),
      1 ≤ Real.log (n : ℝ) →
      taoC3Norm (secondWeightLift (shiftedPlateau (n ^ m) c)) ≤ C * (Real.log n) ^ 12 := by
  obtain ⟨B, hB, htransition⟩ := exists_smoothTransition_C3_bound
  refine ⟨24 * B * 1200 ^ (3 : ℕ) * (m : ℝ) ^ 12, by positivity, ?_⟩
  intro n c hlog
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogPower : Real.log ((n ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log n := by
    rw [Nat.cast_pow, Real.log_pow]
  have hnp : 1 ≤ Real.log ((n ^ m : ℕ) : ℝ) := by rw [hlogPower]; nlinarith
  have hpoint : ∀ i < 4, ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ i (secondWeightLift (shiftedPlateau (n ^ m) c)) z‖ ≤
        6 * B * (1200 * (Real.log ((n ^ m : ℕ) : ℝ)) ^ 4) ^ 3 := by
    intro i hi z
    exact (norm_iteratedFDeriv_secondWeightLift_le (shiftedPlateau_contDiff _ _) i z).trans
      (norm_iteratedFDeriv_shiftedPlateau_le hB htransition hnp hi c z.2)
  have h := taoC3Norm_le_four_mul_of_iteratedFDeriv_le (by positivity) hpoint
  rw [hlogPower] at h
  convert h using 1; ring

lemma integerAvoidingWeight_first_lift_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (factorialPlateauWeightLift (integerAvoidingWeight N)) :=
  Complex.ofRealCLM.contDiff.comp ((integerAvoidingWeight_contDiff N).comp contDiff_fst)

lemma integerAvoidingWeight_first_lift_periodic (N : ℕ) :
    IsZ2Periodic (factorialPlateauWeightLift (integerAvoidingWeight N)) := by
  intro x y m n
  change ((integerAvoidingWeight N (x + (m : ℝ)) : ℝ) : ℂ) =
    ((integerAvoidingWeight N x : ℝ) : ℂ)
  rw [show x + (m : ℝ) = x + (m : ℝ) * 1 by ring,
    (integerAvoidingWeight_periodic N).int_mul m]

lemma exists_integerAvoidingWeight_power_lift_C3_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ Real.log (n : ℝ) →
      taoC3Norm (factorialPlateauWeightLift (integerAvoidingWeight (n ^ m))) ≤
        C * (Real.log n) ^ 12 := by
  obtain ⟨C, hC, hbound⟩ := exists_shiftedPlateau_power_lift_C3_bound m hm
  refine ⟨4 * (1 + C), by positivity, ?_⟩
  intro n hn
  have hlift : factorialPlateauWeightLift (integerAvoidingWeight (n ^ m)) =
      fun z => 1 - factorialPlateauWeightLift
        (shiftedPlateau (n ^ m) (5 * plateauWidth (n ^ m) / 12)) z := by
    funext z
    simp only [factorialPlateauWeightLift, integerAvoidingWeight, Complex.ofReal_sub,
      Complex.ofReal_one]
  rw [hlift]
  have h := taoC3Norm_one_sub_le
    (shiftedPlateau_lift_contDiff (n ^ m) (5 * plateauWidth (n ^ m) / 12))
    (shiftedPlateau_lift_periodic (n ^ m) (5 * plateauWidth (n ^ m) / 12))
  have hc := hbound n (5 * plateauWidth (n ^ m) / 12) hn
  have hpow : 1 ≤ (Real.log (n : ℝ)) ^ 12 := one_le_pow₀ (n := 12) hn
  nlinarith

lemma exists_integerAvoidingWeight_power_second_C3_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ Real.log (n : ℝ) →
      taoC3Norm (secondWeightLift (integerAvoidingWeight (n ^ m))) ≤
        C * (Real.log n) ^ 12 := by
  obtain ⟨C, hC, hbound⟩ := exists_shiftedPlateau_power_second_C3_bound m hm
  refine ⟨4 * (1 + C), by positivity, ?_⟩
  intro n hn
  have hlift : secondWeightLift (integerAvoidingWeight (n ^ m)) =
      fun z => 1 - secondWeightLift
        (shiftedPlateau (n ^ m) (5 * plateauWidth (n ^ m) / 12)) z := by
    funext z
    simp only [secondWeightLift, integerAvoidingWeight, Complex.ofReal_sub,
      Complex.ofReal_one]
  rw [hlift]
  have h := taoC3Norm_one_sub_le
    (secondWeightLift_contDiff (shiftedPlateau_contDiff (n ^ m) (5 * plateauWidth (n ^ m) / 12)))
    (secondWeightLift_periodic (shiftedPlateau_periodic (n ^ m) (5 * plateauWidth (n ^ m) / 12)))
  have hc := hbound n (5 * plateauWidth (n ^ m) / 12) hn
  have hpow : 1 ≤ (Real.log (n : ℝ)) ^ 12 := one_le_pow₀ (n := 12) hn
  nlinarith

end
end Erdos374Research
