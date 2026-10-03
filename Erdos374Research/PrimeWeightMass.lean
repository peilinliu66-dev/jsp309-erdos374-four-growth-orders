import Erdos374Research.QuadraticPeriodMass
import Erdos374Research.PrimeComparison

/-! UNCOMPILED. Reciprocal substitution and the logarithmic prime measure.
The lower bound is for the actual integral used by PrimeComparison. -/

namespace Erdos374Research

open Tao2026 MeasureTheory Set

theorem reciprocal_weight_log_integral_lower
    {n P : ℕ} {b : ℝ} {W : ℝ → ℝ}
    (hn : 0 < n) (hP : 2 ≤ P) (hPn : 2 * P ≤ n) (_hb : 0 ≤ b)
    (hW : Continuous W) (hW0 : ∀ u, 0 ≤ W u)
    (hmass : b * (n : ℝ) / (32 * P) ≤
      ∫ u in (n : ℝ) / (2 * P)..(n : ℝ) / P, W u) :
    b * (P : ℝ) / (32 * Real.log n) ≤
      ∫ v in (P : ℝ)..2 * P, W ((n : ℝ) / v) / Real.log v := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPR : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hPnR : 2 * (P : ℝ) ≤ n := by exact_mod_cast hPn
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hPP : (P : ℝ) ≤ 2 * P := by linarith
  let c := (P : ℝ) ^ 2 / ((n : ℝ) * Real.log n)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hrec : ContinuousOn (fun v : ℝ => (n : ℝ) / v) (uIcc (P : ℝ) (2 * P)) := by
    rw [uIcc_of_le hPP]
    intro v hv
    exact (continuousAt_const.div continuousAt_id
      (by change v ≠ 0; exact (hPR.trans_le hv.1).ne')).continuousWithinAt
  have hcomp := hW.comp_continuousOn hrec
  have hlog : ContinuousOn Real.log (uIcc (P : ℝ) (2 * P)) := by
    rw [uIcc_of_le hPP]
    intro v hv
    exact (Real.continuousAt_log (by linarith [hv.1])).continuousWithinAt
  have hlogne : ∀ v ∈ uIcc (P : ℝ) (2 * P), Real.log v ≠ 0 := by
    rw [uIcc_of_le hPP]
    intro v hv
    exact (Real.log_pos (by linarith [hv.1])).ne'
  have hjac : ContinuousOn (fun v : ℝ => (n : ℝ) / v ^ 2)
      (uIcc (P : ℝ) (2 * P)) := by
    rw [uIcc_of_le hPP]
    intro v hv
    exact (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (by change v ≠ 0; exact (hPR.trans_le hv.1).ne'))).continuousWithinAt
  have hpoint : ∀ v ∈ Icc (P : ℝ) (2 * P),
      c * (((n : ℝ) / v ^ 2) * W ((n : ℝ) / v)) ≤ W ((n : ℝ) / v) / Real.log v := by
    intro v hv
    have hv0 : 0 < v := hPR.trans_le hv.1
    have hlv : 0 < Real.log v := Real.log_pos (by linarith [hv.1])
    have hln : Real.log v ≤ Real.log (n : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hv0 hnR (hv.2.trans hPnR)
    have hsq : (P : ℝ) ^ 2 ≤ v ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hv.1) (add_nonneg hv0.le hPR.le)]
    have hfac : c * ((n : ℝ) / v ^ 2) ≤ 1 / Real.log v := by
      have hprod : (P : ℝ) ^ 2 * Real.log v ≤ v ^ 2 * Real.log n :=
        mul_le_mul hsq hln hlv.le (sq_nonneg v)
      rw [show c * ((n : ℝ) / v ^ 2) = (P : ℝ) ^ 2 / (v ^ 2 * Real.log n) by
        dsimp only [c]; field_simp [hnR.ne', hlogn.ne', hv0.ne']]
      apply (div_le_div_iff₀ (by positivity : 0 < v ^ 2 * Real.log n) hlv).mpr
      simpa only [one_mul] using hprod
    have hmul := mul_le_mul_of_nonneg_right hfac (hW0 ((n : ℝ) / v))
    convert hmul using 1 <;> ring
  have hi := intervalIntegral.integral_mono_on (μ := volume) hPP
    ((continuousOn_const.mul (hjac.mul hcomp)).intervalIntegrable)
    ((hcomp.div hlog hlogne).intervalIntegrable) hpoint
  change (∫ v in (P : ℝ)..2 * P, c * (((n : ℝ) / v ^ 2) * W ((n : ℝ) / v))) ≤
    (∫ v in (P : ℝ)..2 * P, W ((n : ℝ) / v) / Real.log v) at hi
  rw [intervalIntegral.integral_const_mul] at hi
  rw [intervalIntegral_reciprocal_weighted_eq hnR hPR] at hmass
  have hmul := mul_le_mul_of_nonneg_left hmass hc
  have hid : c * (b * (n : ℝ) / (32 * P)) = b * (P : ℝ) / (32 * Real.log n) := by
    dsimp only [c]
    field_simp [hnR.ne', hPR.ne', hlogn.ne']
  rw [hid] at hmul
  exact hmul.trans hi

theorem prime_integral_norm_lower_of_real_reciprocal_mass
    {n P : ℕ} {M b : ℝ} {V : ℝ × ℝ → ℂ} {W : ℝ → ℝ}
    (hn : 0 < n) (hP : 2 ≤ P) (hPn : 2 * P ≤ n) (hb : 0 ≤ b)
    (hW : Continuous W) (hW0 : ∀ u, 0 ≤ W u)
    (heval : ∀ v : ℝ, V ((n : ℝ) / v, M / v ^ 2) = (W ((n : ℝ) / v) : ℂ))
    (hmass : b * (n : ℝ) / (32 * P) ≤
      ∫ u in (n : ℝ) / (2 * P)..(n : ℝ) / P, W u) :
    b * (P : ℝ) / (32 * Real.log n) ≤
      ‖primeEquidistributionIntegral (Ico (P : ℝ) (2 * P)) V n M 2‖ := by
  have hPP : (P : ℝ) ≤ 2 * P := by linarith [Nat.cast_nonneg (α := ℝ) P]
  have heq : primeEquidistributionIntegral (Ico (P : ℝ) (2 * P)) V n M 2 =
      ((∫ v in (P : ℝ)..2 * P, W ((n : ℝ) / v) / Real.log v : ℝ) : ℂ) := by
    unfold primeEquidistributionIntegral
    simp_rw [heval, ← Complex.ofReal_div]
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hPP,
      intervalIntegral.integral_ofReal]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact (reciprocal_weight_log_integral_lower hn hP hPn hb hW hW0 hmass).trans
    (le_abs_self _)

end Erdos374Research
