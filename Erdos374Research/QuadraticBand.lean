import Erdos374Research.IntegerAvoidingWeight
import Tao2026.VeryBadEquidistribution

/-!
# A quadratic good-phase band on the rational reciprocal scale

UNCOMPILED. The nontrivial periodic quadratic-slice estimate is the actual
upstream `veryBadQuadraticReciprocalScale_measure_lower_source`. A linear
change of variable transfers it from M/p to n/p, with no new analytic
estimate and no assumption that the two coefficients are equal.
-/

namespace Erdos374Research

open Tao2026 MeasureTheory Set

noncomputable def rationalQuadraticBand (n M P : ℕ) : Set ℝ :=
  (fun u : ℝ => (M : ℝ) / n * u) ⁻¹' veryBadQuadraticReciprocalScaleSet M P

theorem measurableSet_rationalQuadraticBand (n M P : ℕ) :
    MeasurableSet (rationalQuadraticBand n M P) :=
  (measurableSet_veryBadQuadraticReciprocalScaleSet M P).preimage
    (measurable_const.mul measurable_id)

theorem mem_rationalQuadraticBand {n M P : ℕ}
    (hn : 0 < n) (hM : 0 < M) (hP : 0 < P) {u : ℝ} :
    u ∈ rationalQuadraticBand n M P ↔
      u ∈ Ioo ((n : ℝ) / (2 * P)) ((n : ℝ) / P) ∧
      (2 / 100 : ℝ) ≤ Int.fract ((M : ℝ) * u ^ 2 / (n : ℝ) ^ 2) ∧
      Int.fract ((M : ℝ) * u ^ 2 / (n : ℝ) ^ 2) ≤ 88 / 100 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have ha : (0 : ℝ) < (M : ℝ) / n := div_pos hMR hnR
  have hleft : (M : ℝ) / n * ((n : ℝ) / (2 * P)) = (M : ℝ) / (2 * P) := by
    field_simp
  have hright : (M : ℝ) / n * ((n : ℝ) / P) = (M : ℝ) / P := by
    field_simp
  have hphase : ((M : ℝ) / n * u) ^ 2 / M = (M : ℝ) * u ^ 2 / (n : ℝ) ^ 2 := by
    field_simp
  change (((M : ℝ) / (2 * P) < (M : ℝ) / n * u ∧
      (M : ℝ) / n * u < (M : ℝ) / P) ∧
      (2 / 100 : ℝ) ≤ Int.fract (((M : ℝ) / n * u) ^ 2 / M) ∧
      Int.fract (((M : ℝ) / n * u) ^ 2 / M) ≤ 88 / 100) ↔ _
  rw [hphase, ← hleft, ← hright]
  simp only [mul_lt_mul_iff_right₀ ha, Set.mem_Ioo]

theorem rationalQuadraticBand_measure_lower {n M P : ℕ}
    (hn : 0 < n) (hM : 0 < M) (hP : 0 < P)
    (hscale : (1 / 2 : ℝ) ≤ (M : ℝ) / (P : ℝ) ^ 2) :
    (n : ℝ) / (16 * P) ≤ volume.real (rationalQuadraticBand n M P) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have ha : (0 : ℝ) < (M : ℝ) / n := div_pos hMR hnR
  have hvolume : volume.real (rationalQuadraticBand n M P) =
      ((n : ℝ) / M) * volume.real (veryBadQuadraticReciprocalScaleSet M P) := by
    change (volume ((fun u : ℝ => (M : ℝ) / n * u) ⁻¹'
      veryBadQuadraticReciprocalScaleSet M P)).toReal = _
    rw [Real.volume_preimage_mul_left ha.ne', ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), inv_div, abs_of_pos (div_pos hnR hMR)]
    rfl
  rw [hvolume]
  have hbase := veryBadQuadraticReciprocalScale_measure_lower_source hM hP hscale
  calc
    (n : ℝ) / (16 * P) = ((n : ℝ) / M) * ((M : ℝ) / (16 * P)) := by field_simp
    _ ≤ ((n : ℝ) / M) * volume.real (veryBadQuadraticReciprocalScaleSet M P) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)

/-- On one denominator period, the quadratic phase varies by at most
2A/P. This is the uniform slow-variation estimate behind the good periods. -/
theorem quadratic_phase_variation {n M P : ℕ} {u v A : ℝ}
    (hn : 0 < n) (hP : 0 < P) (hMn : M ≤ n)
    (hu : u ∈ Icc ((n : ℝ) / (2 * P)) ((n : ℝ) / P))
    (hv : v ∈ Icc ((n : ℝ) / (2 * P)) ((n : ℝ) / P))
    (hA : |u - v| ≤ A) :
    |(M : ℝ) * u ^ 2 / (n : ℝ) ^ 2 - (M : ℝ) * v ^ 2 / (n : ℝ) ^ 2| ≤
      2 * A / P := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hMR : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hu0 : 0 ≤ u := (by positivity : (0 : ℝ) ≤ (n : ℝ) / (2 * P)).trans hu.1
  have hv0 : 0 ≤ v := (by positivity : (0 : ℝ) ≤ (n : ℝ) / (2 * P)).trans hv.1
  have hsum : |u + v| ≤ 2 * (n : ℝ) / P := by
    rw [abs_of_nonneg (add_nonneg hu0 hv0)]
    calc
      u + v ≤ (n : ℝ) / P + (n : ℝ) / P := add_le_add hu.2 hv.2
      _ = 2 * (n : ℝ) / P := by ring
  have hid : (M : ℝ) * u ^ 2 / (n : ℝ) ^ 2 - (M : ℝ) * v ^ 2 / (n : ℝ) ^ 2 =
      ((M : ℝ) / (n : ℝ) ^ 2) * (u - v) * (u + v) := by ring
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hcoef0 : 0 ≤ (M : ℝ) / (n : ℝ) ^ 2 := by positivity
  have hcoef : (M : ℝ) / (n : ℝ) ^ 2 ≤ (n : ℝ) / (n : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hMnR (by positivity)
  rw [hid, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ) / (n : ℝ) ^ 2)]
  calc
    ((M : ℝ) / (n : ℝ) ^ 2) * |u - v| * |u + v| ≤
        ((M : ℝ) / (n : ℝ) ^ 2) * A * (2 * (n : ℝ) / P) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA hcoef0) hsum
        (abs_nonneg _) (mul_nonneg hcoef0 hA0)
    _ ≤ ((n : ℝ) / (n : ℝ) ^ 2) * A * (2 * (n : ℝ) / P) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hA0) (by positivity)
    _ = 2 * A / P := by field_simp [hnR.ne', hPR.ne']

end Erdos374Research
