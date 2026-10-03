import Erdos374Research.RationalPhaseGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! UNCOMPILED. Uniform numerical parameter bounds for the rational Fourier
adapter. No analytic-number-theory input is assumed here. -/

namespace Erdos374Research

open Tao2026 Filter Asymptotics Real
open scoped Topology

noncomputable section

lemma eventually_logPow_le_small_rpow (B : ℕ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ B ≤ c * (n : ℝ) ^ d := by
  have h := (isLittleO_log_rpow_rpow_atTop (B : ℝ) hd).comp_tendsto
    tendsto_natCast_atTop_atTop
  filter_upwards [h.bound hc, eventually_ge_atTop (1 : ℕ)] with n hb hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  simpa only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog B),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) d)] using hb

lemma logarithmicRadius_le_twice_logPow {n : ℕ} (hlog : 1 ≤ Real.log (n : ℝ))
    (B : ℕ) :
    (specializedFourierRadius B n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ B := by
  have hceil := specializedFourierRadius_lt_log_pow_add_one
    (B := B) (P := n) (by linarith : 0 ≤ Real.log (n : ℝ))
  have hone := one_le_pow₀ (n := B) hlog
  linarith

/-- Polynomial n-sized phase coefficients fit uniformly in the fixed
stretched-exponential range whenever P≥n^epsilon. -/
lemma eventually_square_le_stretchedExp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ P : ℕ, (n : ℝ) ^ ε ≤ P →
      (n : ℝ) ^ 2 ≤ Real.exp ((Real.log P) ^ (5 / 4 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => ε * Real.log (n : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hε).mpr
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hquarter : ∀ᶠ n : ℕ in atTop,
      2 / ε ≤ (ε * Real.log (n : ℝ)) ^ (1 / 4 : ℝ) :=
    ((_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp ht).eventually
      (eventually_ge_atTop (2 / ε))
  filter_upwards [hquarter, eventually_ge_atTop (2 : ℕ)] with n hquarterN hn
  intro P hP
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hx : 0 < ε * Real.log (n : ℝ) := mul_pos hε hlogn
  have hlogP : ε * Real.log (n : ℝ) ≤ Real.log (P : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hnpos ε) hP
    simpa only [Real.log_rpow hnpos] using h
  have hpower : 2 * Real.log (n : ℝ) ≤
      (ε * Real.log (n : ℝ)) ^ (5 / 4 : ℝ) := by
    calc
      2 * Real.log (n : ℝ) = (ε * Real.log (n : ℝ)) * (2 / ε) := by
        field_simp [hε.ne']
      _ ≤ (ε * Real.log (n : ℝ)) *
          (ε * Real.log (n : ℝ)) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hquarterN hx.le
      _ = (ε * Real.log (n : ℝ)) ^ (5 / 4 : ℝ) := by
        rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num,
          Real.rpow_add hx, Real.rpow_one]
  calc
    (n : ℝ) ^ 2 = Real.exp (2 * Real.log (n : ℝ)) := by
      rw [show 2 * Real.log (n : ℝ) = Real.log (n : ℝ) + Real.log (n : ℝ) by ring,
        Real.exp_add, Real.exp_log hnpos]
      ring
    _ ≤ Real.exp ((ε * Real.log (n : ℝ)) ^ (5 / 4 : ℝ)) :=
      Real.exp_le_exp.mpr hpower
    _ ≤ Real.exp ((Real.log P) ^ (5 / 4 : ℝ)) :=
      Real.exp_le_exp.mpr (Real.rpow_le_rpow hx.le hlogP (by norm_num))

theorem eventually_rationalParameterRanges {α ε : ℝ}
    (hαε : α < ε) (hε : 0 < ε) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ ∀ (a P : ℕ),
      (a : ℝ) ≤ (n : ℝ) ^ α → (n : ℝ) ^ ε ≤ P →
      4 * (a : ℝ) * specializedFourierRadius B n ≤ P ∧
      2 * (specializedFourierRadius B n : ℝ) * n ≤
        Real.exp ((Real.log P) ^ (5 / 4 : ℝ)) ∧
      ε * Real.log (n : ℝ) ≤ Real.log (P : ℝ) := by
  have hgap := eventually_logPow_le_small_rpow B
    (d := ε - α) (c := 1 / 8) (by linarith) (by norm_num)
  have hlinear := eventually_logPow_le_small_rpow B
    (d := 1) (c := 1 / 4) (by norm_num) (by norm_num)
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hgap, hlinear, hlog, eventually_square_le_stretchedExp hε,
    eventually_ge_atTop (2 : ℕ)] with n hgapN hlinearN hlogN hexpN hn
  refine ⟨hn, ?_⟩
  intro a P ha hP
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hradius := logarithmicRadius_le_twice_logPow hlogN B
  have hgap8 : 8 * (Real.log (n : ℝ)) ^ B ≤ (n : ℝ) ^ (ε - α) := by
    nlinarith
  have hcoeff : 2 * (specializedFourierRadius B n : ℝ) ≤ n := by
    rw [Real.rpow_one] at hlinearN
    linarith
  have hgeom : 4 * (a : ℝ) * specializedFourierRadius B n ≤ (n : ℝ) ^ ε := by
    calc
      4 * (a : ℝ) * specializedFourierRadius B n ≤
          (n : ℝ) ^ α * (8 * (Real.log (n : ℝ)) ^ B) := by
        calc
          _ ≤ 4 * ((n : ℝ) ^ α) * (2 * (Real.log (n : ℝ)) ^ B) := by gcongr
          _ = _ := by ring
      _ ≤ (n : ℝ) ^ α * (n : ℝ) ^ (ε - α) :=
        mul_le_mul_of_nonneg_left hgap8 (Real.rpow_nonneg hnpos.le α)
      _ = (n : ℝ) ^ ε := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
  refine ⟨hgeom.trans hP, ?_, ?_⟩
  · exact (show 2 * (specializedFourierRadius B n : ℝ) * n ≤ (n : ℝ) ^ 2 by
      nlinarith [mul_le_mul_of_nonneg_right hcoeff hnpos.le]).trans (hexpN P hP)
  · have h := Real.log_le_log (Real.rpow_pos_of_pos hnpos ε) hP
    simpa only [Real.log_rpow hnpos] using h

end
end Erdos374Research
