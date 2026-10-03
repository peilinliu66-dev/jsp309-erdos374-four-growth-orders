import Erdos374Research.TranslatedPlateau
import Erdos374Research.IntegerAvoidingWeight

/-! UNCOMPILED. A matching support-length upper bound for the existing
normalized periodic plateau. Together with its actual mass lower bound,
this controls the subtraction in the lower-block-dominant construction. -/

namespace Erdos374Research

open Tao2026 MeasureTheory Set
open scoped Topology

theorem normalizedPlateau_unit_mass_upper {N : ℕ}
    (hN : 1 < Real.log (N : ℝ)) :
    (∫ x in (0 : ℝ)..1, factorialNormalizedPlateauWeight N x) ≤ plateauWidth N := by
  let d := plateauWidth N
  let b := 1 - d
  have hd : 0 < d := plateauWidth_pos hN
  have hd1 : d < 1 := (plateauWidth_lt_tenth hN).trans (by norm_num)
  have hb0 : 0 ≤ b := by dsimp only [b]; linarith
  have hb1 : b ≤ 1 := by dsimp only [b]; linarith
  have hcont := (factorialNormalizedPlateauWeight_contDiff N).continuous
  have hzero : (∫ x in (0 : ℝ)..b, factorialNormalizedPlateauWeight N x) = 0 := by
    rw [intervalIntegral.integral_of_le hb0, integral_Ioc_eq_integral_Ioo]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    by_contra hne
    have hs := factorialNormalizedPlateauWeight_supported hN hne
    have hfract : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1.le, hx.2.trans_le hb1⟩
    rw [hfract] at hs
    change 1 - d ≤ x at hs
    dsimp only [b] at hx
    exact (not_lt_of_ge hs) hx.2
  have htail : (∫ x in b..1, factorialNormalizedPlateauWeight N x) ≤ 1 - b := by
    calc
      (∫ x in b..1, factorialNormalizedPlateauWeight N x) ≤
          ∫ _x in b..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hb1 (hcont.intervalIntegrable b 1)
          intervalIntegrable_const (fun x _ => Real.smoothTransition.le_one _)
      _ = 1 - b := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 b) (hcont.intervalIntegrable b 1), hzero, zero_add]
  simpa only [b, sub_sub_cancel] using htail

theorem shiftedPlateau_period_mass_upper {N : ℕ}
    (hN : 1 < Real.log (N : ℝ)) (c a : ℝ) :
    (∫ x in a..a + 1, shiftedPlateau N c x) ≤ plateauWidth N := by
  rw [(shiftedPlateau_periodic N c).intervalIntegral_add_eq a c]
  unfold shiftedPlateau
  rw [intervalIntegral.integral_comp_sub_right]
  convert normalizedPlateau_unit_mass_upper hN using 1
  congr 1 <;> ring

theorem integerAvoidingWeight_period_defect {N : ℕ}
    (hN : 1 < Real.log (N : ℝ)) (a : ℝ) :
    (∫ x in a..a + 1, (1 - integerAvoidingWeight N x)) ≤ plateauWidth N := by
  simpa only [integerAvoidingWeight, sub_sub_cancel] using
    shiftedPlateau_period_mass_upper hN (5 * plateauWidth N / 12) a

end Erdos374Research
