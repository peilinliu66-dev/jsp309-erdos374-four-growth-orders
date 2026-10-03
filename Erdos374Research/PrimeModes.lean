import Tao2026.Theorem25Complete
import Tao2026.SpecializedGrowingFourier

/-!
Uniform real reciprocal-phase comparison for the rational-parameter application
in Yudin, arXiv:2610.01899v1, Lemma 5.1.

UNCOMPILED. Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
External Tao2026 source: smccolm/Lean @
91604dfc9733555f0b762594cd434450728d3d8c.
The chamber partition below adapts S. McColm's MIT-0
SpecializedGrowingFourier proof to independent real parameters. Its analytic
inputs remain attributed to their original authors and public formalizers.
No new analytic estimate is assumed.
-/

namespace Erdos374Research

open Tao2026 Complex Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology

noncomputable section

theorem eventually_rationalMode_highLow
    {A₀ ε : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      (((0 < (q.1 : ℝ) * N ∧ (q.2 : ℝ) * M < 0) ∨
        ((q.1 : ℝ) * N < 0 ∧ 0 < (q.2 : ℝ) * M)) →
        quadraticReciprocalStationaryPoint
          ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) ≤ (P : ℝ) / 2) →
      |(q.1 : ℝ) * N| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      |(q.2 : ℝ) * M| ≤
        A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S +
          vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S : ℝ)) +
          20 * (P : ℝ) /
            ((Real.log b) ^
                vaughanTypeIILogSavingPhaseExponent ((S : ℝ) + 1) *
              Real.log P) := by
  have hPNT := classicalMangoldtDiscrepancyLogSaving_native
  have hVinogradov := vinogradovExponentialSumEstimate_unconditional
  let Sℝ : ℝ := S
  let d : ℝ := vaughanTypeIILogSavingPhaseExponent (Sℝ + 1)
  obtain ⟨D, hsplit⟩ :=
    exists_eventually_reciprocalPhaseScale_low_or_log_rpow_high d
  obtain ⟨C, hC, hlow⟩ :=
    hPNT.eventually_primeFourierMode_sub_integral_Ico_le_logSaving D S
  have hsame :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_sameSign_sourceScale
      hVinogradov hA₀ hε haexp (Nat.cast_nonneg S)
  have hstationary :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_stationary_left
      hVinogradov hA₀ hε haexp (Nat.cast_nonneg S)
  have hzeroLinear :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_zero_linear
      hVinogradov hA₀ hε haexp (Nat.cast_nonneg S)
  have hzeroQuadratic :=
    eventually_norm_primeFourierMode_sub_integral_Ico_le_sourceRange_of_zero_quadratic
      hVinogradov hA₀ hε haexp (Nat.cast_nonneg S)
  have hlogTwo : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hsplit, hlow, hsame, hstationary, hzeroLinear,
    hzeroQuadratic, hlogTwo] with
      P hsplitP hlowP hsameP hstationaryP hzeroLinearP hzeroQuadraticP
      hlogP
  intro a b q N M hPa hab hbP hqGeometry hNupper hMupper
  have hP2 : 2 ≤ P := by
    have hlogPpos : 0 < Real.log (P : ℝ) := by linarith
    have hPone : (1 : ℝ) < P := (Real.log_pos_iff (by positivity)).mp hlogPpos
    have hPoneNat : 1 < P := by exact_mod_cast hPone
    omega
  have hPpos : 0 < (P : ℝ) := by positivity
  have hPb : P ≤ b := hPa.trans hab.le
  have hlogPpos : 0 < Real.log (P : ℝ) := by linarith
  have hlogbpos : 0 < Real.log (b : ℝ) := by
    exact hlogPpos.trans_le
      (Real.log_le_log hPpos (by exact_mod_cast hPb))
  let H : ℝ := (Real.log b) ^ d
  have hHpos : 0 < H := by
    dsimp only [H]
    exact Real.rpow_pos_of_pos hlogbpos d
  have hlogbTwo : 2 ≤ Real.log (b : ℝ) :=
    hlogP.trans (Real.log_le_log hPpos (by exact_mod_cast hPb))
  have hdTwo : (2 : ℝ) ≤ d := by
    dsimp only [d, Sℝ, vaughanTypeIILogSavingPhaseExponent]
    have hScast : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
    nlinarith
  have hHfour : 4 ≤ H := by
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ Real.log (b : ℝ)) hdTwo
    rw [Real.rpow_two] at hpow
    dsimp only [H]
    nlinarith [sq_nonneg (Real.log (b : ℝ) - 2)]
  have hlowTerm : 0 ≤ (P : ℝ) / (Real.log P) ^ S := by positivity
  have hprimeTerm : 0 ≤
      vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
        (Real.log P) ^ (-(S : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg vaughanPrimeQuadraticDecayConstant_pos.le (by positivity))
      (Real.rpow_nonneg hlogPpos.le _)
  have hintegralTerm : 0 ≤ (P : ℝ) / (H * Real.log P) := by positivity
  rcases hsplitP b ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) hPb hbP with
      hlowScale | hhighScale
  · have hbound := hlowP a b q N M hPa hab hbP hlowScale
    have hmajorIntegral : 0 ≤
        20 * (P : ℝ) / (H * Real.log P) := by positivity
    dsimp only [Sℝ, d, H] at *
    linarith
  · have hlogLower : (Real.log b) ^
        vaughanTypeIILogSavingPhaseExponent ((S : ℝ) + 1) ≤ H := by
      rfl
    have hhighScale' : H ≤ reciprocalPhaseScale
        ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) 2 (4 * (P : ℝ)) := by
      simpa only [H, d, Sℝ] using hhighScale
    by_cases hA : (q.1 : ℝ) * N = 0
    · by_cases hB : (q.2 : ℝ) * M = 0
      · have hzero : H ≤ 0 := by
          simpa [hA, hB, reciprocalPhaseScale] using hhighScale'
        exact (not_lt_of_ge hzero hHpos).elim
      · have hbound := hzeroLinearP a b q N M H hPa hab hbP
          hA hB hHpos hlogLower hhighScale' hNupper hMupper
        have hcoeff : (P : ℝ) / (H * Real.log P) ≤
            20 * (P : ℝ) / (H * Real.log P) := by
          apply (div_le_div_iff_of_pos_right (mul_pos hHpos hlogPpos)).2
          nlinarith
        dsimp only [Sℝ, d, H] at *
        linarith
    · by_cases hB : (q.2 : ℝ) * M = 0
      · have hbound := hzeroQuadraticP a b q N M H hPa hab hbP
          hA hB hHpos hlogLower hhighScale' hNupper
        have hcoeff : 2 * (P : ℝ) / (H * Real.log P) ≤
            20 * (P : ℝ) / (H * Real.log P) := by
          apply (div_le_div_iff_of_pos_right (mul_pos hHpos hlogPpos)).2
          nlinarith
        dsimp only [Sℝ, d, H] at *
        linarith
      · by_cases hsign :
          (0 < (q.1 : ℝ) * N ∧ 0 < (q.2 : ℝ) * M) ∨
            ((q.1 : ℝ) * N < 0 ∧ (q.2 : ℝ) * M < 0)
        · have hbound := hsameP a b q N M H hPa hab hbP hsign hHpos
            hlogLower hhighScale' hNupper hMupper
          have hcoeff : 6 * (P : ℝ) / (H * Real.log P) ≤
              20 * (P : ℝ) / (H * Real.log P) := by
            apply (div_le_div_iff_of_pos_right (mul_pos hHpos hlogPpos)).2
            nlinarith
          dsimp only [Sℝ, d, H] at *
          linarith
        · have hopposite :
            (0 < (q.1 : ℝ) * N ∧ (q.2 : ℝ) * M < 0) ∨
              ((q.1 : ℝ) * N < 0 ∧ 0 < (q.2 : ℝ) * M) := by
            rcases lt_or_gt_of_ne hA with hAneg | hApos
            · rcases lt_or_gt_of_ne hB with hBneg | hBpos
              · exact (hsign (Or.inr ⟨hAneg, hBneg⟩)).elim
              · exact Or.inr ⟨hAneg, hBpos⟩
            · rcases lt_or_gt_of_ne hB with hBneg | hBpos
              · exact Or.inl ⟨hApos, hBneg⟩
              · exact (hsign (Or.inl ⟨hApos, hBpos⟩)).elim
          have hsNonneg : 0 ≤ quadraticReciprocalStationaryPoint
              ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) := by
            rcases hopposite with hopposite | hopposite
            · exact (quadraticReciprocalStationaryPoint_pos_of_pos_neg
                hopposite.1 hopposite.2).le
            · exact (quadraticReciprocalStationaryPoint_pos_of_neg_pos
                hopposite.1 hopposite.2).le
          have hsFar := hqGeometry hopposite
          have hbound := hstationaryP a b q N M H hPa hab hbP hA hB
            hHfour hsNonneg hsFar hlogLower hhighScale'
            hNupper hMupper
          dsimp only [Sℝ, d, H] at *
          nlinarith


/-- Uniform prime-minus-integral bound with independent real coefficients.
The only phase-geometry restriction is that an opposite-sign stationary point
lies to the left of half the dyadic scale. All analytic inputs are discharged. -/
theorem eventually_primeMode_comparison
    {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (q : ℤ × ℤ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P →
      (((0 < (q.1 : ℝ) * N ∧ (q.2 : ℝ) * M < 0) ∨
        ((q.1 : ℝ) * N < 0 ∧ 0 < (q.2 : ℝ) * M)) →
        quadraticReciprocalStationaryPoint
          ((q.1 : ℝ) * N) ((q.2 : ℝ) * M) ≤ (P : ℝ) / 2) →
      |(q.1 : ℝ) * N| ≤ K * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      |(q.2 : ℝ) * M| ≤ K * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeFourierModeSum (P : ℝ)
          (Set.Ico (a : ℝ) (b : ℝ)) q N M 2 -
        fourierModeIntegral (Set.Ico (a : ℝ) (b : ℝ)) q N M 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S := by
  have hmajor :=
    eventually_rationalMode_highLow hK hε haexp (S + 2)
  have hlogLarge : ∀ᶠ P : ℕ in atTop, 60 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 60)
  have hlogSqTop : Tendsto (fun P : ℕ => (Real.log P) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hconstant : ∀ᶠ P : ℕ in atTop,
      3 * vaughanPrimeQuadraticDecayConstant ≤ (Real.log P) ^ 2 :=
    hlogSqTop.eventually
      (eventually_ge_atTop (3 * vaughanPrimeQuadraticDecayConstant))
  filter_upwards [hmajor, hlogLarge, hconstant,
    eventually_ge_atTop (1 : ℕ)] with P hmajorP hlogP hconstantP hP
  intro a b q N M hPa hab hbP hgeom hN hM
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast hP
  have hPb : P ≤ b := hPa.trans hab.le
  have hlogPpos : 0 < Real.log (P : ℝ) := by linarith
  have hlogPb : Real.log (P : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log hPpos (by exact_mod_cast hPb)
  have hlogbpos : 0 < Real.log (b : ℝ) := hlogPpos.trans_le hlogPb
  let d : ℝ :=
    vaughanTypeIILogSavingPhaseExponent (((S + 2 : ℕ) : ℝ) + 1)
  have hSd : (S : ℝ) ≤ d := by
    dsimp only [d, vaughanTypeIILogSavingPhaseExponent]
    have hScast : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
    norm_num
    linarith
  have hpower : (Real.log P) ^ S ≤ (Real.log b) ^ d := by
    calc
      (Real.log P) ^ S ≤ (Real.log b) ^ S :=
        pow_le_pow_left₀ hlogPpos.le hlogPb S
      _ = (Real.log b) ^ (S : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (Real.log b) ^ d :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hSd
  have hsource : 60 * (Real.log P) ^ S ≤
      (Real.log b) ^ d * Real.log P := by
    calc
      60 * (Real.log P) ^ S ≤
          Real.log P * (Real.log P) ^ S :=
        mul_le_mul_of_nonneg_right hlogP (pow_nonneg hlogPpos.le S)
      _ ≤ Real.log P * (Real.log b) ^ d :=
        mul_le_mul_of_nonneg_left hpower hlogPpos.le
      _ = (Real.log b) ^ d * Real.log P := by ring
  have hbound := hmajorP a b q N M hPa hab hbP hgeom hN hM
  exact hbound.trans (specializedFourierHighLowMajorant_le_logSaving
    vaughanPrimeQuadraticDecayConstant (P : ℝ) (Real.log P)
      ((Real.log b) ^ d) S (Nat.cast_nonneg P) hlogPpos
      (Real.rpow_pos_of_pos hlogbpos d)
      (by nlinarith [sq_nonneg (Real.log P - 60)])
      hconstantP hsource)


end
end Erdos374Research
