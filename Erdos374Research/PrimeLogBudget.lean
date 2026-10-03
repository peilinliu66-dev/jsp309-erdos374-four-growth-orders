import Erdos374Research.PairedFourier

/-! UNCOMPILED. Elementary scalar budget for the paired Fourier adapter. -/

namespace Erdos374Research

open Tao2026
open scoped BigOperators

noncomputable section

def primeComparisonConstant (K : ℕ) (ε A B : ℝ) : ℝ :=
  4 * (27 * fourierTailConstant * A + 27 * fourierTailConstant * B +
    (27 * fourierTailConstant) ^ 2 * A * B) +
    (27 * fourierMassConstant) ^ 2 * A * B / ε ^ (K + 14)

lemma primeComparisonConstant_nonneg (K : ℕ) {ε A B : ℝ}
    (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ primeComparisonConstant K ε A B := by
  have ht : 0 ≤ fourierTailConstant := tsum_nonneg fourierDecayWeightFiveHalves_nonneg
  unfold primeComparisonConstant
  positivity

lemma primeComparison_scalar_budget
    (K : ℕ)
    {ε A B x y L Z P : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hL : 1 ≤ L) (hZ : 1 ≤ Z) (hP : 1 ≤ P)
    (hscale : ε * L ≤ Z) (hxA : x ≤ A * L ^ K) (hyB : y ≤ B) :
    let dH := 27 * x * (L ^ (-((K + 14 : ℕ) : ℝ)) * fourierTailConstant)
    let dG := 27 * y * (L ^ (-((K + 14 : ℕ) : ℝ)) * fourierTailConstant)
    let δ := dH + dG + dH * dG
    (2 * P + 1) * δ +
        (27 * x * fourierMassConstant) * (27 * y * fourierMassConstant) *
          (P / Z ^ (K + 14)) + (δ / Z) * P ≤
      primeComparisonConstant K ε A B * (P / L ^ 14) := by
  have hLpos : 0 < L := by linarith
  have hZpos : 0 < Z := by linarith
  have hPpos : 0 < P := by linarith
  have ht : 0 ≤ fourierTailConstant := tsum_nonneg fourierDecayWeightFiveHalves_nonneg
  have hm : 0 ≤ fourierMassConstant := tsum_nonneg fourierDecayWeight_nonneg
  let X := 27 * fourierTailConstant * A
  let Y := 27 * fourierTailConstant * B
  let D := X + Y + X * Y
  let C := (27 * fourierMassConstant) ^ 2 * A * B / ε ^ (K + 14)
  let dx := 27 * x * (L ^ (-((K + 14 : ℕ) : ℝ)) * fourierTailConstant)
  let dy := 27 * y * (L ^ (-((K + 14 : ℕ) : ℝ)) * fourierTailConstant)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hdx0 : 0 ≤ dx := by dsimp [dx]; positivity
  have hdy0 : 0 ≤ dy := by dsimp [dy]; positivity
  have hdxEq : dx = 27 * x * fourierTailConstant / L ^ (K + 14) := by
    dsimp only [dx]
    rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
    ring
  have hdyEq : dy = 27 * y * fourierTailConstant / L ^ (K + 14) := by
    dsimp only [dy]
    rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
    ring
  have hdx : dx ≤ X / L ^ 14 := by
    rw [hdxEq]
    calc
      27 * x * fourierTailConstant / L ^ (K + 14) ≤
          27 * (A * L ^ K) * fourierTailConstant / L ^ (K + 14) := by gcongr
      _ = X / L ^ 14 := by
        dsimp only [X]
        rw [pow_add]
        field_simp [hLpos.ne', pow_ne_zero K hLpos.ne']
  have hdyRaw : dy ≤ Y / L ^ (K + 14) := by
    rw [hdyEq]
    calc
      27 * y * fourierTailConstant / L ^ (K + 14) ≤
          27 * B * fourierTailConstant / L ^ (K + 14) := by gcongr
      _ = Y / L ^ (K + 14) := by dsimp only [Y]; ring
  have hL1420 : L ^ 14 ≤ L ^ (K + 14) := by
    calc
      L ^ 14 = L ^ 14 * 1 := by ring
      _ ≤ L ^ 14 * L ^ K :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (n := K) hL) (by positivity)
      _ = L ^ (K + 14) := by rw [pow_add]; ring
  have hdy : dy ≤ Y / L ^ 14 := hdyRaw.trans
    (div_le_div_of_nonneg_left hY (pow_pos hLpos 14) hL1420)
  have hdyY : dy ≤ Y := hdyRaw.trans (by
    exact (div_le_self hY (one_le_pow₀ (n := K + 14) hL)))
  have hprod : dx * dy ≤ (X * Y) / L ^ 14 := by
    calc
      dx * dy ≤ (X / L ^ 14) * Y :=
        mul_le_mul hdx hdyY hdy0 (by positivity)
      _ = (X * Y) / L ^ 14 := by ring
  have hδ : dx + dy + dx * dy ≤ D / L ^ 14 := by
    dsimp only [D]
    have h := add_le_add (add_le_add hdx hdy) hprod
    simpa only [add_div] using h
  have hδ0 : 0 ≤ dx + dy + dx * dy := by positivity
  have hmass :
      (27 * x * fourierMassConstant) * (27 * y * fourierMassConstant) *
          (P / Z ^ (K + 14)) ≤ C * (P / L ^ 14) := by
    have hden : ε ^ (K + 14) * L ^ (K + 14) ≤ Z ^ (K + 14) := by
      simpa only [mul_pow] using
        pow_le_pow_left₀ (mul_nonneg hε.le hLpos.le) hscale (K + 14)
    calc
      (27 * x * fourierMassConstant) * (27 * y * fourierMassConstant) *
          (P / Z ^ (K + 14)) =
        ((27 * fourierMassConstant) ^ 2 * x * y * P) / Z ^ (K + 14) := by ring
      _ ≤ ((27 * fourierMassConstant) ^ 2 * (A * L ^ K) * B * P) / Z ^ (K + 14) := by
        gcongr
      _ ≤ ((27 * fourierMassConstant) ^ 2 * (A * L ^ K) * B * P) /
          (ε ^ (K + 14) * L ^ (K + 14)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = C * (P / L ^ 14) := by
        dsimp only [C]
        simp only [pow_add]
        field_simp [hε.ne', hLpos.ne', pow_ne_zero K hLpos.ne', pow_ne_zero K hε.ne']
  have hfront : (2 * P + 1) * (dx + dy + dx * dy) ≤
      3 * P * (dx + dy + dx * dy) :=
    mul_le_mul_of_nonneg_right (by linarith) hδ0
  have hback : ((dx + dy + dx * dy) / Z) * P ≤ (dx + dy + dx * dy) * P :=
    mul_le_mul_of_nonneg_right (div_le_self hδ0 hZ) hPpos.le
  change (2 * P + 1) * (dx + dy + dx * dy) +
      (27 * x * fourierMassConstant) * (27 * y * fourierMassConstant) *
        (P / Z ^ (K + 14)) + ((dx + dy + dx * dy) / Z) * P ≤ _
  calc
    _ ≤ 3 * P * (dx + dy + dx * dy) + C * (P / L ^ 14) +
        (dx + dy + dx * dy) * P := add_le_add (add_le_add hfront hmass) hback
    _ = 4 * P * (dx + dy + dx * dy) + C * (P / L ^ 14) := by ring
    _ ≤ 4 * P * (D / L ^ 14) + C * (P / L ^ 14) := by gcongr
    _ = primeComparisonConstant K ε A B * (P / L ^ 14) := by
      dsimp only [primeComparisonConstant, X, Y, D, C]
      ring

end
end Erdos374Research
