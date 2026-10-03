import Erdos374Research.HardFactorialFibres

/-! UNCOMPILED. Uniform fixed-exponent Gallagher estimate for the large-index
three-factorial fibres. The deliberately small saving suffices for D3. -/

namespace Erdos374Research

open Tao2026 Filter
open scoped BigOperators Topology

noncomputable section

def d3Eta : ℝ := 1 / 100000
def d3PrimeLowerExponent : ℝ := 1 / 10000
def d3PrimeUpperExponent : ℝ := 999 / 2000
def d3HardExponent : ℝ := 1249 / 2500

def rpowCeil (X : ℕ) (b : ℝ) : ℕ := ⌈(X : ℝ) ^ b⌉₊

lemma rpowCeil_lower (X : ℕ) (b : ℝ) : (X : ℝ) ^ b ≤ (rpowCeil X b : ℝ) := Nat.le_ceil _

lemma rpowCeil_upper {X : ℕ} (hX : 1 ≤ X) {b : ℝ} (hb : 0 ≤ b) :
    (rpowCeil X b : ℝ) ≤ 2 * (X : ℝ) ^ b := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hone : 1 ≤ (X : ℝ) ^ b := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hXR hb
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg X) b)
  change (rpowCeil X b : ℝ) < (X : ℝ) ^ b + 1 at hceil
  linarith

lemma rpowCeil_mono_exponent {X : ℕ} (hX : 1 ≤ X) {a b : ℝ} (hab : a ≤ b) :
    rpowCeil X a ≤ rpowCeil X b := by
  apply Nat.ceil_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) hab

def d3SieveCoefficient : ℝ :=
  1 / 400 + (10000 / 5001 : ℝ) *
    ((1 - 1 / 100000) * d3PrimeUpperExponent - 2 * d3PrimeLowerExponent) - 1

lemma d3SieveCoefficient_lower : (1 / 1250 : ℝ) ≤ d3SieveCoefficient := by
  norm_num [d3SieveCoefficient, d3PrimeUpperExponent, d3PrimeLowerExponent]

lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith

/-- The large-index threshold supplies a positive Gallagher denominator
uniformly over every a,H in a fixed tiny-power box. -/
theorem eventually_hardFactorial_denominator :
    ∀ᶠ X : ℕ in atTop, ∀ a H : ℕ,
      1 ≤ a → 1 ≤ H → (a : ℝ) ≤ (X : ℝ) ^ d3Eta →
      (H : ℝ) ≤ (X : ℝ) ^ d3Eta →
      (H : ℝ) * Real.log ((X : ℝ) + 2) / 100 < a →
      let Y := rpowCeil X d3PrimeLowerExponent
      let Q := rpowCeil X d3PrimeUpperExponent
      a ≤ Y ∧ 2 ≤ Y ∧ Y ≤ Q ∧ 10000 * (H : ℝ) ≤ Real.sqrt Y ∧
        Real.log (X : ℝ) / 2000 ≤ gallagherFactorialDenominator X a H Y Q := by
  obtain ⟨B, hB, hweights⟩ := exists_weightedPrimeLogSum_difference_lower
    (η := 1 / 100000) (by norm_num) (by norm_num)
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1 eventually_nat_factorialUpperHalfTheta_lower
  have hlogTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hindex : ∀ᶠ X : ℕ in atTop, 100 * (A₀ : ℝ) ≤ Real.log (X : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop _)
  have hconstant : ∀ᶠ X : ℕ in atTop,
      (10000 / 5001 : ℝ) * (B + 6) ≤ (3 / 10000 : ℝ) * Real.log (X : ℝ) :=
    ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 3 / 10000)).mpr
      hlogTop).eventually (eventually_ge_atTop _)
  have hsmall : ∀ᶠ X : ℕ in atTop,
      10000 ≤ (X : ℝ) ^ (d3PrimeLowerExponent / 2 - d3Eta) :=
    ((_root_.tendsto_rpow_atTop (by norm_num [d3PrimeLowerExponent, d3Eta])).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 10000)
  have hYtwo : ∀ᶠ X : ℕ in atTop, 2 ≤ (X : ℝ) ^ d3PrimeLowerExponent :=
    ((_root_.tendsto_rpow_atTop (by norm_num [d3PrimeLowerExponent])).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hindex, hconstant, hsmall, hYtwo,
    eventually_ge_atTop (2 : ℕ)] with X hindexX hconstantX hsmallX hYtwoX hX
  intro a H ha hH haX hHX hhard
  let Y := rpowCeil X d3PrimeLowerExponent
  let Q := rpowCeil X d3PrimeUpperExponent
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have haY : a ≤ Y := by
    have h := haX.trans ((Real.rpow_le_rpow_of_exponent_le hXR
      (by norm_num [d3Eta, d3PrimeLowerExponent])).trans
        (rpowCeil_lower X d3PrimeLowerExponent))
    exact_mod_cast h
  have hY : 2 ≤ Y := by exact_mod_cast hYtwoX.trans (rpowCeil_lower X d3PrimeLowerExponent)
  have hYQ : Y ≤ Q := rpowCeil_mono_exponent (by omega : 1 ≤ X)
    (by norm_num [d3PrimeLowerExponent, d3PrimeUpperExponent])
  have hHroot : 10000 * (H : ℝ) ≤ Real.sqrt Y := by
    calc
      10000 * (H : ℝ) ≤ 10000 * (X : ℝ) ^ d3Eta := by gcongr
      _ ≤ (X : ℝ) ^ (d3PrimeLowerExponent / 2 - d3Eta) * (X : ℝ) ^ d3Eta :=
        mul_le_mul_of_nonneg_right hsmallX (Real.rpow_nonneg hXpos.le _)
      _ = (X : ℝ) ^ (d3PrimeLowerExponent / 2) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
      _ = Real.sqrt ((X : ℝ) ^ d3PrimeLowerExponent) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]
        congr 1
        ring
      _ ≤ Real.sqrt Y := Real.sqrt_le_sqrt (rpowCeil_lower X d3PrimeLowerExponent)
  have hlogShift : Real.log (X : ℝ) ≤ Real.log ((X : ℝ) + 2) :=
    Real.log_le_log hXpos (by linarith)
  have hlogShift0 : 0 ≤ Real.log ((X : ℝ) + 2) := hlogX.le.trans hlogShift
  have hAindex : A₀ ≤ a := by
    have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hmul := mul_le_mul_of_nonneg_right hHone hlogShift0
    have h : (A₀ : ℝ) ≤ a := by nlinarith
    exact_mod_cast h
  have hhalf := hA₀ a hAindex
  have hfirst : Real.log (X : ℝ) / 400 ≤
      (∑ p ∈ factorialUpperHalfPrimes a, Real.log (p : ℝ)) / H := by
    apply (le_div_iff₀ hHpos).2
    rw [sum_log_factorialUpperHalfPrimes_eq_theta_sub]
    have hmul := mul_le_mul_of_nonneg_left hlogShift hHpos.le
    nlinarith
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlogY : Real.log (Y : ℝ) ≤ 1 + d3PrimeLowerExponent * Real.log (X : ℝ) := by
    have h := Real.log_le_log hYpos (rpowCeil_upper (by omega : 1 ≤ X)
      (b := d3PrimeLowerExponent) (by norm_num [d3PrimeLowerExponent]))
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hXpos _).ne',
      Real.log_rpow hXpos] at h
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp only [Y] at *
    linarith
  have hlogQ : d3PrimeUpperExponent * Real.log (X : ℝ) ≤ Real.log (Q : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hXpos d3PrimeUpperExponent)
      (rpowCeil_lower X d3PrimeUpperExponent)
    simpa only [Real.log_rpow hXpos] using h
  have hlogY0 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hw := hweights Q Y (by omega) (by omega)
  have hlog4Term := mul_le_mul_of_nonneg_right log_four_le_two (by linarith : 0 ≤ 2 + Real.log (Y : ℝ))
  have hlogQTerm := mul_le_mul_of_nonneg_left hlogQ (by norm_num : (0 : ℝ) ≤ 1 - 1 / 100000)
  have hsecond : ((1 - 1 / 100000 : ℝ) * d3PrimeUpperExponent - 2 * d3PrimeLowerExponent) *
      Real.log (X : ℝ) - (B + 6) ≤ weightedPrimeLogSum Q - weightedPrimeLogSum Y := by
    nlinarith
  have hsecondScaled := mul_le_mul_of_nonneg_left hsecond (by norm_num : (0 : ℝ) ≤ 10000 / 5001)
  have hden : d3SieveCoefficient * Real.log (X : ℝ) -
      (10000 / 5001 : ℝ) * (B + 6) ≤ gallagherFactorialDenominator X a H Y Q := by
    unfold gallagherFactorialDenominator d3SieveCoefficient
    nlinarith
  have hcoefficient := mul_le_mul_of_nonneg_right d3SieveCoefficient_lower hlogX.le
  refine ⟨haY, hY, hYQ, hHroot, ?_⟩
  nlinarith

theorem eventually_hardFactorialFibre_card :
    ∀ᶠ X : ℕ in atTop, ∀ a H : ℕ,
      1 ≤ a → 1 ≤ H → (a : ℝ) ≤ (X : ℝ) ^ d3Eta →
      (H : ℝ) ≤ (X : ℝ) ^ d3Eta →
      (H : ℝ) * Real.log ((X : ℝ) + 2) / 100 < a →
      ((hardFactorialFibre X a H).card : ℝ) ≤
        16000 * (X : ℝ) ^ d3PrimeUpperExponent := by
  have hlog : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_hardFactorial_denominator, hlog,
    eventually_ge_atTop (2 : ℕ)] with X hdenX hlogX hX
  intro a H ha hH haX hHX hhard
  have hdata := hdenX a H ha hH haX hHX hhard
  let Y := rpowCeil X d3PrimeLowerExponent
  let Q := rpowCeil X d3PrimeUpperExponent
  change a ≤ Y ∧ 2 ≤ Y ∧ Y ≤ Q ∧ 10000 * (H : ℝ) ≤ Real.sqrt Y ∧
    Real.log (X : ℝ) / 2000 ≤ gallagherFactorialDenominator X a H Y Q at hdata
  have hD : 0 < gallagherFactorialDenominator X a H Y Q := by linarith [hdata.2.2.2.2]
  have hcard := hardFactorialFibre_card_le (by omega : 1 ≤ X) ha hH hdata.1
    hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hD
  have hQ := rpowCeil_upper (by omega : 1 ≤ X) (b := d3PrimeUpperExponent)
    (by norm_num [d3PrimeUpperExponent])
  calc
    ((hardFactorialFibre X a H).card : ℝ) ≤
        4 * (Q : ℝ) / gallagherFactorialDenominator X a H Y Q := hcard
    _ ≤ 4 * (Q : ℝ) / (Real.log (X : ℝ) / 2000) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdata.2.2.2.2
    _ = 8000 * (Q : ℝ) / Real.log (X : ℝ) := by ring
    _ ≤ 8000 * (Q : ℝ) := div_le_self (by positivity) hlogX
    _ ≤ 16000 * (X : ℝ) ^ d3PrimeUpperExponent := by dsimp only [Q] at *; nlinarith

end
end Erdos374Research
