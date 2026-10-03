import Erdos374Research.ShortBlockCounting
import Erdos374Research.PrimeParameterRanges
import Erdos374Research.HardFibreAsymptotics

/-! UNCOMPILED. The five-parameter short-block union is sublinear. -/

namespace Erdos374Research

open Finset Filter Tao2026
open scoped BigOperators Topology

noncomputable section

def shortBlockCutoff (ε : ℝ) (X : ℕ) : ℕ := ⌈(X : ℝ) ^ (2 * ε)⌉₊

lemma half_rpow_le_nat_sqrt {X : ℕ} (hX : 4 ≤ X) :
    (X : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ (Nat.sqrt X : ℝ) := by
  have hroot := Real.real_sqrt_lt_nat_sqrt_succ (a := X)
  have hK : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hKR : (1 : ℝ) ≤ Nat.sqrt X := by exact_mod_cast hK
  rw [← Real.sqrt_eq_rpow]
  linarith

theorem eventually_shortBlock_sieve_parameters {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 100000) :
    ∀ᶠ X : ℕ in atTop,
      2 ≤ shortBlockCutoff ε X ∧ 128 * (shortBlockCutoff ε X) ^ 2 ≤ Nat.sqrt X ∧
        (Nat.sqrt X : ℝ) / 4 ≤
          Chebyshev.theta (Nat.sqrt X) - Chebyshev.theta ((Nat.sqrt X / 2 : ℕ) : ℝ) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp eventually_nat_factorialUpperHalfTheta_lower
  have hgap := (_root_.tendsto_rpow_atTop
    (show 0 < (1 / 2 : ℝ) - 4 * ε by linarith)).comp tendsto_natCast_atTop_atTop
  have hBlarge := (_root_.tendsto_rpow_atTop (show 0 < 2 * ε by positivity)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [hgap.eventually (eventually_ge_atTop 1024),
    hBlarge.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop (max 4 (M * M))] with X hgapX hBX hX
  have hX4 : 4 ≤ X := (le_max_left _ _).trans hX
  have hXM : M * M ≤ X := (le_max_right _ _).trans hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hBlo : 2 ≤ shortBlockCutoff ε X := by
    exact_mod_cast hBX.trans (Nat.le_ceil ((X : ℝ) ^ (2 * ε)))
  have hBhi : (shortBlockCutoff ε X : ℝ) ≤ 2 * (X : ℝ) ^ (2 * ε) :=
    rpowCeil_upper (by omega : 1 ≤ X) (by positivity : 0 ≤ 2 * ε)
  have hKlo := half_rpow_le_nat_sqrt hX4
  have hmul := mul_le_mul_of_nonneg_right hgapX
    (Real.rpow_nonneg hXpos.le (4 * ε))
  have hidentity : (X : ℝ) ^ (1 / 2 - 4 * ε) * (X : ℝ) ^ (4 * ε) =
      (X : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hXpos]
    congr 1
    ring
  change (1024 : ℝ) * (X : ℝ) ^ (4 * ε) ≤
    (X : ℝ) ^ (1 / 2 - 4 * ε) * (X : ℝ) ^ (4 * ε) at hmul
  rw [hidentity] at hmul
  have hsq : ((X : ℝ) ^ (2 * ε)) ^ 2 = (X : ℝ) ^ (4 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    congr 1
    ring
  have hBR : (0 : ℝ) ≤ (shortBlockCutoff ε X : ℝ) :=
    Nat.cast_nonneg (shortBlockCutoff ε X)
  have hKB : (128 : ℝ) * (shortBlockCutoff ε X : ℝ) ^ 2 ≤ Nat.sqrt X := by
    nlinarith [Real.rpow_nonneg hXpos.le (2 * ε)]
  exact ⟨hBlo, by exact_mod_cast hKB, hM (Nat.sqrt X) (Nat.le_sqrt.mpr hXM)⟩

theorem eventually_shortBlockExceptional_power_bound {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 100000) :
    ∀ᶠ X : ℕ in atTop,
      ((shortBlockExceptional X (shortBlockCutoff ε X)).card : ℝ) ≤
        93312 * (X : ℝ) ^ (3 / 4 : ℝ) := by
  have hparams := eventually_shortBlock_sieve_parameters hε hεsmall
  have hlog := eventually_logPow_le_small_rpow 1
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hparams, hlog, eventually_ge_atTop (4 : ℕ)] with X hparam hlogX hX
  let B := shortBlockCutoff ε X
  let K := Nat.sqrt X
  have hK : 1 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hKlo : (X : ℝ) ^ (1 / 2 : ℝ) / 2 ≤ K := half_rpow_le_nat_sqrt hX
  have hbound := shortBlockExceptional_card_finite_bound (by omega : 2 ≤ X) hK
    (Nat.sqrt_le_self X) ((Nat.sqrt_le X).trans (Nat.le_succ X))
    hparam.1 hparam.2.1 hparam.2.2
  have hBhi : (B : ℝ) + 1 ≤ 3 * (X : ℝ) ^ (2 * ε) := by
    have hb := rpowCeil_upper (by omega : 1 ≤ X) (by positivity : 0 ≤ 2 * ε)
    have hone : 1 ≤ (X : ℝ) ^ (2 * ε) := Real.one_le_rpow hXR (by positivity)
    change (B : ℝ) ≤ 2 * (X : ℝ) ^ (2 * ε) at hb
    linarith
  have hBpow : ((B : ℝ) + 1) ^ 5 ≤ 243 * (X : ℝ) ^ (10 * ε) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ B + 1) hBhi 5
    rw [mul_pow, ← Real.rpow_mul_natCast hXpos.le] at h
    norm_num at h
    convert h using 1
    congr 1
    ring
  have heps : (X : ℝ) ^ (10 * ε) ≤ (X : ℝ) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hXR (by linarith)
  have hlognon := Real.log_nonneg hXR
  have hfront : ((B : ℝ) + 1) ^ 5 * (96 * (X + 1) * Real.log X) ≤
      46656 * (X : ℝ) ^ (5 / 4 : ℝ) := by
    have hXplus : (X : ℝ) + 1 ≤ 2 * X := by linarith
    have hlogbound : Real.log X ≤ (X : ℝ) ^ (1 / 8 : ℝ) := by simpa using hlogX
    calc
      ((B : ℝ) + 1) ^ 5 * (96 * (X + 1) * Real.log X) ≤
          (243 * (X : ℝ) ^ (1 / 8 : ℝ)) *
            (96 * (2 * X) * (X : ℝ) ^ (1 / 8 : ℝ)) := by
        gcongr
        exact hBpow.trans (mul_le_mul_of_nonneg_left heps (by norm_num))
      _ = 46656 * (X : ℝ) ^ (5 / 4 : ℝ) := by
        have hp : (X : ℝ) ^ (1 / 8 : ℝ) * X * (X : ℝ) ^ (1 / 8 : ℝ) =
            (X : ℝ) ^ (5 / 4 : ℝ) := by
          nth_rw 2 [← Real.rpow_one (X : ℝ)]
          rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
          norm_num
        nlinarith
  have hcard0 : (0 : ℝ) ≤ ((shortBlockExceptional X B).card : ℝ) :=
    Nat.cast_nonneg (shortBlockExceptional X B).card
  have hsmall := mul_le_mul_of_nonneg_right hKlo hcard0
  have hcombined : (X : ℝ) ^ (1 / 2 : ℝ) / 2 *
      (shortBlockExceptional X B).card ≤ 46656 * (X : ℝ) ^ (5 / 4 : ℝ) :=
    hsmall.trans (hbound.trans hfront)
  have hpowpos : 0 < (X : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hid : (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) =
      (X : ℝ) ^ (5 / 4 : ℝ) := by rw [← Real.rpow_add hXpos]; norm_num
  have hres : (X : ℝ) ^ (1 / 2 : ℝ) * (shortBlockExceptional X B).card ≤
      (X : ℝ) ^ (1 / 2 : ℝ) * (93312 * (X : ℝ) ^ (3 / 4 : ℝ)) := by nlinarith
  exact le_of_mul_le_mul_left hres hpowpos

theorem eventually_shortBlockExceptional_le_linear {ε δ : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 100000) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop,
      ((shortBlockExceptional X (shortBlockCutoff ε X)).card : ℝ) ≤ δ * X := by
  have hgap := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_shortBlockExceptional_power_bound hε hεsmall,
    hgap.eventually (eventually_ge_atTop (93312 / δ)), eventually_ge_atTop (1 : ℕ)]
      with X hc hpow hX
  have hpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hmul : 93312 ≤ δ * (X : ℝ) ^ (1 / 4 : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hpow
  have h := mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg hpos.le (3 / 4 : ℝ))
  have hid : (X : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) = X := by
    rw [← Real.rpow_add hpos]
    norm_num
  nlinarith

end
end Erdos374Research
