import Erdos374Research.AdmissibleDensity
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Harmonic mass in a power window

UNCOMPILED. A positive lower density supplies logarithmic harmonic mass in
every fixed power window. Abel summation is applied to the window itself;
subtracting two unrelated prefix estimates would not prove this assertion.
-/

namespace Erdos374Research

open Finset Filter
open scoped BigOperators Topology

noncomputable section

def prefixMass (g : ℕ → ℝ) (N : ℕ) : ℝ := ∑ i ∈ Ioc 0 N, g i

def reciprocalWindow (g : ℕ → ℝ) (L U : ℕ) : ℝ :=
  ∑ i ∈ Ioc L U, g i / i

lemma prefixMass_succ (g : ℕ → ℝ) (N : ℕ) :
    prefixMass g (N + 1) = prefixMass g N + g (N + 1) := by
  exact Finset.sum_Ioc_succ_top (Nat.zero_le N) g

lemma reciprocal_prefix_abel (g : ℕ → ℝ) (N : ℕ) :
    reciprocalWindow g 0 N = prefixMass g N / (N + 1) +
      ∑ i ∈ Ioc 0 N, prefixMass g i / ((i : ℝ) * (i + 1)) := by
  induction N with
  | zero => simp [reciprocalWindow, prefixMass]
  | succ N ih =>
      rw [reciprocalWindow, Finset.sum_Ioc_succ_top (Nat.zero_le N)]
      change reciprocalWindow g 0 N + g (N + 1) / ((N + 1 : ℕ) : ℝ) = _
      rw [ih, Finset.sum_Ioc_succ_top (Nat.zero_le N), prefixMass_succ]
      push_cast
      have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp [h1, h2]
      ring

lemma sum_Ioc_window {f : ℕ → ℝ} {L U : ℕ} (hLU : L ≤ U) :
    (∑ i ∈ Ioc L U, f i) =
      (∑ i ∈ Ioc 0 U, f i) - ∑ i ∈ Ioc 0 L, f i := by
  have hu := Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) hLU
  have hd : Disjoint (Ioc 0 L) (Ioc L U) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hs := Finset.sum_union hd (f := f)
  rw [hu] at hs
  linarith

lemma reciprocal_window_abel (g : ℕ → ℝ) {L U : ℕ} (hLU : L ≤ U) :
    reciprocalWindow g L U =
      prefixMass g U / (U + 1) - prefixMass g L / (L + 1) +
        ∑ i ∈ Ioc L U, prefixMass g i / ((i : ℝ) * (i + 1)) := by
  rw [reciprocalWindow, sum_Ioc_window hLU]
  change reciprocalWindow g 0 U - reciprocalWindow g 0 L = _
  rw [reciprocal_prefix_abel, reciprocal_prefix_abel, sum_Ioc_window hLU]
  ring

lemma shifted_harmonic_sum (N : ℕ) :
    (∑ i ∈ Ioc 0 N, ((i : ℝ) + 1)⁻¹) = (harmonic (N + 1) : ℝ) - 1 := by
  induction N with
  | zero => norm_num [harmonic_succ]
  | succ N ih =>
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), harmonic_succ (N + 1)]
      push_cast
      linarith

theorem reciprocal_window_lower (g : ℕ → ℝ) {κ : ℝ} {L U : ℕ}
    (hκ : 0 ≤ κ) (hLU : L ≤ U)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1)
    (hdensity : ∀ i ∈ Ioc L U, κ * i ≤ prefixMass g i) :
    κ * (Real.log (U + 2) - Real.log (L + 1) - 1) - 1 ≤
      reciprocalWindow g L U := by
  have hU : 0 ≤ prefixMass g U := Finset.sum_nonneg (fun i hi => hg0 i)
  have hL : prefixMass g L ≤ L := by
    calc
      prefixMass g L ≤ ∑ i ∈ Ioc 0 L, (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi => hg1 i)
      _ = L := by simp
  have hboundary : prefixMass g L / (L + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < L + 1)).2
    linarith
  have hmain : κ * ∑ i ∈ Ioc L U, ((i : ℝ) + 1)⁻¹ ≤
      ∑ i ∈ Ioc L U, prefixMass g i / ((i : ℝ) * (i + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi0 : 0 < i := lt_of_le_of_lt (Nat.zero_le L) (Finset.mem_Ioc.mp hi).1
    have hiR : (0 : ℝ) < i := by exact_mod_cast hi0
    calc
      κ * ((i : ℝ) + 1)⁻¹ = (κ * i) / ((i : ℝ) * (i + 1)) := by
        field_simp [hiR.ne', (show (i : ℝ) + 1 ≠ 0 by positivity)]
      _ ≤ _ := div_le_div_of_nonneg_right (hdensity i hi) (by positivity)
  have hhs : (∑ i ∈ Ioc L U, ((i : ℝ) + 1)⁻¹) =
      (harmonic (U + 1) : ℝ) - (harmonic (L + 1) : ℝ) := by
    rw [sum_Ioc_window hLU, shifted_harmonic_sum, shifted_harmonic_sum]
    ring
  have hlo := log_add_one_le_harmonic (U + 1)
  have hhi := harmonic_le_one_add_log (L + 1)
  push_cast at hlo hhi
  have hUshift : (U : ℝ) + 1 + 1 = (U : ℝ) + 2 := by ring
  rw [hUshift] at hlo
  have hlog : Real.log (U + 2) - Real.log (L + 1) - 1 ≤
      ∑ i ∈ Ioc L U, ((i : ℝ) + 1)⁻¹ := by rw [hhs]; linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hκ
  have hfront : 0 ≤ prefixMass g U / (U + 1) := by positivity
  rw [reciprocal_window_abel g hLU]
  linarith

def predicateIndicator (A : ℕ → Prop) (i : ℕ) : ℝ := by
  classical
  exact if A i then 1 else 0

def predicatePrefix (A : ℕ → Prop) (N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter A

lemma prefixMass_indicator (A : ℕ → Prop) (N : ℕ) :
    prefixMass (predicateIndicator A) N = ((predicatePrefix A N).card : ℝ) := by
  classical
  change (∑ i ∈ Ioc 0 N, if A i then (1 : ℝ) else 0) =
    (((Ioc 0 N).filter A).card : ℝ)
  rw [← Finset.sum_filter]
  simp

open scoped Classical in
lemma reciprocalWindow_indicator (A : ℕ → Prop) (L U : ℕ) :
    reciprocalWindow (predicateIndicator A) L U =
      ∑ i ∈ (Ioc L U).filter A, (i : ℝ)⁻¹ := by
  classical
  simp [reciprocalWindow, predicateIndicator, Finset.sum_filter,
    ite_div, one_div]

open scoped Classical in
/-- Positive lower density gives a uniform lower bound in the window
`ceil(X^(α/2)) < a ≤ floor(X^α)`. -/
theorem positive_density_power_window (A : ℕ → Prop) {κ α : ℝ}
    (hκ : 0 < κ) (hα : 0 < α)
    (hdensity : ∀ᶠ N : ℕ in atTop, κ * N ≤ (predicatePrefix A N).card) :
    ∀ᶠ X : ℕ in atTop,
      κ * α / 4 * Real.log X ≤
        ∑ a ∈ (Ioc ⌈(X : ℝ) ^ (α / 2)⌉₊ ⌊(X : ℝ) ^ α⌋₊).filter A,
          (a : ℝ)⁻¹ := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdensity
  have hp : Tendsto (fun X : ℕ => (X : ℝ) ^ (α / 2)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hp.eventually (eventually_ge_atTop (max (4 : ℝ) (N : ℝ))),
    hlog.eventually (eventually_ge_atTop ((3 * κ + 1) * 4 / (κ * α))),
    eventually_ge_atTop (2 : ℕ)] with X hpX hlogX hX
  let L : ℕ := ⌈(X : ℝ) ^ (α / 2)⌉₊
  let U : ℕ := ⌊(X : ℝ) ^ α⌋₊
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hhalf0 : 0 ≤ (X : ℝ) ^ (α / 2) := Real.rpow_nonneg hXR.le _
  have hhalf : 4 ≤ (X : ℝ) ^ (α / 2) := (le_max_left _ _).trans hpX
  have hpow : (X : ℝ) ^ α = ((X : ℝ) ^ (α / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXR.le]
    congr 1
    ring
  have hLle : (L : ℝ) ≤ (X : ℝ) ^ (α / 2) + 1 :=
    (Nat.ceil_lt_add_one hhalf0).le
  have hUgt : (X : ℝ) ^ α < (U : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLU : L ≤ U := by
    have h : (L : ℝ) < (U : ℝ) + 1 := by rw [hpow] at hUgt; nlinarith
    have h' : L < U + 1 := by exact_mod_cast h
    omega
  have hNL : N ≤ L := by
    have h := ((le_max_right (4 : ℝ) N).trans hpX).trans (Nat.le_ceil _)
    exact_mod_cast h
  have hlower := reciprocal_window_lower (predicateIndicator A) hκ.le hLU
    (fun i => by simp only [predicateIndicator]; split_ifs <;> norm_num)
    (fun i => by simp only [predicateIndicator]; split_ifs <;> norm_num)
    (fun i hi => by
      rw [prefixMass_indicator]
      exact hN i (hNL.trans (Finset.mem_Ioc.mp hi).1.le))
  have hlogU : α * Real.log X ≤ Real.log (U + 2) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hXR α) (by linarith :
      (X : ℝ) ^ α ≤ (U : ℝ) + 2)
    rwa [Real.log_rpow hXR] at h
  have hlogL : Real.log (L + 1) ≤ α / 2 * Real.log X + 2 := by
    have hLpos : (0 : ℝ) < L + 1 := by positivity
    have h := Real.log_le_log hLpos (show (L : ℝ) + 1 ≤
      3 * (X : ℝ) ^ (α / 2) by linarith)
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hXR _).ne',
      Real.log_rpow hXR] at h
    have hthree := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hbudget : 3 * κ + 1 ≤ κ * α / 4 * Real.log X := by
    apply (div_le_iff₀ (mul_pos hκ hα)).mp at hlogX
    nlinarith
  rw [reciprocalWindow_indicator] at hlower
  change κ * α / 4 * Real.log X ≤
    ∑ a ∈ (Ioc L U).filter A, (a : ℝ)⁻¹
  nlinarith [mul_le_mul_of_nonneg_left hlogU hκ.le,
    mul_le_mul_of_nonneg_left hlogL hκ.le]

end
end Erdos374Research
