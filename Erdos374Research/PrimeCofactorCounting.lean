import Erdos374Research.HarmonicDensity
import Tao2026.FactorialCoefficientBounds

/-!
# Counting products of a small cofactor and a large prime

UNCOMPILED original finite-counting adapter. The analytic input is the
pinned Chebyshev prime number theorem. The cofactor predicate is arbitrary;
its positive lower density is used through `positive_density_power_window`.
-/

namespace Erdos374Research

open Tao2026 Finset Filter
open scoped BigOperators Topology

noncomputable section

def primeCofactorPairs (S : Finset ℕ) (X : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  S.sigma (fun a => factorialUpperHalfPrimes (X / a))

def primeCofactorProducts (S : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (primeCofactorPairs S X).image (fun z => z.1 * z.2)

lemma mem_primeCofactorPairs {S : Finset ℕ} {X a p : ℕ} :
    (⟨a, p⟩ : Σ _ : ℕ, ℕ) ∈ primeCofactorPairs S X ↔
      a ∈ S ∧ X / a / 2 < p ∧ p ≤ X / a ∧ p.Prime := by
  simp [primeCofactorPairs, factorialUpperHalfPrimes, and_assoc]

lemma primeCofactorProducts_le {S : Finset ℕ} {X n : ℕ}
    (hn : n ∈ primeCofactorProducts S X) : n ≤ X := by
  rcases Finset.mem_image.mp hn with ⟨⟨a, p⟩, hp, rfl⟩
  have h := (mem_primeCofactorPairs.mp hp).2.2.1
  exact (Nat.mul_le_mul_left a h).trans (by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self X a)

lemma primeCofactorProducts_gt_half {S : Finset ℕ} {X n : ℕ}
    (hn : n ∈ primeCofactorProducts S X) : X < 2 * n := by
  rcases Finset.mem_image.mp hn with ⟨⟨a, p⟩, hp, rfl⟩
  have hd := mem_primeCofactorPairs.mp hp
  have ha : 0 < a := by
    by_contra hnot
    have hazero : a = 0 := by omega
    simp [hazero] at hd
    omega
  have hqp : X / a + 1 ≤ 2 * p := by omega
  have hr := Nat.mod_lt X ha
  have hid := Nat.mod_add_div X a
  have hlt : X < a * (X / a + 1) := by nlinarith
  have hmul := Nat.mul_le_mul_left a hqp
  nlinarith

lemma card_primeCofactorProducts {S : Finset ℕ} {X : ℕ}
    (hlarge : ∀ a ∈ S, ∀ p ∈ factorialUpperHalfPrimes (X / a),
      ∀ b ∈ S, b < p) :
    (primeCofactorProducts S X).card =
      ∑ a ∈ S, (factorialUpperHalfPrimes (X / a)).card := by
  have hinj : Set.InjOn (fun z : Σ _ : ℕ, ℕ => z.1 * z.2)
      (primeCofactorPairs S X) := by
    rintro ⟨a, p⟩ hp ⟨b, q⟩ hq heq
    have hp' := Finset.mem_sigma.mp hp
    have hq' := Finset.mem_sigma.mp hq
    have hpp := (Finset.mem_filter.mp hp'.2).2
    have hqp := (Finset.mem_filter.mp hq'.2).2
    change a * p = b * q at heq
    have hpd : p ∣ b * q := by rw [← heq]; exact dvd_mul_left p a
    have hpq : p = q := by
      rcases hpp.dvd_mul.mp hpd with hpb | hpq
      · have hb : b < p := hlarge a hp'.1 p hp'.2 b hq'.1
        have hb0 : 0 < b := by
          by_contra hbnot
          have hbzero : b = 0 := by omega
          subst b
          simpa [factorialUpperHalfPrimes] using hq'.2
        exact False.elim ((not_le_of_gt hb) (Nat.le_of_dvd hb0 hpb))
      · exact (Nat.dvd_prime hqp).mp hpq |>.resolve_left hpp.ne_one
    subst q
    have hab : a = b := Nat.eq_of_mul_eq_mul_right hpp.pos heq
    subst b
    rfl
  rw [primeCofactorProducts, Finset.card_image_of_injOn hinj,
    primeCofactorPairs, Finset.card_sigma]

lemma upperHalfPrime_card_lower {Q X : ℕ} (_hQ : 1 ≤ Q) (hQX : Q ≤ X)
    (hmass : (Q : ℝ) / 4 ≤
      Chebyshev.theta Q - Chebyshev.theta ((Q / 2 : ℕ) : ℝ)) :
    (Q : ℝ) / 4 ≤ (factorialUpperHalfPrimes Q).card * Real.log X := by
  rw [← sum_log_factorialUpperHalfPrimes_eq_theta_sub] at hmass
  calc
    (Q : ℝ) / 4 ≤ ∑ p ∈ factorialUpperHalfPrimes Q, Real.log p := hmass
    _ ≤ ∑ p ∈ factorialUpperHalfPrimes Q, Real.log X := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hple := (Finset.mem_Ioc.mp hp'.1).2.trans hQX
      exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hple)
    _ = (factorialUpperHalfPrimes Q).card * Real.log X := by simp

lemma nat_div_ge_half_real_ratio {X a : ℕ} (ha : 0 < a) (haX : a ≤ X) :
    (X : ℝ) / (2 * a) ≤ (X / a : ℕ) := by
  have hq : 1 ≤ X / a := (Nat.one_le_div_iff ha).mpr haX
  have hr := Nat.mod_lt X ha
  have hid := Nat.mod_add_div X a
  have hqr : (1 : ℝ) ≤ (X / a : ℕ) := by exact_mod_cast hq
  have hrr : ((X % a : ℕ) : ℝ) < a := by exact_mod_cast hr
  have hidR : ((X % a : ℕ) : ℝ) + a * (X / a : ℕ) = X := by exact_mod_cast hid
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)).2
  nlinarith [mul_le_mul_of_nonneg_left hqr (Nat.cast_nonneg a)]

lemma primeCofactor_card_finite_lower {S : Finset ℕ} {X : ℕ}
    (hX : 2 ≤ X)
    (ha : ∀ a ∈ S, 0 < a ∧ a ≤ X)
    (hmass : ∀ a ∈ S, (X / a : ℕ) / (4 : ℝ) ≤
      Chebyshev.theta (X / a : ℕ) - Chebyshev.theta ((X / a / 2 : ℕ) : ℝ))
    (hlarge : ∀ a ∈ S, ∀ p ∈ factorialUpperHalfPrimes (X / a),
      ∀ b ∈ S, b < p) :
    (X : ℝ) / (8 * Real.log X) * (∑ a ∈ S, (a : ℝ)⁻¹) ≤
      (primeCofactorProducts S X).card := by
  have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  rw [card_primeCofactorProducts hlarge, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a haS
  have ha' := ha a haS
  have hq := upperHalfPrime_card_lower
    ((Nat.one_le_div_iff ha'.1).mpr ha'.2) (Nat.div_le_self X a) (hmass a haS)
  have hratio := nat_div_ge_half_real_ratio ha'.1 ha'.2
  have haR : (0 : ℝ) < a := by exact_mod_cast ha'.1
  calc
    (X : ℝ) / (8 * Real.log X) * (a : ℝ)⁻¹ ≤
        ((X / a : ℕ) / (4 : ℝ)) / Real.log X := by
      calc
        (X : ℝ) / (8 * Real.log X) * (a : ℝ)⁻¹ =
            ((X : ℝ) / (2 * a) / 4) / Real.log X := by field_simp; ring
        _ ≤ _ := by gcongr
    _ ≤ ((factorialUpperHalfPrimes (X / a)).card * Real.log X) /
        Real.log X := div_le_div_of_nonneg_right hq hlog.le
    _ = (factorialUpperHalfPrimes (X / a)).card := by field_simp

def cofactorPowerWindow (A : ℕ → Prop) (α : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Ioc ⌈(X : ℝ) ^ (α / 2)⌉₊ ⌊(X : ℝ) ^ α⌋₊).filter A

theorem eventually_primeCofactor_window_parameters {α : ℝ}
    (hα : 0 < α) (hαhalf : α < 1 / 2) (M : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ a b : ℕ,
      0 < a → (a : ℝ) ≤ (X : ℝ) ^ α →
      (b : ℝ) ≤ (X : ℝ) ^ α →
      a ≤ X ∧ M ≤ X / a ∧
        ∀ p ∈ factorialUpperHalfPrimes (X / a), b < p := by
  have hpower : Tendsto (fun X : ℕ => (X : ℝ) ^ (1 - α)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hgap : Tendsto (fun X : ℕ => (X : ℝ) ^ (1 - 2 * α)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpower.eventually (eventually_ge_atTop (2 * (M : ℝ))),
    hgap.eventually (eventually_gt_atTop 4), eventually_ge_atTop (2 : ℕ)]
      with X hpowX hgapX hX
  intro a b ha haB hbB
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hXpos : (0 : ℝ) < X := by linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hBX : (X : ℝ) ^ α ≤ X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hXR (by linarith : α ≤ 1)
  have haX : a ≤ X := by exact_mod_cast haB.trans hBX
  have hratio := nat_div_ge_half_real_ratio ha haX
  have hprod : (X : ℝ) ^ α * (X : ℝ) ^ (1 - α) = X := by
    rw [← Real.rpow_add hXpos]
    rw [show α + (1 - α) = 1 by ring, Real.rpow_one]
  have hM : M ≤ X / a := by
    have hmul : 2 * (M : ℝ) * a ≤ X := by
      calc
        2 * (M : ℝ) * a ≤ (X : ℝ) ^ (1 - α) * (X : ℝ) ^ α := by
          gcongr
        _ = X := by simpa only [mul_comm] using hprod
    have hMR : (M : ℝ) ≤ (X : ℝ) / (2 * a) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    exact_mod_cast hMR.trans hratio
  refine ⟨haX, hM, ?_⟩
  intro p hp
  have hp' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hqp : (X / a : ℕ) < 2 * p := by omega
  have hqpR : (X / a : ℕ) < (2 : ℝ) * p := by exact_mod_cast hqp
  have hratio' := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mp hratio
  have hidentity : (X : ℝ) ^ (1 - 2 * α) * ((X : ℝ) ^ α) ^ 2 = X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_add hXpos]
    simp only [Nat.cast_ofNat]
    rw [show (1 - 2 * α) + α * (2 : ℝ) = 1 by ring, Real.rpow_one]
  have hsmall : 4 * ((X : ℝ) ^ α) ^ 2 < X := by
    have hBpos := Real.rpow_pos_of_pos hXpos α
    nlinarith [mul_lt_mul_of_pos_right hgapX (sq_pos_of_pos hBpos)]
  have habsmall : 4 * (a : ℝ) * b < X := by
    have hab := mul_le_mul haB hbB (Nat.cast_nonneg b)
      (Real.rpow_nonneg hXpos.le α)
    nlinarith
  have hbp : (b : ℝ) < p := by
    nlinarith [mul_lt_mul_of_pos_right hqpR haR]
  exact_mod_cast hbp

/-- The candidates themselves already have positive linear density. Every
candidate comes with an actual prime factor in the upper half of `X/a`;
large-prime uniqueness prevents overcounting across different cofactors. -/
theorem positive_density_primeCofactorProducts (A : ℕ → Prop) {κ α : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) (hαhalf : α < 1 / 2)
    (hdensity : ∀ᶠ N : ℕ in atTop, κ * N ≤ (predicatePrefix A N).card) :
    ∀ᶠ X : ℕ in atTop, κ * α / 32 * X ≤
      (primeCofactorProducts (cofactorPowerWindow A α X) X).card := by
  classical
  obtain ⟨M, hM⟩ := eventually_atTop.mp eventually_nat_factorialUpperHalfTheta_lower
  have hh := positive_density_power_window A hκ hα hdensity
  have hparams := eventually_primeCofactor_window_parameters hα hαhalf M
  filter_upwards [hh, hparams, eventually_ge_atTop (2 : ℕ)] with X hhX hpX hX
  let S := cofactorPowerWindow A α X
  have hmem : ∀ a ∈ S, 0 < a ∧ (a : ℝ) ≤ (X : ℝ) ^ α := by
    intro a ha
    have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1
    refine ⟨lt_of_le_of_lt (Nat.zero_le _) h.1, ?_⟩
    have hf := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) α)
    exact (by exact_mod_cast h.2 : (a : ℝ) ≤ ⌊(X : ℝ) ^ α⌋₊).trans hf
  have hcount := primeCofactor_card_finite_lower hX
    (S := S)
    (fun a ha => ⟨(hmem a ha).1,
      (hpX a a (hmem a ha).1 (hmem a ha).2 (hmem a ha).2).1⟩)
    (fun a ha => hM (X / a)
      (hpX a a (hmem a ha).1 (hmem a ha).2 (hmem a ha).2).2.1)
    (fun a ha p hp b hb =>
      (hpX a b (hmem a ha).1 (hmem a ha).2 (hmem b hb).2).2.2 p hp)
  have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hsum : κ * α / 4 * Real.log X ≤ ∑ a ∈ S, (a : ℝ)⁻¹ := hhX
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ (X : ℝ) / (8 * Real.log X) by positivity)
  have hid : (X : ℝ) / (8 * Real.log X) * (κ * α / 4 * Real.log X) =
      κ * α / 32 * X := by field_simp; ring
  rw [hid] at hscaled
  exact hscaled.trans hcount

end
end Erdos374Research
