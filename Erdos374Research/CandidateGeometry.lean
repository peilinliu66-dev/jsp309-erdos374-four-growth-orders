import Erdos374Research.GoodCandidateDensity
import Erdos374Research.OrderedRepresentations

/-! UNCOMPILED. Exact representations and scale transfers for the counted
prime-times-cofactor candidates. Distinctness of every factorial index is
checked explicitly in the construction theorems. -/

namespace Erdos374Research

open Finset Filter Tao2026
open scoped BigOperators Topology

theorem hasRepresentation_five_of_even {n : ℕ} (hn : 8 ≤ n) (heven : Even n) :
    HasRepresentation 5 n := by
  rcases heven with ⟨z, hz⟩
  have hnz : n = 2 * z := by omega
  have hz4 : 4 ≤ z := by omega
  apply hasRepresentation_five (a := 2) (b := z - 1) (c := z) (d := n - 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hid := straus_identity (d := 2) (b := 1) (c := 2) (w := 2) (z := z)
    (by norm_num) (by norm_num) (by omega) straus_even_seed
  rw [← hnz, one_mul] at hid
  refine ⟨n * (n - 1).factorial * (z - 1).factorial, ?_⟩
  calc
    Nat.factorial 2 * (z - 1).factorial * z.factorial *
        (n - 1).factorial * n.factorial =
      n.factorial * (n - 1).factorial * z.factorial * (z - 1).factorial * Nat.factorial 2 := by ring
    _ = _ := by simpa only [pow_two] using hid

theorem hasRepresentation_six_of_separated_factors {a p : ℕ}
    (ha : 3 ≤ a) (hgap : a + 1 < p) : HasRepresentation 6 (a * p) := by
  have hp : 1 ≤ p := by omega
  have hmul : 3 * p ≤ a * p := Nat.mul_le_mul_right p ha
  have hpn : p < a * p - 1 := by omega
  apply hasRepresentation_six (a := a - 1) (b := a) (c := p - 1)
    (d := p) (e := a * p - 1)
    (by omega) (by omega) (by omega) (by omega) hpn (by omega)
  have hid := six_factorial_identity (a := a) (p := p) (by omega) hp
  refine ⟨a * p * (a * p - 1).factorial * (a - 1).factorial * (p - 1).factorial, ?_⟩
  calc
    (a - 1).factorial * a.factorial * (p - 1).factorial * p.factorial *
        (a * p - 1).factorial * (a * p).factorial =
      (a * p).factorial * (a * p - 1).factorial * a.factorial * (a - 1).factorial *
        p.factorial * (p - 1).factorial := by ring
    _ = _ := by simpa only [pow_two] using hid

lemma eventually_lift_through_half {P : ℕ → Prop}
    (hP : ∀ᶠ n : ℕ in atTop, P n) :
    ∀ᶠ X : ℕ in atTop, ∀ n : ℕ, X < 2 * n → P n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  filter_upwards [eventually_ge_atTop (2 * N)] with X hX n hn
  exact hN n (by omega)

theorem eventually_window_power_transfer {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    ∀ᶠ X : ℕ in atTop, ∀ n a : ℕ,
      X < 2 * n → (a : ℝ) ≤ (X : ℝ) ^ u → (a : ℝ) ≤ (n : ℝ) ^ v := by
  have hgap := (_root_.tendsto_rpow_atTop (sub_pos.mpr huv)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hgap.eventually (eventually_ge_atTop ((2 : ℝ) ^ v)),
    eventually_ge_atTop (1 : ℕ)] with X hgapX hX
  intro n a hn ha
  change (2 : ℝ) ^ v ≤ (X : ℝ) ^ (v - u) at hgapX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hhalf : (X : ℝ) / 2 ≤ n := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    exact_mod_cast (show X ≤ n * 2 by omega)
  have htwo : 0 < (2 : ℝ) ^ v := Real.rpow_pos_of_pos (by norm_num) v
  have hmul := mul_le_mul_of_nonneg_right hgapX (Real.rpow_nonneg hXpos.le u)
  have hid : (X : ℝ) ^ (v - u) * (X : ℝ) ^ u = (X : ℝ) ^ v := by
    rw [← Real.rpow_add hXpos]
    congr 1
    ring
  rw [hid] at hmul
  calc
    (a : ℝ) ≤ (X : ℝ) ^ u := ha
    _ ≤ (X : ℝ) ^ v / (2 : ℝ) ^ v := (le_div_iff₀ htwo).mpr (by nlinarith)
    _ = ((X : ℝ) / 2) ^ v :=
      (Real.div_rpow hXpos.le (by norm_num : (0 : ℝ) ≤ 2) v).symm
    _ ≤ (n : ℝ) ^ v := Real.rpow_le_rpow (by positivity) hhalf (by linarith)

theorem eventually_candidate_factor_geometry (A : ℕ → Prop) {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 100000) :
    ∀ᶠ X : ℕ in atTop, ∀ n ∈ primeCofactorProducts (cofactorPowerWindow A (ε / 2) X) X,
      ∃ a p : ℕ, A a ∧ 3 ≤ a ∧ p.Prime ∧ a + 1 < p ∧ n = a * p ∧
        (a : ℝ) ≤ (n : ℝ) ^ (3 * ε / 4) := by
  classical
  have htransfer := eventually_window_power_transfer
    (show 0 ≤ ε / 2 by positivity) (show ε / 2 < 3 * ε / 4 by linarith)
  have hlow := (_root_.tendsto_rpow_atTop (show 0 < ε / 2 / 2 by positivity)).comp
    tendsto_natCast_atTop_atTop
  have hgap := (_root_.tendsto_rpow_atTop (show 0 < 1 - ε by linarith)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [htransfer, hlow.eventually (eventually_ge_atTop 3),
    hgap.eventually (eventually_gt_atTop 8), eventually_ge_atTop (2 : ℕ)]
      with X htrans hlowX hgapX hX
  change (8 : ℝ) < (X : ℝ) ^ (1 - ε) at hgapX
  intro n hn
  obtain ⟨⟨a, p⟩, hpair, hnEq⟩ := Finset.mem_image.mp hn
  have hd := mem_primeCofactorPairs.mp hpair
  have haData := Finset.mem_filter.mp hd.1
  have haRange := Finset.mem_Ioc.mp haData.1
  have hapos : 0 < a := by omega
  have ha3 : 3 ≤ a := by
    have hceil := Nat.le_ceil ((X : ℝ) ^ (ε / 2 / 2))
    have haL : (⌈(X : ℝ) ^ (ε / 2 / 2)⌉₊ : ℝ) < a := by exact_mod_cast haRange.1
    have haR : (3 : ℝ) < a := hlowX.trans_lt (hceil.trans_lt haL)
    exact_mod_cast haR.le
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have haUpper : (a : ℝ) ≤ (X : ℝ) ^ (ε / 2) :=
    (by exact_mod_cast haRange.2 : (a : ℝ) ≤ ⌊(X : ℝ) ^ (ε / 2)⌋₊).trans
      (Nat.floor_le (Real.rpow_nonneg hXpos.le _))
  have haX : a ≤ X := by
    have hp := Real.rpow_le_rpow_of_exponent_le hXR (show ε / 2 ≤ 1 by linarith)
    rw [Real.rpow_one] at hp
    exact_mod_cast haUpper.trans hp
  have hratio := nat_div_ge_half_real_ratio hapos haX
  have hqp : X / a < 2 * p := by omega
  have hqpR : (X / a : ℕ) < (2 : ℝ) * p := by exact_mod_cast hqp
  have hratio' := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mp hratio
  have hidentity : (X : ℝ) ^ (1 - ε) * ((X : ℝ) ^ (ε / 2)) ^ 2 = X := by
    rw [← Real.rpow_two, ← Real.rpow_mul hXpos.le, ← Real.rpow_add hXpos,
      show 1 - ε + ε / 2 * 2 = (1 : ℝ) by ring, Real.rpow_one]
  have hBpos := Real.rpow_pos_of_pos hXpos (ε / 2)
  have hscale : 8 * ((X : ℝ) ^ (ε / 2)) ^ 2 < X := by
    have hmul : 8 * ((X : ℝ) ^ (ε / 2)) ^ 2 <
        (X : ℝ) ^ (1 - ε) * ((X : ℝ) ^ (ε / 2)) ^ 2 :=
      mul_lt_mul_of_pos_right hgapX (sq_pos_of_pos hBpos)
    simpa only [hidentity] using hmul
  have haR : (0 : ℝ) < a := by exact_mod_cast hapos
  have hgapReal : 2 * (a : ℝ) < p := by
    have haSq : (a : ℝ) ^ 2 ≤ ((X : ℝ) ^ (ε / 2)) ^ 2 :=
      pow_le_pow_left₀ haR.le haUpper 2
    have hmul := mul_lt_mul_of_pos_right hqpR (show 0 < 2 * (a : ℝ) by positivity)
    nlinarith
  have hgapNat : a + 1 < p := by
    have h : 2 * a < p := by exact_mod_cast hgapReal
    omega
  refine ⟨a, p, haData.2, ha3, hd.2.2.2, hgapNat, hnEq.symm, ?_⟩
  exact htrans n a (primeCofactorProducts_gt_half hn) haUpper

theorem squarefree_prime_cofactor_product {a p : ℕ}
    (ha : Squarefree a) (hp : p.Prime) (hap : a < p) : Squarefree (a * p) := by
  have hcop : Nat.Coprime p a := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact (not_le_of_gt hap) (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero) hd))
  exact (Nat.squarefree_mul hcop.symm).mpr ⟨ha, hp.squarefree⟩

end Erdos374Research
