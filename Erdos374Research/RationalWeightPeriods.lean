import Erdos374Research.PlateauMass
import Tao2026.VinogradovPhase
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
UNCOMPILED. Exact rational-period averages for the two long-block weights.
The upper-block case uses the first additive character, rather than a
coprimality reduction or an estimate for a finite grid of residues.
-/

namespace Erdos374Research

open Tao2026 MeasureTheory
open scoped BigOperators

lemma additiveCharacter_nat_mul (x : ℝ) (n : ℕ) :
    standardAdditiveCharacter ((n : ℝ) * x) = standardAdditiveCharacter x ^ n := by
  induction n with
  | zero => simp [standardAdditiveCharacter]
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        standardAdditiveCharacter_add, ih, pow_succ]

lemma additiveCharacter_ne_one_of_between {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    standardAdditiveCharacter x ≠ 1 := by
  intro heq
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp heq
  have hi := congrArg Complex.im hk
  have hxk : x = (k : ℝ) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.intCast_re, Complex.intCast_im] at hi
    norm_num at hi
    apply mul_left_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0)
    nlinarith [hi]
  have hk0 : (0 : ℝ) < k := by rwa [hxk] at hx0
  have hk1 : (k : ℝ) < 1 := by rwa [hxk] at hx1
  have : 0 < k := by exact_mod_cast hk0
  have : k < 1 := by exact_mod_cast hk1
  omega

lemma geometric_sum_mul_sub_one (z : ℂ) (a : ℕ) :
    (∑ k ∈ Finset.range a, z ^ k) * (z - 1) = z ^ a - 1 := by
  induction a with
  | zero => simp
  | succ a ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring

lemma rational_character_sum_zero {a t : ℕ} (ht : 0 < t) (hta : t < a) (x : ℝ) :
    (∑ k ∈ Finset.range a,
      standardAdditiveCharacter ((t : ℝ) / a * ((k : ℝ) + x))) = 0 := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (lt_trans ht hta)
  have htheta0 : (0 : ℝ) < (t : ℝ) / a := div_pos (by exact_mod_cast ht) ha
  have htheta1 : (t : ℝ) / a < 1 := (div_lt_one ha).mpr (by exact_mod_cast hta)
  let z := standardAdditiveCharacter ((t : ℝ) / a)
  have hz : z ≠ 1 := additiveCharacter_ne_one_of_between htheta0 htheta1
  have hza : z ^ a = 1 := by
    rw [← additiveCharacter_nat_mul]
    convert standardAdditiveCharacter_int (t : ℤ) using 1
    push_cast
    field_simp
  have hsum : (∑ k ∈ Finset.range a, z ^ k) = 0 := by
    have h := geometric_sum_mul_sub_one z a
    rw [hza, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz)
  calc
    (∑ k ∈ Finset.range a,
      standardAdditiveCharacter ((t : ℝ) / a * ((k : ℝ) + x))) =
        ∑ k ∈ Finset.range a, z ^ k * standardAdditiveCharacter ((t : ℝ) / a * x) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [mul_add, standardAdditiveCharacter_add]
          congr 1
          simpa only [mul_comm] using additiveCharacter_nat_mul ((t : ℝ) / a) k
    _ = 0 := by rw [← Finset.sum_mul, hsum, zero_mul]

lemma integerAvoidingWeight_character_minorant {N : ℕ}
    (hN : 1 < Real.log (N : ℝ)) (x : ℝ) :
    (1 - (standardAdditiveCharacter x).re) / 2 - Real.pi * plateauWidth N ≤
      integerAvoidingWeight N x := by
  have hd := (plateauWidth_pos hN).le
  by_cases hx : integerAvoidingWeight N x = 1
  · rw [hx]
    have hre : -(1 : ℝ) ≤ (standardAdditiveCharacter x).re := by
      have h := Complex.abs_re_le_norm (standardAdditiveCharacter x)
      rw [norm_standardAdditiveCharacter] at h
      exact (abs_le.mp h).1
    nlinarith [Real.pi_pos]
  · have hnear : ∃ k : ℤ, |x - (k : ℝ)| ≤ plateauWidth N := by
      by_contra hn
      push Not at hn
      exact hx (integerAvoidingWeight_eq_one_far hN hn)
    obtain ⟨k, hk⟩ := hnear
    have hnorm := norm_standardAdditiveCharacter_sub_le x (k : ℝ)
    rw [standardAdditiveCharacter_int] at hnorm
    have hre := Complex.abs_re_le_norm (standardAdditiveCharacter x - 1)
    simp only [Complex.sub_re, Complex.one_re] at hre
    have hsmall : 1 - (standardAdditiveCharacter x).re ≤ 2 * Real.pi * plateauWidth N := by
      have habs := (abs_le.mp (hre.trans hnorm)).1
      have hmul := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2 * Real.pi)
      linarith
    have hg := integerAvoidingWeight_nonneg N x
    linarith

theorem rational_orbit_avoiding_weight_sum {N a t : ℕ}
    (hN : 1 < Real.log (N : ℝ)) (hd : plateauWidth N ≤ 1 / 100)
    (ht : 0 < t) (hta : t < a) (x : ℝ) :
    (a : ℝ) / 3 ≤ ∑ k ∈ Finset.range a,
      integerAvoidingWeight N ((t : ℝ) / a * ((k : ℝ) + x)) := by
  have hsum := congrArg Complex.re (rational_character_sum_zero ht hta x)
  simp only [Complex.re_sum, Complex.zero_re] at hsum
  have hminor := Finset.sum_le_sum (s := Finset.range a)
    (fun k _ => integerAvoidingWeight_character_minorant hN ((t : ℝ) / a * (k + x)))
  have hleft : (∑ k ∈ Finset.range a,
      ((1 - (standardAdditiveCharacter ((t : ℝ) / a * ((k : ℝ) + x))).re) / 2 -
        Real.pi * plateauWidth N)) = (a : ℝ) * (1 / 2 - Real.pi * plateauWidth N) := by
    calc
      _ = (∑ k ∈ Finset.range a,
          (1 - (standardAdditiveCharacter ((t : ℝ) / a * ((k : ℝ) + x))).re)) / 2 -
            ∑ _k ∈ Finset.range a, Real.pi * plateauWidth N := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      _ = ((a : ℝ) - 0) / 2 - (a : ℝ) * (Real.pi * plateauWidth N) := by
        rw [Finset.sum_sub_distrib, hsum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      _ = _ := by ring
  rw [hleft] at hminor
  have hc : (1 / 3 : ℝ) ≤ 1 / 2 - Real.pi * plateauWidth N := by
    have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
    have hpd : Real.pi * plateauWidth N ≤ 4 * (1 / 100 : ℝ) :=
      mul_le_mul hpi hd (plateauWidth_pos hN).le (by norm_num)
    linarith
  exact (by nlinarith [Nat.cast_nonneg (α := ℝ) a] :
    (a : ℝ) / 3 ≤ (a : ℝ) * (1 / 2 - Real.pi * plateauWidth N)).trans hminor

lemma integral_sum_range_continuous (F : ℕ → ℝ → ℝ)
    (hF : ∀ k, Continuous (F k)) (n : ℕ) (u v : ℝ) :
    (∫ x in u..v, ∑ k ∈ Finset.range n, F k x) =
      ∑ k ∈ Finset.range n, ∫ x in u..v, F k x := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      rw [intervalIntegral.integral_add
        ((continuous_finsetSum _ fun k _ => hF k).intervalIntegrable u v)
        ((hF n).intervalIntegrable u v), ih]

lemma integral_nat_interval_eq_unit_translates {F : ℝ → ℝ}
    (hF : Continuous F) (a : ℕ) :
    (∫ u in (0 : ℝ)..a, F u) =
      ∫ x in (0 : ℝ)..1, ∑ k ∈ Finset.range a, F (x + k) := by
  rw [integral_sum_range_continuous (fun k x => F (x + k))
    (fun k => hF.comp (continuous_id.add continuous_const))]
  simp_rw [intervalIntegral.integral_comp_add_right, zero_add]
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (f := F) (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := a)
    (fun k _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hF.intervalIntegrable (μ := volume) (k : ℝ) ((k : ℝ) + 1))
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_comm] using h.symm

theorem upper_weight_rational_period_mass {N a t : ℕ} {f : ℝ → ℝ}
    (hN : 1 < Real.log (N : ℝ)) (hd : plateauWidth N ≤ 1 / 100)
    (ht : 0 < t) (hta : t < a)
    (hf : Continuous f) (hfper : Function.Periodic f 1) (hf0 : ∀ x, 0 ≤ f x) :
    ((a : ℝ) / 3) * (∫ x in (0 : ℝ)..1, f x) ≤
      ∫ u in (0 : ℝ)..a, f u * integerAvoidingWeight N ((t : ℝ) / a * u) := by
  have hg := (integerAvoidingWeight_contDiff N).continuous
  rw [integral_nat_interval_eq_unit_translates
    (F := fun u : ℝ => f u * integerAvoidingWeight N ((t : ℝ) / a * u))
    (hf.mul (hg.comp (continuous_const.mul continuous_id)))]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_const.mul hf).intervalIntegrable 0 1)
    ((continuous_finsetSum _ fun k _ =>
      (hf.comp (continuous_id.add continuous_const)).mul
        (hg.comp (continuous_const.mul (continuous_id.add continuous_const)))).intervalIntegrable 0 1)
  intro x hx
  calc
    (a : ℝ) / 3 * f x ≤
        (∑ k ∈ Finset.range a, integerAvoidingWeight N ((t : ℝ) / a * ((k : ℝ) + x))) * f x :=
      mul_le_mul_of_nonneg_right (rational_orbit_avoiding_weight_sum hN hd ht hta x) (hf0 x)
    _ = ∑ k ∈ Finset.range a, f (x + k) * integerAvoidingWeight N ((t : ℝ) / a * (x + k)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hfk : f (x + k) = f x := by
        simpa only [mul_one] using hfper.nat_mul k x
      rw [hfk]
      rw [show (k : ℝ) + x = x + k by ring]
      ring

lemma rational_product_periodic {f g : ℝ → ℝ}
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    {a t : ℕ} (ha : 0 < a) :
    Function.Periodic (fun u => f u * g ((t : ℝ) / a * u)) (a : ℝ) := by
  intro u
  change f (u + (a : ℝ)) * g ((t : ℝ) / a * (u + a)) =
    f u * g ((t : ℝ) / a * u)
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hfu : f (u + (a : ℝ)) = f u := by simpa only [mul_one] using hf.nat_mul a u
  have hgu : g ((t : ℝ) / a * (u + a)) = g ((t : ℝ) / a * u) := by
    rw [show (t : ℝ) / a * (u + a) = (t : ℝ) / a * u + t by field_simp]
    simpa only [mul_one] using hg.nat_mul t ((t : ℝ) / a * u)
  rw [hfu, hgu]

lemma integral_periodic_rational_nat_interval {f : ℝ → ℝ}
    (hf : Continuous f) (hper : Function.Periodic f 1)
    {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    (∫ u in (0 : ℝ)..a, f ((t : ℝ) / a * u)) =
      (a : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [intervalIntegral.integral_comp_mul_left f (div_ne_zero htR haR)]
  have hperiod := hper.intervalIntegral_add_zsmul_eq (t : ℤ) 0
    (fun x y => hf.intervalIntegrable x y)
  simp only [zero_add, zsmul_eq_mul, mul_one, Int.cast_natCast] at hperiod
  rw [mul_zero, div_mul_cancel₀ _ haR, hperiod, smul_eq_mul]
  field_simp

lemma integral_periodic_nat_interval {f : ℝ → ℝ}
    (hf : Continuous f) (hper : Function.Periodic f 1) (a : ℕ) :
    (∫ u in (0 : ℝ)..a, f u) = (a : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
  have h := hper.intervalIntegral_add_zsmul_eq (a : ℤ) 0
    (fun x y => hf.intervalIntegrable x y)
  simpa only [zero_add, zsmul_eq_mul, mul_one, Int.cast_natCast] using h

theorem lower_weight_rational_period_mass {N a t : ℕ} {f : ℝ → ℝ}
    (hN : 1 < Real.log (N : ℝ)) (ha : 0 < a) (ht : 0 < t)
    (hf : Continuous f) (hfper : Function.Periodic f 1)
    (_hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (a : ℝ) * ((∫ x in (0 : ℝ)..1, f x) - plateauWidth N) ≤
      ∫ u in (0 : ℝ)..a, integerAvoidingWeight N u * f ((t : ℝ) / a * u) := by
  have hg := (integerAvoidingWeight_contDiff N).continuous
  have hfc : Continuous (fun u : ℝ => f ((t : ℝ) / a * u)) :=
    hf.comp (continuous_const.mul continuous_id)
  have hpoint : ∀ u : ℝ,
      f ((t : ℝ) / a * u) - (1 - integerAvoidingWeight N u) ≤
        integerAvoidingWeight N u * f ((t : ℝ) / a * u) := by
    intro u
    nlinarith [hf1 ((t : ℝ) / a * u), integerAvoidingWeight_le_one N u,
      mul_nonneg (sub_nonneg.mpr (hf1 ((t : ℝ) / a * u)))
        (sub_nonneg.mpr (integerAvoidingWeight_le_one N u))]
  have hi : (∫ u in (0 : ℝ)..a,
      f ((t : ℝ) / a * u) - (1 - integerAvoidingWeight N u)) ≤
        ∫ u in (0 : ℝ)..a, integerAvoidingWeight N u * f ((t : ℝ) / a * u) :=
    intervalIntegral.integral_mono_on (μ := volume) (by exact_mod_cast ha.le)
    ((hfc.sub (continuous_const.sub hg)).intervalIntegrable 0 a)
    ((hg.mul hfc).intervalIntegrable 0 a) (fun u _ => hpoint u)
  rw [intervalIntegral.integral_sub (hfc.intervalIntegrable 0 a)
    ((continuous_const.sub hg).intervalIntegrable 0 a),
    integral_periodic_rational_nat_interval hf hfper ha ht] at hi
  have hper : Function.Periodic (fun u => 1 - integerAvoidingWeight N u) 1 := by
    intro u
    change 1 - integerAvoidingWeight N (u + 1) = 1 - integerAvoidingWeight N u
    rw [integerAvoidingWeight_periodic N u]
  rw [integral_periodic_nat_interval (continuous_const.sub hg) hper] at hi
  have hd := integerAvoidingWeight_period_defect hN 0
  simp only [zero_add] at hd
  have hmul := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℝ) a)
  nlinarith

end Erdos374Research
