import Erdos374Research.BlockWeightArithmetic
import Erdos374Research.PrimeWeightMass

/-! UNCOMPILED. Exact zero prime sum and positive comparison integral for
the explicit two-block weight. The support implications are arithmetic;
the lower integral is derived from the periodic and quadratic-band lemmas. -/

namespace Erdos374Research

open Tao2026 MeasureTheory Set
open scoped BigOperators ContDiff

noncomputable section

def blockDetectingWeight (n m N P l₁ l₂ j a t : ℕ) : ℝ × ℝ → ℂ :=
  pairedWeight (blockSeparator n N P l₁ l₂ j)
    (secondWeightLift (longBlockSquareWeight N (selectedBlockCenter n m l₁ l₂ j) P))
    ((t : ℝ) / a)

def blockDetectingReal (n m N P l₁ l₂ j a t : ℕ) (u : ℝ) : ℝ :=
  blockSeparatorReal n N P l₁ l₂ j a t u *
    longBlockSquareWeight N (selectedBlockCenter n m l₁ l₂ j) P
      ((selectedBlockCenter n m l₁ l₂ j : ℝ) * u ^ 2 / (n : ℝ) ^ 2)

lemma selectedBlockCenter_pos_le {n m l₁ l₂ j : ℕ}
    (hn : 0 < n) (hmn : m < n) (hl₂ : l₂ ≤ m) (hj : j < l₂) :
    0 < selectedBlockCenter n m l₁ l₂ j ∧ selectedBlockCenter n m l₁ l₂ j ≤ n := by
  unfold selectedBlockCenter
  split_ifs <;> omega

lemma blockDetectingReal_continuous (n m N P l₁ l₂ j a t : ℕ) :
    Continuous (blockDetectingReal n m N P l₁ l₂ j a t) :=
  (blockSeparatorReal_continuous _ _ _ _ _ _ _ _).mul
    ((longBlockSquareWeight_contDiff _ _ _).continuous.comp
      ((continuous_const.mul (continuous_id.pow 2)).div_const _))

lemma blockDetectingReal_nonneg (n m N P l₁ l₂ j a t : ℕ) (u : ℝ) :
    0 ≤ blockDetectingReal n m N P l₁ l₂ j a t u :=
  mul_nonneg (blockSeparatorReal_nonneg _ _ _ _ _ _ _ _ _)
    (longBlockSquareWeight_nonneg _ _ _ _)

lemma blockDetectingWeight_eval {n : ℕ} (hn : 0 < n)
    (m N P l₁ l₂ j a t : ℕ) (v : ℝ) :
    blockDetectingWeight n m N P l₁ l₂ j a t
      ((n : ℝ) / v, (selectedBlockCenter n m l₁ l₂ j : ℝ) / v ^ 2) =
      (blockDetectingReal n m N P l₁ l₂ j a t ((n : ℝ) / v) : ℂ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hphase : (selectedBlockCenter n m l₁ l₂ j : ℝ) * ((n : ℝ) / v) ^ 2 / (n : ℝ) ^ 2 =
      (selectedBlockCenter n m l₁ l₂ j : ℝ) / v ^ 2 := by
    by_cases hv : v = 0
    · simp [hv]
    · field_simp [hnR, hv]
  simp only [blockDetectingWeight, pairedWeight, secondWeightLift,
    blockSeparatorReal_eval, blockDetectingReal, hphase, Complex.ofReal_mul]

theorem blockDetectingWeight_primeSum_zero
    {n m l₁ l₂ j a t N c : ℕ}
    (_hn : 0 < n) (hlog : 2 ≤ Real.log (n : ℝ)) (hN : 1 < Real.log (N : ℝ))
    (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (hl₁n : l₁ ≤ n) (hl₂m : l₂ ≤ m)
    (hj : j < l₂) (ha : 0 < a)
    (hrel : ((m - j : ℕ) : ℝ) = (t : ℝ) / a * n)
    (havoid : longBlockSigma n ≤ plateauWidth N / 12)
    (hL : max l₁ l₂ < longBlockPrimeScale n (max l₁ l₂))
    (hc : c < longBlockPrimeScale n (max l₁ l₂))
    (hsmall : 2 * max l₁ l₂ ≤ (longBlockPrimeScale n (max l₁ l₂)) ^ 2)
    (hscale : (max l₁ l₂ : ℕ) ≤ plateauWidth N / 12 *
      (longBlockPrimeScale n (max l₁ l₂) : ℝ) ^ 2)
    (hsq : IsSquare (falling n l₁ * falling m l₂ * c.factorial)) :
    primeEquidistributionSum (longBlockPrimeScale n (max l₁ l₂) : ℝ)
      (Ico (longBlockPrimeScale n (max l₁ l₂) : ℝ)
        (2 * (longBlockPrimeScale n (max l₁ l₂) : ℝ)))
      (blockDetectingWeight n m N (longBlockPrimeScale n (max l₁ l₂)) l₁ l₂ j a t)
      n (selectedBlockCenter n m l₁ l₂ j) 2 = 0 := by
  classical
  let L := max l₁ l₂
  let P := longBlockPrimeScale n L
  have hP : 2 ≤ P := by dsimp only [P, L]; omega
  unfold primeEquidistributionSum
  apply Finset.sum_eq_zero
  intro p hp
  have hpdata : p.Prime ∧ (p : ℝ) ∈ Ico (P : ℝ) (2 * P) :=
    (mem_primesInScaleSet (by exact_mod_cast hP)
      (fun _ hx => ⟨hx.1, hx.2.le⟩)).mp hp
  have hprime : p.Prime := hpdata.1
  have hPp : P ≤ p := by exact_mod_cast hpdata.2.1
  have hpP : p ≤ 2 * P := by
    have h : (p : ℝ) < 2 * P := hpdata.2.2
    exact_mod_cast h.le
  by_contra hweight
  change blockDetectingWeight n m N P l₁ l₂ j a t
    ((n : ℝ) / p, (selectedBlockCenter n m l₁ l₂ j : ℝ) / (p : ℝ) ^ 2) ≠ 0 at hweight
  have hH : blockSeparator n N P l₁ l₂ j
      ((n : ℝ) / p, (t : ℝ) / a * ((n : ℝ) / p)) ≠ 0 := by
    intro hh
    exact hweight (by simp only [blockDetectingWeight, pairedWeight, hh, zero_mul])
  have hG : longBlockSquareWeight N (selectedBlockCenter n m l₁ l₂ j) P
      ((selectedBlockCenter n m l₁ l₂ j : ℝ) / (p : ℝ) ^ 2) ≠ 0 := by
    intro hh
    exact hweight (by simp only [blockDetectingWeight, pairedWeight, secondWeightLift,
      hh, Complex.ofReal_zero, mul_zero])
  rcases blockSeparator_nonzero_selects_odd_prime hlog hN hl₁ hl₂ hl₁n hl₂m hj ha
    hrel hprime hPp hpP havoid hH with hupper | hlower
  · obtain ⟨hdom, ⟨v, hv, hpv⟩, hfree⟩ := hupper
    have hR : selectedBlockCenter n m l₁ l₂ j = n := if_pos hdom
    rw [hR] at hG
    have hclose₁ : |(n : ℝ) - v| ≤ (l₁ : ℝ) := by
      simpa only [Nat.sub_zero] using
        (block_term_close_to_shift (j := 0) hl₁n (by omega : 0 < l₁) hv)
    have hclose : |(n : ℝ) - v| ≤ L :=
      hclose₁.trans (by exact_mod_cast le_max_left l₁ l₂)
    have hvpos : 0 < v := by have := (Finset.mem_Ioc.mp hv).1; omega
    have hsqfree := longBlockSquareWeight_not_sq_dvd hN hprime.pos hPp hvpos hclose hsmall hscale hG
    exact (not_square_of_selected_block_prime hl₁n hl₂m hprime
      (((le_max_left l₁ l₂).trans_lt hL).trans_le hPp) (hc.trans_le hPp)
      hv hpv hsqfree hfree) hsq
  · obtain ⟨hdom, ⟨v, hv, hpv⟩, hfree⟩ := hlower
    have hR : selectedBlockCenter n m l₁ l₂ j = m - j := if_neg (not_le_of_gt hdom)
    rw [hR] at hG
    have hclose : |((m - j : ℕ) : ℝ) - v| ≤ L :=
      (block_term_close_to_shift hl₂m hj hv).trans (by exact_mod_cast le_max_right l₁ l₂)
    have hvpos : 0 < v := by have := (Finset.mem_Ioc.mp hv).1; omega
    have hsqfree := longBlockSquareWeight_not_sq_dvd hN hprime.pos hPp hvpos hclose hsmall hscale hG
    have hnot := not_square_of_selected_block_prime hl₂m hl₁n hprime
      (((le_max_right l₁ l₂).trans_lt hL).trans_le hPp) (hc.trans_le hPp)
      hv hpv hsqfree hfree
    apply hnot
    convert hsq using 1
    ring

theorem blockDetectingWeight_integral_lower
    {n m l₁ l₂ j a t N P : ℕ}
    (hn : 0 < n) (hmn : m < n) (hl₂m : l₂ ≤ m) (hj : j < l₂)
    (hlog : 1 < Real.log (n : ℝ)) (hN : 1 < Real.log (N : ℝ))
    (hd : plateauWidth N < 1 / 100) (ht : 0 < t) (hta : t < a)
    (hP : 2 ≤ P) (hPn : 2 * P ≤ n)
    (hslow : 200 * (a : ℝ) ≤ P) (hboundary : (a : ℝ) ≤ (n : ℝ) / (32 * P)) :
    (P : ℝ) / (57600000 * (Real.log n) ^ 3) ≤
      ‖primeEquidistributionIntegral (Ico (P : ℝ) (2 * P))
        (blockDetectingWeight n m N P l₁ l₂ j a t) n
        (selectedBlockCenter n m l₁ l₂ j) 2‖ := by
  have hM := selectedBlockCenter_pos_le (l₁ := l₁) hn hmn hl₂m hj
  have haR : (0 : ℝ) < a := by exact_mod_cast (lt_trans ht hta)
  have hb : 0 ≤ longBlockSigma n / 1800000 := by unfold longBlockSigma; positivity
  have hmass := longBlockSquareWeight_reciprocal_mass hn hM.1 (by omega : 0 < P) hM.2
    hN hd haR hb hslow hboundary
    (blockSeparatorReal_continuous _ _ _ _ _ _ _ _)
    (blockSeparatorReal_nonneg _ _ _ _ _ _ _ _)
    (blockSeparatorReal_periodic _ _ _ _ _ _ (lt_trans ht hta))
    (blockSeparatorReal_period_mass hlog hN hd.le ht hta P l₁ l₂ j)
  have h := prime_integral_norm_lower_of_real_reciprocal_mass hn hP hPn hb
    (blockDetectingReal_continuous _ _ _ _ _ _ _ _ _)
    (blockDetectingReal_nonneg _ _ _ _ _ _ _ _ _)
    (blockDetectingWeight_eval hn m N P l₁ l₂ j a t) hmass
  have hid : (longBlockSigma n / 1800000) * (P : ℝ) / (32 * Real.log n) =
      (P : ℝ) / (57600000 * (Real.log n) ^ 3) := by
    unfold longBlockSigma
    field_simp
    ring
  simpa only [hid] using h

end
end Erdos374Research
