import Erdos374Research.LargerSieve
import Erdos374Research.ConsecutiveResidues
import Erdos374Research.WeightedPrimeLogs

/-! UNCOMPILED. The two prime families in the coarse Gallagher improvement
of the nonconsecutive three-factorial count. -/

namespace Erdos374Research

open Tao2026 Finset
open scoped BigOperators

noncomputable section

def hardFactorialFibre (X a H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun N => a < N ∧ N + H ≤ X ∧
    squarefreeComponent (consecutiveProduct N H) = squarefreeComponent a.factorial

lemma mem_hardFactorialFibre {X a H N : ℕ} :
    N ∈ hardFactorialFibre X a H ↔
      (1 ≤ N ∧ N ≤ X) ∧ a < N ∧ N + H ≤ X ∧
        squarefreeComponent (consecutiveProduct N H) = squarefreeComponent a.factorial := by
  classical
  simp only [hardFactorialFibre, Finset.mem_filter, Finset.mem_Icc]

lemma hardFactorialFibre_subset (X a H : ℕ) :
    hardFactorialFibre X a H ⊆ Finset.Icc 1 X := by
  intro N hN
  exact (Finset.mem_filter.mp hN).1

lemma hardFactorialFibre_upperHalf_residues {X a H p : ℕ}
    (ha : 1 ≤ a) (hp : p ∈ factorialUpperHalfPrimes a) :
    ((hardFactorialFibre X a H).image fun N => N % p).card ≤ H := by
  classical
  have hprime := (Finset.mem_filter.mp hp).2
  letI : NeZero p := ⟨hprime.ne_zero⟩
  have hmod := card_natMod_image_le_zmod_set p
    (hardFactorialFibre X a H) (factorialAllowedStartResidues p H) (by
      intro N hN
      have hd := mem_hardFactorialFibre.mp hN
      exact factorialThree_start_mem_allowedResidues ⟨ha, hd.2.1, hd.2.2.2⟩ hp)
  exact hmod.trans (card_factorialAllowedStartResidues_le p H)

lemma hardFactorialFibre_square_residues {X a H p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hap : a < p) (hH : 1 ≤ H) (hHp : H < p) :
    (((hardFactorialFibre X a H).image fun N => N % p).card : ℝ) ≤
      ((p : ℝ) + H + (H - 1 : ℕ) * Real.sqrt p) / 2 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hmod := card_natMod_image_le_zmod_set p
    (hardFactorialFibre X a H) (factorialSquareStartResidues p a H) (by
      intro N hN
      exact factorial_start_mem_squareResidues hHp
        (mem_hardFactorialFibre.mp hN).2.2.2)
  exact (show (((hardFactorialFibre X a H).image fun N => N % p).card : ℝ) ≤
      (factorialSquareStartResidues p a H).card by exact_mod_cast hmod).trans
    (card_factorialSquareStartResidues_le hp2 hap hH hHp)

lemma weil_residue_bound_le_kappa {p H : ℕ} (hp : 2 ≤ p) (hH : 1 ≤ H)
    (hsmall : 10000 * (H : ℝ) ≤ Real.sqrt p) :
    ((p : ℝ) + H + (H - 1 : ℕ) * Real.sqrt p) / 2 ≤
      (5001 / 10000 : ℝ) * p := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hsqrt0 := Real.sqrt_nonneg (p : ℝ)
  have hsqrtSq := Real.sq_sqrt (Nat.cast_nonneg p)
  have hsqrt1 : 1 ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hprod := mul_le_mul_of_nonneg_right hsmall hsqrt0
  have hHroot := mul_le_mul_of_nonneg_left hsqrt1 hH0
  rw [Nat.cast_sub hH, Nat.cast_one]
  nlinarith

def gallagherPrimeBand (Y Q : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 Q).filter Nat.Prime) \ ((Finset.Icc 2 Y).filter Nat.Prime)

lemma mem_gallagherPrimeBand {Y Q p : ℕ} :
    p ∈ gallagherPrimeBand Y Q ↔ p.Prime ∧ Y < p ∧ p ≤ Q := by
  classical
  simp only [gallagherPrimeBand, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hp2, hpQ⟩, hp⟩, hnot⟩
    refine ⟨hp, ?_, hpQ⟩
    by_contra h
    exact hnot ⟨⟨hp2, by omega⟩, hp⟩
  · rintro ⟨hp, hYp, hpQ⟩
    exact ⟨⟨⟨hp.two_le, hpQ⟩, hp⟩, fun h => by omega⟩

lemma gallagherPrimeBand_disjoint_upperHalf {a Y Q : ℕ} (haY : a ≤ Y) :
    Disjoint (factorialUpperHalfPrimes a) (gallagherPrimeBand Y Q) := by
  apply Finset.disjoint_left.mpr
  intro p hp0 hp1
  have hpA := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp0).1).2
  have hpY := (mem_gallagherPrimeBand.mp hp1).2.1
  omega

lemma hardFactorialFibre_band_residues {X a H Y Q p : ℕ}
    (haY : a ≤ Y) (hY : 2 ≤ Y) (hH : 1 ≤ H)
    (hsmall : 10000 * (H : ℝ) ≤ Real.sqrt Y)
    (hp : p ∈ gallagherPrimeBand Y Q) :
    (((hardFactorialFibre X a H).image fun N => N % p).card : ℝ) ≤
      (5001 / 10000 : ℝ) * p := by
  have hd := mem_gallagherPrimeBand.mp hp
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
  have hsqrtY : Real.sqrt (Y : ℝ) ≤ (Y : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨Nat.cast_nonneg Y, ?_⟩
    nlinarith [sq_nonneg ((Y : ℝ) - 1)]
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hHY : H ≤ Y := by
    have h : (H : ℝ) ≤ Y := by nlinarith
    exact_mod_cast h
  have hsqrt : Real.sqrt (Y : ℝ) ≤ Real.sqrt p := Real.sqrt_le_sqrt (by exact_mod_cast hd.2.1.le)
  exact (hardFactorialFibre_square_residues hd.1 (by omega)
    (lt_of_le_of_lt haY hd.2.1) hH (lt_of_le_of_lt hHY hd.2.1)).trans
    (weil_residue_bound_le_kappa hd.1.two_le hH (hsmall.trans hsqrt))

lemma gallagherPrimeBand_weighted_sum {Y Q : ℕ} (hYQ : Y ≤ Q) :
    (∑ p ∈ gallagherPrimeBand Y Q, Real.log (p : ℝ) / p) =
      weightedPrimeLogSum Q - weightedPrimeLogSum Y := by
  have hsub : (Finset.Icc 2 Y).filter Nat.Prime ⊆ (Finset.Icc 2 Q).filter Nat.Prime := by
    intro p hp
    have hd := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hd.1).1, (Finset.mem_Icc.mp hd.1).2.trans hYQ⟩, hd.2⟩
  exact Finset.sum_sdiff_eq_sub hsub

def gallagherFactorialResidueBudget (a H p : ℕ) : ℝ :=
  if p ∈ factorialUpperHalfPrimes a then (H : ℝ) else (5001 / 10000 : ℝ) * p

def gallagherFactorialDenominator (X a H Y Q : ℕ) : ℝ :=
  (∑ p ∈ factorialUpperHalfPrimes a, Real.log (p : ℝ)) / H +
    (10000 / 5001 : ℝ) * (weightedPrimeLogSum Q - weightedPrimeLogSum Y) - Real.log X

lemma gallagherFactorial_denominator_identity {X a H Y Q : ℕ}
    (haY : a ≤ Y) (hYQ : Y ≤ Q) :
    (∑ p ∈ factorialUpperHalfPrimes a ∪ gallagherPrimeBand Y Q,
        Real.log (p : ℝ) / gallagherFactorialResidueBudget a H p) - Real.log X =
      gallagherFactorialDenominator X a H Y Q := by
  classical
  have hdisj := gallagherPrimeBand_disjoint_upperHalf (Q := Q) haY
  rw [Finset.sum_union hdisj]
  have hzero :
      (∑ p ∈ factorialUpperHalfPrimes a, Real.log (p : ℝ) /
        gallagherFactorialResidueBudget a H p) =
      (∑ p ∈ factorialUpperHalfPrimes a, Real.log (p : ℝ)) / H := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [gallagherFactorialResidueBudget, hp, if_true]
  have hone :
      (∑ p ∈ gallagherPrimeBand Y Q, Real.log (p : ℝ) /
        gallagherFactorialResidueBudget a H p) =
      (10000 / 5001 : ℝ) * (weightedPrimeLogSum Q - weightedPrimeLogSum Y) := by
    rw [← gallagherPrimeBand_weighted_sum hYQ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hnot : p ∉ factorialUpperHalfPrimes a := by
      intro hp0
      exact Finset.disjoint_left.mp hdisj hp0 hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_gallagherPrimeBand.mp hp).1.ne_zero
    simp only [gallagherFactorialResidueBudget, hnot, if_false]
    field_simp [hp0]
  rw [hzero, hone]
  rfl

lemma primeRange_log_sum_eq_theta (Q : ℕ) :
    (∑ p ∈ (Finset.Icc 2 Q).filter Nat.Prime, Real.log (p : ℝ)) = Chebyshev.theta Q := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp2, hpQ⟩, hp⟩
      exact ⟨⟨Nat.zero_le _, hpQ⟩, hp⟩
    · rintro ⟨⟨hp0, hpQ⟩, hp⟩
      exact ⟨⟨hp.two_le, hpQ⟩, hp⟩
  · intro p hp
    rfl

lemma gallagherPrimeBand_log_sum_le_theta (Y Q : ℕ) :
    (∑ p ∈ gallagherPrimeBand Y Q, Real.log (p : ℝ)) ≤ Chebyshev.theta Q := by
  rw [← primeRange_log_sum_eq_theta]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.sdiff_subset
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)

lemma gallagher_log_numerator_le {X a Y Q : ℕ} (hX : 1 ≤ X)
    (haY : a ≤ Y) (hYQ : Y ≤ Q) :
    (∑ p ∈ factorialUpperHalfPrimes a ∪ gallagherPrimeBand Y Q,
        Real.log (p : ℝ)) - Real.log X ≤ 4 * (Q : ℝ) := by
  classical
  have hdisj := gallagherPrimeBand_disjoint_upperHalf (Q := Q) haY
  rw [Finset.sum_union hdisj]
  have hfirst : (∑ p ∈ factorialUpperHalfPrimes a, Real.log (p : ℝ)) ≤
      Chebyshev.theta a := by
    rw [sum_log_factorialUpperHalfPrimes_eq_theta_sub]
    exact sub_le_self _ (Chebyshev.theta_nonneg _)
  have hsecond := gallagherPrimeBand_log_sum_le_theta Y Q
  have hthetaA := Chebyshev.theta_le_log4_mul_x (x := (a : ℝ)) (Nat.cast_nonneg a)
  have hthetaQ := Chebyshev.theta_le_log4_mul_x (x := (Q : ℝ)) (Nat.cast_nonneg Q)
  have haQ : (a : ℝ) ≤ Q := by exact_mod_cast haY.trans hYQ
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4upper : Real.log 4 ≤ 2 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hcompare := mul_le_mul_of_nonneg_left haQ hlog4
  have hcompare2 := mul_le_mul_of_nonneg_right hlog4upper (Nat.cast_nonneg Q)
  linarith

/-- Exact finite hard-fibre bound. All two-prime-family residue restrictions
are proved here; the remaining denominator inequality is numerical and is
handled uniformly by the subsequent large-X estimates. -/
theorem hardFactorialFibre_card_le {X a H Y Q : ℕ}
    (hX : 1 ≤ X) (ha : 1 ≤ a) (hH : 1 ≤ H) (haY : a ≤ Y)
    (hY : 2 ≤ Y) (hYQ : Y ≤ Q)
    (hsmall : 10000 * (H : ℝ) ≤ Real.sqrt Y)
    (hpositive : 0 < gallagherFactorialDenominator X a H Y Q) :
    ((hardFactorialFibre X a H).card : ℝ) ≤
      4 * (Q : ℝ) / gallagherFactorialDenominator X a H Y Q := by
  classical
  by_cases hempty : hardFactorialFibre X a H = ∅
  · simp only [hempty, Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (by positivity) hpositive.le
  have hsne := Finset.nonempty_iff_ne_empty.mpr hempty
  let ps := factorialUpperHalfPrimes a ∪ gallagherPrimeBand Y Q
  have hprime : ∀ p ∈ ps, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).2
    · exact (mem_gallagherPrimeBand.mp hp).1
  have hw : ∀ p ∈ ps, 0 ≤ Real.log (p : ℝ) := by
    intro p hp
    exact Real.log_nonneg (by exact_mod_cast (hprime p hp).one_lt.le)
  have hrho : ∀ p ∈ ps, 0 < gallagherFactorialResidueBudget a H p := by
    intro p hp
    unfold gallagherFactorialResidueBudget
    split_ifs
    · exact_mod_cast (show 0 < H by omega)
    · have hpR : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
      positivity
  have himage : ∀ p ∈ ps,
      (((hardFactorialFibre X a H).image fun N => N % p).card : ℝ) ≤
        gallagherFactorialResidueBudget a H p := by
    intro p hp
    by_cases hp0 : p ∈ factorialUpperHalfPrimes a
    · simp only [gallagherFactorialResidueBudget, hp0, if_true]
      exact_mod_cast hardFactorialFibre_upperHalf_residues (X := X) (H := H) ha hp0
    · have hp1 : p ∈ gallagherPrimeBand Y Q := (Finset.mem_union.mp hp).resolve_left hp0
      simpa only [gallagherFactorialResidueBudget, hp0, if_false] using
        hardFactorialFibre_band_residues (X := X) haY hY hH hsmall hp1
  have hs := largerSieve_weighted (hardFactorialFibre X a H) hsne ps
    (fun p N => N % p) (fun p => Real.log (p : ℝ))
    (gallagherFactorialResidueBudget a H) hw hrho himage (by
      intro x hx y hy hne
      exact residuePairWeight_log_le hprime (hardFactorialFibre_subset X a H) hx hy hne)
  have hden := gallagherFactorial_denominator_identity (X := X) (H := H) haY hYQ
  change (∑ p ∈ ps, Real.log (p : ℝ) / gallagherFactorialResidueBudget a H p) -
    Real.log X = gallagherFactorialDenominator X a H Y Q at hden
  rw [hden] at hs
  exact (le_div_iff₀ hpositive).2 (hs.trans (gallagher_log_numerator_le hX haY hYQ))

end
end Erdos374Research
