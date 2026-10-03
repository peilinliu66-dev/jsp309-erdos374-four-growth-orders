import Erdos374Research.TranslatedPlateau

/-!
# A smooth periodic weight excluding neighborhoods of the integers

UNCOMPILED. This explicit complement of a translated source plateau is the
quadratic-reciprocal detector used to exclude divisibility by p². Its support
and plateau conditions are proved for every integer, not sampled phases.
-/

namespace Erdos374Research

open Tao2026
open scoped ContDiff

noncomputable def plateauWidth (N : ℕ) : ℝ := 1 / (10 * (Real.log N) ^ 2)

noncomputable def integerAvoidingWeight (N : ℕ) (x : ℝ) : ℝ :=
  1 - shiftedPlateau N (5 * plateauWidth N / 12) x

theorem plateauWidth_pos {N : ℕ} (hN : 1 < Real.log (N : ℝ)) : 0 < plateauWidth N := by
  unfold plateauWidth
  positivity

theorem plateauWidth_lt_tenth {N : ℕ} (hN : 1 < Real.log (N : ℝ)) :
    plateauWidth N < 1 / 10 := by
  unfold plateauWidth
  have hsq : 1 < (Real.log (N : ℝ)) ^ 2 := by nlinarith
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 10 * (Real.log N) ^ 2)).mpr
  nlinarith

theorem integerAvoidingWeight_contDiff (N : ℕ) : ContDiff ℝ ∞ (integerAvoidingWeight N) :=
  contDiff_const.sub (shiftedPlateau_contDiff _ _)

theorem integerAvoidingWeight_periodic (N : ℕ) :
    Function.Periodic (integerAvoidingWeight N) 1 := by
  intro x
  unfold integerAvoidingWeight
  rw [shiftedPlateau_periodic N (5 * plateauWidth N / 12) x]

theorem integerAvoidingWeight_nonneg (N : ℕ) (x : ℝ) : 0 ≤ integerAvoidingWeight N x := by
  unfold integerAvoidingWeight
  linarith [shiftedPlateau_le_one N (5 * plateauWidth N / 12) x]

theorem integerAvoidingWeight_le_one (N : ℕ) (x : ℝ) : integerAvoidingWeight N x ≤ 1 := by
  unfold integerAvoidingWeight
  linarith [shiftedPlateau_nonneg N (5 * plateauWidth N / 12) x]

theorem integerAvoidingWeight_zero_near_integer {N : ℕ}
    (hN : 1 < Real.log (N : ℝ)) {x : ℝ} (k : ℤ)
    (hx : |x - (k : ℝ)| ≤ plateauWidth N / 12) :
    integerAvoidingWeight N x = 0 := by
  let d := plateauWidth N
  let c := 5 * d / 12
  have hd : 0 < d := plateauWidth_pos hN
  have hdsmall : d < 1 / 10 := plateauWidth_lt_tenth hN
  have habs := abs_le.mp hx
  change -(d / 12) ≤ x - (k : ℝ) ∧ x - (k : ℝ) ≤ d / 12 at habs
  have hfloor : ⌊x - c⌋ = k - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> dsimp [c] <;> linarith
  have hfract : Int.fract (x - c) = x - c - (k : ℝ) + 1 := by
    rw [Int.fract, hfloor]
    push_cast
    ring
  have hlogne : Real.log (N : ℝ) ≠ 0 := by linarith
  have hleft : factorialPlateauArcLeft N = 1 - d / 2 := by
    dsimp [factorialPlateauArcLeft, d, plateauWidth]
    field_simp [hlogne]
    ring
  have hright : factorialPlateauArcRight N = 1 - d / 3 := by
    dsimp [factorialPlateauArcRight, d, plateauWidth]
    field_simp [hlogne]
    ring
  have hplateau : shiftedPlateau N c x = 1 := by
    apply shiftedPlateau_eq_one hN
    · rw [hleft, hfract]
      dsimp [c]
      linarith
    · rw [hright, hfract]
      dsimp [c]
      linarith
  change 1 - shiftedPlateau N c x = 0
  rw [hplateau]
  ring

theorem integerAvoidingWeight_eq_one_far {N : ℕ}
    (hN : 1 < Real.log (N : ℝ)) {x : ℝ}
    (hx : ∀ k : ℤ, plateauWidth N < |x - (k : ℝ)|) :
    integerAvoidingWeight N x = 1 := by
  let d := plateauWidth N
  let c := 5 * d / 12
  have hd : 0 < d := plateauWidth_pos hN
  have hw : shiftedPlateau N c x = 0 := by
    by_contra hne
    have hs := shiftedPlateau_supported hN hne
    change 1 - d ≤ Int.fract (x - c) at hs
    have ht : Int.fract (x - c) < 1 := Int.fract_lt_one _
    let k : ℤ := ⌊x - c⌋ + 1
    have hid : x - (k : ℝ) = c + Int.fract (x - c) - 1 := by
      change x - ((⌊x - c⌋ + 1 : ℤ) : ℝ) =
        c + (x - c - (⌊x - c⌋ : ℝ)) - 1
      rw [Int.cast_add, Int.cast_one]
      ring
    have hdist : |x - (k : ℝ)| ≤ d := by
      rw [hid]
      apply abs_le.mpr
      dsimp [c]
      constructor <;> linarith
    exact (not_lt_of_ge hdist) (hx k)
  change 1 - shiftedPlateau N c x = 1
  rw [hw]
  ring

theorem integerAvoidingWeight_ne_zero_imp_far {N : ℕ}
    (hN : 1 < Real.log (N : ℝ)) {x : ℝ}
    (hx : integerAvoidingWeight N x ≠ 0) (k : ℤ) :
    plateauWidth N / 12 < |x - (k : ℝ)| := by
  by_contra hnot
  exact hx (integerAvoidingWeight_zero_near_integer hN k (le_of_not_gt hnot))

/-- Nonzero detector weight excludes the square of the candidate prime
from every integer in the selected block. No primality is needed for this
pure divisibility implication. -/
theorem not_sq_dvd_of_integerAvoidingWeight {N p v : ℕ} {M L : ℝ}
    (hN : 1 < Real.log (N : ℝ)) (hp : 0 < p)
    (hclose : |M - (v : ℝ)| ≤ L)
    (hscale : L ≤ plateauWidth N / 12 * (p : ℝ) ^ 2)
    (hweight : integerAvoidingWeight N (M / (p : ℝ) ^ 2) ≠ 0) :
    ¬ p ^ 2 ∣ v := by
  rintro ⟨k, hk⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpSq : (0 : ℝ) < (p : ℝ) ^ 2 := sq_pos_of_pos hpR
  have hv : (v : ℝ) = (p : ℝ) ^ 2 * k := by exact_mod_cast hk
  have hid : M / (p : ℝ) ^ 2 - (k : ℝ) = (M - v) / (p : ℝ) ^ 2 := by
    rw [hv]
    field_simp
  have hnear : |M / (p : ℝ) ^ 2 - (k : ℝ)| ≤ plateauWidth N / 12 := by
    rw [hid, abs_div, abs_of_pos hpSq]
    exact (div_le_iff₀ hpSq).mpr (hclose.trans hscale)
  have hfar := integerAvoidingWeight_ne_zero_imp_far hN hweight (k : ℤ)
  simp only [Int.cast_natCast] at hfar
  exact (not_lt_of_ge hnear) hfar

end Erdos374Research
