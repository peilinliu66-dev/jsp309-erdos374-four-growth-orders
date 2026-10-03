import Tao2026.BurgessWeilPrimeSimpleRoot
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
UNCOMPILED. Square-value residue counts for a nonzero scalar times a product
of distinct linear factors. The sharp character-sum estimate is the actual
public Tao2026 Stepanov/Newton proof at smccolm/Lean commit
91604dfc9733555f0b762594cd434450728d3d8c. This module supplies the finite
quadratic-character cardinality adapter used in Yudin's sieve arguments.
-/

namespace Erdos374Research

open Tao2026 Finset Polynomial
open scoped BigOperators Classical

noncomputable section

def complexQuadraticChar (p : ℕ) [NeZero p] [Fact p.Prime] : MulChar (ZMod p) ℂ := by
  classical
  exact (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

lemma complexQuadraticChar_apply (p : ℕ) [NeZero p] [Fact p.Prime] (x : ZMod p) :
    complexQuadraticChar p x = (quadraticChar (ZMod p) x : ℂ) := rfl

lemma complexQuadraticChar_ne_one (p : ℕ) [NeZero p] [Fact p.Prime] (hp2 : p ≠ 2) :
    complexQuadraticChar p ≠ 1 := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  exact (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).2
    (quadraticChar_ne_one hchar)

lemma norm_complexQuadraticChar_of_ne_zero (p : ℕ) [NeZero p] [Fact p.Prime]
    {x : ZMod p} (hx : x ≠ 0) : ‖complexQuadraticChar p x‖ = 1 := by
  classical
  rw [complexQuadraticChar_apply]
  rcases quadraticChar_dichotomy hx with h | h <;> simp [h]

def splitValue {p : ℕ} (coeff : ZMod p) (s : Finset (ZMod p)) (x : ZMod p) : ZMod p :=
  coeff * ∏ r ∈ s, (x - r)

def splitSquareResidues (p : ℕ) [NeZero p] (coeff : ZMod p) (s : Finset (ZMod p)) :
    Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun x => IsSquare (splitValue coeff s x)

lemma splitValue_eq_zero_iff {p : ℕ} [NeZero p] [Fact p.Prime]
    {coeff : ZMod p} (hcoeff : coeff ≠ 0) (s : Finset (ZMod p)) (x : ZMod p) :
    splitValue coeff s x = 0 ↔ x ∈ s := by
  classical
  simp only [splitValue, mul_eq_zero, hcoeff, false_or, Finset.prod_eq_zero_iff,
    sub_eq_zero]
  constructor
  · rintro ⟨r, hr, hxr⟩
    simpa only [hxr] using hr
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma eval_finsetRootPolynomial (p : ℕ) [NeZero p] [Fact p.Prime]
    (s : Finset (ZMod p)) (x : ZMod p) :
    (primeKummerRootMultisetPolynomial s.val).eval x = ∏ r ∈ s, (x - r) := by
  classical
  change (∏ r ∈ s, (Polynomial.X - Polynomial.C r)).eval x = _
  simp [Polynomial.eval_prod]

lemma norm_sum_complexQuadraticChar_splitValue_le
    (p : ℕ) [NeZero p] [Fact p.Prime] (hp2 : p ≠ 2)
    {coeff : ZMod p} (hcoeff : coeff ≠ 0) (s : Finset (ZMod p)) (hs : s.Nonempty) :
    ‖∑ x : ZMod p, complexQuadraticChar p (splitValue coeff s x)‖ ≤
      (s.card - 1 : ℕ) * Real.sqrt p := by
  classical
  obtain ⟨a, ha⟩ := hs
  let P := primeKummerRootMultisetPolynomial s.val
  have hroot : P.rootMultiplicity a = 1 := by
    rw [primeKummerRootMultisetPolynomial_rootMultiplicity]
    exact Multiset.count_eq_one_of_mem s.nodup ha
  have hweil := norm_primePolynomialCharacterCorrelation_le_of_monic_split_simple_root
    p (complexQuadraticChar p) (complexQuadraticChar_ne_one p hp2) P
    (primeKummerRootMultisetPolynomial_splits s.val)
    (primeKummerRootMultisetPolynomial_monic s.val) a hroot
  have hroots : P.roots.toFinset.card = s.card := by
    simp only [P, primeKummerRootMultisetPolynomial_roots, Finset.val_toFinset]
  rw [hroots] at hweil
  have hsum : (∑ x : ZMod p, complexQuadraticChar p (splitValue coeff s x)) =
      complexQuadraticChar p coeff * primePolynomialCharacterCorrelation p
        (complexQuadraticChar p) P := by
    unfold primePolynomialCharacterCorrelation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [splitValue, map_mul, eval_finsetRootPolynomial]
  rw [hsum, norm_mul, norm_complexQuadraticChar_of_ne_zero p hcoeff, one_mul]
  exact hweil

lemma quadratic_square_indicator {p : ℕ} [NeZero p] [Fact p.Prime] (x : ZMod p) :
    2 * (if IsSquare x then (1 : ℝ) else 0) =
      1 + (quadraticChar (ZMod p) x : ℝ) + (if x = 0 then 1 else 0) := by
  classical
  by_cases hx : x = 0
  · norm_num [hx, IsSquare.zero]
  · by_cases hs : IsSquare x
    · rw [(quadraticChar_one_iff_isSquare hx).2 hs]
      norm_num [hs, hx]
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hs]
      norm_num [hs, hx]

lemma sum_indicator_eq_card {F : Type*} [Fintype F] (S : F → Prop) [DecidablePred S] :
    (∑ x : F, if S x then (1 : ℝ) else 0) =
      ((Finset.univ.filter S).card : ℝ) := by
  classical
  exact Finset.sum_boole S Finset.univ

lemma splitSquareResidues_card_identity
    (p : ℕ) [NeZero p] [Fact p.Prime] {coeff : ZMod p} (hcoeff : coeff ≠ 0)
    (s : Finset (ZMod p)) :
    2 * ((splitSquareResidues p coeff s).card : ℝ) =
      (p : ℝ) + (∑ x : ZMod p, (quadraticChar (ZMod p) (splitValue coeff s x) : ℝ)) +
        s.card := by
  classical
  have hzeros : (Finset.univ.filter fun x : ZMod p => splitValue coeff s x = 0) = s := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, splitValue_eq_zero_iff hcoeff]
  calc
    2 * ((splitSquareResidues p coeff s).card : ℝ) =
        ∑ x : ZMod p, 2 * (if IsSquare (splitValue coeff s x) then (1 : ℝ) else 0) := by
      rw [← Finset.mul_sum, sum_indicator_eq_card]
      rfl
    _ = ∑ x : ZMod p, (1 + (quadraticChar (ZMod p) (splitValue coeff s x) : ℝ) +
        (if splitValue coeff s x = 0 then 1 else 0)) :=
      Finset.sum_congr rfl fun x _ => quadratic_square_indicator (splitValue coeff s x)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_indicator_eq_card, hzeros]
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

/-- Generic sharp square-value residue bound, including the zeros of the
polynomial. A nonempty finite set supplies distinct roots and a simple root;
the scalar coefficient can be any nonzero field element. -/
theorem card_splitSquareResidues_le
    (p : ℕ) [NeZero p] [Fact p.Prime] (hp2 : p ≠ 2)
    {coeff : ZMod p} (hcoeff : coeff ≠ 0) (s : Finset (ZMod p)) (hs : s.Nonempty) :
    ((splitSquareResidues p coeff s).card : ℝ) ≤
      ((p : ℝ) + s.card + (s.card - 1 : ℕ) * Real.sqrt p) / 2 := by
  classical
  have hid := splitSquareResidues_card_identity p hcoeff s
  have hweil := norm_sum_complexQuadraticChar_splitValue_le p hp2 hcoeff s hs
  have hre : (∑ x : ZMod p, (quadraticChar (ZMod p) (splitValue coeff s x) : ℝ)) ≤
      ‖∑ x : ZMod p, complexQuadraticChar p (splitValue coeff s x)‖ := by
    have hcast : (∑ x : ZMod p, complexQuadraticChar p (splitValue coeff s x)) =
        ((∑ x : ZMod p, quadraticChar (ZMod p) (splitValue coeff s x) : ℤ) : ℂ) := by
      simp only [complexQuadraticChar_apply, Int.cast_sum]
    rw [hcast, Complex.norm_intCast, Int.cast_sum]
    exact le_abs_self _
  linarith

end
end Erdos374Research
