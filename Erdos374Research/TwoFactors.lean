import Erdos374Research.OrderedRepresentations
import Tao2026.ErdosSelfridgeComplete
import Tao2026.FactorialOneTerm

/-!
# Exact two-factor classification

UNCOMPILED. The nonconsecutive case uses the public square specialization
of Erdős--Selfridge. Its dependency is stated in the import, not introduced
as a new axiom or as a premise of the final classification.
-/

namespace Erdos374Research

theorem hasRepresentation_two_iff_square {n : ℕ} :
    HasRepresentation 2 n ↔ 4 ≤ n ∧ IsSquare n := by
  rw [hasRepresentation_two_iff]
  constructor
  · rintro ⟨a, ha, han, r, hr⟩
    have hcomp : Tao2026.squarefreeComponent a.factorial =
        Tao2026.squarefreeComponent n.factorial :=
      (Tao2026.squarefreeComponent_eq_iff_mul_eq_sq
        (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero n)).mpr
          ⟨r, by simpa only [pow_two] using hr⟩
    have hblock :=
      (Tao2026.squarefreeComponent_factorial_eq_iff_consecutiveProduct_square han.le).mp hcomp
    have hgap : n - a < 2 := by
      by_contra hnot
      exact Tao2026.erdosSelfridgeSquare a (n - a) (by omega) hblock
    have hnext : n = a + 1 := by omega
    rw [hnext] at hcomp
    obtain ⟨q, hq⟩ := (Tao2026.squarefreeComponent_factorial_succ_eq_iff_square a).mp hcomp
    have hnq : n = q ^ 2 := hnext.trans hq
    have hq2 : 2 ≤ q := by
      have hn2 : 2 ≤ n := by omega
      nlinarith
    exact ⟨by nlinarith, q, by simpa only [pow_two] using hnq⟩
  · rintro ⟨hn, q, hq⟩
    refine ⟨n - 1, by omega, by omega, q * (n - 1).factorial, ?_⟩
    calc
      (n - 1).factorial * n.factorial = n * (n - 1).factorial ^ 2 := by
        rw [mul_comm, paired_factorials (by omega)]
      _ = (q * (n - 1).factorial) * (q * (n - 1).factorial) := by
        rw [hq]
        ring

theorem isInD_two_iff_square {n : ℕ} : IsInD 2 n ↔ 4 ≤ n ∧ IsSquare n := by
  constructor
  · intro h
    exact hasRepresentation_two_iff_square.mp h.2.1
  · intro h
    refine ⟨by decide, hasRepresentation_two_iff_square.mpr h, ?_⟩
    intro j hj hj2
    omega

theorem numbersInD_two_eq_squares (X : ℕ) :
    numbersInDUpTo 2 X = Tao2026.nontrivialSquaresUpTo X := by
  classical
  ext n
  rw [mem_numbersInDUpTo]
  simp only [Tao2026.nontrivialSquaresUpTo, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨hn1, hnX, hnD⟩
    obtain ⟨hn4, q, hq⟩ := isInD_two_iff_square.mp hnD
    have hq2 : 2 ≤ q := by nlinarith
    refine ⟨q, ⟨hq2, ?_⟩, ?_⟩
    · rw [Nat.le_sqrt]
      nlinarith
    · simpa only [pow_two] using hq.symm
  · rintro ⟨q, ⟨hq2, hqX⟩, rfl⟩
    have hqSqX : q ^ 2 ≤ X :=
      (Nat.pow_le_pow_left hqX 2).trans (Nat.sqrt_le' X)
    refine ⟨by nlinarith, hqSqX, isInD_two_iff_square.mpr ?_⟩
    exact ⟨by nlinarith, q, by ring⟩

theorem countD_two (X : ℕ) : countD 2 X = Nat.sqrt X - 1 := by
  unfold countD
  rw [numbersInD_two_eq_squares, Tao2026.card_nontrivialSquaresUpTo]

theorem isInD_three_of_representation_of_not_square {n : ℕ}
    (hrep : HasRepresentation 3 n) (hnsq : ¬ IsSquare n) : IsInD 3 n := by
  refine ⟨by decide, hrep, ?_⟩
  intro j hj hj3 hjrep
  have hj2 : j = 2 := by omega
  subst j
  exact hnsq (hasRepresentation_two_iff_square.mp hjrep).2

end Erdos374Research
