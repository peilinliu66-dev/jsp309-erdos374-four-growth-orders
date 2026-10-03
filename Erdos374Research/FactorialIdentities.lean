import Erdos374Research.Definitions
import Tao2026.FactorialIntervals

/-!
# Exact factorial-square identities

UNCOMPILED. The four- and six-factor constructions are the classical
Erdős--Graham identities recalled by Yudin; the five-factor construction is
attributed there to Straus. These algebraic identities do not assert that
their indices are distinct or that the number of factors is minimal.
Those conditions are kept as separate obligations in the counting proof.
-/

namespace Erdos374Research

open Finset
open scoped BigOperators

theorem factorial_eq_mul_pred {n : ℕ} (hn : 1 ≤ n) :
    n.factorial = n * (n - 1).factorial := by
  have heq : n - 1 + 1 = n := by omega
  simpa only [heq] using Nat.factorial_succ (n - 1)

theorem paired_factorials {n : ℕ} (hn : 1 ≤ n) :
    n.factorial * (n - 1).factorial = n * (n - 1).factorial ^ 2 := by
  rw [factorial_eq_mul_pred hn]
  ring

theorem four_factorial_identity {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (v ^ 2 * u).factorial * (v ^ 2 * u - 1).factorial *
        u.factorial * (u - 1).factorial =
      (v * u * (v ^ 2 * u - 1).factorial * (u - 1).factorial) ^ 2 := by
  have hn : 1 ≤ v ^ 2 * u := by nlinarith
  calc
    _ = ((v ^ 2 * u).factorial * (v ^ 2 * u - 1).factorial) *
        (u.factorial * (u - 1).factorial) := by ring
    _ = (v ^ 2 * u * (v ^ 2 * u - 1).factorial ^ 2) *
        (u * (u - 1).factorial ^ 2) := by
      rw [paired_factorials hn, paired_factorials hu]
    _ = _ := by ring

theorem six_factorial_identity {a p : ℕ} (ha : 1 ≤ a) (hp : 1 ≤ p) :
    (a * p).factorial * (a * p - 1).factorial *
        a.factorial * (a - 1).factorial * p.factorial * (p - 1).factorial =
      (a * p * (a * p - 1).factorial * (a - 1).factorial * (p - 1).factorial) ^ 2 := by
  have hn : 1 ≤ a * p := Nat.mul_pos ha hp
  calc
    _ = ((a * p).factorial * (a * p - 1).factorial) *
        (a.factorial * (a - 1).factorial) *
        (p.factorial * (p - 1).factorial) := by ring
    _ = (a * p * (a * p - 1).factorial ^ 2) *
        (a * (a - 1).factorial ^ 2) *
        (p * (p - 1).factorial ^ 2) := by
      rw [paired_factorials hn, paired_factorials ha, paired_factorials hp]
    _ = _ := by ring

theorem five_factorial_identity {n m c w : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hsq : n * m * c.factorial = w ^ 2) :
    n.factorial * (n - 1).factorial * m.factorial * (m - 1).factorial * c.factorial =
      (w * (n - 1).factorial * (m - 1).factorial) ^ 2 := by
  calc
    _ = (n.factorial * (n - 1).factorial) *
        (m.factorial * (m - 1).factorial) * c.factorial := by ring
    _ = (n * (n - 1).factorial ^ 2) *
        (m * (m - 1).factorial ^ 2) * c.factorial := by
      rw [paired_factorials hn, paired_factorials hm]
    _ = (n * m * c.factorial) * ((n - 1).factorial * (m - 1).factorial) ^ 2 := by ring
    _ = _ := by rw [hsq]; ring

theorem straus_identity {d b c w z : ℕ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (hz : 1 ≤ z)
    (hseed : d * b * c.factorial = w ^ 2) :
    (d * z).factorial * (d * z - 1).factorial *
        (b * z).factorial * (b * z - 1).factorial * c.factorial =
      (w * z * (d * z - 1).factorial * (b * z - 1).factorial) ^ 2 := by
  apply five_factorial_identity (Nat.mul_pos hd hz) (Nat.mul_pos hb hz)
  calc
    d * z * (b * z) * c.factorial = (d * b * c.factorial) * z ^ 2 := by ring
    _ = (w * z) ^ 2 := by rw [hseed]; ring

theorem straus_even_seed : (2 : ℕ) * 1 * Nat.factorial 2 = 2 ^ 2 := by norm_num
theorem straus_odd_seed : (3 : ℕ) * 2 * Nat.factorial 3 = 6 ^ 2 := by norm_num

/-- The factorial quotient is represented as an actual product, so no
truncating natural division can hide a nonintegral square root. -/
noncomputable def falling (n l : ℕ) : ℕ := Tao2026.consecutiveProduct (n - l) l

theorem falling_pos (n l : ℕ) : 0 < falling n l :=
  Nat.pos_of_ne_zero (Tao2026.consecutiveProduct_ne_zero (n - l) l)

theorem factorial_mul_falling {n l : ℕ} (hl : l ≤ n) :
    (n - l).factorial * falling n l = n.factorial := by
  have hsum : n - l + l = n := Nat.sub_add_cancel hl
  simpa only [falling, hsum] using
    Tao2026.factorial_mul_consecutiveProduct (n - l) l

theorem paired_block_factorials {n l : ℕ} (hl : l ≤ n) :
    n.factorial * (n - l).factorial = (n - l).factorial ^ 2 * falling n l := by
  rw [← factorial_mul_falling hl]
  ring

theorem square_mul_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSquare (a ^ 2 * b) ↔ IsSquare b := by
  constructor
  · rintro ⟨r, hr⟩
    have hr' : a ^ 2 * b = r ^ 2 := by simpa only [pow_two] using hr
    obtain ⟨s, hs⟩ := Tao2026.exists_eq_sq_of_sq_mul_eq_sq ha hb hr'
    exact ⟨s, by simpa only [pow_two] using hs⟩
  · rintro ⟨s, hs⟩
    refine ⟨a * s, ?_⟩
    rw [hs]
    ring

theorem two_blocks_square_iff {n m l₁ l₂ c : ℕ}
    (hl₁ : l₁ ≤ n) (hl₂ : l₂ ≤ m) :
    IsSquare (n.factorial * (n - l₁).factorial *
      m.factorial * (m - l₂).factorial * c.factorial) ↔
    IsSquare (falling n l₁ * falling m l₂ * c.factorial) := by
  have hid : n.factorial * (n - l₁).factorial *
      m.factorial * (m - l₂).factorial * c.factorial =
      ((n - l₁).factorial * (m - l₂).factorial) ^ 2 *
        (falling n l₁ * falling m l₂ * c.factorial) := by
    calc
      _ = (n.factorial * (n - l₁).factorial) *
          (m.factorial * (m - l₂).factorial) * c.factorial := by ring
      _ = _ := by rw [paired_block_factorials hl₁, paired_block_factorials hl₂]; ring
  rw [hid]
  exact square_mul_iff
    (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
    (mul_ne_zero (mul_ne_zero (falling_pos _ _).ne' (falling_pos _ _).ne')
      (Nat.factorial_ne_zero _))

end Erdos374Research
