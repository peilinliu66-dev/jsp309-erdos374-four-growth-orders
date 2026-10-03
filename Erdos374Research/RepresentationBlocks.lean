import Erdos374Research.OrderedRepresentations
import Erdos374Research.TwoBlockArithmetic

/-! UNCOMPILED. Literal representations are transferred to two ordered
nonempty falling-factorial blocks, retaining the smallest factorial index. -/

namespace Erdos374Research

open Finset
open scoped BigOperators

structure OrderedTwoBlocks (n m l₁ l₂ c : ℕ) : Prop where
  first_pos : 1 ≤ l₁
  first_lt : l₁ < n
  second_pos : 1 ≤ l₂
  second_lt : l₂ < m
  coefficient_pos : 1 ≤ c
  coefficient_le : c ≤ m - l₂
  separated : m < n - l₁
  square : IsSquare (falling n l₁ * falling m l₂ * c.factorial)

theorem four_representation_has_blocks {n : ℕ} (h : HasRepresentation 4 n) :
    ∃ m l₁ l₂ : ℕ, OrderedTwoBlocks n m l₁ l₂ 1 := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, hasRepresentation_succ_iff] at h
  rcases h with ⟨f, hf, hfpos, hlast, hsq⟩
  have h01 := hf (show (0 : Fin 4) < 1 by decide)
  have h12 := hf (show (1 : Fin 4) < 2 by decide)
  have h23 := hf (show (2 : Fin 4) < 3 by decide)
  have hn : f 3 = n := hlast
  rw [hn] at h23
  refine ⟨f 1, n - f 2, f 1 - f 0, ?_⟩
  have hfst : n - (n - f 2) = f 2 := Nat.sub_sub_self h23.le
  have hsnd : f 1 - (f 1 - f 0) = f 0 := Nat.sub_sub_self h01.le
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  apply (two_blocks_square_iff (Nat.sub_le _ _) (Nat.sub_le _ _)).mp
  rw [hfst, hsnd, Nat.factorial_one, mul_one]
  have hprod : (∏ i : Fin 4, (f i).factorial) =
      n.factorial * (f 2).factorial * (f 1).factorial * (f 0).factorial := by
    simp [Fin.prod_univ_succ, hn, mul_comm, mul_left_comm, mul_assoc]
    exact Or.inl (by ring)
  rwa [hprod] at hsq

theorem five_representation_has_blocks {n : ℕ} (h : HasRepresentation 5 n) :
    ∃ m l₁ l₂ c : ℕ, OrderedTwoBlocks n m l₁ l₂ c := by
  rw [show (5 : ℕ) = 4 + 1 by rfl, hasRepresentation_succ_iff] at h
  rcases h with ⟨f, hf, hfpos, hlast, hsq⟩
  have h01 := hf (show (0 : Fin 5) < 1 by decide)
  have h12 := hf (show (1 : Fin 5) < 2 by decide)
  have h23 := hf (show (2 : Fin 5) < 3 by decide)
  have h34 := hf (show (3 : Fin 5) < 4 by decide)
  have hn : f 4 = n := hlast
  rw [hn] at h34
  refine ⟨f 2, n - f 3, f 2 - f 1, f 0, ?_⟩
  have hfst : n - (n - f 3) = f 3 := Nat.sub_sub_self h34.le
  have hsnd : f 2 - (f 2 - f 1) = f 1 := Nat.sub_sub_self h12.le
  refine ⟨by omega, by omega, by omega, by omega, hfpos, by omega, by omega, ?_⟩
  apply (two_blocks_square_iff (Nat.sub_le _ _) (Nat.sub_le _ _)).mp
  rw [hfst, hsnd]
  have hprod : (∏ i : Fin 5, (f i).factorial) =
      n.factorial * (f 3).factorial * (f 2).factorial * (f 1).factorial * (f 0).factorial := by
    simp [Fin.prod_univ_succ, hn, mul_comm, mul_left_comm]
    exact Or.inl (by ring)
  rwa [hprod] at hsq

theorem falling_eq_prod_range {n l : ℕ} (hl : l ≤ n) :
    falling n l = ∏ i ∈ Finset.range l, (n - i) := by
  rw [falling_eq_prod_Ioc hl]
  apply Finset.prod_bij (fun v _ => n - v)
  · intro v hv
    have hd := Finset.mem_Ioc.mp hv
    exact Finset.mem_range.mpr (by omega)
  · intro v hv w hw heq
    have hvn := (Finset.mem_Ioc.mp hv).2
    have hwn := (Finset.mem_Ioc.mp hw).2
    omega
  · intro i hi
    have hil := Finset.mem_range.mp hi
    refine ⟨n - i, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro v hv
    exact (Nat.sub_sub_self (Finset.mem_Ioc.mp hv).2).symm

def puncturedFalling (m l j : ℕ) : ℕ :=
  ∏ i ∈ (Finset.range l).erase j, (m - i)

theorem falling_eq_term_mul_punctured {m l j : ℕ} (hl : l ≤ m) (hj : j < l) :
    falling m l = (m - j) * puncturedFalling m l j := by
  rw [falling_eq_prod_range hl]
  exact (Finset.mul_prod_erase (Finset.range l) (fun i => m - i)
    (Finset.mem_range.mpr hj)).symm

theorem puncturedFalling_pos {m l j : ℕ} (hl : l ≤ m) :
    0 < puncturedFalling m l j := by
  apply Finset.prod_pos
  intro i hi
  have hil := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
  omega

theorem first_singleton_punctured_square {n m l c a p j t : ℕ}
    (hn : 1 ≤ n) (hl : l ≤ m) (hj : j < l) (hp : 1 ≤ p)
    (ha : 1 ≤ a) (ht : 1 ≤ t) (hnap : n = a * p) (hmjp : m - j = t * p)
    (hsq : IsSquare (falling n 1 * falling m l * c.factorial)) :
    IsSquare (a * t * c.factorial * puncturedFalling m l j) := by
  have hfirst : falling n 1 = n := by rw [falling_eq_prod_range hn]; simp
  rw [hfirst, falling_eq_term_mul_punctured hl hj, hnap, hmjp] at hsq
  have hid : (a * p) * ((t * p) * puncturedFalling m l j) * c.factorial =
      p ^ 2 * (a * t * c.factorial * puncturedFalling m l j) := by ring
  rw [hid] at hsq
  exact (square_mul_iff (by omega)
    (by have := puncturedFalling_pos (j := j) hl; positivity)).mp hsq

end Erdos374Research
