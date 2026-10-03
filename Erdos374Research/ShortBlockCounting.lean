import Erdos374Research.ShortBlockResidues
import Erdos374Research.PrimeCofactorCounting

/-!
# Uniform counting of punctured short-block solutions

UNCOMPILED. A single fibre has O(sqrt X log X) possibilities. All five
parameters are retained in the finite union; their counting cost is explicit.
-/

namespace Erdos374Research

open Finset Filter Tao2026
open scoped BigOperators Topology

noncomputable section

def puncturedSolutionsUpTo (X a t c l j : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 X).filter fun m => l ≤ m ∧
    IsSquare (a * t * c.factorial * puncturedFalling m l j)

lemma upperHalfPrime_large_for_short_block {K B q : ℕ}
    (hB : 2 ≤ B) (hKB : 128 * B ^ 2 ≤ K)
    (hq : q ∈ factorialUpperHalfPrimes K) :
    B < q ∧ q ≠ 2 ∧ 8 * (B : ℝ) ≤ Real.sqrt q := by
  have hd := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
  have hKq : K < 2 * q := by omega
  have hBq : B < q := by nlinarith
  refine ⟨hBq, by omega, ?_⟩
  have hKR : (128 : ℝ) * B ^ 2 ≤ K := by exact_mod_cast hKB
  have hKqR : (K : ℝ) < 2 * q := by exact_mod_cast hKq
  have hs := Real.sq_sqrt (Nat.cast_nonneg q)
  have hr := Real.sqrt_nonneg (q : ℝ)
  have hBR : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  nlinarith

theorem puncturedSolutions_card_finite_bound
    {X K B a t c l j : ℕ} (hX : 2 ≤ X) (hK : 1 ≤ K) (hKX : K ≤ X)
    (hKK : K * K ≤ X + 1) (hB : 2 ≤ B) (hKB : 128 * B ^ 2 ≤ K)
    (ha : 1 ≤ a) (ht : 1 ≤ t) (hl : 2 ≤ l)
    (haB : a ≤ B) (htB : t ≤ B) (hcB : c ≤ B) (hlB : l ≤ B)
    (hmass : (K : ℝ) / 4 ≤
      Chebyshev.theta K - Chebyshev.theta ((K / 2 : ℕ) : ℝ)) :
    (K : ℝ) * (puncturedSolutionsUpTo X a t c l j).card ≤
      96 * (X + 1) * Real.log X := by
  classical
  let S := factorialUpperHalfPrimes K
  let A := puncturedSolutionsUpTo X a t c l j
  let R : (q : SieveModulus) → Finset (ZMod q.modulus) :=
    fun q => puncturedSquareResidues q.modulus a t c l j
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hcard : ∀ p : ↥S,
      ((R (primeSieveModulus S hS p)).card : ℝ) ≤ 3 / 4 * p.1 := by
    intro p
    have hp := hS p.1 p.2
    letI : NeZero p.1 := ⟨hp.ne_zero⟩
    letI : Fact p.1.Prime := ⟨hp⟩
    change ((puncturedSquareResidues p.1 a t c l j).card : ℝ) ≤ 3 / 4 * p.1
    obtain ⟨hBq, hq2, hroot⟩ := upperHalfPrime_large_for_short_block hB hKB p.2
    exact puncturedSquareResidues_card_le_three_quarters hq2 ha ht
      (haB.trans_lt hBq) (htB.trans_lt hBq) (hcB.trans_lt hBq) hl
      ((by exact_mod_cast Nat.mul_le_mul_left 8 hlB : 8 * (l : ℝ) ≤ 8 * B).trans hroot)
  have hres : ∀ m ∈ A, ∀ p : ↥S,
      (m : ZMod (primeSieveModulus S hS p).modulus) ∈ R (primeSieveModulus S hS p) := by
    intro m hm p
    have hmD := (Finset.mem_filter.mp hm).2
    have hBq := (upperHalfPrime_large_for_short_block hB hKB p.2).1
    exact puncturedSquareResidues_mem hmD.1 (hlB.trans hBq.le) hmD.2
  have hglobal := shortBlock_largeSieve_card_mul_prime_count S A X K hS
    (fun p hp => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2) hKK
    (fun m hm => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).2) R
    (fun q => puncturedSquareResidues_nonempty q.modulus a t c hl) hcard hres
  have hprime := upperHalfPrime_card_lower hK hKX hmass
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have h1 := mul_le_mul_of_nonneg_right hprime (Nat.cast_nonneg A.card)
  have h2 := mul_le_mul_of_nonneg_right hglobal hlog
  change (K : ℝ) * A.card ≤ _
  nlinarith

abbrev ShortBlockKey (B : ℕ) := Fin 5 → Fin (B + 1)

def shortBlockSlice (X B : ℕ) (s : ShortBlockKey B) : Finset ℕ := by
  classical
  let a := (s 0).val
  let t := (s 1).val
  let c := (s 2).val
  let l := (s 3).val
  let j := (s 4).val
  exact if 1 ≤ a ∧ 1 ≤ t ∧ 2 ≤ l ∧ j < l then
    (puncturedSolutionsUpTo X a t c l j).image (fun m => a * (m - j) / t)
  else ∅

def shortBlockExceptional (X B : ℕ) : Finset ℕ :=
  Finset.univ.biUnion (shortBlockSlice X B)

theorem mem_shortBlockExceptional {X B n m a t c l j : ℕ}
    (hmX : m ≤ X) (hlm : l ≤ m) (ha : 1 ≤ a) (ht : 1 ≤ t) (hl : 2 ≤ l) (hj : j < l)
    (haB : a ≤ B) (htB : t ≤ B) (hcB : c ≤ B) (hlB : l ≤ B)
    (hrelation : a * (m - j) = t * n)
    (hsq : IsSquare (a * t * c.factorial * puncturedFalling m l j)) :
    n ∈ shortBlockExceptional X B := by
  classical
  have hjB : j ≤ B := hj.le.trans hlB
  let s : ShortBlockKey B := ![⟨a, by omega⟩, ⟨t, by omega⟩, ⟨c, by omega⟩,
    ⟨l, by omega⟩, ⟨j, by omega⟩]
  apply Finset.mem_biUnion.mpr
  refine ⟨s, Finset.mem_univ _, ?_⟩
  change n ∈ (if 1 ≤ a ∧ 1 ≤ t ∧ 2 ≤ l ∧ j < l then
    (puncturedSolutionsUpTo X a t c l j).image (fun m => a * (m - j) / t)
    else ∅)
  rw [if_pos (show 1 ≤ a ∧ 1 ≤ t ∧ 2 ≤ l ∧ j < l from ⟨ha, ht, hl, hj⟩)]
  apply Finset.mem_image.mpr
  refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hmX⟩, hlm, hsq⟩, ?_⟩
  rw [hrelation, Nat.mul_div_cancel_left n (by omega : 0 < t)]

theorem shortBlockExceptional_card_finite_bound
    {X K B : ℕ} (hX : 2 ≤ X) (hK : 1 ≤ K) (hKX : K ≤ X)
    (hKK : K * K ≤ X + 1) (hB : 2 ≤ B) (hKB : 128 * B ^ 2 ≤ K)
    (hmass : (K : ℝ) / 4 ≤
      Chebyshev.theta K - Chebyshev.theta ((K / 2 : ℕ) : ℝ)) :
    (K : ℝ) * (shortBlockExceptional X B).card ≤
      ((B : ℝ) + 1) ^ 5 * (96 * (X + 1) * Real.log X) := by
  classical
  have hKnon : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hslice : ∀ s : ShortBlockKey B,
      (K : ℝ) * (shortBlockSlice X B s).card ≤ 96 * (X + 1) * Real.log X := by
    intro s
    dsimp only [shortBlockSlice]
    split_ifs with hvalid
    · have hbound := puncturedSolutions_card_finite_bound (j := (s 4).val)
        hX hK hKX hKK hB hKB
        hvalid.1 hvalid.2.1 hvalid.2.2.1
        (Nat.le_of_lt_succ (s 0).isLt) (Nat.le_of_lt_succ (s 1).isLt)
        (Nat.le_of_lt_succ (s 2).isLt) (Nat.le_of_lt_succ (s 3).isLt) hmass
      have hc : (((puncturedSolutionsUpTo X (s 0) (s 1) (s 2) (s 3) (s 4)).image
          (fun m => (s 0).val * (m - (s 4).val) / (s 1).val)).card : ℝ) ≤
          (puncturedSolutionsUpTo X (s 0) (s 1) (s 2) (s 3) (s 4)).card := by
        exact_mod_cast Finset.card_image_le
      exact (mul_le_mul_of_nonneg_left hc hKnon).trans hbound
    · simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
      have hlog : 0 ≤ Real.log (X : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
      positivity
  have hcard : ((shortBlockExceptional X B).card : ℝ) ≤
      ∑ s : ShortBlockKey B, ((shortBlockSlice X B s).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := shortBlockSlice X B))
  calc
    (K : ℝ) * (shortBlockExceptional X B).card ≤
        (K : ℝ) * ∑ s : ShortBlockKey B, ((shortBlockSlice X B s).card : ℝ) :=
      mul_le_mul_of_nonneg_left hcard hKnon
    _ = ∑ s : ShortBlockKey B, (K : ℝ) * (shortBlockSlice X B s).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _s : ShortBlockKey B, (96 * (X + 1) * Real.log X) :=
      Finset.sum_le_sum (fun s hs => hslice s)
    _ = ((B : ℝ) + 1) ^ 5 * (96 * (X + 1) * Real.log X) := by
      simp [ShortBlockKey]

end
end Erdos374Research
