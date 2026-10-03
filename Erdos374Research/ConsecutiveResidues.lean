import Erdos374Research.WeilResidues
import Tao2026.FactorialLargeSieve

/-! UNCOMPILED. Specialization of the generic Weil square-value bound to
consecutive-factorial interval starts. -/

namespace Erdos374Research

open Tao2026 Finset
open scoped BigOperators

noncomputable section

lemma consecutiveProduct_eq_prod_offsets (N H : ℕ) :
    consecutiveProduct N H = ∏ i ∈ Finset.Icc 1 H, (N + i) := by
  classical
  symm
  unfold consecutiveProduct consecutiveInterval
  apply Finset.prod_bij (fun i _ => N + i)
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj hij
    omega
  · intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    exact ⟨k - N, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro i hi
    rfl

lemma injectiveOn_negative_natCast_Icc (p H : ℕ) [NeZero p] (hHp : H < p) :
    Set.InjOn (fun i : ℕ => -(i : ZMod p)) (Finset.Icc 1 H) := by
  intro i hi j hj hij
  have hiH := (Finset.mem_Icc.mp hi).2
  have hjH := (Finset.mem_Icc.mp hj).2
  have hv := congrArg ZMod.val (neg_injective hij)
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hiH.trans_lt hHp),
    Nat.mod_eq_of_lt (hjH.trans_lt hHp)] using hv

lemma card_factorialAllowedStartResidues_eq (p H : ℕ) [NeZero p] (hHp : H < p) :
    (factorialAllowedStartResidues p H).card = H := by
  rw [factorialAllowedStartResidues, Finset.card_image_iff.mpr
    (injectiveOn_negative_natCast_Icc p H hHp)]
  simp

lemma cast_consecutiveProduct_eq_rootProduct (p N H : ℕ) [NeZero p] (hHp : H < p) :
    (consecutiveProduct N H : ZMod p) =
      ∏ r ∈ factorialAllowedStartResidues p H, ((N : ZMod p) - r) := by
  classical
  rw [consecutiveProduct_eq_prod_offsets, Nat.cast_prod,
    factorialAllowedStartResidues, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i hi
    push_cast
    ring
  · exact injectiveOn_negative_natCast_Icc p H hHp

lemma factorial_cast_ne_zero_of_lt {p a : ℕ} [NeZero p] [Fact p.Prime]
    (hap : a < p) : (a.factorial : ZMod p) ≠ 0 := by
  intro hz
  have hdiv : p ∣ a.factorial := by simpa only [ZMod.natCast_eq_zero_iff] using hz
  have hpa := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hdiv
  omega

def factorialSquareStartResidues (p a H : ℕ) [NeZero p] : Finset (ZMod p) :=
  splitSquareResidues p (a.factorial : ZMod p) (factorialAllowedStartResidues p H)

lemma factorial_start_mem_squareResidues {p N H a : ℕ}
    [NeZero p] [Fact p.Prime] (hHp : H < p)
    (hcomponent : squarefreeComponent (consecutiveProduct N H) =
      squarefreeComponent a.factorial) :
    (N : ZMod p) ∈ factorialSquareStartResidues p a H := by
  classical
  obtain ⟨r, hr⟩ := (squarefreeComponent_eq_iff_mul_eq_sq
    (consecutiveProduct_ne_zero N H) (Nat.factorial_ne_zero a)).mp hcomponent
  rw [factorialSquareStartResidues, splitSquareResidues, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, (r : ZMod p), ?_⟩
  calc
    splitValue (a.factorial : ZMod p) (factorialAllowedStartResidues p H) N =
        ((consecutiveProduct N H * a.factorial : ℕ) : ZMod p) := by
      rw [splitValue, ← cast_consecutiveProduct_eq_rootProduct p N H hHp,
        Nat.cast_mul]
      ring
    _ = ((r ^ 2 : ℕ) : ZMod p) := congrArg (fun k : ℕ => (k : ZMod p)) hr
    _ = (r : ZMod p) * r := by push_cast; ring

theorem card_factorialSquareStartResidues_le {p a H : ℕ}
    [NeZero p] [Fact p.Prime] (hp2 : p ≠ 2) (hap : a < p)
    (hH : 1 ≤ H) (hHp : H < p) :
    ((factorialSquareStartResidues p a H).card : ℝ) ≤
      ((p : ℝ) + H + (H - 1 : ℕ) * Real.sqrt p) / 2 := by
  have h := card_splitSquareResidues_le p hp2 (factorial_cast_ne_zero_of_lt hap)
    (factorialAllowedStartResidues p H) (factorialAllowedStartResidues_nonempty p H hH)
  simpa only [factorialSquareStartResidues, card_factorialAllowedStartResidues_eq p H hHp] using h

/-- Natural remainder counts inherit any verified ZMod residue restriction. -/
lemma card_natMod_image_le_zmod_set (p : ℕ) [NeZero p]
    (A : Finset ℕ) (B : Finset (ZMod p))
    (h : ∀ N ∈ A, (N : ZMod p) ∈ B) :
    (A.image fun N => N % p).card ≤ B.card := by
  classical
  have hsub : (A.image fun N => N % p) ⊆ B.image ZMod.val := by
    intro r hr
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image.mpr ⟨(N : ZMod p), h N hN, by simp⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end
end Erdos374Research
