import Mathlib

/-!
# Counting a fixed finite set of residue classes

UNCOMPILED. This elementary finite-block count is used for the squarefree
cofactor supply. The modulus may be very large, but is fixed before X tends
to infinity; its boundary error is retained explicitly.
-/

namespace Erdos374Research

open Finset
open scoped BigOperators

def residuePrefix (X M : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (Finset.range X).filter fun n => n % M ∈ R

theorem residue_block_injective {M : ℕ} (hM : 0 < M) (K : ℕ) (R : Finset ℕ)
    (hR : R ⊆ Finset.range M) :
    Set.InjOn (fun kr : ℕ × ℕ => kr.1 * M + kr.2) ((Finset.range K).product R) := by
  intro kr hkr ls hls heq
  change kr.1 * M + kr.2 = ls.1 * M + ls.2 at heq
  have hkrd := Finset.mem_product.mp hkr
  have hlsd := Finset.mem_product.mp hls
  have hkrM : kr.2 < M := Finset.mem_range.mp (hR hkrd.2)
  have hlsM : ls.2 < M := Finset.mem_range.mp (hR hlsd.2)
  have hres := congrArg (fun n => n % M) heq
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod,
    zero_add, Nat.mod_eq_of_lt hkrM, Nat.mod_eq_of_lt hlsM] at hres
  have hquot : kr.1 = ls.1 := by
    have hmul : kr.1 * M = ls.1 * M := by omega
    exact Nat.eq_of_mul_eq_mul_right hM hmul
  exact Prod.ext hquot hres

theorem residuePrefix_card_ge_blocks (X : ℕ) {M : ℕ} (hM : 0 < M)
    (R : Finset ℕ) (hR : R ⊆ Finset.range M) :
    (X / M) * R.card ≤ (residuePrefix X M R).card := by
  let S := ((Finset.range (X / M)).product R).image (fun kr => kr.1 * M + kr.2)
  have hsub : S ⊆ residuePrefix X M R := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨⟨k, r⟩, hkr, rfl⟩
    have hkrd := Finset.mem_product.mp hkr
    have hk : k < X / M := Finset.mem_range.mp hkrd.1
    have hr : r < M := Finset.mem_range.mp (hR hkrd.2)
    have hkM := Nat.mul_le_mul_right M (Nat.succ_le_of_lt hk)
    have hXM := Nat.div_mul_le_self X M
    have hlt : k * M + r < X := by nlinarith
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hlt, ?_⟩
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero,
      Nat.zero_mod, zero_add, Nat.mod_eq_of_lt hr] using hkrd.2
  have hcard : S.card = (X / M) * R.card := by
    rw [Finset.card_image_of_injOn (residue_block_injective hM _ R hR)]
    simp
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem residuePrefix_card_lower_real (X : ℕ) {M : ℕ} (hM : 0 < M)
    (R : Finset ℕ) (hR : R ⊆ Finset.range M) :
    (R.card : ℝ) / M * X - M ≤ (residuePrefix X M R).card := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcardM : R.card ≤ M := by simpa using Finset.card_le_card hR
  have hcardMR : (R.card : ℝ) ≤ M := by exact_mod_cast hcardM
  have hmod : X % M < M := Nat.mod_lt X hM
  have hdiv : (X : ℝ) = (X / M : ℕ) * (M : ℝ) + (X % M : ℕ) := by
    exact_mod_cast (show X = (X / M) * M + X % M by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod X M).symm)
  have hmodR : ((X % M : ℕ) : ℝ) < M := by exact_mod_cast hmod
  have hquot : (X : ℝ) / M - 1 ≤ (X / M : ℕ) := by
    have h' : (X : ℝ) / M ≤ ((X / M : ℕ) : ℝ) + 1 :=
      (div_le_iff₀ hMR).mpr (by nlinarith)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hquot (Nat.cast_nonneg R.card)
  have hblocks : ((X / M : ℕ) : ℝ) * R.card ≤ (residuePrefix X M R).card := by
    exact_mod_cast residuePrefix_card_ge_blocks X hM R hR
  calc
    (R.card : ℝ) / M * X - M ≤ (R.card : ℝ) / M * X - R.card := by linarith
    _ = ((X : ℝ) / M - 1) * R.card := by ring
    _ ≤ ((X / M : ℕ) : ℝ) * R.card := hmul
    _ ≤ (residuePrefix X M R).card := hblocks

end Erdos374Research
