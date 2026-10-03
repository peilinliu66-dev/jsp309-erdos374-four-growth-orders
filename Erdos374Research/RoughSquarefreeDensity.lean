import Erdos374Research.CRTCounting
import Erdos374Research.EulerProductBounds
import Erdos374Research.SquarefreeSieveBounds

/-!
# Positive density of rough squarefree integers

UNCOMPILED. A finite CRT sieve has density at least 1/(2B); removing
square divisors above 8B loses at most X/(8B). The finite-period boundary
is explicit and disappears at an eventual threshold depending on B.
-/

namespace Erdos374Research

open Finset Filter
open scoped BigOperators Topology

noncomputable section

def roughPrimeSet (Z : ℕ) : Finset ℕ := (Finset.Icc 2 Z).filter Nat.Prime
def roughModulus (B p : ℕ) : ℕ := if p ≤ B then p else p ^ 2

theorem roughModulus_pos {B p : ℕ} (hp : p.Prime) : 0 < roughModulus B p := by
  unfold roughModulus
  split_ifs
  · exact hp.pos
  · exact pow_pos hp.pos 2

instance roughModulus_neZero (B Z : ℕ) (p : ↥(roughPrimeSet Z)) :
    NeZero (roughModulus B p.1) :=
  ⟨(roughModulus_pos (Finset.mem_filter.mp p.2).2).ne'⟩

theorem roughModulus_pairwise (B Z : ℕ) :
    Pairwise (Function.onFun Nat.Coprime (fun p : ↥(roughPrimeSet Z) => roughModulus B p.1)) := by
  intro p q hpq
  have hc : Nat.Coprime p.1 q.1 :=
    (Nat.coprime_primes (Finset.mem_filter.mp p.2).2 (Finset.mem_filter.mp q.2).2).mpr
      (fun h => hpq (Subtype.ext h))
  change Nat.Coprime (roughModulus B p.1) (roughModulus B q.1)
  unfold roughModulus
  split_ifs
  · exact hc
  · exact hc.pow_right 2
  · exact hc.pow_left 2
  · exact hc.pow 2 2

def roughPeriod (B Z : ℕ) : ℕ := ∏ p : ↥(roughPrimeSet Z), roughModulus B p.1

theorem roughPeriod_pos (B Z : ℕ) : 0 < roughPeriod B Z := by
  unfold roughPeriod
  exact Finset.prod_pos fun p hp => roughModulus_pos (Finset.mem_filter.mp p.2).2

theorem rough_modulus_ratio (B Z : ℕ) :
    ((∏ p : ↥(roughPrimeSet Z), (roughModulus B p.1 - 1) : ℕ) : ℝ) / roughPeriod B Z =
      ∏ p ∈ roughPrimeSet Z, (1 - (1 : ℝ) / roughModulus B p) := by
  unfold roughPeriod
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  rw [Finset.prod_coe_sort (roughPrimeSet Z)
    (fun p : ℕ => ((roughModulus B p - 1 : ℕ) : ℝ) / (roughModulus B p : ℝ))]
  apply Finset.prod_congr rfl
  intro p hp
  have hpos : 0 < roughModulus B p := roughModulus_pos (Finset.mem_filter.mp hp).2
  have hreal : (0 : ℝ) < roughModulus B p := by exact_mod_cast hpos
  rw [Nat.cast_sub (by omega : 1 ≤ roughModulus B p), Nat.cast_one]
  field_simp [hreal.ne']

theorem rough_modulus_density_lower {B Z : ℕ} (hB : 1 ≤ B) (hBZ : B ≤ Z) :
    (1 : ℝ) / (2 * B) ≤
      ((∏ p : ↥(roughPrimeSet Z), (roughModulus B p.1 - 1) : ℕ) : ℝ) / roughPeriod B Z := by
  rw [rough_modulus_ratio]
  have hsmall : (roughPrimeSet Z).filter (fun p => p ≤ B) = (Finset.Icc 2 B).filter Nat.Prime := by
    ext p
    simp only [roughPrimeSet, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hp2, hpZ⟩, hp⟩, hpB⟩
      exact ⟨⟨hp2, hpB⟩, hp⟩
    · rintro ⟨⟨hp2, hpB⟩, hp⟩
      exact ⟨⟨⟨hp2, hpB.trans hBZ⟩, hp⟩, hpB⟩
  have hlarge : (roughPrimeSet Z).filter (fun p => ¬ p ≤ B) =
      (Finset.Icc (B + 1) Z).filter Nat.Prime := by
    ext p
    simp only [roughPrimeSet, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hp2, hpZ⟩, hp⟩, hpB⟩
      exact ⟨⟨by omega, hpZ⟩, hp⟩
    · rintro ⟨⟨hpB, hpZ⟩, hp⟩
      exact ⟨⟨⟨hp.two_le, hpZ⟩, hp⟩, by omega⟩
  rw [← Finset.prod_filter_mul_prod_filter_not (roughPrimeSet Z) (fun p => p ≤ B),
    hsmall, hlarge]
  have heqSmall :
      (∏ p ∈ (Finset.Icc 2 B).filter Nat.Prime, (1 - (1 : ℝ) / roughModulus B p)) =
      ∏ p ∈ (Finset.Icc 2 B).filter Nat.Prime, (1 - (1 : ℝ) / p) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [roughModulus, if_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2]
  have heqLarge :
      (∏ p ∈ (Finset.Icc (B + 1) Z).filter Nat.Prime, (1 - (1 : ℝ) / roughModulus B p)) =
      ∏ p ∈ (Finset.Icc (B + 1) Z).filter Nat.Prime, (1 - (1 : ℝ) / (p : ℝ) ^ 2) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpB : ¬ p ≤ B := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega
    rw [roughModulus, if_neg hpB, Nat.cast_pow]
  rw [heqSmall, heqLarge]
  have h1 := prime_product_lower B hB
  have h2 := prime_square_product_lower B Z hB (hB.trans hBZ)
  calc
    (1 : ℝ) / (2 * B) = ((1 : ℝ) / B) * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul h1 h2 (by norm_num) ((by positivity : (0 : ℝ) ≤ 1 / B).trans h1)

def IsRoughSquarefree (B a : ℕ) : Prop :=
  1 ≤ a ∧ Squarefree a ∧ ∀ p : ℕ, p.Prime → p ≤ B → ¬ p ∣ a

def roughSquarefreeUpTo (B X : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Ioc 0 X).filter (IsRoughSquarefree B)

def finiteRoughSieve (B Z X : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range X).filter fun n => ∀ p : ↥(roughPrimeSet Z), ¬ roughModulus B p.1 ∣ n

theorem finiteRoughSieve_subset_union {B Z X : ℕ} (hB : 2 ≤ B) (hBZ : B ≤ Z) :
    finiteRoughSieve B Z X ⊆ roughSquarefreeUpTo B X ∪ largeSquareMultiples X Z := by
  classical
  intro n hn
  have hnd := Finset.mem_filter.mp hn
  have hnX : n ≤ X := (Finset.mem_range.mp hnd.1).le
  have htwo : 2 ∈ roughPrimeSet Z :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hB.trans hBZ⟩, Nat.prime_two⟩
  have hn0 : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := by omega
    exact hnd.2 ⟨2, htwo⟩ (by simp [hnzero])
  have hrough : ∀ p : ℕ, p.Prime → p ≤ B → ¬ p ∣ n := by
    intro p hp hpB
    have hpS : p ∈ roughPrimeSet Z :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpB.trans hBZ⟩, hp⟩
    simpa only [roughModulus, if_pos hpB] using hnd.2 ⟨p, hpS⟩
  by_cases hsq : Squarefree n
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hn0, hnX⟩, hn0, hsq, hrough⟩)
  · rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpd⟩ := hsq
    have hpSq : p ^ 2 ∣ n := by simpa only [pow_two] using hpd
    have hpZ : Z < p := by
      by_contra hnot
      have hpLe : p ≤ Z := Nat.le_of_not_gt hnot
      have hpS : p ∈ roughPrimeSet Z :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpLe⟩, hp⟩
      apply hnd.2 ⟨p, hpS⟩
      unfold roughModulus
      split_ifs
      · exact dvd_trans (show p ∣ p ^ 2 from ⟨p, by ring⟩) hpSq
      · exact hpSq
    have hpSqrt : p ≤ Nat.sqrt X := by
      rw [Nat.le_sqrt]
      have hle := (Nat.le_of_dvd hn0 hpSq).trans hnX
      simpa only [pow_two] using hle
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_Icc.mpr ⟨by omega, hpSqrt⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn0, hnX⟩, hpSq⟩⟩)

theorem roughSquarefree_count_lower {B Z : ℕ} (hB : 2 ≤ B) (hBZ : B ≤ Z) (X : ℕ) :
    (X : ℝ) / (2 * B) - roughPeriod B Z - (X : ℝ) / Z ≤
      ((roughSquarefreeUpTo B X).card : ℝ) := by
  let q := fun p : ↥(roughPrimeSet Z) => roughModulus B p.1
  have hcrt := crt_avoidance_prefix_lower q (roughModulus_pairwise B Z) X (roughPeriod_pos B Z)
  have hrho := rough_modulus_density_lower (by omega : 1 ≤ B) hBZ
  have hfinite : (X : ℝ) / (2 * B) - roughPeriod B Z ≤ (finiteRoughSieve B Z X).card := by
    calc
      _ ≤ (((∏ p : ↥(roughPrimeSet Z), (roughModulus B p.1 - 1) : ℕ) : ℝ) /
          roughPeriod B Z) * X - roughPeriod B Z := by
        have h := mul_le_mul_of_nonneg_right hrho (Nat.cast_nonneg X)
        convert sub_le_sub_right h (roughPeriod B Z : ℝ) using 1
        ring
      _ ≤ _ := hcrt
  have hcard : (finiteRoughSieve B Z X).card ≤
      (roughSquarefreeUpTo B X).card + (largeSquareMultiples X Z).card :=
    (Finset.card_le_card (finiteRoughSieve_subset_union hB hBZ)).trans (Finset.card_union_le _ _)
  have hcardR : ((finiteRoughSieve B Z X).card : ℝ) ≤
      (roughSquarefreeUpTo B X).card + (largeSquareMultiples X Z).card := by exact_mod_cast hcard
  have htail := card_largeSquareMultiples_le X Z (by omega : 1 ≤ Z)
  linarith

theorem eventually_roughSquarefree_positive_density {B : ℕ} (hB : 2 ≤ B) :
    ∀ᶠ X : ℕ in atTop, (X : ℝ) / (4 * B) ≤ (roughSquarefreeUpTo B X).card := by
  let M := roughPeriod B (8 * B)
  filter_upwards [eventually_ge_atTop (8 * B * M)] with X hX
  have hBR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hbound := roughSquarefree_count_lower hB (by omega : B ≤ 8 * B) X
  have hMR : (M : ℝ) ≤ (X : ℝ) / (8 * B) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
    exact_mod_cast (show M * (8 * B) ≤ X by nlinarith)
  have hid : (X : ℝ) / (2 * B) - (X : ℝ) / (8 * B) - (X : ℝ) / (8 * B) =
      (X : ℝ) / (4 * B) := by field_simp [hBR.ne']; ring
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hbound
  change (X : ℝ) / (2 * B) - M - (X : ℝ) / (8 * B) ≤ _ at hbound
  linarith

end
end Erdos374Research
