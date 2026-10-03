import Erdos374Research.SingletonReduction
import Erdos374Research.ThreeFourGrowth

/-!
# Final finite-counting assembly for D5 and D6

UNCOMPILED. This module isolates the last analytic interface. Its final
theorem is conditional on `eventually BlocksAreShort`; the public endpoint
must instantiate that interface with the proved long-block reduction.
-/

namespace Erdos374Research

open Finset Filter
open scoped BigOperators Topology

def BlocksAreShort (ε : ℝ) (n : ℕ) : Prop :=
  ∀ m l₁ l₂ c a p : ℕ, OrderedTwoBlocks n m l₁ l₂ c →
    p.Prime → 3 ≤ a → a + 1 < p → n = a * p →
    (a : ℝ) ≤ (n : ℝ) ^ (3 * ε / 4) →
    (max l₁ l₂ : ℕ) < (n : ℝ) ^ ε ∧ (c : ℝ) ≤ (n : ℝ) ^ (2 * ε)

lemma squarefree_not_isSquare {n : ℕ} (hn : 1 < n) (hsf : Squarefree n) :
    ¬ IsSquare n := by
  simpa only [mul_one] using not_isSquare_mul_of_squarefree_left
    (m := 1) hsf (by decide) hn

theorem no_four_representation_of_short_good_candidate
    {X n a p : ℕ} {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 100000)
    (hn : 1 < n) (hnX : n ≤ X) (hsf : Squarefree n)
    (hp : p.Prime) (ha : 3 ≤ a) (hgap : a + 1 < p) (hnap : n = a * p)
    (haSmall : (a : ℝ) ≤ (n : ℝ) ^ (3 * ε / 4))
    (hlarge : HasLargeSquarefreePrime (3 * ε) X n)
    (hshort : BlocksAreShort ε n)
    (hnot : n ∉ shortBlockExceptional X (shortBlockCutoff ε X)) :
    ¬ HasRepresentation 4 n := by
  intro hrep
  obtain ⟨m, l₁, l₂, hb⟩ := four_representation_has_blocks hrep
  have hs := hshort m l₁ l₂ 1 a p hb hp ha hgap hnap haSmall
  obtain ⟨rfl, rfl⟩ := short_blocks_singletons_of_not_exceptional hε hεsmall hn hnX hb hp
    (by omega : 1 ≤ a) (by omega : a < p) hnap haSmall hlarge hs.1 hs.2 hnot
  exact singleton_blocks_not_square_for_squarefree hb hsf

theorem no_five_representation_of_short_admissible_candidate
    {X n a p : ℕ} {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 100000)
    (hn : 1 < n) (hnX : n ≤ X) (hadm : AdmissibleCofactor a)
    (hp : p.Prime) (ha : 3 ≤ a) (hgap : a + 1 < p) (hnap : n = a * p)
    (haSmall : (a : ℝ) ≤ (n : ℝ) ^ (3 * ε / 4))
    (hlarge : HasLargeSquarefreePrime (3 * ε) X n)
    (hshort : BlocksAreShort ε n)
    (hnot : n ∉ shortBlockExceptional X (shortBlockCutoff ε X)) :
    ¬ HasRepresentation 5 n := by
  intro hrep
  obtain ⟨m, l₁, l₂, c, hb⟩ := five_representation_has_blocks hrep
  have hs := hshort m l₁ l₂ c a p hb hp ha hgap hnap haSmall
  obtain ⟨rfl, rfl⟩ := short_blocks_singletons_of_not_exceptional hε hεsmall hn hnX hb hp
    (by omega : 1 ≤ a) (by omega : a < p) hnap haSmall hlarge hs.1 hs.2 hnot
  have hpBig := cofactor_prime_gt_power hn hnap haSmall
    (show 3 * ε / 4 + 2 * ε < 1 by linarith)
  have hcp : c < p := by exact_mod_cast hs.2.trans_lt hpBig
  exact singleton_blocks_not_square_for_admissible hb hadm hp (by omega) hnap hcp

theorem even_good_candidate_in_D5
    {X n a p : ℕ} {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 100000)
    (hnX : n ≤ X) (haEven : EvenSquarefreeCofactor a)
    (hp : p.Prime) (ha : 3 ≤ a) (hgap : a + 1 < p) (hnap : n = a * p)
    (haSmall : (a : ℝ) ≤ (n : ℝ) ^ (3 * ε / 4))
    (hlarge : HasLargeSquarefreePrime (3 * ε) X n) (hshort : BlocksAreShort ε n)
    (hnot : n ∉ shortBlockExceptional X (shortBlockCutoff ε X))
    (hnot3 : n ∉ numbersInDUpTo 3 X) : IsInD 5 n := by
  have hn8 : 8 ≤ n := by have := hp.two_le; rw [hnap]; nlinarith
  have hn : 1 < n := by omega
  have hsf : Squarefree n := by
    rw [hnap]
    exact squarefree_prime_cofactor_product haEven.2.1 hp (by omega)
  have hnsq := squarefree_not_isSquare hn hsf
  have hno2 : ¬ HasRepresentation 2 n := fun h => hnsq (hasRepresentation_two_iff_square.mp h).2
  have hno3 : ¬ HasRepresentation 3 n := by
    intro h
    exact hnot3 (mem_numbersInDUpTo.mpr ⟨by omega, hnX,
      isInD_three_of_representation_of_not_square h hnsq⟩)
  have hno4 := no_four_representation_of_short_good_candidate hε hεsmall hn hnX hsf
    hp ha hgap hnap haSmall hlarge hshort hnot
  have hEven : Even n := by
    rcases haEven.2.2 with ⟨b, hb⟩
    refine ⟨b * p, ?_⟩
    rw [hnap, hb]
    ring
  refine ⟨by decide, hasRepresentation_five_of_even hn8 hEven, ?_⟩
  intro k hk2 hk5 hrep
  have hcases : k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact hno2 hrep
  · exact hno3 hrep
  · exact hno4 hrep

theorem admissible_good_candidate_in_D6
    {X n a p : ℕ} {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 100000)
    (hnX : n ≤ X) (hadm : AdmissibleCofactor a)
    (hp : p.Prime) (ha : 3 ≤ a) (hgap : a + 1 < p) (hnap : n = a * p)
    (haSmall : (a : ℝ) ≤ (n : ℝ) ^ (3 * ε / 4))
    (hlarge : HasLargeSquarefreePrime (3 * ε) X n) (hshort : BlocksAreShort ε n)
    (hnot : n ∉ shortBlockExceptional X (shortBlockCutoff ε X))
    (hnot3 : n ∉ numbersInDUpTo 3 X) : IsInD 6 n := by
  have hn : 1 < n := by have := hp.two_le; rw [hnap]; nlinarith
  have hsf : Squarefree n := by
    rw [hnap]
    exact squarefree_prime_cofactor_product hadm.2.1 hp (by omega)
  have hnsq := squarefree_not_isSquare hn hsf
  have hno2 : ¬ HasRepresentation 2 n := fun h => hnsq (hasRepresentation_two_iff_square.mp h).2
  have hno3 : ¬ HasRepresentation 3 n := by
    intro h
    exact hnot3 (mem_numbersInDUpTo.mpr ⟨by omega, hnX,
      isInD_three_of_representation_of_not_square h hnsq⟩)
  have hno4 := no_four_representation_of_short_good_candidate hε hεsmall hn hnX hsf
    hp ha hgap hnap haSmall hlarge hshort hnot
  have hno5 := no_five_representation_of_short_admissible_candidate hε hεsmall hn hnX hadm
    hp ha hgap hnap haSmall hlarge hshort hnot
  refine ⟨by decide, ?_, ?_⟩
  · rw [hnap]
    exact hasRepresentation_six_of_separated_factors ha hgap
  · intro k hk2 hk6 hrep
    have hcases : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact hno2 hrep
    · exact hno3 hrep
    · exact hno4 hrep
    · exact hno5 hrep

theorem eventually_countD_three_le_linear {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, (countD 3 X : ℝ) ≤ δ * X := by
  obtain ⟨C, hC, hbound⟩ := eventually_countD_three_upper
  filter_upwards [hbound, tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop ((C / δ) ^ 2))] with X hc hX
  have hroot := Real.sqrt_nonneg (X : ℝ)
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg X)
  have hratio : 0 < C / δ := by positivity
  have hlow : C / δ ≤ Real.sqrt X := by nlinarith
  have hCroot : C ≤ δ * Real.sqrt X := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlow
  have hmul := mul_le_mul_of_nonneg_right hCroot hroot
  nlinarith

theorem count_of_cover_le {A S : Finset ℕ} {k X : ℕ}
    (hcover : A ⊆ numbersInDUpTo k X ∪ S ∪ numbersInDUpTo 3 X) :
    (A.card : ℝ) ≤ countD k X + (S.card : ℝ) + countD 3 X := by
  have h1 := Finset.card_le_card hcover
  have h2 : (numbersInDUpTo k X ∪ S ∪ numbersInDUpTo 3 X).card ≤
      (numbersInDUpTo k X).card + S.card + (numbersInDUpTo 3 X).card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  exact_mod_cast h1.trans h2

theorem growth_five_and_six_of_short_blocks {ε δ : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 100000) (hδ : 0 < δ)
    (hshort : ∀ᶠ n : ℕ in atTop, BlocksAreShort ε n)
    (hfive : ∀ᶠ X : ℕ in atTop, δ * X ≤
      (goodPrimeCofactorProducts EvenSquarefreeCofactor (ε / 2) (3 * ε) X).card)
    (hsix : ∀ᶠ X : ℕ in atTop, δ * X ≤
      (goodPrimeCofactorProducts AdmissibleCofactor (ε / 2) (3 * ε) X).card) :
    HasOrder (countD 5) (fun X => X) ∧ HasOrder (countD 6) (fun X => X) := by
  have hcommon := eventually_lift_through_half hshort
  have hgeom5 := eventually_candidate_factor_geometry EvenSquarefreeCofactor hε hεsmall
  have hgeom6 := eventually_candidate_factor_geometry AdmissibleCofactor hε hεsmall
  have hexcept := eventually_shortBlockExceptional_le_linear hε hεsmall
    (show 0 < δ / 4 by positivity)
  have hthree := eventually_countD_three_le_linear (show 0 < δ / 4 by positivity)
  have hboth : ∀ᶠ X : ℕ in atTop,
      δ / 2 * X ≤ countD 5 X ∧ δ / 2 * X ≤ countD 6 X := by
    classical
    filter_upwards [hcommon, hgeom5, hgeom6, hexcept, hthree, hfive, hsix]
      with X hshortX hg5 hg6 he h3 h5 h6
    have hcover5 : goodPrimeCofactorProducts EvenSquarefreeCofactor (ε / 2) (3 * ε) X ⊆
        numbersInDUpTo 5 X ∪ shortBlockExceptional X (shortBlockCutoff ε X) ∪ numbersInDUpTo 3 X := by
      intro n hn
      have hd := Finset.mem_filter.mp hn
      by_cases heN : n ∈ shortBlockExceptional X (shortBlockCutoff ε X)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ heN)
      by_cases h3N : n ∈ numbersInDUpTo 3 X
      · exact Finset.mem_union_right _ h3N
      obtain ⟨a, p, haEven, ha, hp, hgap, hnap, hasmall⟩ := hg5 n hd.1
      have hnX := primeCofactorProducts_le hd.1
      have hshortN := hshortX n (primeCofactorProducts_gt_half hd.1)
      have hD := even_good_candidate_in_D5 hε hεsmall hnX haEven hp ha hgap hnap hasmall
        hd.2 hshortN heN h3N
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (mem_numbersInDUpTo.mpr ⟨by have := hD.two_le_endpoint; omega, hnX, hD⟩))
    have hcover6 : goodPrimeCofactorProducts AdmissibleCofactor (ε / 2) (3 * ε) X ⊆
        numbersInDUpTo 6 X ∪ shortBlockExceptional X (shortBlockCutoff ε X) ∪ numbersInDUpTo 3 X := by
      intro n hn
      have hd := Finset.mem_filter.mp hn
      by_cases heN : n ∈ shortBlockExceptional X (shortBlockCutoff ε X)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ heN)
      by_cases h3N : n ∈ numbersInDUpTo 3 X
      · exact Finset.mem_union_right _ h3N
      obtain ⟨a, p, hadm, ha, hp, hgap, hnap, hasmall⟩ := hg6 n hd.1
      have hnX := primeCofactorProducts_le hd.1
      have hshortN := hshortX n (primeCofactorProducts_gt_half hd.1)
      have hD := admissible_good_candidate_in_D6 hε hεsmall hnX hadm hp ha hgap hnap hasmall
        hd.2 hshortN heN h3N
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (mem_numbersInDUpTo.mpr ⟨by have := hD.two_le_endpoint; omega, hnX, hD⟩))
    have hc5 := count_of_cover_le hcover5
    have hc6 := count_of_cover_le hcover6
    constructor <;> linarith
  exact ⟨hasOrder_linear_of_lower 5 ⟨δ / 2, by positivity, hboth.mono (fun X hX => hX.1)⟩,
    hasOrder_linear_of_lower 6 ⟨δ / 2, by positivity, hboth.mono (fun X hX => hX.2)⟩⟩

end Erdos374Research
