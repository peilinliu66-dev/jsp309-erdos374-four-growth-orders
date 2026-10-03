import Mathlib

/-!
# Disjoint blocks turn exceptional measure into a uniform mass bound

Original auxiliary arguments for the Yudin formalization. UNCOMPILED.
No exceptional-set estimate or prime theorem is assumed implicitly here;
those inputs are explicit and will be discharged in the analytic adapter.
-/

namespace Erdos374Research

open MeasureTheory Set Finset
open scoped BigOperators

def firstHalf (A B : ℝ) (j : ℕ) : Set ℝ :=
  Set.Ico (A + 2 * B * j) (A + 2 * B * j + B)

theorem firstHalf_pairwiseDisjoint (A : ℝ) {B : ℝ} (hB : 0 < B)
    (s : Finset ℕ) : Set.PairwiseDisjoint (s : Set ℕ) (firstHalf A B) := by
  intro i hi j hj hij
  change Disjoint (firstHalf A B i) (firstHalf A B j)
  rw [Set.disjoint_left]
  intro x hx hy
  change A + 2 * B * i ≤ x ∧ x < A + 2 * B * i + B at hx
  change A + 2 * B * j ≤ x ∧ x < A + 2 * B * j + B at hy
  rcases lt_or_gt_of_ne hij with h | h
  · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    have hmul := mul_le_mul_of_nonneg_left hcast hB.le
    nlinarith
  · have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
    have hmul := mul_le_mul_of_nonneg_left hcast hB.le
    nlinarith

theorem firstHalf_volume (A : ℝ) {B : ℝ} (hB : 0 ≤ B) (j : ℕ) :
    volume.real (firstHalf A B j) = B := by
  unfold firstHalf
  rw [Real.volume_real_Ico_of_le (by linarith)]
  ring

theorem bad_blocks_mass_le_exceptional_measure
    (A : ℝ) {B : ℝ} (hB : 0 < B) (bad : Finset ℕ) (E : Set ℝ)
    (hE : volume E ≠ ⊤)
    (hbad : ∀ j ∈ bad, firstHalf A B j ⊆ E) :
    (bad.card : ℝ) * B ≤ volume.real E := by
  have hsub : (⋃ j ∈ bad, firstHalf A B j) ⊆ E := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hj, hx⟩
    exact hbad j hj hx
  have hvol : volume.real (⋃ j ∈ bad, firstHalf A B j) = (bad.card : ℝ) * B := by
    rw [measureReal_biUnion_finset (firstHalf_pairwiseDisjoint A hB bad)
      (fun j hj => measurableSet_Ico)
      (fun j hj => measure_ne_top_of_subset (hbad j hj) hE)]
    simp only [firstHalf_volume A hB.le, Finset.sum_const, nsmul_eq_mul]
  rw [← hvol]
  exact measureReal_mono hsub hE

theorem sum_increments (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, (f (j + 1) - f j)) = f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem mass_lower_of_good_blocks
    (F : ℝ → ℝ) (hF : Monotone F) (A : ℝ) {B c : ℝ}
    (hB : 0 ≤ B) (_hc : 0 ≤ c) (N : ℕ) (bad : Finset ℕ)
    (hbad : bad ⊆ Finset.range N)
    (hgood : ∀ j ∈ Finset.range N, j ∉ bad →
      c ≤ F (A + 2 * B * (j + 1 : ℕ)) - F (A + 2 * B * j)) :
    ((N : ℝ) - bad.card) * c ≤ F (A + 2 * B * N) - F A := by
  classical
  let good := Finset.range N \ bad
  have hgoodsub : good ⊆ Finset.range N := Finset.sdiff_subset
  have hcard : (good.card : ℝ) = (N : ℝ) - bad.card := by
    dsimp [good]
    rw [Finset.card_sdiff_of_subset hbad, Nat.cast_sub (Finset.card_le_card hbad)]
    simp
  have hnonneg : ∀ j : ℕ,
      0 ≤ F (A + 2 * B * (j + 1 : ℕ)) - F (A + 2 * B * j) := by
    intro j
    apply sub_nonneg.mpr
    apply hF
    push_cast
    nlinarith
  have hlow : (good.card : ℝ) * c ≤
      ∑ j ∈ good, (F (A + 2 * B * (j + 1 : ℕ)) - F (A + 2 * B * j)) := by
    calc
      (good.card : ℝ) * c = ∑ j ∈ good, c := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_sdiff.mp hj
        exact hgood j hj'.1 hj'.2
  have hsum :
      (∑ j ∈ good, (F (A + 2 * B * (j + 1 : ℕ)) - F (A + 2 * B * j))) ≤
      ∑ j ∈ Finset.range N, (F (A + 2 * B * (j + 1 : ℕ)) - F (A + 2 * B * j)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hgoodsub
      (fun j hj hjnot => hnonneg j)
  have htel := sum_increments (fun j => F (A + 2 * B * j)) N
  simp only [Nat.cast_zero, mul_zero, add_zero] at htel
  rw [hcard] at hlow
  exact hlow.trans (hsum.trans_eq htel)

/-- A useful local interval inside a block transfers its mass to the whole
block for any monotone cumulative mass function. -/
theorem block_mass_ge_local_mass
    (F : ℝ → ℝ) (hF : Monotone F) (A B t r c : ℝ) (j : ℕ)
    (ht : t ∈ firstHalf A B j) (hr : r ≤ B)
    (hmass : c ≤ F (t + r) - F t) :
    c ≤ F (A + 2 * B * (j + 1 : ℕ)) - F (A + 2 * B * j) := by
  have hleft : F (A + 2 * B * j) ≤ F t := hF ht.1
  have hright : F (t + r) ≤ F (A + 2 * B * (j + 1 : ℕ)) := by
    apply hF
    have hupper := ht.2
    change t < A + 2 * B * j + B at hupper
    push_cast
    linarith
  linarith

end Erdos374Research
