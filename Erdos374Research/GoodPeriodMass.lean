import Erdos374Research.RationalWeightPeriods
import Erdos374Research.QuadraticBand

/-!
UNCOMPILED. A finite full-period covering argument. Only the last incomplete
period is discarded. The band itself is measured, whereas the detecting
weight is integrated on complete periods where the slow factor is one.
-/

namespace Erdos374Research

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

def realPeriodCell (A a : ℝ) (k : ℕ) : Set ℝ :=
  Ico (A + k * a) (A + ((k : ℝ) + 1) * a)

lemma realPeriodCells_disjoint {A a : ℝ} (ha : 0 < a) :
    Pairwise (Disjoint on realPeriodCell A a) := by
  intro k l hkl
  change Disjoint (realPeriodCell A a k) (realPeriodCell A a l)
  rw [Set.disjoint_left]
  intro u huk hul
  change A + k * a ≤ u ∧ u < A + ((k : ℝ) + 1) * a at huk
  change A + l * a ≤ u ∧ u < A + ((l : ℝ) + 1) * a at hul
  rcases lt_or_gt_of_ne hkl with h | h
  · have h' : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
    nlinarith
  · have h' : (l : ℝ) + 1 ≤ k := by exact_mod_cast h
    nlinarith

lemma realPeriodCell_measure {A a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    volume.real (realPeriodCell A a k) = a := by
  change (volume (Ico (A + k * a) (A + ((k : ℝ) + 1) * a))).toReal = a
  rw [Real.volume_Ico, show A + ((k : ℝ) + 1) * a - (A + k * a) = a by ring,
    ENNReal.toReal_ofReal ha]

lemma mem_realPeriodCell_floor {A a u : ℝ} (ha : 0 < a) (hu : A ≤ u) :
    u ∈ realPeriodCell A a ⌊(u - A) / a⌋₊ := by
  have hr : 0 ≤ (u - A) / a := div_nonneg (sub_nonneg.mpr hu) ha.le
  have hlo := Nat.floor_le hr
  have hhi := Nat.lt_floor_add_one ((u - A) / a)
  change A + (⌊(u - A) / a⌋₊ : ℝ) * a ≤ u ∧
    u < A + ((⌊(u - A) / a⌋₊ : ℝ) + 1) * a
  constructor
  · have := (le_div_iff₀ ha).mp hlo; linarith
  · have := (div_lt_iff₀ ha).mp hhi; linarith

theorem periodic_weight_integral_lower_from_band
    {A B a μ : ℝ} {S : Set ℝ} {F W : ℝ → ℝ}
    (ha : 0 < a) (hAB : A ≤ B) (hμ : 0 ≤ μ)
    (_hF : Continuous F) (hW : Continuous W) (hW0 : ∀ u, 0 ≤ W u)
    (hper : Function.Periodic F a) (hmass : μ ≤ ∫ u in (0 : ℝ)..a, F u)
    (hS : S ⊆ Ioo A B)
    (hnear : ∀ u ∈ S, ∀ v ∈ Icc A B, |v - u| ≤ a → W v = F v) :
    (volume.real S - a) / a * μ ≤ ∫ u in A..B, W u := by
  classical
  let K : ℕ := ⌊(B - A) / a⌋₊
  let G : Finset ℕ := (Finset.range K).filter
    (fun k => ∃ u ∈ S, u ∈ realPeriodCell A a k)
  let U : Set ℝ := ⋃ k ∈ G, realPeriodCell A a k
  let V : Set ℝ := ⋃ k ∈ insert K G, realPeriodCell A a k
  have hK : (K : ℝ) * a ≤ B - A := by
    exact (le_div_iff₀ ha).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hAB) ha.le))
  have hKG : K ∉ G := by simp [G]
  have hcover : S ⊆ V := by
    intro u hu
    have huAB := hS hu
    let k : ℕ := ⌊(u - A) / a⌋₊
    have hku : u ∈ realPeriodCell A a k := mem_realPeriodCell_floor ha huAB.1.le
    have hkK : k ≤ K := Nat.floor_mono
      (div_le_div_of_nonneg_right (sub_le_sub_right huAB.2.le A) ha.le)
    have hkin : k ∈ insert K G := by
      by_cases hk : k = K
      · simp [hk]
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_ne hkK hk), u, hu, hku⟩
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hkin, hku⟩⟩
  have hVfinite : volume V ≠ ⊤ := by
    exact ((measure_biUnion_finset_le (μ := volume) (insert K G) (realPeriodCell A a)).trans_lt
      (ENNReal.sum_lt_top.mpr (fun k hk => measure_Ico_lt_top))).ne
  have hmeasure : volume.real S ≤ ((G.card : ℝ) + 1) * a := by
    calc
      volume.real S ≤ volume.real V := measureReal_mono hcover hVfinite
      _ ≤ ∑ k ∈ insert K G, volume.real (realPeriodCell A a k) :=
        measureReal_biUnion_finset_le _ _
      _ = ((G.card : ℝ) + 1) * a := by
        simp only [realPeriodCell_measure ha.le, Finset.sum_const, nsmul_eq_mul,
          Finset.card_insert_of_notMem hKG, Nat.cast_add, Nat.cast_one]
  have hcell : ∀ k ∈ G, realPeriodCell A a k ⊆ Icc A B := by
    intro k hk v hv
    have hkK : k < K := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hkR : (k : ℝ) + 1 ≤ K := by exact_mod_cast hkK
    change A + k * a ≤ v ∧ v < A + ((k : ℝ) + 1) * a at hv
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    constructor <;> nlinarith
  have hU : U ⊆ Icc A B := by
    intro v hv
    change v ∈ ⋃ k ∈ G, realPeriodCell A a k at hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨k, hk, hv⟩ := hv
    exact hcell k hk hv
  have hcellmass : ∀ k ∈ G, μ ≤ ∫ u in realPeriodCell A a k, W u := by
    intro k hk
    obtain ⟨v, hvS, hvcell⟩ := (Finset.mem_filter.mp hk).2
    have hstart : A + (k : ℝ) * a ≤ A + ((k : ℝ) + 1) * a := by nlinarith
    have heq : (∫ u in realPeriodCell A a k, W u) =
        ∫ u in realPeriodCell A a k, F u := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro u hu
      apply hnear v hvS u (hcell k hk hu)
      change A + k * a ≤ u ∧ u < A + ((k : ℝ) + 1) * a at hu
      change A + k * a ≤ v ∧ v < A + ((k : ℝ) + 1) * a at hvcell
      apply abs_le.mpr
      constructor <;> linarith
    rw [heq, realPeriodCell, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hstart]
    have hp := hper.intervalIntegral_add_eq (A + k * a) 0
    simp only [zero_add] at hp
    calc
      μ ≤ ∫ u in (0 : ℝ)..a, F u := hmass
      _ = ∫ u in A + (k : ℝ) * a..A + ((k : ℝ) + 1) * a, F u := by
        convert hp.symm using 1
        congr 1
        ring
  have hsum : (G.card : ℝ) * μ ≤ ∫ u in U, W u := by
    rw [show U = ⋃ k ∈ G, realPeriodCell A a k from rfl,
      integral_biUnion_finset (f := W) (μ := volume) G (s := realPeriodCell A a)
        (fun k _ => measurableSet_Ico)
        (fun k _ l _ hkl => realPeriodCells_disjoint ha hkl)
        (fun k hk => (hW.continuousOn.integrableOn_Icc).mono_set (hcell k hk))]
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hcellmass
  have hmono : (∫ u in U, W u) ≤ ∫ u in A..B, W u := by
    have h := setIntegral_mono_set (μ := volume) (f := W) (s := U) (t := Icc A B)
      (hW.continuousOn.integrableOn_Icc (μ := volume))
      (Filter.Eventually.of_forall hW0) (Filter.Eventually.of_forall hU)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB] at h
    exact h
  have hcard : (volume.real S - a) / a ≤ (G.card : ℝ) := by
    apply (div_le_iff₀ ha).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_right hcard hμ).trans (hsum.trans hmono)

end
end Erdos374Research
