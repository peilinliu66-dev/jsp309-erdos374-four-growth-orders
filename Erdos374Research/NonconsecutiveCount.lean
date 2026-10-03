import Erdos374Research.HardFibreAsymptotics
import Tao2026.Theorem19And110Complete

/-!
UNCOMPILED. A fixed sub-square-root bound for the actual non-one-term
three-factorial endpoints. The small-index branch is the existing Tao2026
Pell count. The complementary branch uses the new finite Gallagher adapter.
The original mathematical improvement is Yudin's two-prime-family idea;
the deliberately coarse split here only aims at one exponent below 1/2.
-/

namespace Erdos374Research

open Tao2026 Filter Finset Asymptotics
open scoped BigOperators Topology

noncomputable section

def largeIndexSourceIntervals (X : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo X) := by
  classical
  exact (nontrivialFactorialThreeIntervalsUpTo X).attach.filter fun t =>
    (t.1.2 : ℝ) * Real.log ((X : ℝ) + 2) / 100 <
      (chosenFactorialRelationCertificate X t).factorialIndex

def largeIndexSourceEndpoints (X : ℕ) : Finset ℕ :=
  (largeIndexSourceIntervals X).image fun t => t.1.1 + t.1.2

lemma mem_largeIndexSourceIntervals {X : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo X)} :
    t ∈ largeIndexSourceIntervals X ↔
      (t.1.2 : ℝ) * Real.log ((X : ℝ) + 2) / 100 <
        (chosenFactorialRelationCertificate X t).factorialIndex := by
  classical
  simp [largeIndexSourceIntervals]

lemma nontrivialFactorialThreeCount_le_small_large (X : ℕ) :
    nontrivialFactorialThreeCount X ≤
      (factorialSmallIndexSourceEndpointsUpTo X).card + (largeIndexSourceEndpoints X).card := by
  classical
  have hsub : nontrivialFactorialThreeNumbersUpTo X ⊆
      factorialSmallIndexSourceEndpointsUpTo X ∪ largeIndexSourceEndpoints X := by
    intro n hn
    obtain ⟨v, hv, hnv⟩ := Finset.mem_image.mp
      (nontrivialFactorialThreeNumbersUpTo_subset_endpointImage X hn)
    let t : ↥(nontrivialFactorialThreeIntervalsUpTo X) := ⟨v, hv⟩
    by_cases hsmall : ((chosenFactorialRelationCertificate X t).factorialIndex : ℝ) ≤
        (v.2 : ℝ) * Real.log ((X : ℝ) + 2) / 100
    · apply Finset.mem_union_left
      change n ∈ (factorialSmallIndexSourceIntervalsUpTo X).image _
      exact Finset.mem_image.mpr ⟨t,
        mem_factorialSmallIndexSourceIntervalsUpTo.mpr hsmall, hnv⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨t,
        mem_largeIndexSourceIntervals.mpr (lt_of_not_ge hsmall), hnv⟩
  rw [← card_nontrivialFactorialThreeNumbersUpTo]
  exact (Finset.card_le_card hsub).trans
    (Finset.card_union_le (factorialSmallIndexSourceEndpointsUpTo X)
      (largeIndexSourceEndpoints X))

def hardParameterPairs (X A G : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 A).product (Finset.Icc 1 G)).filter fun v =>
    (v.2 : ℝ) * Real.log ((X : ℝ) + 2) / 100 < v.1

def hardEndpointEnvelope (X A G : ℕ) : Finset ℕ :=
  (hardParameterPairs X A G).biUnion fun v =>
    (hardFactorialFibre X v.1 v.2).image fun N => N + v.2

lemma largeIndexSourceEndpoints_subset_envelope {X A G : ℕ}
    (hbudgets : ∀ t : ↥(nontrivialFactorialThreeIntervalsUpTo X),
      (chosenFactorialRelationCertificate X t).factorialIndex ≤ A ∧ t.1.2 ≤ G) :
    largeIndexSourceEndpoints X ⊆ hardEndpointEnvelope X A G := by
  classical
  intro n hn
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
  let c := chosenFactorialRelationCertificate X t
  have hc := chosenFactorialRelationCertificate_spec X t
  change c.Certifies t.1.1 t.1.2 at hc
  have hbase := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  have hhard := mem_largeIndexSourceIntervals.mp ht
  change (t.1.2 : ℝ) * Real.log ((X : ℝ) + 2) / 100 < c.factorialIndex at hhard
  have hp : (c.factorialIndex, t.1.2) ∈ hardParameterPairs X A G := by
    rw [hardParameterPairs, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hc.1, (hbudgets t).1⟩,
        Finset.mem_Icc.mpr ⟨(by decide : 1 ≤ 2).trans hbase.2.1,
          (hbudgets t).2⟩⟩, hhard⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(c.factorialIndex, t.1.2), hp, Finset.mem_image.mpr ⟨t.1.1, ?_, rfl⟩⟩
  apply mem_hardFactorialFibre.mpr
  exact ⟨⟨hc.1.trans (Nat.le_of_lt hc.2.1), hbase.1⟩,
    hc.2.1, hbase.2.2.2.1, hc.2.2.1⟩

lemma hardEndpointEnvelope_card_bound {X A G : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (hfibres : ∀ a ∈ Finset.Icc 1 A, ∀ H ∈ Finset.Icc 1 G,
      (H : ℝ) * Real.log ((X : ℝ) + 2) / 100 < a →
      ((hardFactorialFibre X a H).card : ℝ) ≤ E) :
    ((hardEndpointEnvelope X A G).card : ℝ) ≤ (A : ℝ) * G * E := by
  classical
  have hcard : (hardParameterPairs X A G).card ≤ A * G := by
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  have hraw : (hardEndpointEnvelope X A G).card ≤
      ∑ v ∈ hardParameterPairs X A G, (hardFactorialFibre X v.1 v.2).card := by
    refine Finset.card_biUnion_le.trans ?_
    exact Finset.sum_le_sum fun v hv => Finset.card_image_le
  calc
    ((hardEndpointEnvelope X A G).card : ℝ) ≤
        ∑ v ∈ hardParameterPairs X A G, ((hardFactorialFibre X v.1 v.2).card : ℝ) := by
      exact_mod_cast hraw
    _ ≤ ∑ _v ∈ hardParameterPairs X A G, E := by
      apply Finset.sum_le_sum
      intro v hv
      have hd := Finset.mem_filter.mp hv
      have hpair := Finset.mem_product.mp hd.1
      exact hfibres v.1 hpair.1 v.2 hpair.2 hd.2
    _ = ((hardParameterPairs X A G).card : ℝ) * E := by simp
    _ ≤ ((A * G : ℕ) : ℝ) * E :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE
    _ = (A : ℝ) * G * E := by push_cast; ring

lemma eventually_le_rpow_of_powerUpperBound_zero (f : ℕ → ℕ)
    (hf : PowerUpperBound (fun X => (f X : ℝ)) 0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop, (f X : ℝ) ≤ (X : ℝ) ^ η := by
  obtain ⟨C, hC⟩ := (hf (η / 2) (by positivity)).bound
  have hCpower : ∀ᶠ X : ℕ in atTop, C ≤ (X : ℝ) ^ (η / 2) :=
    ((_root_.tendsto_rpow_atTop (by positivity : 0 < η / 2)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop C)
  filter_upwards [hC, hCpower, eventually_ge_atTop (1 : ℕ)] with X hX hCX hX1
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hp0 : 0 ≤ (X : ℝ) ^ (η / 2) := Real.rpow_nonneg hXpos.le _
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), zero_add,
    Real.norm_of_nonneg hp0] at hX
  calc
    (f X : ℝ) ≤ C * (X : ℝ) ^ (η / 2) := hX
    _ ≤ (X : ℝ) ^ (η / 2) * (X : ℝ) ^ (η / 2) :=
      mul_le_mul_of_nonneg_right hCX hp0
    _ = (X : ℝ) ^ η := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring

theorem eventually_largeIndexSourceEndpoints_card :
    ∀ᶠ X : ℕ in atTop, ((largeIndexSourceEndpoints X).card : ℝ) ≤
      16000 * (X : ℝ) ^ d3HardExponent := by
  have hA := eventually_le_rpow_of_powerUpperBound_zero factorialLemma41IndexBudget
    factorialLemma41IndexBudget_powerUpperBound (η := d3Eta) (by norm_num [d3Eta])
  have hG := eventually_le_rpow_of_powerUpperBound_zero factorialLemma42GapBudget
    factorialLemma42GapBudget_powerUpperBound (η := d3Eta) (by norm_num [d3Eta])
  have hbudget := eventually_nontrivialFactorialThreeInterval_parameters_le_budgets
    taoLemma42_unconditional
  filter_upwards [hA, hG, hbudget, eventually_hardFactorialFibre_card,
    eventually_ge_atTop (1 : ℕ)] with X hAX hGX hbudgetX hfibreX hX
  let A := factorialLemma41IndexBudget X
  let G := factorialLemma42GapBudget X
  have hsub := largeIndexSourceEndpoints_subset_envelope hbudgetX
  have hcount := hardEndpointEnvelope_card_bound
    (X := X) (A := A) (G := G)
    (E := 16000 * (X : ℝ) ^ d3PrimeUpperExponent) (by positivity) (by
      intro a ha H hH hhard
      have ha' := Finset.mem_Icc.mp ha
      have hH' := Finset.mem_Icc.mp hH
      exact hfibreX a H ha'.1 hH'.1
        ((show (a : ℝ) ≤ A by exact_mod_cast ha'.2).trans hAX)
        ((show (H : ℝ) ≤ G by exact_mod_cast hH'.2).trans hGX) hhard)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  calc
    ((largeIndexSourceEndpoints X).card : ℝ) ≤
        (hardEndpointEnvelope X A G).card := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (A : ℝ) * G * (16000 * (X : ℝ) ^ d3PrimeUpperExponent) := hcount
    _ ≤ (X : ℝ) ^ d3Eta * (X : ℝ) ^ d3Eta *
        (16000 * (X : ℝ) ^ d3PrimeUpperExponent) := by gcongr
    _ = 16000 * (X : ℝ) ^ (d3PrimeUpperExponent + 2 * d3Eta) := by
      rw [show (X : ℝ) ^ d3Eta * (X : ℝ) ^ d3Eta *
          (16000 * (X : ℝ) ^ d3PrimeUpperExponent) =
        16000 * ((X : ℝ) ^ d3Eta * (X : ℝ) ^ d3Eta *
          (X : ℝ) ^ d3PrimeUpperExponent) by ring,
        ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
      congr 2
      ring
    _ ≤ 16000 * (X : ℝ) ^ d3HardExponent := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le hXR
        (by norm_num [d3PrimeUpperExponent, d3Eta, d3HardExponent])

/-- The completed bounded task: the literal upstream non-one-term endpoint
count has a fixed exponent 1249/2500 strictly below one half. -/
theorem eventually_nontrivialFactorialThreeCount_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      (nontrivialFactorialThreeCount X : ℝ) ≤ C * (X : ℝ) ^ d3HardExponent := by
  have hsmall := factorialSmallIndexSourceEndpointCount_powerUpperBound_of_lemma42
    taoLemma42_unconditional
  obtain ⟨C₀, hC₀⟩ := (hsmall (1 / 8) (by norm_num)).bound
  let C := |C₀| + 16001
  have hC : 0 < C := by dsimp only [C]; linarith [abs_nonneg C₀]
  refine ⟨C, hC, ?_⟩
  filter_upwards [hC₀, eventually_largeIndexSourceEndpoints_card,
    eventually_ge_atTop (1 : ℕ)] with X hsmallX hlargeX hX
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hp0 : 0 ≤ (X : ℝ) ^ (3 / 8 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg X) _
  have hsmall' : ((factorialSmallIndexSourceEndpointsUpTo X).card : ℝ) ≤
      C₀ * (X : ℝ) ^ (3 / 8 : ℝ) := by
    norm_num only [show (1 / 4 + 1 / 8 : ℝ) = 3 / 8 by norm_num,
      Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hp0] at hsmallX
    exact hsmallX
  have hsmallBound : ((factorialSmallIndexSourceEndpointsUpTo X).card : ℝ) ≤
      (|C₀| + 1) * (X : ℝ) ^ d3HardExponent := by
    refine hsmall'.trans ?_
    calc
      C₀ * (X : ℝ) ^ (3 / 8 : ℝ) ≤ (|C₀| + 1) * (X : ℝ) ^ (3 / 8 : ℝ) := by
        gcongr
        linarith [le_abs_self C₀]
      _ ≤ (|C₀| + 1) * (X : ℝ) ^ d3HardExponent := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hXR (by norm_num [d3HardExponent])
  have hsplit : (nontrivialFactorialThreeCount X : ℝ) ≤
      (factorialSmallIndexSourceEndpointsUpTo X).card + (largeIndexSourceEndpoints X).card := by
    exact_mod_cast nontrivialFactorialThreeCount_le_small_large X
  calc
    (nontrivialFactorialThreeCount X : ℝ) ≤
        (factorialSmallIndexSourceEndpointsUpTo X).card + (largeIndexSourceEndpoints X).card := hsplit
    _ ≤ (|C₀| + 1) * (X : ℝ) ^ d3HardExponent +
        16000 * (X : ℝ) ^ d3HardExponent := add_le_add hsmallBound hlargeX
    _ = C * (X : ℝ) ^ d3HardExponent := by dsimp only [C]; ring

theorem nontrivialFactorialThreeCount_isBigO_rpow :
    (fun X : ℕ => (nontrivialFactorialThreeCount X : ℝ)) =O[atTop]
      (fun X : ℕ => (X : ℝ) ^ d3HardExponent) := by
  obtain ⟨C, hC, hbound⟩ := eventually_nontrivialFactorialThreeCount_le
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hbound] with X hX
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) d3HardExponent)] using hX

theorem d3HardExponent_lt_half : d3HardExponent < (1 / 2 : ℝ) := by
  norm_num [d3HardExponent]

end
end Erdos374Research
