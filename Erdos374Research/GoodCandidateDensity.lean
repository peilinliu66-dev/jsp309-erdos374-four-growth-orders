import Erdos374Research.EvenCofactorDensity
import Erdos374Research.SmoothComponentDensity

/-!
# Candidate density after the large squarefree-prime restriction

UNCOMPILED. The predecessor map is injective on these positive candidates.
The discarded set is bounded by the independently proved full-interval
smooth-component estimate, so no independence assumption is made.
-/

namespace Erdos374Research

open Finset Filter
open scoped BigOperators Topology

noncomputable section

def HasLargeSquarefreePrime (β : ℝ) (X n : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q ∣ Tao2026.squarefreeComponent (n - 1) ∧ (X : ℝ) ^ β < q

def goodPrimeCofactorProducts (A : ℕ → Prop) (α β : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (primeCofactorProducts (cofactorPowerWindow A α X) X).filter
    (HasLargeSquarefreePrime β X)

def badPrimeCofactorProducts (A : ℕ → Prop) (α β : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (primeCofactorProducts (cofactorPowerWindow A α X) X).filter
    (fun n => ¬ HasLargeSquarefreePrime β X n)

theorem card_badPrimeCofactors_le_smooth (A : ℕ → Prop) (α β : ℝ)
    {X : ℕ} (hX : 4 ≤ X) :
    (badPrimeCofactorProducts A α β X).card ≤
      (smoothComponentsInUpperRange X β).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun n : ℕ => n - 1)
  · intro n hn
    change n - 1 ∈ smoothComponentsInUpperRange X β
    have hd := Finset.mem_filter.mp hn
    have hlo := primeCofactorProducts_gt_half hd.1
    have hhi := primeCofactorProducts_le hd.1
    have hn2 : 2 ≤ n := by omega
    have hsm : SmoothSquarefreeComponent ((X : ℝ) ^ β) (n - 1) := by
      intro q hq hqd
      by_contra hnot
      exact hd.2 ⟨q, hq, hqd, lt_of_not_ge hnot⟩
    have hpred : (X : ℝ) / 4 ≤ (n - 1 : ℕ) := by
      have hloR : (X : ℝ) < 2 * n := by exact_mod_cast hlo
      have hXR : (4 : ℝ) ≤ X := by exact_mod_cast hX
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hpred, hsm⟩
  · intro n hn m hm heq
    change n - 1 = m - 1 at heq
    have hnlo := primeCofactorProducts_gt_half (Finset.mem_filter.mp hn).1
    have hmlo := primeCofactorProducts_gt_half (Finset.mem_filter.mp hm).1
    omega

theorem card_candidates_le_good_add_bad (A : ℕ → Prop) (α β : ℝ) (X : ℕ) :
    (primeCofactorProducts (cofactorPowerWindow A α X) X).card ≤
      (goodPrimeCofactorProducts A α β X).card +
        (badPrimeCofactorProducts A α β X).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := primeCofactorProducts (cofactorPowerWindow A α X) X)
    (p := HasLargeSquarefreePrime β X)
  exact le_of_eq h.symm

theorem eventually_goodCandidate_count_lower (A : ℕ → Prop) {κ α β : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) (hαhalf : α < 1 / 2) (hβ : 0 < β)
    (hdensity : ∀ᶠ N : ℕ in atTop, κ * N ≤ (predicatePrefix A N).card) :
    ∀ᶠ X : ℕ in atTop,
      (κ * α / 32 - smallPrimeMomentConstant * Real.exp (-(1 / (3 * β)))) * X -
        2 * (X : ℝ) ^ (3 / 4 : ℝ) ≤ (goodPrimeCofactorProducts A α β X).card := by
  filter_upwards [positive_density_primeCofactorProducts A hκ hα hαhalf hdensity,
    eventually_smoothComponent_density_bound hβ, eventually_ge_atTop (4 : ℕ)]
      with X hc hs hX
  have hb : ((badPrimeCofactorProducts A α β X).card : ℝ) ≤
      (smoothComponentsInUpperRange X β).card := by
    exact_mod_cast card_badPrimeCofactors_le_smooth A α β hX
  have hsplit : ((primeCofactorProducts (cofactorPowerWindow A α X) X).card : ℝ) ≤
      (goodPrimeCofactorProducts A α β X).card + (badPrimeCofactorProducts A α β X).card := by
    exact_mod_cast card_candidates_le_good_add_bad A α β X
  nlinarith

theorem exists_small_candidate_exponent {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 100000 ∧
      smallPrimeMomentConstant * Real.exp (-(1 / (9 * ε))) ≤ κ * ε / 128 := by
  have hlim : Tendsto (fun r : ℕ => smallPrimeMomentConstant *
      ((r : ℝ) * Real.exp (-(r : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one, mul_zero] using
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        tendsto_natCast_atTop_atTop).const_mul smallPrimeMomentConstant
  have hevent : ∀ᶠ r : ℕ in atTop, smallPrimeMomentConstant *
      ((r : ℝ) * Real.exp (-(r : ℝ))) < κ / 1152 :=
    hlim.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < κ / 1152))
  obtain ⟨r, hr, hsmall⟩ := ((eventually_ge_atTop (100000 : ℕ)).and hevent).exists
  have hrR : (100000 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  refine ⟨1 / (9 * r), by positivity, ?_, ?_⟩
  · apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 9 * r) (by norm_num)).mpr
    linarith
  · have hid : (1 : ℝ) / (9 * (1 / (9 * r))) = r := by field_simp
    rw [hid]
    have hdivide := div_le_div_of_nonneg_right hsmall.le hrpos.le
    convert hdivide using 1 <;> field_simp
    norm_num

lemma eventually_two_rpow_three_quarters_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, 2 * (X : ℝ) ^ (3 / 4 : ℝ) ≤ δ * X := by
  have hp := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [hp.eventually (eventually_ge_atTop (2 / δ)),
    eventually_ge_atTop (1 : ℕ)] with X hpow hX
  have hpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hmul : 2 ≤ δ * (X : ℝ) ^ (1 / 4 : ℝ) :=
    by simpa only [mul_comm] using (div_le_iff₀ hδ).mp hpow
  have h := mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg hpos.le (3 / 4 : ℝ))
  have hid : (X : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) = X := by
    rw [← Real.rpow_add hpos]
    norm_num
  nlinarith

theorem good_candidates_linear_for_small_exponent (A : ℕ → Prop) {κ ε : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hεsmall : ε < 1 / 100000)
    (herror : smallPrimeMomentConstant * Real.exp (-(1 / (9 * ε))) ≤ κ * ε / 128)
    (hdensity : ∀ᶠ N : ℕ in atTop, κ * N ≤ (predicatePrefix A N).card) :
    ∀ᶠ X : ℕ in atTop, κ * ε / 256 * X ≤
      (goodPrimeCofactorProducts A (ε / 2) (3 * ε) X).card := by
  have hcount := eventually_goodCandidate_count_lower A hκ
    (show 0 < ε / 2 by positivity) (show ε / 2 < 1 / 2 by linarith)
    (show 0 < 3 * ε by positivity) hdensity
  have htail := eventually_two_rpow_three_quarters_le
    (show 0 < κ * ε / 256 by positivity)
  filter_upwards [hcount, htail] with X hc ht
  have hden : (1 : ℝ) / (3 * (3 * ε)) = 1 / (9 * ε) := by ring
  rw [hden] at hc
  have herrX := mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg X)
  nlinarith

/-- Both cofactor families use the same sufficiently small exponent. This
is the complete candidate-supply step for the five- and six-factor cases. -/
theorem two_candidate_families_positive_density :
    ∃ ε δ : ℝ, 0 < ε ∧ ε < 1 / 100000 ∧ 0 < δ ∧
      (∀ᶠ X : ℕ in atTop, δ * X ≤
        (goodPrimeCofactorProducts EvenSquarefreeCofactor (ε / 2) (3 * ε) X).card) ∧
      (∀ᶠ X : ℕ in atTop, δ * X ≤
        (goodPrimeCofactorProducts AdmissibleCofactor (ε / 2) (3 * ε) X).card) := by
  obtain ⟨κR, hκR, hR⟩ := admissibleCofactors_positive_lower_density
  let κ := min κR (1 / 24 : ℝ)
  have hκ : 0 < κ := lt_min hκR (by norm_num)
  have heven : ∀ᶠ X : ℕ in atTop, κ * X ≤
      (predicatePrefix EvenSquarefreeCofactor X).card := by
    filter_upwards [evenSquarefree_positive_lower_density] with X hX
    exact (mul_le_mul_of_nonneg_right (min_le_right κR (1 / 24 : ℝ))
      (Nat.cast_nonneg X)).trans hX
  have hadm : ∀ᶠ X : ℕ in atTop, κ * X ≤
      (predicatePrefix AdmissibleCofactor X).card := by
    filter_upwards [hR] with X hX
    exact (mul_le_mul_of_nonneg_right (min_le_left κR (1 / 24 : ℝ))
      (Nat.cast_nonneg X)).trans hX
  obtain ⟨ε, hε, hεsmall, herror⟩ := exists_small_candidate_exponent hκ
  exact ⟨ε, κ * ε / 256, hε, hεsmall, by positivity,
    good_candidates_linear_for_small_exponent EvenSquarefreeCofactor hκ hε hεsmall herror heven,
    good_candidates_linear_for_small_exponent AdmissibleCofactor hκ hε hεsmall herror hadm⟩

end
end Erdos374Research
