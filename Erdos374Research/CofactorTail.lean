import Erdos374Research.CofactorExclusions

/-!
# A uniformly small tail over every finite set of bad factorial indices

UNCOMPILED. This formulation permits finite witness selection for an
arbitrary finite set of cofactors; no unjustified infinite union of
finite-cardinality estimates is needed later.
-/

namespace Erdos374Research

open Filter Finset
open scoped BigOperators Topology

theorem sum_exp_large_indices_le (B : ℕ) (S : Finset ℕ)
    (hS : ∀ c ∈ S, B < c) :
    (∑ c ∈ S, Real.exp (-(c : ℝ) / 16)) ≤
      Real.exp (-((B + 1 : ℕ) : ℝ) / 16) / (1 - Real.exp (-1 / 16)) := by
  let r : ℝ := Real.exp (-1 / 16)
  let A : ℝ := Real.exp (-((B + 1 : ℕ) : ℝ) / 16)
  let T := S.image (fun c => c - (B + 1))
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hrnorm : ‖r‖ < 1 := by simpa only [Real.norm_of_nonneg hr0.le] using hr1
  have hinj : Set.InjOn (fun c => c - (B + 1)) S := by
    intro c hc d hd heq
    change c - (B + 1) = d - (B + 1) at heq
    have hcB := hS c hc
    have hdB := hS d hd
    omega
  have hterm : ∀ c ∈ S, Real.exp (-(c : ℝ) / 16) = A * r ^ (c - (B + 1)) := by
    intro c hc
    have hshift : c = (B + 1) + (c - (B + 1)) := by have := hS c hc; omega
    have hshiftR : (c : ℝ) = ((B + 1 : ℕ) : ℝ) + ((c - (B + 1) : ℕ) : ℝ) := by
      exact_mod_cast hshift
    have he : -(c : ℝ) / 16 = -((B + 1 : ℕ) : ℝ) / 16 +
        ((c - (B + 1) : ℕ) : ℝ) * (-1 / 16) := by linarith
    rw [he, Real.exp_add, Real.exp_nat_mul]
  have hsum : (∑ c ∈ S, Real.exp (-(c : ℝ) / 16)) = A * ∑ k ∈ T, r ^ k := by
    rw [Finset.mul_sum]
    dsimp only [T]
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl hterm
  have hgeo := hasSum_geometric_of_norm_lt_one hrnorm
  have hbound : (∑ k ∈ T, r ^ k) ≤ 1 / (1 - r) := by
    have h := hgeo.summable.sum_le_tsum T (fun k hk => pow_nonneg hr0.le k)
    simpa only [hgeo.tsum_eq, one_div] using h
  rw [hsum]
  calc
    A * ∑ k ∈ T, r ^ k ≤ A * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
    _ = _ := by dsimp [A, r]; ring

theorem tendsto_nat_mul_exp_sixteenth :
    Tendsto (fun B : ℕ => (B : ℝ) * Real.exp (-(B : ℝ) / 16)) atTop (𝓝 0) := by
  have hscale : Tendsto (fun B : ℕ => (B : ℝ) / 16) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 16)).mpr
      (tendsto_natCast_atTop_atTop : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop)
    convert h using 1
    ext B
    ring
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale).const_mul 16
  convert h using 1
  · ext B
    simp only [Function.comp_apply, pow_one]
    have he : -((B : ℝ) / 16) = -(B : ℝ) / 16 := by ring
    rw [he]
    ring
  · norm_num

theorem exists_badFactorialWeight_tail_small :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ S : Finset ℕ, (∀ c ∈ S, B < c) →
      (∑ c ∈ S, badFactorialWeight c) ≤ (1 : ℝ) / (8 * B) := by
  obtain ⟨C, hC, hdom⟩ := eventually_badFactorialWeight_le_exp
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdom
  let r : ℝ := Real.exp (-1 / 16)
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hden : 0 < 1 - r := by linarith
  have hlim : Tendsto (fun B : ℕ => (8 * C / (1 - r)) *
      ((B : ℝ) * Real.exp (-(B : ℝ) / 16))) atTop (𝓝 0) := by
    simpa using tendsto_nat_mul_exp_sixteenth.const_mul (8 * C / (1 - r))
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (8 * C / (1 - r)) * ((B : ℝ) * Real.exp (-(B : ℝ) / 16)) < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨B, hBs, hBl⟩ := (hsmall.and (eventually_ge_atTop (max 2 N))).exists
  have hB2 : 2 ≤ B := (le_max_left _ _).trans hBl
  have hBN : N ≤ B := (le_max_right _ _).trans hBl
  have hBR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hbudget : C * Real.exp (-(B : ℝ) / 16) / (1 - r) ≤ (1 : ℝ) / (8 * B) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
    have hle := hBs.le
    convert hle using 1
    ring
  refine ⟨B, hB2, ?_⟩
  intro S hS
  have hpoint : ∀ c ∈ S, badFactorialWeight c ≤ C * Real.exp (-(c : ℝ) / 16) := by
    intro c hc
    exact hN c (hBN.trans (hS c hc).le)
  have hexp : Real.exp (-((B + 1 : ℕ) : ℝ) / 16) ≤ Real.exp (-(B : ℝ) / 16) := by
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  calc
    (∑ c ∈ S, badFactorialWeight c) ≤ ∑ c ∈ S, C * Real.exp (-(c : ℝ) / 16) :=
      Finset.sum_le_sum hpoint
    _ = C * ∑ c ∈ S, Real.exp (-(c : ℝ) / 16) := by rw [Finset.mul_sum]
    _ ≤ C * (Real.exp (-((B + 1 : ℕ) : ℝ) / 16) / (1 - r)) :=
      mul_le_mul_of_nonneg_left (sum_exp_large_indices_le B S hS) hC.le
    _ ≤ C * (Real.exp (-(B : ℝ) / 16) / (1 - r)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hexp hden.le) hC.le
    _ = C * Real.exp (-(B : ℝ) / 16) / (1 - r) := by ring
    _ ≤ (1 : ℝ) / (8 * B) := hbudget

end Erdos374Research
