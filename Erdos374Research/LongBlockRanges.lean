import Erdos374Research.LongBlockDetection

/-! UNCOMPILED. All rounding, derivative-period and support budgets are
uniform in the two block lengths. Fixed cofactor constants are absorbed
only after the outer integer n tends to infinity. -/

namespace Erdos374Research

open Filter Tao2026
open scoped Topology

lemma exists_fixed_integerAvoidingWeight :
    ∃ N : ℕ, 1 < Real.log (N : ℝ) ∧ plateauWidth N < 1 / 100 := by
  have h : ∀ᶠ N : ℕ in atTop, 11 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 11)
  obtain ⟨N, hN⟩ := h.exists
  refine ⟨N, by linarith, ?_⟩
  unfold plateauWidth
  apply (div_lt_iff₀ (by positivity : 0 < 10 * Real.log (N : ℝ) ^ 2)).mpr
  nlinarith

lemma exists_longBlockSquareWeight_C3_bound (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M P : ℕ,
      taoC3Norm (secondWeightLift (longBlockSquareWeight N M P)) ≤ C := by
  let A := taoC3Norm (secondWeightLift (fun _ : ℝ => 1))
  let B := taoC3Norm (secondWeightLift (integerAvoidingWeight N))
  have hA : 0 ≤ A := taoC3Norm_nonneg_of_smooth _
    (secondWeightLift_contDiff contDiff_const)
    (secondWeightLift_periodic (fun _ => rfl))
  have hB : 0 ≤ B := taoC3Norm_nonneg_of_smooth _
    (secondWeightLift_contDiff (integerAvoidingWeight_contDiff N))
    (secondWeightLift_periodic (integerAvoidingWeight_periodic N))
  refine ⟨A + B + 1, by positivity, ?_⟩
  intro M P
  unfold longBlockSquareWeight
  split_ifs <;> linarith

set_option maxHeartbeats 1000000 in
theorem eventually_longBlockScale_ranges {α ε γ D : ℝ} {N : ℕ}
    (_hα : 0 ≤ α) (hαε : α < ε) (hgap : α + γ < 1) (hD : 0 < D)
    (hN : 1 < Real.log (N : ℝ)) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 2 ≤ Real.log (n : ℝ) ∧
      longBlockSigma n ≤ plateauWidth N / 12 ∧
      ∀ L a c : ℕ, 0 < a → (a : ℝ) ≤ (n : ℝ) ^ α →
        (n : ℝ) ^ ε ≤ L → (L : ℝ) ≤ (n : ℝ) ^ γ →
        (c : ℝ) ≤ D * ((L : ℝ) * Real.log n + 1) →
        let P := longBlockPrimeScale n L
        2 ≤ P ∧ L < P ∧ c < P ∧ 2 * P ≤ n ∧
        (n : ℝ) ^ ε ≤ P ∧ 200 * (a : ℝ) ≤ P ∧
        (a : ℝ) ≤ (n : ℝ) / (32 * P) ∧
        2 * L ≤ P ^ 2 ∧ (L : ℝ) ≤ plateauWidth N / 12 * (P : ℝ) ^ 2 := by
  have hd : 0 < plateauWidth N := plateauWidth_pos hN
  have hlog : ∀ᶠ n : ℕ in atTop,
      max 2 (max (4 * D + 2) (12 / plateauWidth N + 2)) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  have hperiod := eventually_logPow_le_small_rpow 2
    (d := 1 - α - γ) (c := 1 / 64) (by linarith) (by norm_num)
  have hslow := eventually_logPow_le_small_rpow 0
    (d := ε - α) (c := 1 / 200) (by linarith) (by norm_num)
  filter_upwards [hlog, hperiod, hslow, eventually_ge_atTop (2 : ℕ)]
    with n hlogn hperiodn hslown hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog2 : 2 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hlogn
  have hlogD : 4 * D + 2 ≤ Real.log (n : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlogn)
  have hlogN : 12 / plateauWidth N + 2 ≤ Real.log (n : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlogn)
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hsigma : longBlockSigma n ≤ plateauWidth N / 12 := by
    unfold longBlockSigma
    apply (div_le_div_iff₀ (sq_pos_of_pos hlogpos) (by norm_num : (0 : ℝ) < 12)).mpr
    have hq : 12 ≤ plateauWidth N * Real.log n := by
      have h := (div_le_iff₀ hd).mp (by linarith : 12 / plateauWidth N ≤ Real.log n)
      nlinarith
    have hs : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hd.le]
  refine ⟨hnpos, hlog2, hsigma, ?_⟩
  intro L a c ha haN hLlow hLhigh hc
  let P := longBlockPrimeScale n L
  have hLpos : 0 < L := by
    have h : (0 : ℝ) < L := (Real.rpow_pos_of_pos hnR ε).trans_le hLlow
    exact_mod_cast h
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hPbounds := longBlockPrimeScale_bounds (by linarith : 1 ≤ Real.log (n : ℝ))
    (by omega : 1 ≤ L)
  have hP4 : 4 * (L : ℝ) ≤ P := by
    have hs : 4 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg L)).trans hPbounds.1
  have hLP : L < P := by exact_mod_cast (by nlinarith : (L : ℝ) < P)
  have hP2 : 2 ≤ P := by omega
  have hPR : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hcp : c < P := by
    have hbase : 1 ≤ (L : ℝ) * Real.log n := by nlinarith
    have hc' : (c : ℝ) ≤ 2 * D * (L : ℝ) * Real.log n := by
      have h := mul_le_mul_of_nonneg_left hbase hD.le
      nlinarith
    have hstrict : 2 * D * (L : ℝ) * Real.log n < (L : ℝ) * Real.log n ^ 2 := by
      nlinarith [mul_pos (by linarith : 0 < Real.log (n : ℝ) - 2 * D)
        (by positivity : 0 < (L : ℝ) * Real.log n)]
    exact_mod_cast (hc'.trans_lt (hstrict.trans_le hPbounds.1))
  have haP : 32 * (a : ℝ) * P ≤ n := by
    calc
      32 * (a : ℝ) * P ≤ 64 * ((n : ℝ) ^ α * (n : ℝ) ^ γ) * Real.log n ^ 2 := by
        have hPup : (P : ℝ) ≤ 2 * (n : ℝ) ^ γ * Real.log n ^ 2 :=
          hPbounds.2.trans (by gcongr)
        have h := mul_le_mul haN hPup (Nat.cast_nonneg P) (Real.rpow_nonneg hnR.le α)
        nlinarith
      _ = 64 * (n : ℝ) ^ (α + γ) * Real.log n ^ 2 := by rw [Real.rpow_add hnR]
      _ ≤ (n : ℝ) ^ (α + γ) * (n : ℝ) ^ (1 - α - γ) := by
        have h := mul_le_mul_of_nonneg_left hperiodn (Real.rpow_nonneg hnR.le (α + γ))
        nlinarith
      _ = n := by rw [← Real.rpow_add hnR]; convert Real.rpow_one (n : ℝ) using 1; ring
  have h2P : 2 * P ≤ n := by exact_mod_cast (by nlinarith : 2 * (P : ℝ) ≤ n)
  have hPε : (n : ℝ) ^ ε ≤ P := hLlow.trans (by exact_mod_cast hLP.le)
  have hslowP : 200 * (a : ℝ) ≤ P := by
    have hgapN : 200 ≤ (n : ℝ) ^ (ε - α) := by
      simp only [pow_zero] at hslown
      nlinarith
    calc
      200 * (a : ℝ) ≤ 200 * (n : ℝ) ^ α := by gcongr
      _ ≤ (n : ℝ) ^ α * (n : ℝ) ^ (ε - α) := by
        have h := mul_le_mul_of_nonneg_left hgapN (Real.rpow_nonneg hnR.le α)
        nlinarith
      _ = (n : ℝ) ^ ε := by rw [← Real.rpow_add hnR]; congr 1; ring
      _ ≤ P := hPε
  have hboundary : (a : ℝ) ≤ (n : ℝ) / (32 * P) :=
    (le_div_iff₀ (by positivity : 0 < 32 * (P : ℝ))).mpr (by nlinarith)
  have hsmall : 2 * L ≤ P ^ 2 := by
    have h : 2 * (L : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith
    exact_mod_cast h
  have hLPsigma : (L : ℝ) ≤ longBlockSigma n * P :=
    (div_le_iff₀ hPR).mp (longBlock_ratio_bounds (by linarith) (by omega)).2
  have hsquare : (L : ℝ) ≤ plateauWidth N / 12 * (P : ℝ) ^ 2 := by
    have h := hLPsigma.trans (mul_le_mul_of_nonneg_right hsigma hPR.le)
    have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
    exact h.trans (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity))
  exact ⟨hP2, hLP, hcp, h2P, hPε, hslowP, hboundary, hsmall, hsquare⟩

end Erdos374Research
