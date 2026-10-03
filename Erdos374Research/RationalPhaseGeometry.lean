import Erdos374Research.PairedFourier

/-!
UNCOMPILED. Integer separation of rational linear coefficients and the resulting
stationary-point bound. This uses theta=t/a from Yudin's large-prime-factor
reduction and does not assume a Diophantine approximation theorem.
-/

namespace Erdos374Research

open Tao2026 Filter
open scoped BigOperators Topology

noncomputable section

lemma pairedLinear_integer_identity (q : ℤ × ℤ) {a : ℕ} (ha : 0 < a)
    (t : ℕ) (N : ℝ) :
    (a : ℝ) * pairedLinear q ((t : ℝ) / a) N =
      (((a : ℤ) * q.1 + (t : ℤ) * q.2 : ℤ) : ℝ) * N := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  unfold pairedLinear
  push_cast
  field_simp [ha0]

lemma pairedLinear_separation (q : ℤ × ℤ) {a : ℕ} (ha : 0 < a)
    (t : ℕ) {N : ℝ} (hN : 0 < N)
    (hU : pairedLinear q ((t : ℝ) / a) N ≠ 0) :
    N / a ≤ |pairedLinear q ((t : ℝ) / a) N| := by
  let z : ℤ := (a : ℤ) * q.1 + (t : ℤ) * q.2
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hid := pairedLinear_integer_identity q ha t N
  change (a : ℝ) * pairedLinear q ((t : ℝ) / a) N = (z : ℝ) * N at hid
  have hz : z ≠ 0 := by
    intro hz
    have hid0 : (a : ℝ) * pairedLinear q ((t : ℝ) / a) N = 0 := by
      simpa only [hz, Int.cast_zero, zero_mul] using hid
    exact (mul_ne_zero haR.ne' hU) hid0
  have hzabs : (1 : ℤ) ≤ |z| := by
    rcases lt_or_gt_of_ne hz with hzneg | hzpos
    · rw [abs_of_neg hzneg]
      omega
    · rw [abs_of_pos hzpos]
      omega
  have hzR : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast hzabs
  have habs := congrArg abs hid
  simp only [abs_mul, abs_of_pos haR, abs_of_pos hN] at habs
  apply (div_le_iff₀ haR).2
  change (a : ℝ) * |pairedLinear q ((t : ℝ) / a) N| = |(z : ℝ)| * N at habs
  nlinarith

lemma pairedLinear_box_bound {R : ℕ} {q : ℤ × ℤ}
    (hq : q ∈ fourierFrequencyBox R) {θ N : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hN : 0 ≤ N) :
    |pairedLinear q θ N| ≤ 2 * (R : ℝ) * N := by
  have hq' := mem_fourierFrequencyBox.mp hq
  have hq1 : |(q.1 : ℝ)| ≤ R := by exact_mod_cast hq'.1
  have hq2 : |(q.2 : ℝ)| ≤ R := by exact_mod_cast hq'.2
  unfold pairedLinear
  rw [abs_mul, abs_of_nonneg hN]
  apply mul_le_mul_of_nonneg_right _ hN
  calc
    |(q.1 : ℝ) + (q.2 : ℝ) * θ| ≤ |(q.1 : ℝ)| + |(q.2 : ℝ) * θ| := abs_add_le _ _
    _ = |(q.1 : ℝ)| + |(q.2 : ℝ)| * θ := by rw [abs_mul, abs_of_nonneg hθ]
    _ ≤ (R : ℝ) + (R : ℝ) * 1 := by gcongr
    _ = 2 * (R : ℝ) := by ring

lemma pairedQuadratic_box_bound {R : ℕ} {r : ℤ × ℤ}
    (hr : r ∈ fourierFrequencyBox R) {M N : ℝ} (hM : |M| ≤ N) :
    |pairedQuadratic r M| ≤ (R : ℝ) * N := by
  have hr2 : |(r.2 : ℝ)| ≤ R := by exact_mod_cast (mem_fourierFrequencyBox.mp hr).2
  unfold pairedQuadratic
  rw [abs_mul]
  exact mul_le_mul hr2 hM (abs_nonneg _) (Nat.cast_nonneg _)

lemma paired_stationaryPoint_le {a R : ℕ} (ha : 0 < a) (t : ℕ)
    (q r : ℤ × ℤ) {N M : ℝ} (hN : 0 < N) (hM : |M| ≤ N)
    (hr : r ∈ fourierFrequencyBox R)
    (hU : pairedLinear q ((t : ℝ) / a) N ≠ 0) :
    quadraticReciprocalStationaryPoint
      (pairedLinear q ((t : ℝ) / a) N) (pairedQuadratic r M) ≤
        2 * (a : ℝ) * R := by
  let U := pairedLinear q ((t : ℝ) / a) N
  let V := pairedQuadratic r M
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hsep := (div_le_iff₀ haR).mp (pairedLinear_separation q ha t hN hU)
  have hV := pairedQuadratic_box_bound hr hM
  have hUabs : 0 < |U| := abs_pos.mpr hU
  have hnum : 2 * |V| ≤ (2 * (a : ℝ) * R) * |U| := by
    dsimp only [U, V] at *
    calc
      2 * |pairedQuadratic r M| ≤ 2 * ((R : ℝ) * N) := by gcongr
      _ ≤ 2 * ((R : ℝ) * (|pairedLinear q ((t : ℝ) / a) N| * a)) := by gcongr
      _ = _ := by ring
  change -2 * V / U ≤ _
  calc
    -2 * V / U ≤ |-2 * V / U| := le_abs_self _
    _ = 2 * |V| / |U| := by rw [abs_div, abs_mul]; norm_num
    _ ≤ 2 * (a : ℝ) * R := (div_le_iff₀ hUabs).2 hnum

/-- The rational-parameter mode estimate has only explicit numerical range
conditions. In particular, its conclusion is not an input hypothesis. -/
theorem eventually_rational_modes (S : ℕ) :
    ∀ᶠ P : ℕ in atTop, ∀ (l u a t R : ℕ) (N M : ℝ),
      P ≤ l → l < u → u ≤ 2 * P → 0 < a → t < a →
      0 < N → |M| ≤ N → 4 * (a : ℝ) * R ≤ P →
      2 * (R : ℝ) * N ≤ Real.exp ((Real.log P) ^ (5 / 4 : ℝ)) →
      ∀ q ∈ fourierFrequencyBox R, ∀ r ∈ fourierFrequencyBox R,
      ‖primeFourierModeSum (P : ℝ) (Set.Ico (l : ℝ) (u : ℝ)) (1, 1)
          (pairedLinear q ((t : ℝ) / a) N) (pairedQuadratic r M) 2 -
        fourierModeIntegral (Set.Ico (l : ℝ) (u : ℝ)) (1, 1)
          (pairedLinear q ((t : ℝ) / a) N) (pairedQuadratic r M) 2‖ ≤
        (P : ℝ) / (Real.log P) ^ S := by
  have hmode := eventually_primeMode_comparison (K := 1) (ε := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) S
  filter_upwards [hmode] with P hmodeP
  intro l u a t R N M hPl hlu huP ha ht hN hM hgeom hsize q hq r hr
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hθ0 : 0 ≤ (t : ℝ) / a := by positivity
  have hθ1 : (t : ℝ) / a ≤ 1 := by
    apply (div_le_one haR).2
    exact_mod_cast ht.le
  have hU := (pairedLinear_box_bound hq hθ0 hθ1 hN.le).trans hsize
  have hV := (pairedQuadratic_box_bound hr hM).trans
    ((show (R : ℝ) * N ≤ 2 * (R : ℝ) * N by
      nlinarith [mul_nonneg (Nat.cast_nonneg R) hN.le]).trans hsize)
  have hstationary :
      (((0 < (pairedLinear q ((t : ℝ) / a) N) ∧ pairedQuadratic r M < 0) ∨
        (pairedLinear q ((t : ℝ) / a) N < 0 ∧ 0 < pairedQuadratic r M)) →
        quadraticReciprocalStationaryPoint
          (pairedLinear q ((t : ℝ) / a) N) (pairedQuadratic r M) ≤ (P : ℝ) / 2) := by
    intro hs
    have hne : pairedLinear q ((t : ℝ) / a) N ≠ 0 := by
      rcases hs with hs | hs
      · exact hs.1.ne'
      · exact hs.1.ne
    exact (paired_stationaryPoint_le ha t q r hN hM hr hne).trans (by linarith)
  apply hmodeP l u (1, 1) (pairedLinear q ((t : ℝ) / a) N)
    (pairedQuadratic r M) hPl hlu huP
  · simpa only [Int.cast_one, one_mul] using hstationary
  · simpa only [Int.cast_one, one_mul,
      show (3 / 2 - 1 / 4 : ℝ) = 5 / 4 by norm_num] using hU
  · simpa only [Int.cast_one, one_mul,
      show (3 / 2 - 1 / 4 : ℝ) = 5 / 4 by norm_num] using hV

end
end Erdos374Research
