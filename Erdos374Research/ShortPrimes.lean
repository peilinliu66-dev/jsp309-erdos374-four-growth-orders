import Erdos374Research.BlockPacking
import GafniTao.AllIntervals
import Tao2026.PrimeIntervals

/-!
# Uniform short prime intervals from the pinned Gafni--Tao theorem

UNCOMPILED original adapter. The analytic theorem is attributed to the
Gafni--Tao/Guth--Maynard formalization in smccolm/Lean at the fixed dependency
commit. The present code supplies finite-sum and endpoint transfers.
-/

namespace Erdos374Research

open Filter Finset MeasureTheory
open scoped BigOperators Topology ArithmeticFunction.vonMangoldt

theorem primeMangoldtIntervalSum_eq_theta_sub (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    GafniTao.primeMangoldtIntervalSum x y =
      Chebyshev.theta (x + y) - Chebyshev.theta x := by
  classical
  let f : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have hfloor : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (by linarith)
  have hdisj : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hunion : Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊ =
      Finset.Ioc 0 ⌊x + y⌋₊ :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hfloor
  have hsum := Finset.sum_union hdisj (f := f)
  rw [hunion] at hsum
  have hprime : GafniTao.primeMangoldtIntervalSum x y =
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f n := by
    unfold GafniTao.primeMangoldtIntervalSum
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [f]
    split_ifs with hp
    · exact ArithmeticFunction.vonMangoldt_apply_prime hp
    · rfl
  rw [hprime, Chebyshev.theta, Chebyshev.theta,
    Finset.sum_filter, Finset.sum_filter]
  change (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, f n) =
    (∑ n ∈ Finset.Ioc 0 ⌊x + y⌋₊, f n) -
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n)
  linarith

theorem eventually_primePowerTail_le_quarter {theta : ℝ}
    (htheta : 0 < theta) (hupper : theta ≤ 1) :
    ∀ᶠ x : ℝ in atTop,
      GafniTao.primePowerTailIntervalSum x (x ^ theta) ≤ x ^ theta / 4 := by
  have hsmall :=
    (GafniTao.localReplacementRemainderEnvelope_isLittleO (u := 1) htheta).bound
      (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hsmall, eventually_ge_atTop (3 : ℝ)] with x hx hxlarge
  have hnonneg : 0 ≤ x := by linarith
  calc
    GafniTao.primePowerTailIntervalSum x (x ^ theta) ≤
        GafniTao.localReplacementRemainderEnvelope theta 1 x :=
      Tao2026.primePowerTailIntervalSum_le_remainderEnvelope hxlarge hupper
    _ ≤ |GafniTao.localReplacementRemainderEnvelope theta 1 x| := le_abs_self _
    _ ≤ (1 / 4 : ℝ) * |x ^ theta| := hx
    _ = x ^ theta / 4 := by
      rw [abs_of_nonneg (Real.rpow_nonneg hnonneg theta)]
      ring

/-- The exact fixed exponent 3/5 is covered by the stronger public
all-interval theorem (whose lower threshold is 17/30). -/
theorem eventually_theta_forward_three_fifths :
    ∀ᶠ x : ℝ in atTop,
      x ^ (3 / 5 : ℝ) / 2 ≤
        Chebyshev.theta (x + x ^ (3 / 5 : ℝ)) - Chebyshev.theta x := by
  have hnative := GafniTao.gafniTaoTheorem11_allIntervals_guthMaynard_native
    (theta := (3 / 5 : ℝ)) (by norm_num) (by norm_num)
  have hpsi := hnative (1 / 4) (by norm_num)
  have htail := eventually_primePowerTail_le_quarter
    (theta := (3 / 5 : ℝ)) (by norm_num) (by norm_num)
  filter_upwards [hpsi, htail, eventually_ge_atTop (0 : ℝ)] with x hx ht hx0
  have hlow : -(1 / 4 : ℝ) * x ^ (3 / 5 : ℝ) <
      GafniTao.mangoldtIntervalSum x (x ^ (3 / 5 : ℝ)) - x ^ (3 / 5 : ℝ) := by
    simpa only [GafniTao.shortIntervalDiscrepancy, GafniTao.mangoldtShortSum,
      neg_mul] using (abs_lt.mp hx).1
  have hsplit := GafniTao.mangoldtIntervalSum_eq_prime_add_tail x (x ^ (3 / 5 : ℝ))
  rw [primeMangoldtIntervalSum_eq_theta_sub x (Real.rpow_nonneg hx0 _)] at hsplit
  linarith

theorem rpow_half_ge_half {m theta : ℝ} (hm : 0 < m)
    (_hlo : 0 ≤ theta) (hhi : theta ≤ 1) :
    m ^ theta / 2 ≤ (m / 2) ^ theta := by
  have htwo : (2 : ℝ) ^ theta ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hhi
  have hid : m ^ theta = (2 : ℝ) ^ theta * (m / 2) ^ theta := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right htwo
    (Real.rpow_nonneg (show 0 ≤ m / 2 by positivity) theta)
  rw [← hid] at hmul
  linarith

/-- A forward lower bound for one fixed power length implies a lower bound
for every longer backward interval. All intervals here have real endpoints. -/
theorem uniform_backward_mass_of_forward
    (F : ℝ → ℝ) (hF : Monotone F) {theta : ℝ}
    (hlo : 0 ≤ theta) (hhi : theta ≤ 1)
    (hforward : ∀ᶠ x : ℝ in atTop,
      x ^ theta / 2 ≤ F (x + x ^ theta) - F x) :
    ∀ᶠ m : ℝ in atTop, ∀ y : ℝ,
      m ^ theta ≤ y → y ≤ m / 2 → y / 8 ≤ F m - F (m - y) := by
  classical
  obtain ⟨M, hM⟩ := eventually_atTop.mp hforward
  filter_upwards [eventually_ge_atTop (max 2 (2 * M))] with m hm y hBy hym
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hm
  have hmM : 2 * M ≤ m := (le_max_right _ _).trans hm
  have hmpos : 0 < m := by linarith
  let B : ℝ := m ^ theta
  let A : ℝ := m - y
  let N : ℕ := ⌊y / B⌋₊
  have hBpos : 0 < B := Real.rpow_pos_of_pos hmpos theta
  have hypos : 0 < y := hBpos.trans_le hBy
  have hratio : 1 ≤ y / B := (le_div_iff₀ hBpos).mpr (by simpa using hBy)
  have hN : 1 ≤ N := by
    dsimp [N]
    exact (Nat.one_le_floor_iff (y / B)).2 hratio
  have hNB : (N : ℝ) * B ≤ y := by
    have hf := Nat.floor_le (show 0 ≤ y / B by positivity)
    change (N : ℝ) ≤ y / B at hf
    exact (le_div_iff₀ hBpos).mp hf
  have hyNB : y < ((N : ℝ) + 1) * B := by
    have hf := Nat.lt_floor_add_one (y / B)
    change y / B < (N : ℝ) + 1 at hf
    exact (div_lt_iff₀ hBpos).mp hf
  have hNBhalf : y / 2 ≤ (N : ℝ) * B := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hscale := mul_le_mul_of_nonneg_right hNreal hBpos.le
    nlinarith
  have hblock : ∀ j ∈ Finset.range N,
      B / 4 ≤ F (A + B * (j + 1 : ℕ)) - F (A + B * j) := by
    intro j hj
    have hjN : j + 1 ≤ N := Finset.mem_range.mp hj
    have hjNr : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hjN
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    let x : ℝ := A + B * j
    have hxlo : m / 2 ≤ x := by
      have hprod : 0 ≤ B * (j : ℝ) := mul_nonneg hBpos.le hj0
      dsimp [x, A]
      linarith
    have hxhi : x + B ≤ m := by
      have hmul := mul_le_mul_of_nonneg_left hjNr hBpos.le
      push_cast at hmul
      dsimp [x, A]
      nlinarith
    have hxM : M ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    have hpowupper : x ^ theta ≤ B :=
      Real.rpow_le_rpow hxpos.le (by linarith) hlo
    have hpowerhalf : B / 2 ≤ x ^ theta := by
      exact (rpow_half_ge_half hmpos hlo hhi).trans
        (Real.rpow_le_rpow (by positivity) hxlo hlo)
    have hlocal := hM x hxM
    have hmon := hF (show x + x ^ theta ≤ A + B * (j + 1 : ℕ) by
      dsimp [x]
      push_cast
      linarith)
    change B / 4 ≤ F (A + B * (j + 1 : ℕ)) - F x
    linarith
  have hsum : (N : ℝ) * (B / 4) ≤
      ∑ j ∈ Finset.range N, (F (A + B * (j + 1 : ℕ)) - F (A + B * j)) := by
    calc
      (N : ℝ) * (B / 4) = ∑ j ∈ Finset.range N, B / 4 := by simp
      _ ≤ _ := Finset.sum_le_sum hblock
  have htel := sum_increments (fun j => F (A + B * j)) N
  simp only [Nat.cast_zero, mul_zero, add_zero] at htel
  rw [htel] at hsum
  have hend : A + B * N ≤ m := by dsimp [A]; nlinarith
  have hmon := hF hend
  dsimp [A] at hsum
  linarith

/-- The lower Chebyshev estimate needed in Yudin's preliminary block lemma.
This is unconditional relative to the pinned upstream proof dependency. -/
theorem eventually_theta_backward_three_fifths :
    ∀ᶠ m : ℝ in atTop, ∀ y : ℝ,
      m ^ (3 / 5 : ℝ) ≤ y → y ≤ m / 2 →
        y / 8 ≤ Chebyshev.theta m - Chebyshev.theta (m - y) :=
  uniform_backward_mass_of_forward Chebyshev.theta Chebyshev.theta_mono
    (by norm_num) (by norm_num) eventually_theta_forward_three_fifths

end Erdos374Research
