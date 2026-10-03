import Erdos374Research.SmallPrimeMoment
import Erdos374Research.CofactorExclusions
import Erdos374Research.SquarefreeSieveBounds

/-!
# Few integers have a very smooth squarefree component

UNCOMPILED. The square-part tail and the elementary finite moment estimate
give an exponentially small density in the reciprocal smoothness exponent.
The estimate is for a full interval, not only a density-zero exceptional set.
-/

namespace Erdos374Research

open Finset Filter
open scoped BigOperators Topology

noncomputable section

def SmoothSquarefreeComponent (y : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ Tao2026.squarefreeComponent n → (p : ℝ) ≤ y

lemma squarefreeComponent_rpow_le_moment {y : ℝ} {n : ℕ}
    (hy : 0 < Real.log y) (hn : SmoothSquarefreeComponent y n) :
    (Tao2026.squarefreeComponent n : ℝ) ^ (1 / Real.log y) ≤
      smallPrimeMoment y n := by
  let S := (Tao2026.squarefreeComponent n).primeFactors
  let P := smallPrimeSet y
  have hsub : S ⊆ P := by
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hp'.1.two_le, Nat.le_floor (hn p hp'.1 hp'.2.1)⟩, hp'.1⟩
  have hfilter : P.filter (fun p => p ∈ S) = S := by
    ext p
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hsub h, h⟩⟩
  have hprod : (∏ p ∈ S, (p : ℝ) ^ (1 / Real.log y)) =
      (Tao2026.squarefreeComponent n : ℝ) ^ (1 / Real.log y) := by
    rw [Real.finsetProd_rpow S (fun p : ℕ => (p : ℝ))
      (fun p hp => Nat.cast_nonneg p), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree (Tao2026.squarefree_squarefreeComponent n)]
  rw [← hprod, ← hfilter, Finset.prod_filter]
  unfold smallPrimeMoment
  apply Finset.prod_le_prod
  · intro p hp
    split_ifs <;> positivity
  · intro p hp
    by_cases hpS : p ∈ S
    · have hpd := (Nat.mem_primeFactors.mp hpS).2.1.trans
        (Tao2026.squarefreeComponent_dvd n)
      simp [hpS, hpd]
    · simp only [if_neg hpS]
      split_ifs
      · exact Real.one_le_rpow
          (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
          (by positivity)
      · exact le_rfl

def largeSmoothComponents (X : ℕ) (y T : ℝ) : Finset ℕ := by
  classical
  exact (Ioc 0 X).filter fun n => T ≤ (Tao2026.squarefreeComponent n : ℝ) ∧
    SmoothSquarefreeComponent y n

theorem card_largeSmoothComponents_le {y T : ℝ} (hypos : 0 < y)
    (hy : 1 ≤ Real.log y) (hT : 0 < T) (X : ℕ) :
    ((largeSmoothComponents X y T).card : ℝ) ≤
      smallPrimeMomentConstant * X / T ^ (1 / Real.log y) := by
  classical
  have hlog : 0 < Real.log y := by linarith
  have hpow : 0 < T ^ (1 / Real.log y) := Real.rpow_pos_of_pos hT _
  have hmass : (largeSmoothComponents X y T).card * T ^ (1 / Real.log y) ≤
      ∑ n ∈ largeSmoothComponents X y T, smallPrimeMoment y n := by
    calc
      (largeSmoothComponents X y T).card * T ^ (1 / Real.log y) =
          ∑ n ∈ largeSmoothComponents X y T, T ^ (1 / Real.log y) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        have hd := (Finset.mem_filter.mp hn).2
        exact (Real.rpow_le_rpow hT.le hd.1 (by positivity)).trans
          (squarefreeComponent_rpow_le_moment hlog hd.2)
  have hsum : (∑ n ∈ largeSmoothComponents X y T, smallPrimeMoment y n) ≤
      ∑ n ∈ Ioc 0 X, smallPrimeMoment y n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro n hn hnnot
    unfold smallPrimeMoment
    apply Finset.prod_nonneg
    intro p hp
    split_ifs <;> positivity
  exact (le_div_iff₀ hpow).mpr (hmass.trans (hsum.trans (sum_smallPrimeMoment_le hypos hy X)))

def smoothComponentsInUpperRange (X : ℕ) (β : ℝ) : Finset ℕ := by
  classical
  exact (Ioc 0 X).filter fun n => (X : ℝ) / 4 ≤ n ∧
    SmoothSquarefreeComponent ((X : ℝ) ^ β) n

lemma small_square_part_large_component {X n q Z : ℕ} {R V : ℝ}
    (_hn : 0 < n) (hnlow : (X : ℝ) / 4 ≤ n)
    (hq : q ^ 2 * Tao2026.squarefreeComponent n = n)
    (hqZ : q ≤ Z) (hZR : (Z : ℝ) ≤ R) (hR : 0 < R)
    (_hV : 0 < V) (hscale : 4 * R ^ 2 * V ≤ X) :
    V ≤ (Tao2026.squarefreeComponent n : ℝ) := by
  have hqZreal : (q : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hqZ
  have hqR : (q : ℝ) ≤ R := hqZreal.trans hZR
  have hqR2 : (q : ℝ) ^ 2 ≤ R ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q]
  have hs0 : 0 ≤ (Tao2026.squarefreeComponent n : ℝ) := Nat.cast_nonneg _
  have hqreal : (q : ℝ) ^ 2 * Tao2026.squarefreeComponent n = n := by exact_mod_cast hq
  by_contra hnot
  have hs : (Tao2026.squarefreeComponent n : ℝ) < V := lt_of_not_ge hnot
  have h1 := mul_le_mul_of_nonneg_right hqR2 hs0
  have h2 := mul_lt_mul_of_pos_left hs (sq_pos_of_pos hR)
  nlinarith

theorem eventually_smoothComponent_density_bound {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ X : ℕ in atTop,
      ((smoothComponentsInUpperRange X β).card : ℝ) ≤
        smallPrimeMomentConstant * Real.exp (-(1 / (3 * β))) * X +
          2 * (X : ℝ) ^ (3 / 4 : ℝ) := by
  classical
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun X : ℕ => (X : ℝ) ^ (1 / 6 : ℝ)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 / β)),
    hpow.eventually (eventually_ge_atTop 4), eventually_ge_atTop (2 : ℕ)]
      with X hlogX hpowX hX
  let Z : ℕ := ⌊(X : ℝ) ^ (1 / 4 : ℝ)⌋₊
  let R : ℝ := (X : ℝ) ^ (1 / 4 : ℝ)
  let V : ℝ := (X : ℝ) ^ (1 / 3 : ℝ)
  let y : ℝ := (X : ℝ) ^ β
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hRpos : 0 < R := Real.rpow_pos_of_pos hXpos _
  have hVpos : 0 < V := Real.rpow_pos_of_pos hXpos _
  have hypos : 0 < y := Real.rpow_pos_of_pos hXpos _
  have hlogy : 1 ≤ Real.log y := by
    dsimp [y]
    rw [Real.log_rpow hXpos]
    simpa only [mul_comm] using (div_le_iff₀ hβ).mp hlogX
  have hR4 : 4 ≤ R := hpowX.trans
    (Real.rpow_le_rpow_of_exponent_le hXR (by norm_num : (1 / 6 : ℝ) ≤ 1 / 4))
  have hZ : 1 ≤ Z := by
    change 1 ≤ ⌊R⌋₊
    exact (Nat.one_le_floor_iff R).mpr (by linarith)
  have hZR : (Z : ℝ) ≤ R := Nat.floor_le hRpos.le
  have hRZ : R < (Z : ℝ) + 1 := Nat.lt_floor_add_one R
  have hZhalf : R / 2 ≤ (Z : ℝ) := by
    have hZR1 : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
    linarith
  have hidentity : (X : ℝ) ^ (1 / 6 : ℝ) * R ^ 2 * V = X := by
    dsimp [R, V]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le,
      ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
    norm_num
  have hscale : 4 * R ^ 2 * V ≤ X := by
    nlinarith [mul_le_mul_of_nonneg_right hpowX (show 0 ≤ R ^ 2 * V by positivity)]
  have hsub : smoothComponentsInUpperRange X β ⊆
      largeSquareMultiples X Z ∪ largeSmoothComponents X y V := by
    intro n hnS
    have hnD := Finset.mem_filter.mp hnS
    have hnI := Finset.mem_Ioc.mp hnD.1
    obtain ⟨q, hq⟩ := Tao2026.exists_sq_mul_squarefreeComponent hnI.1
    by_cases hqZ : q ≤ Z
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hnD.1, small_square_part_large_component hnI.1 hnD.2.1 hq hqZ hZR hRpos hVpos hscale,
          hnD.2.2⟩)
    · have hq2 : q ^ 2 ≤ X := by
        have hs1 : 1 ≤ Tao2026.squarefreeComponent n :=
          Nat.pos_of_ne_zero (Tao2026.squarefree_squarefreeComponent n).ne_zero
        nlinarith
      have hqs : q ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa only [pow_two] using hq2)
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_Icc.mpr ⟨by omega, hqs⟩,
          Finset.mem_filter.mpr ⟨hnD.1, ⟨Tao2026.squarefreeComponent n, hq.symm⟩⟩⟩)
  have hcard : ((smoothComponentsInUpperRange X β).card : ℝ) ≤
      (largeSquareMultiples X Z).card + (largeSmoothComponents X y V).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans
      (Finset.card_union_le (largeSquareMultiples X Z) (largeSmoothComponents X y V))
  have hlarge := card_largeSquareMultiples_le X Z hZ
  have hsmooth := card_largeSmoothComponents_le hypos hlogy hVpos X
  have hVp : V ^ (1 / Real.log y) = Real.exp (1 / (3 * β)) := by
    rw [Real.rpow_def_of_pos hVpos]
    dsimp [V, y]
    rw [Real.log_rpow hXpos, Real.log_rpow hXpos]
    congr 1
    field_simp
  rw [hVp] at hsmooth
  have hrewrite : smallPrimeMomentConstant * X / Real.exp (1 / (3 * β)) =
      smallPrimeMomentConstant * Real.exp (-(1 / (3 * β))) * X := by
    rw [Real.exp_neg]
    ring
  rw [hrewrite] at hsmooth
  have htail : (X : ℝ) / Z ≤ 2 * (X : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      (X : ℝ) / Z ≤ (X : ℝ) / (R / 2) :=
        div_le_div_of_nonneg_left hXpos.le (by positivity) hZhalf
      _ = 2 * (X : ℝ) ^ (3 / 4 : ℝ) := by
        have hratio : (X : ℝ) / R = (X : ℝ) ^ (3 / 4 : ℝ) := by
          dsimp [R]
          simpa only [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, Real.rpow_one]
            using (Real.rpow_sub hXpos 1 (1 / 4)).symm
        calc
          (X : ℝ) / (R / 2) = 2 * ((X : ℝ) / R) := by
            rw [div_div_eq_mul_div]
            ring
          _ = 2 * (X : ℝ) ^ (3 / 4 : ℝ) := by rw [hratio]
  linarith

end
end Erdos374Research
