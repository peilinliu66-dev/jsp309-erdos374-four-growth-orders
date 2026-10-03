import Erdos374Research.TwoBlockArithmetic
import Erdos374Research.IntegerAvoidingWeight
import Erdos374Research.LongBlockWeights

/-! UNCOMPILED. The exact divisor and parity implications consumed by the
smooth long-block weights. These lemmas do not assume a positive witness. -/

namespace Erdos374Research

open Tao2026
open scoped BigOperators

theorem shiftedPlateau_ne_zero_offset {N : ℕ} (hN : 1 < Real.log (N : ℝ))
    {c x : ℝ} (hx : shiftedPlateau N c x ≠ 0) :
    ∃ k : ℤ, c - plateauWidth N ≤ x - (k : ℝ) ∧ x - (k : ℝ) < c := by
  let k : ℤ := ⌊x - c⌋ + 1
  have hlo := shiftedPlateau_supported hN hx
  have hhi := Int.fract_lt_one (x - c)
  have hid : x - (k : ℝ) = c + Int.fract (x - c) - 1 := by
    dsimp only [k, Int.fract]
    push_cast
    ring
  refine ⟨k, ?_, ?_⟩ <;> rw [hid]
  · change 1 - plateauWidth N ≤ Int.fract (x - c) at hlo
    linarith
  · linarith

theorem not_dvd_of_integerAvoidingWeight {N p v : ℕ} {M L : ℝ}
    (hN : 1 < Real.log (N : ℝ)) (hp : 0 < p)
    (hclose : |M - (v : ℝ)| ≤ L)
    (hscale : L ≤ plateauWidth N / 12 * p)
    (hweight : integerAvoidingWeight N (M / p) ≠ 0) : ¬ p ∣ v := by
  rintro ⟨k, hk⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hv : (v : ℝ) = p * k := by exact_mod_cast hk
  have hid : M / p - (k : ℝ) = (M - v) / p := by
    rw [hv]
    field_simp [hpR.ne']
  have hnear : |M / p - (k : ℝ)| ≤ plateauWidth N / 12 := by
    rw [hid, abs_div, abs_of_pos hpR]
    exact (div_le_iff₀ hpR).2 (hclose.trans hscale)
  have hfar := integerAvoidingWeight_ne_zero_imp_far hN hweight (k : ℤ)
  norm_cast at hfar
  exact (not_lt_of_ge hnear) hfar

theorem exists_dvd_falling_of_small_fract {n l p : ℕ}
    (hl : l ≤ n) (hp : 0 < p)
    (hfrac : Int.fract ((n : ℝ) / p) < (l : ℝ) / p) :
    ∃ v ∈ Finset.Ioc (n - l) n, p ∣ v := by
  let r := n % p
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : r < l := by
    rw [Int.fract_div_natCast_eq_div_natCast_mod] at hfrac
    have h := (div_lt_div_iff_of_pos_right hpR).mp hfrac
    exact_mod_cast h
  have hrn : r ≤ n := Nat.mod_le _ _
  refine ⟨n - r, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
  refine ⟨n / p, ?_⟩
  have h := Nat.mod_add_div n p
  dsimp only [r] at *
  omega

theorem exists_dvd_block_of_centered_integer {m l j p : ℕ}
    (hl : l ≤ m) (hj : j < l) (hp : 0 < p) (k : ℤ)
    (hlo : -(j : ℝ) < ((m - j : ℕ) : ℝ) - (p : ℝ) * k)
    (hhi : ((m - j : ℕ) : ℝ) - (p : ℝ) * k < (l : ℝ) - j) :
    ∃ v ∈ Finset.Ioc (m - l) m, p ∣ v := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hjm : j ≤ m := by omega
  rw [Nat.cast_sub hjm] at hlo hhi
  have hml : (0 : ℝ) ≤ (m : ℝ) - l := by
    have hlR : (l : ℝ) ≤ m := by exact_mod_cast hl
    linarith
  have hkR : (0 : ℝ) < k := by nlinarith
  have hk : (0 : ℤ) ≤ k := by exact_mod_cast hkR.le
  have hkcast : ((k.toNat : ℕ) : ℝ) = k := by exact_mod_cast Int.toNat_of_nonneg hk
  let v := p * k.toNat
  have hv : (v : ℝ) = (p : ℝ) * k := by dsimp only [v]; push_cast; rw [hkcast]
  have hvlo : m - l < v := by
    have hreal : ((m - l : ℕ) : ℝ) < v := by rw [Nat.cast_sub hl, hv]; linarith
    exact_mod_cast hreal
  have hvhi : v ≤ m := by
    have hreal : (v : ℝ) ≤ m := by rw [hv]; linarith
    exact_mod_cast hreal
  exact ⟨v, Finset.mem_Ioc.mpr ⟨hvlo, hvhi⟩, dvd_mul_right p k.toNat⟩

theorem factorization_eq_one_of_prime_dvd_not_sq {v p : ℕ}
    (hv : 0 < v) (hp : p.Prime) (hdiv : p ∣ v) (hnot : ¬p ^ 2 ∣ v) :
    v.factorization p = 1 := by
  have hlo := (hp.dvd_iff_one_le_factorization hv.ne').mp hdiv
  have hhi : ¬2 ≤ v.factorization p := by
    intro h
    exact hnot ((hp.pow_dvd_iff_le_factorization hv.ne').2 h)
  omega

theorem not_square_of_selected_block_prime {n m l₁ l₂ c p v : ℕ}
    (hl₁ : l₁ ≤ n) (hl₂ : l₂ ≤ m) (hp : p.Prime)
    (hlp : l₁ < p) (hcp : c < p)
    (hv : v ∈ Finset.Ioc (n - l₁) n) (hpv : p ∣ v) (hpsq : ¬p ^ 2 ∣ v)
    (havoid : ∀ w ∈ Finset.Ioc (m - l₂) m, ¬p ∣ w) :
    ¬IsSquare (falling n l₁ * falling m l₂ * c.factorial) := by
  intro hsq
  have hvpos : 0 < v := by have := (Finset.mem_Ioc.mp hv).1; omega
  have hfirst : (falling n l₁).factorization p = 1 :=
    (factorization_falling_eq_unique hl₁ hp hlp hv hpv).trans
      (factorization_eq_one_of_prime_dvd_not_sq hvpos hp hpv hpsq)
  have hfirst0 : falling n l₁ ≠ 0 := consecutiveProduct_ne_zero _ _
  have hsecond0 : falling m l₂ ≠ 0 := consecutiveProduct_ne_zero _ _
  have hsecond : (falling m l₂).factorization p = 0 := by
    apply prime_factorization_zero hp hsecond0
    intro hdiv
    rw [falling_eq_prod_Ioc hl₂] at hdiv
    obtain ⟨w, hw, hpw⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdiv
    exact havoid w hw hpw
  have hfact : c.factorial.factorization p = 0 := by
    apply prime_factorization_zero hp (Nat.factorial_ne_zero c)
    exact fun h => (not_le_of_gt hcp) (hp.dvd_factorial.mp h)
  have heven := even_factorization_of_isSquare (p := p) hsq
  rw [Nat.factorization_mul (mul_ne_zero hfirst0 hsecond0) (Nat.factorial_ne_zero c),
    Nat.factorization_mul hfirst0 hsecond0] at heven
  have heven1 : Even (1 : ℕ) := by
    simpa only [Finsupp.add_apply, hfirst, hsecond, hfact, add_zero] using heven
  exact (by decide : ¬Even (1 : ℕ)) heven1

lemma block_term_close_to_shift {m l j v : ℕ}
    (hl : l ≤ m) (hj : j < l) (hv : v ∈ Finset.Ioc (m - l) m) :
    |((m - j : ℕ) : ℝ) - v| ≤ l := by
  have hmj : j ≤ m := by omega
  obtain ⟨hv0, hv1⟩ := Finset.mem_Ioc.mp hv
  have hv0R : ((m - l : ℕ) : ℝ) < v := by exact_mod_cast hv0
  have hv1R : (v : ℝ) ≤ m := by exact_mod_cast hv1
  have hjR : (j : ℝ) < l := by exact_mod_cast hj
  rw [Nat.cast_sub hl] at hv0R
  rw [Nat.cast_sub hmj]
  apply abs_le.mpr
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j]

lemma longBlockSquareWeight_not_sq_dvd {N M L P p v : ℕ}
    (hN : 1 < Real.log (N : ℝ)) (hp : 0 < p) (hPp : P ≤ p) (hv : 0 < v)
    (hclose : |(M : ℝ) - v| ≤ L) (hsmall : 2 * L ≤ P ^ 2)
    (hscale : (L : ℝ) ≤ plateauWidth N / 12 * (P : ℝ) ^ 2)
    (hw : longBlockSquareWeight N M P ((M : ℝ) / (p : ℝ) ^ 2) ≠ 0) :
    ¬p ^ 2 ∣ v := by
  unfold longBlockSquareWeight at hw
  split_ifs at hw with hcase
  · have hvR : (v : ℝ) ≤ M + L := by have := (abs_le.mp hclose).1; linarith
    have hvNat : v ≤ M + L := by exact_mod_cast hvR
    have hlt : M + L < P ^ 2 := by omega
    exact Nat.not_dvd_of_pos_of_lt hv (lt_of_le_of_lt hvNat (hlt.trans_le (Nat.pow_le_pow_left hPp 2)))
  · apply not_sq_dvd_of_integerAvoidingWeight hN hp hclose _ hw
    have hPpR : (P : ℝ) ≤ p := by exact_mod_cast hPp
    exact hscale.trans (mul_le_mul_of_nonneg_left (by nlinarith [Nat.cast_nonneg (α := ℝ) P])
      (div_nonneg (plateauWidth_pos hN).le (by norm_num)))

theorem blockSeparator_nonzero_selects_odd_prime
    {n m l₁ l₂ j a t N p : ℕ}
    (hlog : 2 ≤ Real.log (n : ℝ)) (hN : 1 < Real.log (N : ℝ))
    (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) (hl₁n : l₁ ≤ n) (hl₂m : l₂ ≤ m)
    (hj : j < l₂) (_ha : 0 < a)
    (hrel : ((m - j : ℕ) : ℝ) = (t : ℝ) / a * n)
    (hp : p.Prime)
    (hPp : longBlockPrimeScale n (max l₁ l₂) ≤ p)
    (hpP : p ≤ 2 * longBlockPrimeScale n (max l₁ l₂))
    (havoid : longBlockSigma n ≤ plateauWidth N / 12)
    (hw : blockSeparator n N (longBlockPrimeScale n (max l₁ l₂)) l₁ l₂ j
      ((n : ℝ) / p, (t : ℝ) / a * ((n : ℝ) / p)) ≠ 0) :
    (l₂ ≤ 2000 * l₁ ∧
      (∃ v ∈ Finset.Ioc (n - l₁) n, p ∣ v) ∧
      (∀ v ∈ Finset.Ioc (m - l₂) m, ¬p ∣ v)) ∨
    (2000 * l₁ < l₂ ∧
      (∃ v ∈ Finset.Ioc (m - l₂) m, p ∣ v) ∧
      (∀ v ∈ Finset.Ioc (n - l₁) n, ¬p ∣ v)) := by
  let L := max l₁ l₂
  let P := longBlockPrimeScale n L
  have hL : 1 ≤ L := hl₁.trans (le_max_left _ _)
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by linarith
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hP : 0 < P := longBlockPrimeScale_pos hlog1 hL
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hPpR : (P : ℝ) ≤ p := by exact_mod_cast hPp
  have hpPR : (p : ℝ) ≤ 2 * P := by exact_mod_cast hpP
  have hratio : longBlockSigma n / 2 ≤ (L : ℝ) / P ∧
      (L : ℝ) / P ≤ longBlockSigma n := longBlock_ratio_bounds hlog1 hL
  have hsigma : 0 < longBlockSigma n := by unfold longBlockSigma; positivity
  have hphase : (t : ℝ) / a * ((n : ℝ) / p) = ((m - j : ℕ) : ℝ) / p := by
    rw [hrel]
    ring
  unfold blockSeparator at hw
  split_ifs at hw with hdom
  · left
    change upperBlockSeparator n N P l₁
      ((n : ℝ) / p, (t : ℝ) / a * ((n : ℝ) / p)) ≠ 0 at hw
    refine ⟨hdom, ?_, ?_⟩
    · have hf : shiftedPlateau (n ^ 100) ((l₁ : ℝ) / (4 * P)) ((n : ℝ) / p) ≠ 0 := by
        intro hf
        exact hw (by simp only [upperBlockSeparator, hf, Complex.ofReal_zero, zero_mul])
      have hn100 : 1 < Real.log ((n ^ 100 : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
        linarith
      obtain ⟨k, hk0, hk1⟩ := shiftedPlateau_ne_zero_offset hn100 hf
      rw [plateauWidth_natPower (by norm_num : 1 ≤ (100 : ℕ))] at hk0
      norm_num at hk0
      have hLdom : L ≤ 2000 * l₁ := max_le (by omega) hdom
      have hLdomR : (L : ℝ) ≤ 2000 * l₁ := by exact_mod_cast hLdom
      have hc : longBlockSigma n / 16000 ≤ (l₁ : ℝ) / (4 * P) := by
        have hratio0 := hratio.1
        change longBlockSigma n / 2 ≤ (L : ℝ) / P at hratio0
        have hmul := (le_div_iff₀ hPR).mp hratio0
        apply (le_div_iff₀ (by positivity : 0 < 4 * (P : ℝ))).mpr
        nlinarith
      have hpos : 0 < (n : ℝ) / p - k := by linarith
      apply exists_dvd_block_of_centered_integer hl₁n (by omega : 0 < l₁) hp.pos k
      · simp only [Nat.sub_zero, Nat.cast_zero, neg_zero]
        have hid : (n : ℝ) - p * k = (p : ℝ) * ((n : ℝ) / p - k) := by
          field_simp [hpR.ne']
        rw [hid]
        positivity
      · simp only [Nat.sub_zero, Nat.cast_zero, sub_zero]
        have hmul := mul_lt_mul_of_pos_left hk1 hpR
        have hcP : (p : ℝ) * ((l₁ : ℝ) / (4 * P)) ≤ (l₁ : ℝ) / 2 := by
          calc
            (p : ℝ) * ((l₁ : ℝ) / (4 * P)) ≤
                (2 * P) * ((l₁ : ℝ) / (4 * P)) :=
              mul_le_mul_of_nonneg_right hpPR (by positivity)
            _ = (l₁ : ℝ) / 2 := by field_simp; ring
        have hid : (p : ℝ) * ((n : ℝ) / p - k) = (n : ℝ) - p * k := by
          field_simp [hpR.ne']
        rw [hid] at hmul
        have hlR : (0 : ℝ) < l₁ := by exact_mod_cast hl₁
        linarith
    · intro v hv
      have hg : integerAvoidingWeight N (((m - j : ℕ) : ℝ) / p) ≠ 0 := by
        intro hg
        apply hw
        simp only [upperBlockSeparator, hphase, hg, Complex.ofReal_zero, mul_zero]
      have hl₂L : (l₂ : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast (le_max_right l₁ l₂)
      have hcloseL : |((m - j : ℕ) : ℝ) - v| ≤ (L : ℝ) :=
        (block_term_close_to_shift hl₂m hj hv).trans hl₂L
      apply not_dvd_of_integerAvoidingWeight hN hp.pos hcloseL _ hg
      have hLP : (L : ℝ) ≤ longBlockSigma n * P := (div_le_iff₀ hPR).mp hratio.2
      exact hLP.trans ((mul_le_mul_of_nonneg_right havoid hPR.le).trans
        (mul_le_mul_of_nonneg_left hPpR
          (div_nonneg (plateauWidth_pos hN).le (by norm_num))))
  · right
    change lowerBlockSeparator n P l₂ j
      ((n : ℝ) / p, (t : ℝ) / a * ((n : ℝ) / p)) ≠ 0 at hw
    have hdom' : 2000 * l₁ < l₂ := lt_of_not_ge hdom
    have hL₂ : L = l₂ := max_eq_right (by omega)
    refine ⟨hdom', ?_, ?_⟩
    · have hf : shiftedPlateau n (((l₂ : ℝ) - j) / (2 * P))
          (((m - j : ℕ) : ℝ) / p) ≠ 0 := by
        intro hf
        apply hw
        simp only [lowerBlockSeparator, hphase, hf, Complex.ofReal_zero, mul_zero]
      obtain ⟨k, hk0, hk1⟩ := shiftedPlateau_ne_zero_offset (by linarith : 1 < Real.log (n : ℝ)) hf
      have hwid : plateauWidth n = longBlockSigma n / 10 := by
        unfold plateauWidth longBlockSigma
        ring
      rw [hwid] at hk0
      have hwide : longBlockSigma n / 4 ≤ (l₂ : ℝ) / (2 * P) := by
        have hr₂ : longBlockSigma n / 2 ≤ (l₂ : ℝ) / P := by
          calc
            longBlockSigma n / 2 ≤ (L : ℝ) / P := hratio.1
            _ = (l₂ : ℝ) / P := by rw [hL₂]
        rw [show (l₂ : ℝ) / (2 * P) = ((l₂ : ℝ) / P) / 2 by ring]
        linarith only [hr₂]
      have hxlo : -(j : ℝ) / (2 * P) < ((m - j : ℕ) : ℝ) / p - k := by
        rw [neg_div]
        have hid : ((l₂ : ℝ) - j) / (2 * P) + (j : ℝ) / (2 * P) = (l₂ : ℝ) / (2 * P) := by ring
        linarith only [hk0, hwide, hid, hsigma]
      have hid : (p : ℝ) * (((m - j : ℕ) : ℝ) / p - k) =
          ((m - j : ℕ) : ℝ) - p * k := by
        field_simp [hpR.ne']
      apply exists_dvd_block_of_centered_integer hl₂m hj hp.pos k
      · have hx := (div_lt_iff₀ (by positivity : 0 < 2 * (P : ℝ))).mp hxlo
        by_cases hxi : 0 ≤ ((m - j : ℕ) : ℝ) / p - k
        · have hprod := mul_nonneg hpR.le hxi
          have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg _
          rw [← hid]
          by_cases hj0 : j = 0
          · subst j
            simp only [Nat.cast_zero, neg_zero, zero_div] at hxlo ⊢
            exact mul_pos hpR hxlo
          · have hjpos : (0 : ℝ) < j := by exact_mod_cast (Nat.pos_of_ne_zero hj0)
            linarith
        · have hmul := mul_le_mul_of_nonpos_right hpPR (lt_of_not_ge hxi).le
          rw [← hid]
          linarith
      · have hlR : (0 : ℝ) < (l₂ : ℝ) - j := by
          have hjR : (j : ℝ) < l₂ := by exact_mod_cast hj
          linarith
        have hmul := mul_lt_mul_of_pos_left hk1 hpR
        have hcP : (p : ℝ) * (((l₂ : ℝ) - j) / (2 * P)) ≤ (l₂ : ℝ) - j := by
          calc
            (p : ℝ) * (((l₂ : ℝ) - j) / (2 * P)) ≤
                (2 * P) * (((l₂ : ℝ) - j) / (2 * P)) :=
              mul_le_mul_of_nonneg_right hpPR
                (div_nonneg hlR.le (by positivity : (0 : ℝ) ≤ 2 * (P : ℝ)))
            _ = (l₂ : ℝ) - j := by field_simp [hPR.ne']
        rw [hid] at hmul
        linarith
    · intro v hv
      have hg : integerAvoidingWeight (n ^ 3) ((n : ℝ) / p) ≠ 0 := by
        intro hg
        exact hw (by simp only [lowerBlockSeparator, hg, Complex.ofReal_zero, zero_mul])
      have hn3 : 1 < Real.log ((n ^ 3 : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
        linarith
      have hclose : |(n : ℝ) - v| ≤ (l₁ : ℝ) := by
        simpa only [Nat.sub_zero] using
          (block_term_close_to_shift (j := 0) hl₁n (by omega : 0 < l₁) hv)
      apply not_dvd_of_integerAvoidingWeight hn3 hp.pos hclose _ hg
      have hdwidth := lower_dominant_avoided_width hlog1 hl₂ hdom'
      change (l₁ : ℝ) / longBlockPrimeScale n l₂ < plateauWidth (n ^ 3) / 12 at hdwidth
      have hP₂ : P = longBlockPrimeScale n l₂ := by
        change longBlockPrimeScale n L = longBlockPrimeScale n l₂
        rw [hL₂]
      rw [← hP₂] at hdwidth
      exact ((div_lt_iff₀ hPR).mp hdwidth).le.trans
        (mul_le_mul_of_nonneg_left hPpR
          (div_nonneg (plateauWidth_pos hn3).le (by norm_num)))

end Erdos374Research
