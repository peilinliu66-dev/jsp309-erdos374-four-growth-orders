import Mathlib

/-!
UNCOMPILED. Finite weighted form of Gallagher's larger sieve.
The proof is the classical fibre Cauchy--Schwarz / ordered-pair argument,
not a new mathematical inequality. Arithmetic residue bounds will be supplied
by separate lemmas in the factorial application.
-/

namespace Erdos374Research

open Finset
open scoped BigOperators

noncomputable section

variable {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]

def residueFibreMass (s : Finset α) (f : α → β) (b : β) : ℝ :=
  ((s.filter fun x => f x = b).card : ℝ)

def residueCollisionMass (s : Finset α) (f : α → β) : ℝ :=
  ∑ b ∈ s.image f, residueFibreMass s f b ^ 2

omit [DecidableEq α] in
lemma residueFibreMass_nonneg (s : Finset α) (f : α → β) (b : β) :
    0 ≤ residueFibreMass s f b := Nat.cast_nonneg _

omit [DecidableEq α] in
lemma residueFibreMass_sum (s : Finset α) (f : α → β) :
    ∑ b ∈ s.image f, residueFibreMass s f b = (s.card : ℝ) := by
  unfold residueFibreMass
  exact_mod_cast (Finset.card_eq_sum_card_image f s).symm

omit [DecidableEq α] in
lemma residueCollisionMass_nonneg (s : Finset α) (f : α → β) :
    0 ≤ residueCollisionMass s f := Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq α] in
lemma residueCollisionMass_eq_sum (s : Finset α) (f : α → β) :
    residueCollisionMass s f = ∑ x ∈ s, residueFibreMass s f (f x) := by
  simpa only [residueCollisionMass, residueFibreMass, nsmul_eq_mul, pow_two]
    using (Finset.sum_comp (s := s) (fun b => residueFibreMass s f b) f).symm

omit [DecidableEq α] in
lemma residueFibreMass_eq_sum (s : Finset α) (f : α → β) (b : β) :
    residueFibreMass s f b = ∑ x ∈ s, if f x = b then (1 : ℝ) else 0 := by
  simp only [residueFibreMass, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _hx
  split_ifs <;> norm_num

omit [DecidableEq α] in
lemma residueCollisionMass_lower (s : Finset α) (f : α → β)
    {ρ : ℝ} (hρ : 0 < ρ) (himage : ((s.image f).card : ℝ) ≤ ρ) :
    (s.card : ℝ) ^ 2 / ρ ≤ residueCollisionMass s f := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := s.image f)
    (f := residueFibreMass s f)
  rw [residueFibreMass_sum] at hcs
  apply (div_le_iff₀ hρ).2
  calc
    (s.card : ℝ) ^ 2 ≤ ((s.image f).card : ℝ) * residueCollisionMass s f := hcs
    _ ≤ ρ * residueCollisionMass s f :=
      mul_le_mul_of_nonneg_right himage (residueCollisionMass_nonneg s f)
    _ = residueCollisionMass s f * ρ := mul_comm _ _

def residuePairWeight (ps : Finset ι) (f : ι → α → β) (w : ι → ℝ)
    (x y : α) : ℝ :=
  ∑ p ∈ ps, if f p y = f p x then w p else 0

omit [DecidableEq α] [DecidableEq ι] in
lemma weighted_collision_identity (s : Finset α) (ps : Finset ι)
    (f : ι → α → β) (w : ι → ℝ) :
    ∑ p ∈ ps, w p * residueCollisionMass s (f p) =
      ∑ x ∈ s, ∑ y ∈ s, residuePairWeight ps f w x y := by
  classical
  simp_rw [residueCollisionMass_eq_sum, residueFibreMass_eq_sum,
    Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.sum_comm]
  rfl

omit [DecidableEq ι] in
lemma weighted_collision_upper (s : Finset α) (ps : Finset ι)
    (f : ι → α → β) (w : ι → ℝ) {D : ℝ}
    (hpair : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → residuePairWeight ps f w x y ≤ D) :
    ∑ p ∈ ps, w p * residueCollisionMass s (f p) ≤
      (s.card : ℝ) * ((∑ p ∈ ps, w p) + ((s.card : ℝ) - 1) * D) := by
  rw [weighted_collision_identity]
  have hxBound : ∀ x ∈ s, (∑ y ∈ s, residuePairWeight ps f w x y) ≤
      (∑ p ∈ ps, w p) + ((s.card : ℝ) - 1) * D := by
    intro x hx
    have herase : ((s.erase x).card : ℝ) = (s.card : ℝ) - 1 := by
      have hcard := Finset.card_erase_add_one hx
      have hcast : ((s.erase x).card : ℝ) + 1 = s.card := by exact_mod_cast hcard
      linarith
    calc
      ∑ y ∈ s, residuePairWeight ps f w x y =
          (∑ y ∈ s.erase x, residuePairWeight ps f w x y) +
            residuePairWeight ps f w x x := (Finset.sum_erase_add _ _ hx).symm
      _ ≤ (∑ _y ∈ s.erase x, D) + residuePairWeight ps f w x x := by
        refine add_le_add ?_ le_rfl
        apply Finset.sum_le_sum
        intro y hy
        exact hpair x hx y (Finset.mem_erase.mp hy).2 (Finset.mem_erase.mp hy).1.symm
      _ = (∑ p ∈ ps, w p) + ((s.card : ℝ) - 1) * D := by
        simp only [Finset.sum_const, nsmul_eq_mul, residuePairWeight, if_true, herase]
        ring
  calc
    ∑ x ∈ s, ∑ y ∈ s, residuePairWeight ps f w x y ≤
        ∑ _x ∈ s, ((∑ p ∈ ps, w p) + ((s.card : ℝ) - 1) * D) :=
      Finset.sum_le_sum hxBound
    _ = _ := by simp [mul_add]

omit [DecidableEq ι] in
/-- Abstract finite larger sieve, in a form that separates the elementary
residue-class and prime-divisor facts used by applications. -/
theorem largerSieve_weighted (s : Finset α) (hs : s.Nonempty) (ps : Finset ι)
    (f : ι → α → β) (w ρ : ι → ℝ) {D : ℝ}
    (hw : ∀ p ∈ ps, 0 ≤ w p) (hρ : ∀ p ∈ ps, 0 < ρ p)
    (himage : ∀ p ∈ ps, ((s.image (f p)).card : ℝ) ≤ ρ p)
    (hpair : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → residuePairWeight ps f w x y ≤ D) :
    (s.card : ℝ) * ((∑ p ∈ ps, w p / ρ p) - D) ≤ (∑ p ∈ ps, w p) - D := by
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hlo : (s.card : ℝ) ^ 2 * (∑ p ∈ ps, w p / ρ p) ≤
      ∑ p ∈ ps, w p * residueCollisionMass s (f p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    calc
      (s.card : ℝ) ^ 2 * (w p / ρ p) = w p * ((s.card : ℝ) ^ 2 / ρ p) := by ring
      _ ≤ w p * residueCollisionMass s (f p) :=
        mul_le_mul_of_nonneg_left (residueCollisionMass_lower s (f p)
          (hρ p hp) (himage p hp)) (hw p hp)
  have hhi := weighted_collision_upper s ps f w hpair
  have hcancel : (s.card : ℝ) * (∑ p ∈ ps, w p / ρ p) ≤
      (∑ p ∈ ps, w p) + ((s.card : ℝ) - 1) * D := by
    apply (mul_le_mul_iff_right₀ hN).mp
    simpa only [pow_two, mul_assoc] using hlo.trans hhi
  nlinarith

omit [DecidableEq ι] in
theorem largerSieve_card_bound (s : Finset α) (hs : s.Nonempty) (ps : Finset ι)
    (f : ι → α → β) (w ρ : ι → ℝ) {D : ℝ}
    (hw : ∀ p ∈ ps, 0 ≤ w p) (hρ : ∀ p ∈ ps, 0 < ρ p)
    (himage : ∀ p ∈ ps, ((s.image (f p)).card : ℝ) ≤ ρ p)
    (hpair : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → residuePairWeight ps f w x y ≤ D)
    (hpositive : 0 < (∑ p ∈ ps, w p / ρ p) - D) :
    (s.card : ℝ) ≤ ((∑ p ∈ ps, w p) - D) / ((∑ p ∈ ps, w p / ρ p) - D) := by
  exact (le_div_iff₀ hpositive).2 (largerSieve_weighted s hs ps f w ρ hw hρ himage hpair)

lemma sum_log_prime_divisors_le (ps : Finset ℕ) {d : ℕ} (hd : 0 < d)
    (hprime : ∀ p ∈ ps, p.Prime) (hdiv : ∀ p ∈ ps, p ∣ d) :
    ∑ p ∈ ps, Real.log (p : ℝ) ≤ Real.log (d : ℝ) := by
  have hsubset : ps ⊆ d.primeFactors := by
    intro p hp
    exact (hprime p hp).mem_primeFactors (hdiv p hp) hd.ne'
  have hprodDvd : ∏ p ∈ ps, p ∣ d :=
    (Finset.prod_dvd_prod_of_subset ps d.primeFactors id hsubset).trans
      (Nat.prod_primeFactors_dvd d)
  have hprodPos : 0 < ∏ p ∈ ps, p := Finset.prod_pos fun p hp => (hprime p hp).pos
  have hprodLe : ∏ p ∈ ps, p ≤ d := Nat.le_of_dvd hd hprodDvd
  have hlog : Real.log (((∏ p ∈ ps, p) : ℕ) : ℝ) ≤ Real.log (d : ℝ) :=
    Real.log_le_log (by exact_mod_cast hprodPos) (by exact_mod_cast hprodLe)
  rw [Nat.cast_prod, Real.log_prod] at hlog
  · exact hlog
  · intro p hp
    exact_mod_cast (hprime p hp).ne_zero

lemma prime_dvd_dist_of_mod_eq {p x y : ℕ} (h : y % p = x % p) :
    p ∣ Nat.dist x y := by
  rcases le_total x y with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy]
    exact (Nat.modEq_iff_dvd' hxy).mp h.symm
  · rw [Nat.dist_eq_sub_of_le_right hyx]
    exact (Nat.modEq_iff_dvd' hyx).mp h

lemma residuePairWeight_log_le {s ps : Finset ℕ} {X : ℕ}
    (hprime : ∀ p ∈ ps, p.Prime) (hs : s ⊆ Finset.Icc 1 X)
    {x y : ℕ} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    residuePairWeight ps (fun p x => x % p) (fun p => Real.log (p : ℝ)) x y ≤
      Real.log (X : ℝ) := by
  let qs := ps.filter fun p => y % p = x % p
  have hd : 0 < Nat.dist x y := Nat.dist_pos_of_ne hne
  have hdX : Nat.dist x y ≤ X := by
    have hxX := Finset.mem_Icc.mp (hs hx)
    have hyX := Finset.mem_Icc.mp (hs hy)
    rcases le_total x y with hxy | hyx
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hyx]
      omega
  have hlog := sum_log_prime_divisors_le qs hd
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => prime_dvd_dist_of_mod_eq (Finset.mem_filter.mp hp).2)
  have hid : residuePairWeight ps (fun p x => x % p)
      (fun p => Real.log (p : ℝ)) x y = ∑ p ∈ qs, Real.log (p : ℝ) := by
    simp only [residuePairWeight, qs, Finset.sum_filter]
  rw [hid]
  exact hlog.trans (Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdX))

/-- Literal natural-number larger sieve. Its hypotheses are just prime
moduli, residue counts and a positive sieve denominator. The pairwise
logarithmic bound is proved from divisibility of nonzero differences. -/
theorem largerSieve_nat_card_bound (s ps : Finset ℕ) (hsne : s.Nonempty)
    {X : ℕ} (hs : s ⊆ Finset.Icc 1 X) (ρ : ℕ → ℝ)
    (hprime : ∀ p ∈ ps, p.Prime) (hρ : ∀ p ∈ ps, 0 < ρ p)
    (himage : ∀ p ∈ ps, ((s.image fun x => x % p).card : ℝ) ≤ ρ p)
    (hpositive : 0 < (∑ p ∈ ps, Real.log (p : ℝ) / ρ p) - Real.log X) :
    (s.card : ℝ) ≤
      ((∑ p ∈ ps, Real.log (p : ℝ)) - Real.log X) /
        ((∑ p ∈ ps, Real.log (p : ℝ) / ρ p) - Real.log X) := by
  apply largerSieve_card_bound s hsne ps (fun p x => x % p)
    (fun p => Real.log (p : ℝ)) ρ
  · intro p hp
    exact Real.log_nonneg (by exact_mod_cast (hprime p hp).one_lt.le)
  · exact hρ
  · exact himage
  · intro x hx y hy hne
    exact residuePairWeight_log_le hprime hs hx hy hne
  · exact hpositive

end
end Erdos374Research
