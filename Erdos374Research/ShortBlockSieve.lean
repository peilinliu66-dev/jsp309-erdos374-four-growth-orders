import Tao2026.LargeSieveDenominator

/-!
# A finite large sieve with at most three quarters of each prime's residues

UNCOMPILED. This specializes the actual upstream global tensor large sieve
to singleton prime selections. It is the loss-free finite inequality used
for Yudin's short second block; it is distinct from Gallagher's larger sieve.
-/

namespace Erdos374Research

open Tao2026 Finset
open scoped BigOperators

noncomputable section

def allowedRestrictions (R : (q : SieveModulus) → Finset (ZMod q.modulus)) :
    (qs : List SieveModulus) → SieveRestrictions qs
  | [] => PUnit.unit
  | q :: qs => ((R q)ᶜ, allowedRestrictions R qs)

theorem allowedRestrictions_proper
    (R : (q : SieveModulus) → Finset (ZMod q.modulus))
    (hR : ∀ q, (R q).Nonempty) :
    ∀ qs, SieveRestrictionsProper (allowedRestrictions R qs)
  | [] => by simp [SieveRestrictionsProper]
  | q :: qs => by
      constructor
      · change (R q)ᶜ.card < q.modulus
        simpa only [ZMod.card] using (Finset.card_compl_lt_iff_nonempty (R q)).mpr (hR q)
      · exact allowedRestrictions_proper R hR qs

theorem allowedRestrictions_avoids
    (R : (q : SieveModulus) → Finset (ZMod q.modulus)) (n : ℕ) :
    ∀ qs, SieveAvoids (allowedRestrictions R qs) (natSieveCube qs n) ↔
      ∀ q ∈ qs, (n : ZMod q.modulus) ∈ R q
  | [] => by simp [SieveAvoids]
  | q :: qs => by
      simp only [allowedRestrictions, SieveAvoids, natSieveCube,
        Finset.mem_compl, not_not, List.mem_cons, forall_eq_or_imp,
        allowedRestrictions_avoids R n qs]

def primeSieveModulus (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (p : ↥S) : SieveModulus := ⟨p.1, (hS p.1 p.2).ne_zero⟩

theorem restrictionRatio_ge_third (q : SieveModulus)
    (R : Finset (ZMod q.modulus)) (hR : R.Nonempty)
    (hcard : (R.card : ℝ) ≤ 3 / 4 * q.modulus) :
    (1 / 3 : ℝ) ≤ (Rᶜ.card : ℝ) / R.card := by
  have hpos : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.mpr hR
  have hle : R.card ≤ q.modulus := by simpa only [ZMod.card] using Finset.card_le_univ R
  rw [Finset.card_compl, ZMod.card, Nat.cast_sub hle]
  apply (le_div_iff₀ hpos).mpr
  linarith

/-- The numerator is the actual number of primes supplied, and the
survivor set contains actual integers in [0,X]. -/
theorem shortBlock_largeSieve_card_mul_prime_count
    (S A : Finset ℕ) (X K : ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hSK : ∀ p ∈ S, p ≤ K) (hK : K * K ≤ X + 1)
    (hAX : ∀ n ∈ A, n ≤ X)
    (R : (q : SieveModulus) → Finset (ZMod q.modulus))
    (hR : ∀ q, (R q).Nonempty)
    (hcard : ∀ p : ↥S, ((R (primeSieveModulus S hS p)).card : ℝ) ≤ 3 / 4 * p.1)
    (hres : ∀ n ∈ A, ∀ p : ↥S,
      (n : ZMod (primeSieveModulus S hS p).modulus) ∈ R (primeSieveModulus S hS p)) :
    (S.card : ℝ) / 3 * A.card ≤ 8 * (X + 1) := by
  classical
  let Q := ↥S
  let modulus : Q → SieveModulus := primeSieveModulus S hS
  let embed : ↥A ↪ Fin (X + 1) :=
    { toFun := fun n => ⟨n.1, Nat.lt_succ_iff.mpr (hAX n.1 n.2)⟩
      inj' := by intro n m h; apply Subtype.ext; exact congrArg Fin.val h }
  let survivors := A.attach.map embed
  have hsurvCard : survivors.card = A.card := by simp [survivors]
  have hbase : ∀ p q : Q, p ≠ q →
      (modulus p).modulus.Coprime (modulus q).modulus := by
    intro p q hpq
    exact (Nat.coprime_primes (hS p.1 p.2) (hS q.1 q.2)).mpr
      (fun h => hpq (Subtype.ext h))
  have hprod : ∀ s : FixedCardModulusSelections Q 1,
      sieveModulusProduct (selectedModuliList modulus s) ≤ K := by
    intro s
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp s.2
    simpa [selectedModuliList, hp, sieveModulusProduct, modulus, primeSieveModulus] using hSK p.1 p.2
  have havoid : ∀ n ∈ survivors, ∀ s : FixedCardModulusSelections Q 1,
      SieveAvoids (allowedRestrictions R (selectedModuliList modulus s))
        (natSieveCube (selectedModuliList modulus s) n) := by
    intro n hn s
    rcases Finset.mem_map.mp hn with ⟨m, hm, rfl⟩
    rw [allowedRestrictions_avoids]
    intro q hq
    rw [selectedModuliList, List.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩
    exact hres m.1 m.2 p
  have hglobal := montgomery_global_survivor_card_fixedCardSelections
    modulus hbase (by omega : 0 < X + 1) hprod hK
    (fun s => allowedRestrictions R (selectedModuliList modulus s))
    (fun s => allowedRestrictions_proper R hR _) survivors havoid
  have hden : (S.card : ℝ) / 3 ≤
      ∑ s : FixedCardModulusSelections Q 1,
        sieveRestrictionRatio (allowedRestrictions R (selectedModuliList modulus s)) := by
    calc
      (S.card : ℝ) / 3 = ∑ _s : FixedCardModulusSelections Q 1, (1 / 3 : ℝ) := by
        simp [card_fixedCardModulusSelections, Q, div_eq_mul_inv]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        obtain ⟨p, hp⟩ := Finset.card_eq_one.mp s.2
        have hr := restrictionRatio_ge_third (modulus p) (R (modulus p)) (hR _) (hcard p)
        have hselected : selectedModuliList modulus s = [modulus p] := by
          change s.1.toList.map modulus = [modulus p]
          rw [hp, Finset.toList_singleton]
          rfl
        rw [hselected]
        change (1 / 3 : ℝ) ≤
          ((R (modulus p))ᶜ.card : ℝ) / (((R (modulus p))ᶜ)ᶜ.card : ℝ) * 1
        simpa only [compl_compl, mul_one] using hr
  rw [hsurvCard] at hglobal
  simp only [Nat.cast_add, Nat.cast_one] at hglobal
  exact (mul_le_mul_of_nonneg_right hden (Nat.cast_nonneg A.card)).trans hglobal

end
end Erdos374Research
