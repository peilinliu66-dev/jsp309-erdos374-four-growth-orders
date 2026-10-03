import Erdos374Research.FiveSixAssembly
import Erdos374Research.OrderedBlockShortness

/-!
# Erdős problem 374: the four original orders of growth

UNCOMPILED. All four clauses are assembled here with no extra mathematical
premises. The imported public analytic results and Yudin's mathematical
argument are attributed in SOURCE_ATTRIBUTION.md. This source file is not a
claim of successful Lean elaboration, axiom closure, novelty, or prize status.
-/

namespace Erdos374Research

open Filter
open scoped Topology

theorem eventually_blocksAreShort {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 100000) :
    ∀ᶠ n : ℕ in atTop, BlocksAreShort ε n := by
  have h := eventually_orderedTwoBlocks_small_parameters
    (show 0 ≤ 3 * ε / 4 by positivity)
    (show 3 * ε / 4 < ε by linarith)
    (show 3 * ε / 4 < 1 / 3 by linarith)
  filter_upwards [h] with n hn
  intro m l₁ l₂ c a p hb hp ha hgap hnap hasmall
  have hd := hn a p m l₁ l₂ c hp hnap hasmall hb
  exact ⟨hd.1, hd.2.1.le⟩

theorem growth_five_and_six :
    HasOrder (countD 5) (fun X => X) ∧ HasOrder (countD 6) (fun X => X) := by
  obtain ⟨ε, δ, hε, hεsmall, hδ, hfive, hsix⟩ := two_candidate_families_positive_density
  exact growth_five_and_six_of_short_blocks hε hεsmall hδ
    (eventually_blocksAreShort hε hεsmall) hfive hsix

theorem growth_five : HasOrder (countD 5) (fun X => X) := growth_five_and_six.1

theorem growth_six : HasOrder (countD 6) (fun X => X) := growth_five_and_six.2

/-- Literal original-scope endpoint: D3 has order sqrt X; D4, D5 and D6
have order X. There are no unproved seed, density, sieve, or equidistribution
hypotheses in this declaration. It is an uncompiled source draft. -/
theorem erdos_374_original_growth : OriginalGrowthConclusion :=
  ⟨growth_three, growth_four, growth_five, growth_six⟩

end Erdos374Research
