import LatticeProb.Prob.CorrelatedBMConeWindowStationarity
import LatticeProb.Prob.ConeWindowStrictEntrance

/-! # Local cone intervals around a fixed time -/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Under almost-every-time cone-window coverage, every neighbourhood of a
fixed time contains a cone interval whose interior contains that time. -/
theorem ae_forall_exists_cone_interval_of_coverage
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → Path2) (hB : Measurable B) {γ : ℝ}
    (hLaw : IsCorrelatedBM2 γ (P.map B))
    (hcoverage : ∀ l r : ℝ, l < r → ∀ᵐ ω ∂P,
      ∀ᵐ t ∂volume.restrict (Ioo l r),
        (coordinatePaths (B ω), t) ∈ Prod.fst '' coneWindowWitness l r)
    (u : ℝ) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a < u → u < b →
      ∃ s t : ℝ, a < s ∧ s < u ∧ u < t ∧ t < b ∧
        IsGLB {v : ℝ | v < t ∧ ∀ w ∈ Icc v t,
          (coordinatePaths (B ω)).1 t ≤ (coordinatePaths (B ω)).1 w ∧
          (coordinatePaths (B ω)).2 t ≤ (coordinatePaths (B ω)).2 w} s := by
  have hq (p q : ℚ) : ∀ᵐ ω ∂P,
      (p : ℝ) < u → u < (q : ℝ) →
        (coordinatePaths (B ω), u) ∈ Prod.fst '' coneWindowWitness (p : ℝ) (q : ℝ) := by
    by_cases hp : (p : ℝ) < u
    · by_cases hq : u < (q : ℝ)
      · filter_upwards [ae_coneWindowCoverage_fixedTime_of_correlatedBM P B hB hLaw hcoverage hp hq] with ω hω
        exact fun _ _ => hω
      · exact Filter.Eventually.of_forall fun _ _ h => (hq h).elim
    · exact Filter.Eventually.of_forall fun _ h _ => (hp h).elim
  filter_upwards [ae_all_iff.2 fun p => ae_all_iff.2 (hq p)] with ω hω
  intro a b hau hub
  obtain ⟨p, hap, hpu⟩ := exists_rat_btwn hau
  obtain ⟨q, huq, hqb⟩ := exists_rat_btwn hub
  obtain ⟨⟨⟨z, x⟩, t⟩, ht, heq⟩ := hω p q hpu huq
  have hz : z = coordinatePaths (B ω) := congrArg Prod.fst heq
  have hx : x = u := congrArg Prod.snd heq
  subst z
  subst x
  rcases (mem_coneWindowWitness_iff_strict_start_isGLB _ _ _ _ _).1 ht with
    ⟨_, hut, htq, s, hps, hsu, hs⟩
  exact ⟨s, t, lt_of_lt_of_le hap hps, hsu, hut, lt_of_le_of_lt htq hqb, hs⟩

end LatticeProb.CorrelatedBM
