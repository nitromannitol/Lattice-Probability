/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Mass at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Overlap
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Geom

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

 


theorem laneA3_across_mass_of_crossing_pieces
    {ι : Type*} (s : Finset ι)
    (U E F : ι → Set ℂ) (γ : ℝ → ℂ) {z w : ℂ}
    (hγ : IsPiecewiseC1Path γ z w) (ξ : ℝ) (f : ℂ → ℝ)
    (N : ℕ)
    (hcard : ∀ q : ℂ, (s.filter fun i => q ∈ U i).card ≤ N)
    (hpiece : ∀ i ∈ s, ∃ a c : ℝ,
      0 ≤ a ∧ a ≤ c ∧ c ≤ 1 ∧
      (∀ r ∈ Icc a c, γ r ∈ U i) ∧
      ((γ a ∈ E i ∧ γ c ∈ F i) ∨
        (γ c ∈ E i ∧ γ a ∈ F i))) :
    ∑ i ∈ s, crossLenIn ξ f (U i) (E i) (F i) ≤
      (N : ℝ≥0∞) * lfppLen ξ f γ := by
  have hpaid : ∀ i ∈ s, ∃ a c : ℝ,
      Icc a c ⊆ Icc (0 : ℝ) 1 ∧
      (∀ r ∈ Icc a c, γ r ∈ U i) ∧
      crossLenIn ξ f (U i) (E i) (F i) ≤
        ∫⁻ r in Icc a c, lenDens ξ f γ r := by
    intro i hi
    obtain ⟨a, c, ha, hac, hc, hU, hends⟩ := hpiece i hi
    refine ⟨a, c, (fun r hr => ⟨ha.trans hr.1, hr.2.trans hc⟩), hU, ?_⟩
    have hcross : crossLenIn ξ f (U i) (E i) (F i) ≤
        ∫⁻ r in Ioo a c, lenDens ξ f γ r := by
      rcases hends with h | h
      · exact crossLenIn_le_setLIntegral_Ioo hγ ha hac hc hU h.1 h.2
      · exact crossLenIn_le_setLIntegral_Ioo_rev hγ ha hac hc hU h.1 h.2
    exact hcross.trans (lintegral_mono_set
      (fun r hr => ⟨hr.1.le, hr.2.le⟩))
  have hsum := laneA3_sum_paid_pieces_le s U γ (lenDens ξ f γ)
    (fun i => crossLenIn ξ f (U i) (E i) (F i)) N hcard hpaid
  rwa [← lfppLen_eq] at hsum

end SupercriticalLQGUniqueness.B2.DG20Conc
