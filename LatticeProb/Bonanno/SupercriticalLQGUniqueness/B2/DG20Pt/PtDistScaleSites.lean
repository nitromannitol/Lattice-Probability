/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleSites at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSiteEvent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNet

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistAllSitesGood {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ)
    (F : Finset ℂ) (T : ℝ) : Set Ω :=
  {ω | ∀ x ∈ F, ω ∈ ptDistSiteGood P W ξ Q ζ C n k x T}

 

theorem pt_dist_all_sites_bad_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ)
    (F : Finset ℂ) (T : ℝ) (R : ℝ≥0∞)
    (hsite : ∀ x ∈ F,
      P (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ ≤ R) :
    P (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ ≤ (F.card : ℝ≥0∞) * R := by
  have hsub : (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ ⊆
      ⋃ x ∈ F, (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ := by
    intro ω hω
    simp only [ptDistAllSitesGood, mem_compl_iff, mem_ofPred_eq,
      not_forall, mem_iUnion, mem_compl_iff] at hω ⊢
    obtain ⟨x, hx⟩ := hω
    exact ⟨x, hx.1, hx.2⟩
  calc
    P (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ ≤
        P (⋃ x ∈ F, (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ) := measure_mono hsub
    _ ≤ ∑ x ∈ F, P (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ _x ∈ F, R := Finset.sum_le_sum fun x hx => hsite x hx
    _ = (F.card : ℝ≥0∞) * R := by simp

 

end SupercriticalLQGUniqueness.B2.DG20Pt
