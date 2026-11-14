/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScales at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleEvent

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistAllScalesGood {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n : ℕ)
    (F : ℕ → Finset ℂ) (V : Set ℂ) (R T : ℝ)
    (t : ℕ → ℝ) : Set Ω :=
  {ω | ∀ k ∈ Finset.range (n + 1),
    ω ∈ ptDistScaleGood P W ξ Q ζ C n k (F k) V R (t k) T}

 

theorem pt_dist_all_scales_bad_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n : ℕ)
    (F : ℕ → Finset ℂ) (V : Set ℂ) (R T : ℝ)
    (t : ℕ → ℝ) :
    P (ptDistAllScalesGood P W ξ Q ζ C n F V R T t)ᶜ ≤
      ∑ k ∈ Finset.range (n + 1),
        P (ptDistScaleGood P W ξ Q ζ C n k (F k) V R (t k) T)ᶜ := by
  have hsub :
      (ptDistAllScalesGood P W ξ Q ζ C n F V R T t)ᶜ ⊆
        ⋃ k ∈ Finset.range (n + 1),
          (ptDistScaleGood P W ξ Q ζ C n k (F k) V R (t k) T)ᶜ := by
    intro ω hω
    simp only [ptDistAllScalesGood, mem_compl_iff, mem_ofPred_eq,
      not_forall, mem_iUnion, mem_compl_iff] at hω ⊢
    obtain ⟨k, hk⟩ := hω
    exact ⟨k, hk.1, hk.2⟩
  exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)

end SupercriticalLQGUniqueness.B2.DG20Pt
