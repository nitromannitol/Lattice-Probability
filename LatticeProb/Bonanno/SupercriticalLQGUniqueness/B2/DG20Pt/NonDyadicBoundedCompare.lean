/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicBoundedCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicBoxContain

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_non_dyadic_bounded_compare_pos
    (U : Set ℂ) (hU : Bornology.IsBounded U) :
    ∃ x₀ : ℂ, ∃ b : ℝ, 0 < b ∧ U ⊆ ferniqueBox x₀ b ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (n : ℕ) (s u : ℝ), 0 < s → s ≤ 1 → 0 ≤ u →
        let r : ℝ := (2 : ℝ) ^ s
        let W' := dg20ScaledNoise r (by positivity : 0 < r) W
        P.real {ω | ∃ z ∈ U,
          ferniqueCF * Real.sqrt ((8 * b) * b) + u <
            |phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 z ω -
              phiMN W P 0 n ((r : ℂ) * z) ω|} ≤
          2 * Real.exp (-u ^ 2 / 2) := by
  obtain ⟨x₀, b, hb, hsub⟩ := dg20_bounded_subset_ferniqueBox U hU
  refine ⟨x₀, b, hb, hsub, ?_⟩
  intro Ω _ P W hW n s u hs hs1 hu
  exact dg20_non_dyadic_compare_on_box P W hW U x₀ b hb hsub n s u hs hs1 hu

end SupercriticalLQGUniqueness.B2.DG20Pt
