import LatticeProb.Analysis.ClockedCellIntervalStrict
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0
import LatticeProb.LQG.CoupledAreaTimeChange

/-! # Clocked Brownian cell comparisons -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- On one full-measure event for a mating-of-trees coupling, every increasing
clock and every positive mesh have only countably many phases at which a weak
cell-to-middle comparison of either Brownian coordinate fails to be strict. -/
theorem ae_countable_clocked_brownian_strict_failures
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ψ : ℝ ≃o ℝ) (ε : ℝ), 0 < ε →
      {θ : ℝ | ∃ (k : Fin 2) (i j : ℤ), i + 1 < j ∧
        let a := ψ (ε * ((i : ℝ) - 1 + θ))
        let b := ψ (ε * ((i : ℝ) + θ))
        let c := ψ (ε * ((j : ℝ) - 1 + θ))
        let d := ψ (ε * ((j : ℝ) + θ))
        let f := fun t => lrCoord k t (bm ω)
        let l := sInf (f '' Icc a b)
        let m := sInf (f '' Icc b c)
        let r := sInf (f '' Icc c d)
        max l r ≤ m ∧ ¬ max l r < m}.Countable := by
  have hmin := ae_of_ae_map hC.measurable_curves.2.2.2.aemeasurable
    (ae_locMinDistinct hC.boundaryLawBM)
  filter_upwards [hmin] with ω hω
  intro ψ ε hε
  apply countable_clocked_cell_interval_strict_failures
    (fun k t => lrCoord k t (bm ω)) ?_ ψ ε hε hω
  intro k
  simp only [lrCoord]
  split <;> fun_prop

end LatticeProb
