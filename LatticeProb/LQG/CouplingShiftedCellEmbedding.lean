import LatticeProb.LQG.BrownianShiftedCellEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry

/-! # Shifted cellular embeddings in mating-of-trees couplings -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- At a fixed positive mesh, almost every coupling sample has a rooted cellular
embedding with the shifted curve cells for almost every in-mesh phase. -/
theorem ae_shifted_cellularEmbedding_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᵐ c : ℝ ∂volume, 0 ≤ c → c ≤ ε →
      ∃ (hlf : IsLocallyFinite ε
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩)
        (H : CellularEmbedding (MatedCRT.graph ε
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩ hlf) 0),
        H.cell = fun x : ℤ => (fun t => η ω (t + c)) ''
          Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  have hBM := ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable
    (ae_shifted_cellularEmbedding_of_correlatedBM D.boundaryLawBM hε)
  filter_upwards [hBM, ae_peanosphere D, ae_curve_intervals_have_interior D,
    D.areaParam, D.spaceFilling] with ω hBM hP hi harea hspace
  rcases harea with ⟨⟨φ, hφ0, hη⟩, _⟩
  rcases hspace with ⟨_, _, hηL0, hvol⟩
  have hη0 : η ω 0 = 0 := by rw [hη, hφ0, hηL0]
  filter_upwards [hBM (η ω) hP] with c hc
  intro hc0 hcε
  obtain ⟨H, hH⟩ := hc hc0 hcε hη0 hi (ηL ω) φ hη hvol
  exact ⟨hP.locallyFinite_time_translate hε c, H, hH⟩

end MatedCRTHarmonic.MoTInput
