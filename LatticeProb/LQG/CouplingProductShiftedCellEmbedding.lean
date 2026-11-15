import LatticeProb.LQG.CouplingShiftedSideStrict
import LatticeProb.LQG.PeanosphereCellEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry

/-! # Product-almost-everywhere shifted cellular embeddings -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

/-- A coupling sample and an independent absolutely continuous phase almost surely
have a matching rooted shifted cellular embedding whenever the phase is in the mesh interval. -/
theorem ae_prod_shifted_cellularEmbedding_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∀ᵐ p ∂P.prod Q, 0 ≤ p.2 → p.2 ≤ ε →
      let w : Path2 := ⟨fun t => bm p.1 (t + p.2),
        (bm p.1).continuous.comp (by fun_prop)⟩
      ∃ (hlf : IsLocallyFinite ε w)
        (H : CellularEmbedding (MatedCRT.graph ε w hlf) 0),
        H.cell = fun x : ℤ => (fun t => η p.1 (t + p.2)) ''
          Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hs := ae_prod_shifted_sideStrict_of_coupling D hε Q hQ
  have hp := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually (ae_peanosphere D)
  have hi := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually (ae_curve_intervals_have_interior D)
  have ha := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually D.areaParam
  have hf := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).tendsto_ae.eventually D.spaceFilling
  filter_upwards [hs, hp, hi, ha, hf] with p hs hp hi ha hf
  intro hc0 hcε
  rcases ha with ⟨⟨φ, hφ0, hη⟩, _⟩
  rcases hf with ⟨_, _, hηL0, hvol⟩
  have hη0 : η p.1 0 = 0 := by rw [hη, hφ0, hηL0]
  exact ⟨hp.locallyFinite_time_translate hε p.2,
    peanosphereCellularEmbedding hε hc0 hcε hη0 hp hs hi φ hη hvol, rfl⟩

end MatedCRTHarmonic.MoTInput
