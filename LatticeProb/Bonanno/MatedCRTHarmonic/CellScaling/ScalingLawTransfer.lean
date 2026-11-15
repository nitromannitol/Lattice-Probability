/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source modules MatedCRTHarmonic.CellScaling.Model and Scaling and
   MatedCRTHarmonic.MesoModel.MesoInterfaces at commit fdb5cad;
   selected declarations with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ScalingGridEvent
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableEvent

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal Pointwise

namespace MatedCRTHarmonic.MesoModel

/-- **Joint-scaling event-transfer interface.**
For every dyadic mesh and grid parameters, the failure probability of the scaled-grid
event on the mesh-`2⁻ᵏ` cell model equals the failure probability of its scaled version on the
unit-mesh embedding at radius `R_{2ᵏ}`. This follows from the joint quantum-cone / SLE
scaling law, with the deterministic Brownian graph rescaling in `MesoModel.TransferScaling`. This is
the event consequence consumed in the mesoscopic-control construction, rather than an extra estimate. -/
def MatedCRTProposition23GridScalingInput {γ : ℝ} (M : MatedCRTUnitMesoModel γ) : Prop :=
  ∀ k χ β p,
    M.coupled.family.P
      {ω | ¬ (M.unitEmbedding ω).ScaledGridControl (M.radius ω k)
        (CellFamily.mesh k) χ β M.q M.ρ p} =
    M.coupled.family.P
      {ω | ¬ (M.coupled.family.H k ω).ScaledGridControl 1
        (CellFamily.mesh k) χ β M.q M.ρ p}

end MatedCRTHarmonic.MesoModel

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- **Joint-scaling identity:** for every `b > 0`,
`(h_b, η^b) =d (h, η)`, where `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b` and `η^b = R_b⁻¹ η(b ·)`; stated as equality of
the probabilities of every measurable set of (field, curve) pairs (no `Measure.map` junk).
Sources: [14, Prop 4.13(i)] for the field and [18, §3.3] for the joint law.
The proof combines dilation invariance of whole-plane space-filling SLE (`igMap`),
independence from `h` (`indep_curve`), area parametrization (`areaParam`), and
the SLE-free area-scaling law `AreaScalingLaw`. -/
def ConeJointScaling {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  ∀ b : ℝ, 0 < b → ∀ S : Set (LQGMetric.DistC × C(ℝ, ℂ)), MeasurableSet S →
    M.coupled.family.P {ω | (coneRescaleField γ (D.scale b ω) b (D.field ω),
        coneRescaleCurve (D.scale b ω) b (D.curve ω)) ∈ S} =
      M.coupled.family.P {ω | (D.field ω, D.curve ω) ∈ S}

/-- **Boundary-length covariance** (the coupling field `boundaryLength`):
`bm` is a measurable functional `BL` of `(h, η)` (DMS Theorem 1.9: `(L, R)` is the boundary-length process of
`(h, η)`), and under the rescaling of quantum lengths scale by `b^{-1/2}`
when areas scale by `b⁻¹`, so `BL(h_b, η^b) = b^{-1/2} bm(b ·)` a.s. -/
def BoundaryLengthCovariance {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  ∃ BL : LQGMetric.DistC × C(ℝ, ℂ) → MatedCRT.Path2, Measurable BL ∧
    (∀ᵐ ω ∂M.coupled.family.P, M.coupled.bm ω = BL (D.field ω, D.curve ω)) ∧
    ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂M.coupled.family.P,
      BL (coneRescaleField γ (D.scale b ω) b (D.field ω), coneRescaleCurve (D.scale b ω) b (D.curve ω)) =
        brownRescale b (M.coupled.bm ω)

/-- **`(b^{-1/2} bm(b ·), η^b) =d (bm, η)`** for every `b > 0` (from the joint-scaling identity as printed and the
boundary-length covariance): equality of probabilities of every measurable set of `(path, curve)` pairs. -/
theorem configScalingLaw {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M)
    (h23 : ConeJointScaling D) (hBL : BoundaryLengthCovariance D) {b : ℝ} (hb : 0 < b)
    {S : Set (MatedCRT.Path2 × C(ℝ, ℂ))} (hS : MeasurableSet S) :
    M.coupled.family.P {ω | (brownRescale b (M.coupled.bm ω),
        coneRescaleCurve (D.scale b ω) b (D.curve ω)) ∈ S} =
      M.coupled.family.P {ω | (M.coupled.bm ω, D.curve ω) ∈ S} := by
  obtain ⟨BL, hBLm, hbm, hcov⟩ := hBL
  set G : LQGMetric.DistC × C(ℝ, ℂ) → MatedCRT.Path2 × C(ℝ, ℂ) := fun d => (BL d, d.2) with hG
  have hGm : Measurable G := hBLm.prodMk measurable_snd
  have hS' : MeasurableSet (G ⁻¹' S) := hGm hS
  have h1 : {ω | (brownRescale b (M.coupled.bm ω), coneRescaleCurve (D.scale b ω) b (D.curve ω)) ∈ S} =ᵐ[M.coupled.family.P]
      {ω | (coneRescaleField γ (D.scale b ω) b (D.field ω), coneRescaleCurve (D.scale b ω) b (D.curve ω)) ∈
        G ⁻¹' S} := by
    filter_upwards [hcov b hb] with ω hω
    simp only [mem_preimage, hG, hω]
  have h2 : {ω | (M.coupled.bm ω, D.curve ω) ∈ S} =ᵐ[M.coupled.family.P]
      {ω | (D.field ω, D.curve ω) ∈ G ⁻¹' S} := by
    filter_upwards [hbm] with ω hω
    simp only [mem_preimage, hG, hω]
  rw [measure_congr h1, measure_congr h2]
  exact h23 b hb _ hS'

/-! ### Joint scaling in the form used in the mesoscopic construction -/

/-- **the joint-scaling identity, §6 event-transfer form** : the mesoscopic construction's
`MesoModel.MatedCRTProposition23GridScalingInput`, for the SLE/LQG cone realization, from the joint-scaling identity as printed
(`ConeJointScaling`), the boundary-length covariance and the measurability of the mesh event. -/
theorem matedCRTProposition23GridScalingInput_of_cone {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ}
    (D : ConeRealization M) (h23 : ConeJointScaling D) (hBL : BoundaryLengthCovariance D)
    (hmeas : MeshGridEventMeasurable) :
    MesoModel.MatedCRTProposition23GridScalingInput M := by
  intro k χ β p
  set S := meshGridGood k χ β M.q M.ρ p with hS
  have hb : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hconf := configScalingLaw D h23 hBL hb (hmeas k χ β M.q M.ρ p).compl
  have hunit : {ω | ¬ (M.unitEmbedding ω).ScaledGridControl (M.radius ω k) (CellFamily.mesh k) χ β M.q M.ρ p}
      =ᵐ[M.coupled.family.P] {ω | (brownRescale ((2 : ℝ) ^ k) (M.coupled.bm ω),
        coneRescaleCurve (D.scale ((2 : ℝ) ^ k) ω) ((2 : ℝ) ^ k) (D.curve ω)) ∈ Sᶜ} := by
    filter_upwards [D.radius_eq, D.cell_eq] with ω hrad hcell
    have hcellfun : (M.unitEmbedding ω).cell = fun x : ℤ => D.curve ω '' Icc ((x : ℝ) - 1) x := by
      funext x
      rw [M.unitEmbedding_cell ω]
      exact hcell x
    have hR : M.radius ω k = D.scale ((2 : ℝ) ^ k) ω := hrad k
    have hc : 0 < D.scale ((2 : ℝ) ^ k) ω := Real.exp_pos _
    apply propext
    change (¬ RawScaledGridControl _ (M.unitEmbedding ω).cell (M.radius ω k) (CellFamily.mesh k) χ β M.q M.ρ p) ↔ _
    rw [hcellfun, hR, rawScaledGridControl_unit_iff_meshGridGood k _ (M.unitLocallyFinite ω) _ hc]
    rfl
  have hfam : {ω | ¬ (M.coupled.family.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β M.q M.ρ p}
      =ᵐ[M.coupled.family.P] {ω | (M.coupled.bm ω, D.curve ω) ∈ Sᶜ} := by
    filter_upwards [D.meshCell_eq k, M.coupled.meshGraph_eq k] with ω hcell hgraph
    obtain ⟨hE, hlf, hG⟩ := hgraph
    have hcellfun : (M.coupled.family.H k ω).cell = meshCells (CellFamily.mesh k) (D.curve ω) := by
      funext x
      exact hcell x
    apply propext
    change (¬ RawScaledGridControl _ (M.coupled.family.H k ω).cell 1 (CellFamily.mesh k) χ β M.q M.ρ p) ↔ _
    rw [hcellfun, rawScaledGridControl_cast_iff hE hG]
    simp only [mem_compl_iff, hS, meshGridGood, mem_ofPred_eq]
    constructor
    · intro h ⟨hlf', h'⟩
      exact h h'
    · intro h h'
      exact h ⟨hlf, h'⟩
  rw [measure_congr hunit, measure_congr hfam]
  exact hconf

end MatedCRTHarmonic.CellScaling
