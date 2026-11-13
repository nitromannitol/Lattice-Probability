/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTInput.ConeRealization at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.MeshFamily
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model

/-!
# Full-space Meso and cone-realization adapters for the mating bundle

The bundle supplies the cellular embeddings almost surely. This file changes the curve and Brownian
path only on a measurable null set, using one fixed sample where all dyadic embeddings exist. The
resulting Meso model is defined on the bundle's original standard-Borel probability space, so the
consumer map is the identity and the GFF, Brownian, and independence fields transfer directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

variable (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
include D

/-- A sample point in the measurable full-measure set on which every dyadic curve-cell
embedding exists. -/
noncomputable def meshGoodPoint : Ω := by
  classical
  have hS := (meshGoodSetData D).property
  have hnonempty : ∃ ω, ω ∈ (meshGoodSetData D).val := by
    by_contra h
    have hfalse : ∀ᵐ ω ∂P, False := hS.2.2.mono (by
      intro ω hω
      exact h (Exists.intro ω hω))
    have hzero : P Set.univ = 0 := by
      simpa using hfalse
    haveI := D.isProbabilityMeasure
    rw [measure_univ] at hzero
    exact (by norm_num : (1 : ℝ≥0∞) ≠ 0) hzero
  exact Classical.choose hnonempty

theorem meshGoodPoint_mem : meshGoodPoint D ∈ (meshGoodSetData D).val := by
  classical
  exact Classical.choose_spec (by
    by_contra h
    have hfalse : ∀ᵐ ω ∂P, False := (meshGoodSetData D).property.2.2.mono (by
      intro ω hω
      exact h (Exists.intro ω hω))
    have hzero : P Set.univ = 0 := by simpa using hfalse
    haveI := D.isProbabilityMeasure
    rw [measure_univ] at hzero
    exact (by norm_num : (1 : ℝ≥0∞) ≠ 0) hzero)

/-- The bundle's Brownian boundary path, replaced off the good set by its value at
`meshGoodPoint`. -/
noncomputable def bundleBM (ω : Ω) : Path2 := by
  classical
  exact if ω ∈ (meshGoodSetData D).val then bm ω else bm (meshGoodPoint D)

/-- The bundle's area-parametrized curve, replaced off the good set by its value at
`meshGoodPoint`. -/
noncomputable def bundleCurve (ω : Ω) : C(ℝ, ℂ) := by
  classical
  exact if ω ∈ (meshGoodSetData D).val then η ω else η (meshGoodPoint D)

theorem ae_bundleBM_eq : (fun ω => bundleBM (D := D) ω) =ᵐ[P] bm := by
  filter_upwards [(meshGoodSetData D).property.2.2] with ω hω
  simp [bundleBM, hω]

theorem ae_bundleCurve_eq : (fun ω => bundleCurve (D := D) ω) =ᵐ[P] η := by
  filter_upwards [(meshGoodSetData D).property.2.2] with ω hω
  simp [bundleCurve, hω]

theorem measurable_bundleBM : Measurable (bundleBM (D := D)) := by
  exact Measurable.ite (meshGoodSetData D).property.1
    D.measurable_curves.2.2.2 measurable_const

theorem measurable_bundleCurve : Measurable (bundleCurve (D := D)) := by
  exact Measurable.ite (meshGoodSetData D).property.1
    D.measurable_curves.2.1 measurable_const

theorem bundleBM_eq_of_mem (ω : Ω) (hω : ω ∈ (meshGoodSetData D).val) :
    bundleBM (D := D) ω = bm ω := by
  simp [bundleBM, hω]

theorem bundleBM_eq_of_not_mem (ω : Ω) (hω : ω ∉ (meshGoodSetData D).val) :
    bundleBM (D := D) ω = bm (meshGoodPoint D) := by
  simp [bundleBM, hω]

/-! The dependent pair of local-finiteness witness and embedding at one sample and mesh. -/
abbrev BundleGeometry (w : Path2) (k : ℕ) :=
  Σ' h : IsLocallyFinite (CellFamily.mesh k) w,
    CellularEmbedding (MatedCRT.graph (CellFamily.mesh k) w h) 0

@[simp] theorem BundleGeometry.embedding_cell_cast {w w' : Path2} (k : ℕ) (h : w = w')
    (G : BundleGeometry w k) :
    (h ▸ G).2.cell = G.2.cell := by
  cases h
  rfl

/-- At each sample and mesh, choose the locally finite graph and its cellular embedding; on the
null-set fallback these are taken from `meshGoodPoint`. -/
noncomputable def bundleGeometry (ω : Ω) (k : ℕ) :
    BundleGeometry (bundleBM (D := D) ω) k := by
  classical
  exact if hω : ω ∈ (meshGoodSetData D).val then
    let H := ((meshGoodSetData D).property.2.1 ω hω).2 k
    (bundleBM_eq_of_mem D ω hω).symm ▸
      (⟨Classical.choose H, Classical.choose (Classical.choose_spec H)⟩ : BundleGeometry (bm ω) k)
  else
    let H := ((meshGoodSetData D).property.2.1 (meshGoodPoint D)
      (meshGoodPoint_mem D)).2 k
    (bundleBM_eq_of_not_mem D ω hω).symm ▸
      (⟨Classical.choose H, Classical.choose (Classical.choose_spec H)⟩ :
        BundleGeometry (bm (meshGoodPoint D)) k)

theorem bundleGeometry_cell (ω : Ω) (k : ℕ) :
    (bundleGeometry (D := D) ω k).2.cell = fun x : ℤ => bundleCurve (D := D) ω '' Icc
      (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) := by
  classical
  by_cases hω : ω ∈ (meshGoodSetData D).val
  · let H := ((meshGoodSetData D).property.2.1 ω hω).2 k
    let G : BundleGeometry (bm ω) k :=
      ⟨Classical.choose H, Classical.choose (Classical.choose_spec H)⟩
    have hcell : G.2.cell = fun x : ℤ => η ω '' Icc
        (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) :=
      Classical.choose_spec (Classical.choose_spec H)
    have hb := bundleBM_eq_of_mem D ω hω
    rw [bundleGeometry, dite_eq_left hω, bundleCurve, if_pos hω]
    change (hb.symm ▸ G).2.cell = _
    exact (BundleGeometry.embedding_cell_cast (D := D) k hb.symm G).trans hcell
  · let H := ((meshGoodSetData D).property.2.1 (meshGoodPoint D)
      (meshGoodPoint_mem D)).2 k
    let G : BundleGeometry (bm (meshGoodPoint D)) k :=
      ⟨Classical.choose H, Classical.choose (Classical.choose_spec H)⟩
    have hcell : G.2.cell = fun x : ℤ => η (meshGoodPoint D) '' Icc
        (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) :=
      Classical.choose_spec (Classical.choose_spec H)
    have hb := bundleBM_eq_of_not_mem D ω hω
    rw [bundleGeometry, dite_eq_right hω, bundleCurve, if_neg hω]
    change (hb.symm ▸ G).2.cell = _
    exact (BundleGeometry.embedding_cell_cast (D := D) k hb.symm G).trans hcell

/-- The all-sample dyadic random-cell family on the original bundle space. Its graph edge subtype
and graph are exactly those of the mated-CRT map at each dyadic mesh. -/
noncomputable def bundleRandomCellFamily : CellFamily.RandomCellFamily := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact
    { Ω := Ω
      P := P
      E := fun k ω => MatedCRT.Edge (CellFamily.mesh k) (bundleBM (D := D) ω)
      G := fun k ω => MatedCRT.graph (CellFamily.mesh k) (bundleBM (D := D) ω)
        (bundleGeometry (D := D) ω k).1
      H := fun k ω => (bundleGeometry (D := D) ω k).2 }

/-- A repaired full-space version of the dyadic family, with the original bundle as its sample
space. -/
noncomputable def bundleMatedMeshFamily : CellFamily.MultigraphCoupledRandomFamily γ := by
  let F := bundleRandomCellFamily D
  let b : F.Ω → Path2 := bundleBM (D := D)
  let c : F.Ω → ℤ → Set ℂ := fun ω x => bundleCurve (D := D) ω '' Icc ((x : ℝ) - 1) x
  have hLaw : IsCorrelatedBM2 γ (P.map b) := by
    change IsCorrelatedBM2 γ (P.map (bundleBM (D := D)))
    rw [Measure.map_congr (ae_bundleBM_eq D)]
    exact D.boundaryLawBM
  have hCoupling : IsCellCoupling γ P b c := by
    refine ⟨measurable_bundleBM D, hLaw, ?_⟩
    filter_upwards [] with ω
    refine ⟨(bundleGeometry (D := D) ω 0).1,
      (bundleGeometry (D := D) ω 0).2, ?_⟩
    funext x
    have hc := bundleGeometry_cell D ω 0
    simpa [CellFamily.mesh] using congrArg (fun f : ℤ → Set ℂ => f x) hc
  have hGraph : CellFamily.MatedCRTMultigraphIdentification F b := by
    intro k
    exact Filter.Eventually.of_forall fun ω =>
      ⟨rfl, (bundleGeometry (D := D) ω k).1, rfl⟩
  exact CellFamily.MultigraphCoupledRandomFamily.ofMultigraph F b c hCoupling hGraph

/-- The bundle supplies a unit-mesh mesoscopic model on its original standard-Borel probability
space. -/
noncomputable def unitMesoModelOfCoupling
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    MesoModel.MatedCRTUnitMesoModel γ := by
  letI : StandardBorelSpace Ω := hstd
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  refine
    { coupled := bundleMatedMeshFamily D
      standardBorel := hstd
      unitLocallyFinite := fun ω => (bundleGeometry (D := D) ω 0).1
      unitEmbedding := fun ω => (bundleGeometry (D := D) ω 0).2
      unitEmbedding_cell := ?_
      radius := fun ω k => CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω)
        ((2 : ℝ) ^ k)
      radius_pos := fun _ _ => Real.exp_pos _
      ρ := 1 / 2
      hρ := by norm_num
      q := 1 / (2 + γ) ^ 2
      hq := ?_
      hγ := hγ }
  · intro ω
    change (bundleGeometry (D := D) ω 0).2.cell =
      fun x : ℤ => bundleCurve (D := D) ω '' Icc ((x : ℝ) - 1) x
    funext x
    have hc := bundleGeometry_cell D ω 0
    have hx := congrArg (fun f : ℤ → Set ℂ => f x) hc
    simpa [CellFamily.mesh] using hx
  · have hden : 0 < (2 + γ) ^ 2 := by
      have : 0 < 2 + γ := by
        rcases hγ with ⟨hγ0, hγ2⟩
        linarith
      positivity
    constructor
    · positivity
    · have hi : 0 < ((2 + γ) ^ 2)⁻¹ := inv_pos.mpr hden
      have hlt := mul_lt_mul_of_pos_right (by norm_num : (1 : ℝ) < 2) hi
      simpa [one_div, div_eq_mul_inv] using hlt

/-- A cone realization induced by the mating bundle, on the same full-space unit Meso model. -/
noncomputable def coneRealizationOfCoupling
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    CellScaling.ConeRealization (unitMesoModelOfCoupling D hstd hγ) where
  X := X
  B := B
  B' := B'
  curve := bundleCurve (D := D)
  gff := D.gff
  brownian := D.bm_B
  brownian' := D.bm_B'
  indep := D.indep_cone
  measurable_curve := measurable_bundleCurve D
  radius_eq := Filter.Eventually.of_forall fun ω k => rfl
  cell_eq := Filter.Eventually.of_forall fun ω x => by
    rfl
  meshCell_eq := fun k => Filter.Eventually.of_forall fun ω x => by
    change (bundleGeometry (D := D) ω k).2.cell x =
      bundleCurve (D := D) ω '' Icc (CellFamily.mesh k * ((x : ℝ) - 1))
        (CellFamily.mesh k * x)
    exact congrArg (fun f : ℤ → Set ℂ => f x) (bundleGeometry_cell D ω k)

end MatedCRTHarmonic.MoTInput
