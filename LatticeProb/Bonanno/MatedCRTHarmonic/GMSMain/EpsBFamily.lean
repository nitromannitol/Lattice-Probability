/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBDiagonal
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBRescale
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15AModel
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Density
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4F.Prop210Degree47

/-!
# The band family of a mating-of-trees coupling at real meshes `θₖ`

For a frozen coupling `D` (bundle `MatedCRT.MatingOfTreesInput γ`) and any meshes `θ : ℕ → ℝ`
(`θ k > 0`), `bandFamily D θ hθ` is the `CellFamily.RandomCellFamily` whose `k`-th member is the embedded mated-CRT map of
mesh `θ k` of [18]: the frozen multigraph `MatedCRT.graph (θ k) (bm ω)` with the SLE/LQG cells
`η([θₖ(x−1), θₖx])` (`MoTInput.cellularEmbeddingOfCurveAt`), on the measurable full-measure subspace where all these
cells form cellular embeddings. Nothing here is dyadic; the landed [18] machinery measures member `k` against the
nominal scale `2⁻ᵏ`, and the inputs below are stated in that form for band sequences (`θ k ∈ (2⁻ᵏ⁻¹, 2⁻ᵏ]`):

* `bandFamily_graphConnected`, `bandFamily_graphLoopless` — every mesh graph (frozen `matedCRT_graph_connected`;
  edges have `src < tgt`);
* `bandFamily_peanosphereG0` — `CellFamily.PeanosphereG0`, whose witness must have the nominal mesh `2⁻ᵏ`: the time change
  `t ↦ (θₖ/2⁻ᵏ) t` of the Brownian pair and of the curve (`EpsBRescale`) presents the mesh-`θₖ` map as a mesh-`2⁻ᵏ`
  one;
* `bandFamily_uDens_le` — [18] (4.20) at mesh `θₖ`: `u^ε ≤ 2 u_*^ε` a.e. (the landed deterministic (4.7)
  `GMS4F.matedCRT_degree_le_two_local_degrees` and (4.5) `Canon.selectedCell_rawCoef_le_two_uStar` at any mesh);
* `lemma27_real` — [18] Lemma 2.7 at every real `ε ∈ (0, 1)` for the bundle curve (landed
  `GMSLemma27.lemma27_segments`, already real-mesh), and its two consumers' forms on the band family;
* `Prop410Real` (the same proposition as `EpsAProp410At`) and `bandFamily_prop210At` — [18] Proposition 2.10 on the
  band family from Proposition 4.10 at real meshes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.EpsB

open MatedCRTHarmonic

/-- **[18] Proposition 4.10 at every real mesh** for the area-parametrized curve `η` at ambient radius `ρ` and test
constant `C`: the body of `GMSMain.EpsAProp410At` (`GMSMain/EpsAProp410.lean`), verbatim, so that `epsA_prop410At` instantiates it by `id`. -/
def Prop410Real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (ρ C : ℝ) : Prop :=
  ∃ β A α Cfail : ℝ, 0 < β ∧ 0 < α ∧ 0 ≤ A ∧ 0 ≤ Cfail ∧
    ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible ε ρ C β V f →
      P (BundleSec4.Prop410Bad η ε V f A (ε ^ α)) ≤ ENNReal.ofReal (Cfail * ε ^ α)

/-- The segment form of [18] Lemma 2.7's event at mesh `ε` for one curve: every segment `c([a, b])` with
`b − a ≤ ε` meeting `B_ρ(0)` has diameter `≤ ε^q`. -/
def SegDiamGood (c : C(ℝ, ℂ)) (ε q ρ : ℝ) : Prop :=
  ∀ a b : ℝ, b - a ≤ ε → (c '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty → diam (c '' Icc a b) ≤ ε ^ q

/-- The geometric good event at the meshes `θ k`: the Peanosphere bundle, the strict side condition and local
finiteness at every `θ k`, `η(0) = 0`, cells with interior and pairwise null intersections. -/
structure BandGood (θ : ℕ → ℝ) (w : MatedCRT.Path2) (c : C(ℝ, ℂ)) : Prop where
  peano : RouteM.Peanosphere w c
  side : ∀ k, RouteM.SideStrict (θ k) w
  locFin : ∀ k, MatedCRT.IsLocallyFinite (θ k) w
  zero : c 0 = 0
  interior : ∀ a b : ℝ, a < b → (interior (c '' Icc a b)).Nonempty
  null : ∀ k (x y : ℤ), x ≠ y →
    volume ((c '' Icc (θ k * ((x : ℝ) - 1)) (θ k * x)) ∩ (c '' Icc (θ k * ((y : ℝ) - 1)) (θ k * y))) = 0

/-- Rate comparison along a band sequence: `θₖ^α ≤ (2⁻ᵏ)^α`. -/
theorem rpow_le_mesh_rpow {θ : ℕ → ℝ} (hθ : IsBandSeq θ) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    θ k ^ α ≤ CellFamily.mesh k ^ α :=
  Real.rpow_le_rpow (hθ.pos k).le (hθ k).2.1 hα

/-- [18] Proposition 2.10's admissibility at a mesh `ε` implies it at any finer mesh `ε' ∈ (0, ε]`. -/
theorem prop210Admissible_mono {ε ε' ρ C β : ℝ} {V : Set ℂ} {f : ℂ → ℝ} (h0 : 0 < ε') (hle : ε' ≤ ε)
    (h : GMS4.Prop210Admissible ε ρ C β V f) : GMS4.Prop210Admissible ε' ρ C β V f := by
  obtain ⟨_, hε1, hρ0, hρ1, hC, hβ, hV, hVc, hVρ, hthick, hf, hlip⟩ := h
  have hpow : ε ^ (-β) ≤ ε' ^ (-β) := Real.rpow_le_rpow_of_nonpos h0 hle (by linarith)
  have hC0 : 0 ≤ C := by linarith
  refine ⟨h0, lt_of_le_of_lt hle hε1, hρ0, hρ1, hC, hβ, hV, hVc, hVρ, hthick, fun z hz => ?_,
    fun z hz w hw => ?_⟩
  · exact ⟨(hf z hz).1, (hf z hz).2.trans (mul_le_mul_of_nonneg_left hpow hC0)⟩
  · exact (hlip z hz w hw).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC0) dist_nonneg)

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The geometric good event holds almost surely at any countable family of positive meshes. -/
theorem ae_bandGood (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {θ : ℕ → ℝ} (hθ : ∀ k, 0 < θ k) : ∀ᵐ ω ∂P, BandGood θ (bm ω) (η ω) := by
  have hside : ∀ᵐ ω ∂P, ∀ k, RouteM.SideStrict (θ k) (bm ω) := by
    refine ae_all_iff.2 fun k => ?_
    exact ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable
      (MatedCRT.ae_sideStrict D.boundaryLawBM (θ k) (hθ k))
  have hlocal : ∀ᵐ ω ∂P, ∀ k, MatedCRT.IsLocallyFinite (θ k) (bm ω) := by
    refine ae_all_iff.2 fun k => ?_
    exact ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable
      (MatedCRTHarmonic.ae_isLocallyFinite_holds γ (P.map bm) D.boundaryLawBM (θ k) (hθ k))
  filter_upwards [MoTInput.ae_peanosphere D, hside, hlocal, MoTInput.ae_curve_intervals_have_interior D,
    D.areaParam, D.spaceFilling] with ω hP hs hl hint harea hspace
  rcases harea with ⟨⟨φ, hφ0, hη⟩, _⟩
  rcases hspace with ⟨_, _, hηL0, hvol⟩
  exact ⟨hP, hs, hl, by rw [hη, hφ0, hηL0], hint,
    fun k x y hxy => MoTInput.volume_inter_mesh_cells_zero (hθ k) hη hvol hxy⟩

/-- A measurable full-measure subset of the geometric good event. -/
noncomputable def bandGoodSetData (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (θ : ℕ → ℝ) (hθ : ∀ k, 0 < θ k) :
    {S : Set Ω // MeasurableSet S ∧ (∀ ω, ω ∈ S → BandGood θ (bm ω) (η ω)) ∧ ∀ᵐ ω ∂P, ω ∈ S} := by
  classical
  let A : Set Ω := {ω | BandGood θ (bm ω) (η ω)}
  have hA : ∀ᵐ ω ∂P, ω ∈ A := ae_bandGood D hθ
  have hbad : P Aᶜ = 0 := by
    have hset : {ω | ¬ ω ∈ A} = Aᶜ := by ext ω; simp
    rw [← hset]
    exact ae_iff.mp hA
  let N := Classical.choose (exists_measurable_superset_of_null hbad)
  have hN := Classical.choose_spec (exists_measurable_superset_of_null hbad)
  refine ⟨Nᶜ, hN.2.1.compl, fun ω hω => ?_, ?_⟩
  · by_contra h
    exact hω (hN.1 h)
  · rw [ae_iff]
    have hset : {ω | ¬ ω ∈ Nᶜ} = N := by ext ω; simp
    rw [hset]
    exact hN.2.2

/-- The measurable full-measure subtype carrying the band family. -/
abbrev BandSpace (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (θ : ℕ → ℝ) (hθ : ∀ k, 0 < θ k) :=
  {ω : Ω // ω ∈ (bandGoodSetData D θ hθ).val}

variable (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
  (θ : ℕ → ℝ) (hθ : ∀ k, 0 < θ k)

theorem bandSpace_measurePreserving :
    MeasurePreserving (Subtype.val : BandSpace D θ hθ → Ω) (P.comap Subtype.val) P := by
  have hS := (bandGoodSetData D θ hθ).property
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [map_comap_subtype_coe hS.1]
  exact Measure.restrict_eq_self_of_ae_mem hS.2.2

theorem bandSpace_probability : IsProbabilityMeasure (P.comap (Subtype.val : BandSpace D θ hθ → Ω)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hMP := bandSpace_measurePreserving D θ hθ
  have : IsProbabilityMeasure ((P.comap (Subtype.val : BandSpace D θ hθ → Ω)).map Subtype.val) := by
    rw [hMP.map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map hMP.measurable.aemeasurable

theorem bandSpace_good (ω : BandSpace D θ hθ) : BandGood θ (bm ω.1) (η ω.1) :=
  (bandGoodSetData D θ hθ).property.2.1 ω.1 ω.2

/-- The mesh-`θₖ` cellular embedding with the SLE/LQG cells `η([θₖ(x−1), θₖx])`. -/
noncomputable def bandEmbedding (ω : BandSpace D θ hθ) (k : ℕ) :
    CellularEmbedding (MatedCRT.graph (θ k) (bm ω.1) ((bandSpace_good D θ hθ ω).locFin k)) 0 :=
  MoTInput.cellularEmbeddingOfCurveAt (hθ k) ((bandSpace_good D θ hθ ω).locFin k)
    (bandSpace_good D θ hθ ω).peano ((bandSpace_good D θ hθ ω).side k) (bandSpace_good D θ hθ ω).zero
    (fun x => (bandSpace_good D θ hθ ω).interior _ _ (by have := hθ k; nlinarith))
    ((bandSpace_good D θ hθ ω).null k)

theorem bandEmbedding_cell (ω : BandSpace D θ hθ) (k : ℕ) (x : ℤ) :
    (bandEmbedding D θ hθ ω k).cell x = η ω.1 '' Icc (θ k * ((x : ℝ) - 1)) (θ k * x) := rfl

/-- **The band family**: member `k` is the embedded mated-CRT map of mesh `θ k`. -/
noncomputable def bandFamily : CellFamily.RandomCellFamily := by
  let _ : IsProbabilityMeasure (P.comap (Subtype.val : BandSpace D θ hθ → Ω)) := bandSpace_probability D θ hθ
  exact
    { Ω := BandSpace D θ hθ
      P := P.comap Subtype.val
      E := fun k ω => MatedCRT.Edge (θ k) (bm ω.1)
      G := fun k ω => MatedCRT.graph (θ k) (bm ω.1) ((bandSpace_good D θ hθ ω).locFin k)
      H := fun k ω => bandEmbedding D θ hθ ω k }

theorem bandFamily_measurePreserving :
    MeasurePreserving (Subtype.val : BandSpace D θ hθ → Ω) (bandFamily D θ hθ).P P :=
  bandSpace_measurePreserving D θ hθ

theorem bandFamily_graphConnected : CellFamily.GraphConnected (bandFamily D θ hθ) := fun k =>
  Filter.Eventually.of_forall fun (ω : BandSpace D θ hθ) =>
    Implementation.matedCRT_graph_connected_impl (θ k) (bm ω.1) ((bandSpace_good D θ hθ ω).locFin k)

theorem bandFamily_graphLoopless : CellFamily.GraphLoopless (bandFamily D θ hθ) := fun k =>
  Filter.Eventually.of_forall fun (ω : BandSpace D θ hθ) e =>
    CellFamily.matedCRT_graph_src_ne_tgt (θ k) (bm ω.1) ((bandSpace_good D θ hθ ω).locFin k) e

/-- **`CellFamily.PeanosphereG0` for the band family**, through the time change `t ↦ (θₖ/2⁻ᵏ) t`: the mesh-`θₖ` map of
`(bm, η)` is the mesh-`2⁻ᵏ` map of the time-changed pair. -/
theorem bandFamily_peanosphereG0 : CellFamily.PeanosphereG0 (bandFamily D θ hθ) := by
  intro k
  refine Filter.Eventually.of_forall fun (ω : BandSpace D θ hθ) => ?_
  have hg := bandSpace_good D θ hθ ω
  have hm := mesh_pos k
  have hc : 0 < θ k / CellFamily.mesh k := div_pos (hθ k) hm
  have hcm : θ k / CellFamily.mesh k * CellFamily.mesh k = θ k := div_mul_cancel₀ _ hm.ne'
  have hlf' : MatedCRT.IsLocallyFinite (CellFamily.mesh k) (rescalePath (θ k / CellFamily.mesh k) (bm ω.1)) :=
    isLocallyFinite_rescale hc (by rw [hcm]; exact hg.locFin k)
  have hP' : RouteM.Peanosphere (rescalePath (θ k / CellFamily.mesh k) (bm ω.1))
      (rescaleCurve (θ k / CellFamily.mesh k) (η ω.1)) := peanosphere_rescale hc hg.peano
  have hside' : RouteM.SideStrict (CellFamily.mesh k) (rescalePath (θ k / CellFamily.mesh k) (bm ω.1)) :=
    sideStrict_rescale hc (by rw [hcm]; exact hg.side k)
  have h0' : rescaleCurve (θ k / CellFamily.mesh k) (η ω.1) 0 = 0 := by
    rw [rescaleCurve_apply, mul_zero]
    exact hg.zero
  have hcell : ∀ x : ℤ, rescaleCurve (θ k / CellFamily.mesh k) (η ω.1) ''
      Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) =
      η ω.1 '' Icc (θ k * ((x : ℝ) - 1)) (θ k * x) := by
    intro x
    rw [rescaleCurve_cell hc, hcm]
  have hint' : ∀ x : ℤ, (interior (rescaleCurve (θ k / CellFamily.mesh k) (η ω.1) ''
      Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x))).Nonempty := by
    intro x
    rw [hcell]
    exact hg.interior _ _ (by have := hθ k; nlinarith)
  have hnull' : ∀ x y : ℤ, x ≠ y →
      volume ((rescaleCurve (θ k / CellFamily.mesh k) (η ω.1) ''
        Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x)) ∩
        (rescaleCurve (θ k / CellFamily.mesh k) (η ω.1) ''
          Icc (CellFamily.mesh k * ((y : ℝ) - 1)) (CellFamily.mesh k * y))) = 0 := by
    intro x y hxy
    rw [hcell, hcell]
    exact hg.null k x y hxy
  refine ⟨rescalePath (θ k / CellFamily.mesh k) (bm ω.1), rescaleCurve (θ k / CellFamily.mesh k) (η ω.1), hlf',
    MoTInput.cellularEmbeddingOfCurveAt hm hlf' hP' hside' h0' hint' hnull', hP', hside', ?_, ?_, ?_⟩
  · intro x y
    exact adj_iff_of_isEdge_eq (by rw [isEdge_rescale hc, hcm]) _ _ x y
  · intro x
    exact (hcell x).symm
  · intro x
    rfl

/-- **[18] (4.20) at mesh `θₖ`** on every outcome of the band family: `u^ε ≤ 2 u_*^ε` Lebesgue-a.e., for G3's
density of the band embedding and the geometric localized density of the curve. -/
theorem bandFamily_uDens_le (ω : BandSpace D θ hθ) (k : ℕ) :
    ∀ᵐ z ∂volume, GMS3.uDens (bandEmbedding D θ hθ ω k) z ≤ 2 * GMS4b.uStar (θ k) (η ω.1) z := by
  have hg := bandSpace_good D θ hθ ω
  have hε := hθ k
  have hcellH : ∀ x : ℤ, (bandEmbedding D θ hθ ω k).cell x = Canon.cell (θ k) (η ω.1) x := fun x => rfl
  have hc : ∀ z, z ∈ (bandEmbedding D θ hθ ω k).cell (Canon.selectedIndex (θ k) (η ω.1) z) := by
    intro z
    rw [hcellH]
    exact BundleSec4.bundle_mem_cellOf_selectedIndex hε hg.peano.surj hg.peano.transient z
  filter_upwards [GMS3.uDens_ae_eq (bandEmbedding D θ hθ ω k)
    (fun z => Canon.selectedIndex (θ k) (η ω.1) z) hc] with z hz
  rw [hz]
  have hcoefH : GMS3.uCoef (bandEmbedding D θ hθ ω k) (Canon.selectedIndex (θ k) (η ω.1) z) =
      Canon.rawCellCoef (θ k) (η ω.1) (bm ω.1) (Canon.selectedIndex (θ k) (η ω.1) z) :=
    (Canon.rawCellCoef_eq_uCoef (θ k) (η ω.1) (bm ω.1) (hg.locFin k) (bandEmbedding D θ hθ ω k)
      (Canon.selectedIndex (θ k) (η ω.1) z) (hcellH _)).symm
  rw [hcoefH]
  have hWinInt : (interior (GMS4b.locWindow (θ k) (η ω.1) (GMS4b.hitTime (η ω.1) z))).Nonempty := by
    simpa only [GMS4b.locWindow] using hg.interior _ _ (by linarith)
  have hD := GMS4F.diam_locWindow_pos_of_interior_nonempty (η ω.1).continuous hWinInt
  exact Canon.selectedCell_rawCoef_le_two_uStar hε (η ω.1) (bm ω.1) (hg.locFin k) z
    (GMS4F.matedCRT_degree_le_two_local_degrees hε hg.peano (hg.side k) (hg.locFin k) (η ω.1).continuous
      (GMS4b.hitTime (η ω.1) z) hD)

/-- **One test of [18] Proposition 2.10 on the band family** from the same test of Proposition 4.10 at the real
mesh `θₖ` (threshold `2A`, nominal tolerance `(2⁻ᵏ)^{α/2}`, rate `(Cfail + 2)(2⁻ᵏ)^{α/2}`). -/
theorem bandFamily_prop210Bad_le (hθb : IsBandSeq θ) {k : ℕ} {V : Set ℂ} {f : ℂ → ℝ} {A α Cfail : ℝ}
    (hV : MeasurableSet V) (hα : 0 < α) (hCfail : 0 ≤ Cfail)
    (hbound : P (BundleSec4.Prop410Bad η (θ k) V f A (θ k ^ α)) ≤ ENNReal.ofReal (Cfail * θ k ^ α)) :
    (bandFamily D θ hθ).P (GMS4.Prop210Bad (bandFamily D θ hθ) k V f (2 * A) (CellFamily.mesh k ^ (α / 2))) ≤
      ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α / 2)) := by
  have : IsProbabilityMeasure (bandFamily D θ hθ).P := (bandFamily D θ hθ).prob
  have hm := mesh_pos k
  have ht0 : 0 < CellFamily.mesh k ^ (α / 2) := Real.rpow_pos_of_pos hm _
  have htt : CellFamily.mesh k ^ α = CellFamily.mesh k ^ (α / 2) * CellFamily.mesh k ^ (α / 2) := by
    rw [← Real.rpow_add hm, add_halves]
  have hθα : θ k ^ α ≤ CellFamily.mesh k ^ α := rpow_le_mesh_rpow hθb k hα.le
  have hpow : CellFamily.mesh k ^ α ≤ CellFamily.mesh k ^ (α / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hm (mesh_le_one k) (by linarith)
  by_cases hsmall : 2 * CellFamily.mesh k ^ α ≤ CellFamily.mesh k ^ (α / 2)
  · have hsub : GMS4.Prop210Bad (bandFamily D θ hθ) k V f (2 * A) (CellFamily.mesh k ^ (α / 2)) ⊆
        (Subtype.val : BandSpace D θ hθ → Ω) ⁻¹' BundleSec4.Prop410Bad η (θ k) V f A (θ k ^ α) := by
      intro ω hbad
      change ω ∈ (GMS4.Prop210Good (bandFamily D θ hθ) k V f (2 * A) (CellFamily.mesh k ^ (α / 2)))ᶜ at hbad
      intro hgood410
      apply hbad
      have hgood : (∫⁻ z in V, ENNReal.ofReal (f z) * GMS4b.uStar (θ k) (η ω.1) z) ≤
          ENNReal.ofReal A * (∫⁻ z in V, ENNReal.ofReal (f z)) + ENNReal.ofReal (θ k ^ α) := hgood410
      have hb := GMS4.prop210Bound_of_localized_integral_ae (bandEmbedding D θ hθ ω k) hV f
        (fun z => GMS4b.uStar (θ k) (η ω.1) z) (ae_restrict_of_ae (bandFamily_uDens_le D θ hθ ω k)) hgood
      exact BundleSec4.bundle_prop210Bound_mono_tol _ (by linarith) hb
    calc (bandFamily D θ hθ).P (GMS4.Prop210Bad (bandFamily D θ hθ) k V f (2 * A) (CellFamily.mesh k ^ (α / 2)))
        ≤ (bandFamily D θ hθ).P ((Subtype.val : BandSpace D θ hθ → Ω) ⁻¹'
            BundleSec4.Prop410Bad η (θ k) V f A (θ k ^ α)) := measure_mono hsub
      _ ≤ P (BundleSec4.Prop410Bad η (θ k) V f A (θ k ^ α)) :=
          (bandFamily_measurePreserving D θ hθ).measure_preimage_le _
      _ ≤ ENNReal.ofReal (Cfail * θ k ^ α) := hbound
      _ ≤ ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α / 2)) := by
          apply ENNReal.ofReal_le_ofReal
          calc Cfail * θ k ^ α ≤ Cfail * CellFamily.mesh k ^ (α / 2) :=
                mul_le_mul_of_nonneg_left (hθα.trans hpow) hCfail
            _ ≤ (Cfail + 2) * CellFamily.mesh k ^ (α / 2) := by nlinarith
  · push Not at hsmall
    have hhalf : 1 / 2 < CellFamily.mesh k ^ (α / 2) := by nlinarith
    calc (bandFamily D θ hθ).P (GMS4.Prop210Bad (bandFamily D θ hθ) k V f (2 * A) (CellFamily.mesh k ^ (α / 2)))
        ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α / 2)) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)

/-- **[18] Proposition 2.10 on the band family** at `(ρ, C)` (the fixed-parameter instance consumed by the
Lemma 3.8 estimate), from Proposition 4.10 at every real mesh at `(ρ, C)`. -/
theorem bandFamily_prop210At (hθb : IsBandSeq θ) {ρ C : ℝ} (h410 : Prop410Real P η ρ C) :
    BundleSec4.Prop210At (bandFamily D θ hθ) ρ C := by
  obtain ⟨β, A, α, Cfail, hβ, hα, hA, hCfail, h⟩ := h410
  refine ⟨β, A, α / 2, Cfail + 2, hβ, by positivity, hA, by positivity, fun k V f hadm => ?_⟩
  have hadm' := prop210Admissible_mono (hθ k) (hθb k).2.1 hadm
  exact bandFamily_prop210Bad_le D θ hθ hθb hadm.2.2.2.2.2.2.1.measurableSet hα hCfail
    (h (θ k) ⟨hθ k, (hθb k).2.2⟩ V f hadm')

include D in
/-- **[18] Lemma 2.7 at every real mesh `ε ∈ (0, 1)`** for the bundle's curve `η` (segment form; landed
`GMSLemma27.lemma27_segments` for the cone realization's cell model, transported along `bundleCurve = η` a.s.). -/
theorem lemma27_real (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα : α < GMSLemma27.lemma27Exponent q γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, P {ω | ¬ SegDiamGood (η ω) ε q ρ} ≤ ENNReal.ofReal (C * ε ^ α) := by
  let Cr := MoTInput.coneRealizationOfCoupling D hstd hγ
  let hpar : CellScaling.AreaParametrization Cr := MesoModel.final_areaParametrization_of_coupling D hstd hγ
  have hSLE := MesoModel.final_segmentsContainBalls_of_coupling D hstd hγ hpar
  have hGMC := GMCFacts.gmcLowerTail_holds hγ.1 hγ.2
  have hdom := GMCFacts.areaDominates_toCellModel Cr hpar hγ.1 hγ.2
  obtain ⟨C, hC⟩ := GMSLemma27.lemma27_segments (Cr.toCellModel hpar) hSLE hGMC hdom hγ.1 hq hq' hρ0 hρ1 hα
  refine ⟨max C 0, le_max_right _ _, fun ε hε => ?_⟩
  have hsub : {ω | ¬ SegDiamGood (η ω) ε q ρ} ≤ᵐ[P]
      (GMSLemma27.segmentDiamGood (Cr.toCellModel hpar) ε q ρ)ᶜ := by
    filter_upwards [MoTInput.ae_bundleCurve_eq D] with ω hω
    intro hbad hgood
    apply hbad
    have hcurve : (Cr.toCellModel hpar).curve ω = ⇑(η ω) := by
      change ⇑(MoTInput.bundleCurve (D := D) ω) = ⇑(η ω)
      rw [hω]
    intro a b hab hne
    have h := hgood a b hab
    rw [hcurve] at h
    exact h hne
  calc P {ω | ¬ SegDiamGood (η ω) ε q ρ}
      ≤ P (GMSLemma27.segmentDiamGood (Cr.toCellModel hpar) ε q ρ)ᶜ := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (C * ε ^ α) := hC ε hε
    _ ≤ ENNReal.ofReal (max C 0 * ε ^ α) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.1.le _))

/-- The band family's cells are segments of length `θₖ`; on Lemma 2.7's segment event at `(θₖ, q, ρ'')`, those
meeting `B_{ρ''}(0)` have diameter `≤ θₖ^q ≤ (2⁻ᵏ)^q`. -/
theorem bandFamily_diam_le_of_segDiamGood (hθb : IsBandSeq θ) {k : ℕ} {q ρ'' : ℝ} (hq : 0 ≤ q)
    (ω : BandSpace D θ hθ) (hgood : SegDiamGood (η ω.1) (θ k) q ρ'') (x : ℤ)
    (hx : ((bandEmbedding D θ hθ ω k).cell x ∩ ball (0 : ℂ) ρ'').Nonempty) :
    diam ((bandEmbedding D θ hθ ω k).cell x) ≤ CellFamily.mesh k ^ q := by
  rw [bandEmbedding_cell] at hx ⊢
  have hlen : θ k * x - θ k * ((x : ℝ) - 1) ≤ θ k := by ring_nf; rfl
  exact (hgood _ _ hlen hx).trans (Real.rpow_le_rpow (hθ k).le (hθb k).2.1 hq)

/-- **`CellFamily.Lemma27CellDiamBad` on the band family** at radius `ρ`, from [18] Lemma 2.7 at real meshes at any
`ρ'' > ρ`. -/
theorem bandFamily_lemma27Bad (hθb : IsBandSeq θ) {q ρ ρ'' α C : ℝ} (hq : 0 ≤ q) (hα : 0 < α) (hC : 0 ≤ C)
    (hρ : ρ < ρ'')
    (hL : ∀ ε ∈ Ioo (0 : ℝ) 1, P {ω | ¬ SegDiamGood (η ω) ε q ρ''} ≤ ENNReal.ofReal (C * ε ^ α)) :
    CellFamily.Lemma27CellDiamBad (bandFamily D θ hθ) q ρ := by
  refine ⟨α, hα, C, fun k => ?_⟩
  have hsub : (CellFamily.DiameterGood (bandFamily D θ hθ) k q ρ)ᶜ ⊆
      (Subtype.val : BandSpace D θ hθ → Ω) ⁻¹' {ω | ¬ SegDiamGood (η ω) (θ k) q ρ''} := by
    intro ω hω hgood
    apply hω
    intro x hx
    obtain ⟨w, hw1, hw2⟩ := hx
    refine bandFamily_diam_le_of_segDiamGood D θ hθ hθb hq ω hgood x ⟨w, hw1, ?_⟩
    rw [mem_closedBall, dist_zero_right] at hw2
    rw [mem_ball, dist_zero_right]
    linarith
  calc (bandFamily D θ hθ).P (CellFamily.DiameterGood (bandFamily D θ hθ) k q ρ)ᶜ
      ≤ (bandFamily D θ hθ).P ((Subtype.val : BandSpace D θ hθ → Ω) ⁻¹'
          {ω | ¬ SegDiamGood (η ω) (θ k) q ρ''}) := measure_mono hsub
    _ ≤ P {ω | ¬ SegDiamGood (η ω) (θ k) q ρ''} := (bandFamily_measurePreserving D θ hθ).measure_preimage_le _
    _ ≤ ENNReal.ofReal (C * θ k ^ α) := hL (θ k) ⟨hθ k, (hθb k).2.2⟩
    _ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (rpow_le_mesh_rpow hθb k hα.le) hC)

/-- **G3's `CellDiamBound` on the band family** at radius `ρ`, from [18] Lemma 2.7 at real meshes at `ρ`. -/
theorem bandFamily_cellDiamBound_bad (hθb : IsBandSeq θ) {q ρ α C : ℝ} (hq : 0 ≤ q) (hα : 0 < α) (hC : 0 ≤ C)
    (hL : ∀ ε ∈ Ioo (0 : ℝ) 1, P {ω | ¬ SegDiamGood (η ω) ε q ρ} ≤ ENNReal.ofReal (C * ε ^ α)) (k : ℕ) :
    (bandFamily D θ hθ).P {ω | GMS3.CellDiamBound ((bandFamily D θ hθ).H k ω) ρ (CellFamily.mesh k ^ q)}ᶜ ≤
      ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
  have hsub : {ω | GMS3.CellDiamBound ((bandFamily D θ hθ).H k ω) ρ (CellFamily.mesh k ^ q)}ᶜ ⊆
      (Subtype.val : BandSpace D θ hθ → Ω) ⁻¹' {ω | ¬ SegDiamGood (η ω) (θ k) q ρ} := by
    intro ω hω hgood
    apply hω
    intro x hx
    exact bandFamily_diam_le_of_segDiamGood D θ hθ hθb hq ω hgood x hx
  calc (bandFamily D θ hθ).P {ω | GMS3.CellDiamBound ((bandFamily D θ hθ).H k ω) ρ (CellFamily.mesh k ^ q)}ᶜ
      ≤ (bandFamily D θ hθ).P ((Subtype.val : BandSpace D θ hθ → Ω) ⁻¹'
          {ω | ¬ SegDiamGood (η ω) (θ k) q ρ}) := measure_mono hsub
    _ ≤ P {ω | ¬ SegDiamGood (η ω) (θ k) q ρ} := (bandFamily_measurePreserving D θ hθ).measure_preimage_le _
    _ ≤ ENNReal.ofReal (C * θ k ^ α) := hL (θ k) ⟨hθ k, (hθb k).2.2⟩
    _ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (rpow_le_mesh_rpow hθb k hα.le) hC)

end Coupling

end MatedCRTHarmonic.GMSMain.EpsB
