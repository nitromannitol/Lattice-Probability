/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.Density at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Density
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.L27Bridge
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FinalAssembly
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Prop210Source
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.CellScalingCellModelCoupling

/-!
# the concrete density comparison (4.20) on MTC's mated-CRT family

Adapter : G4FS's record field `L27GMSALocalizedProp210Producer.density_comparison_ae` (the spatially
a.e. form of [18] (4.20)) for the bundle model, from CANON's selected-cell
coefficient bound `Canon.ae_cone_selectedCell_rawCoef_le_two_uStar` (itself from G4FS's (4.7)
`GMS4F.ae_matedCRT_degree_le_two_local_degrees` and (4.5) `GMS4b.segRatio_le_locDA`), CANON's identification of the
Brownian coefficient with G3's `uCoef` (`Canon.rawCellCoef_eq_uCoef`), G3's a.e. selection identity
`GMS3.uDens_ae_eq`, and the first-hit identity `GMS4b.hitTime_spec` on the bundle's Peanosphere event:

* `ae_uDens_le_two_uStar`: a.s., for every dyadic mesh `2^{-k}`, for Lebesgue-a.e. `z`,
  `u^ε(z) ≤ 2 u_*^ε(z)` where `u^ε` is G3's density of MTC's cellular embedding (`F.H k ω`) and
  `u_*^ε = GMS4b.uStar (2^{-k}) (η ω) z` is the geometric localized density of the γ-cone curve `η`;
* `ae_uDens_le_two_uStar_bundleCurve`: the same with the curve of MTC's cell model (`bundleCurve`), in the exact
  shape of G4FS's record field (`density_comparison_ae`) for `S = C.toCellModelGraphCoupling hpar`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The selected cell `x = ⌈τ_z/ε⌉` of a surjective, proper curve contains `z`. -/
theorem bundle_mem_cellOf_selectedIndex {ε : ℝ} (hε : 0 < ε) {c : C(ℝ, ℂ)}
    (hsurj : Function.Surjective c)
    (htrans : Filter.Tendsto c (Filter.cocompact ℝ) (Filter.cocompact ℂ)) (z : ℂ) :
    z ∈ c '' Icc (ε * ((Canon.selectedIndex ε c z : ℝ) - 1)) (ε * (Canon.selectedIndex ε c z : ℝ)) := by
  have ht := Canon.firstHit_mem_selectedCellTime hε c z
  refine ⟨GMS4b.hitTime c z, ⟨ht.1.le, ht.2⟩, ?_⟩
  exact GMS4b.hitTime_spec c.continuous htrans (hsurj z)

/-- The concrete (4.20) on MTC's chosen cellular embedding `bundleGeometry`, at one good sample. -/
theorem bundle_uDens_bundleGeometry_le_two_uStar
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (ω : Ω) (k : ℕ)
    (hB : MoTInput.bundleBM (D := D) ω = bm ω) (hC : MoTInput.bundleCurve (D := D) ω = η ω)
    (hP : RouteM.Peanosphere (bm ω) (η ω))
    (hcoef : ∀ (k : ℕ) (z : ℂ), Canon.rawCellCoef (CellFamily.mesh k) (η ω) (bm ω)
      (Canon.selectedIndex (CellFamily.mesh k) (η ω) z) ≤ 2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z) :
    ∀ᵐ z ∂volume, GMS3.uDens (MoTInput.bundleGeometry (D := D) ω k).2 z ≤
      2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z := by
  have hε : 0 < CellFamily.mesh k := bundle_mesh_pos k
  -- the cells of the embedding are the mesh cells of `η ω`
  have hcellH : ∀ x : ℤ, (MoTInput.bundleGeometry (D := D) ω k).2.cell x =
      Canon.cell (CellFamily.mesh k) (η ω) x := by
    intro x
    have h := congrFun (MoTInput.bundleGeometry_cell D ω k) x
    rw [h, hC]
    rfl
  -- the selection `z ↦ ⌈τ_z/ε⌉`
  have hc : ∀ z, z ∈ (MoTInput.bundleGeometry (D := D) ω k).2.cell
      (Canon.selectedIndex (CellFamily.mesh k) (η ω) z) := by
    intro z
    rw [hcellH]
    exact bundle_mem_cellOf_selectedIndex hε hP.surj hP.transient z
  filter_upwards [GMS3.uDens_ae_eq (MoTInput.bundleGeometry (D := D) ω k).2
    (fun z => Canon.selectedIndex (CellFamily.mesh k) (η ω) z) hc] with z hz
  rw [hz]
  have hcoefH : GMS3.uCoef (MoTInput.bundleGeometry (D := D) ω k).2
      (Canon.selectedIndex (CellFamily.mesh k) (η ω) z) =
      Canon.rawCellCoef (CellFamily.mesh k) (η ω) (MoTInput.bundleBM (D := D) ω)
        (Canon.selectedIndex (CellFamily.mesh k) (η ω) z) :=
    (Canon.rawCellCoef_eq_uCoef (CellFamily.mesh k) (η ω) (MoTInput.bundleBM (D := D) ω)
      (MoTInput.bundleGeometry (D := D) ω k).1 (MoTInput.bundleGeometry (D := D) ω k).2
      (Canon.selectedIndex (CellFamily.mesh k) (η ω) z) (hcellH _)).symm
  rw [hcoefH, hB]
  exact hcoef k z

/-- **The concrete (4.20)**: a.s., at every dyadic mesh, `u^ε ≤ 2 u_*^ε` Lebesgue-a.e., for G3's density of MTC's
cellular embedding and the geometric localized density of the bundle's γ-cone curve `η`. -/
theorem ae_uDens_le_two_uStar
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᵐ z ∂volume,
      GMS3.uDens ((MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.H k ω) z ≤
        2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z := by
  filter_upwards [MoTInput.ae_bundleBM_eq D, MoTInput.ae_bundleCurve_eq D, MoTInput.ae_peanosphere D,
    Canon.ae_cone_selectedCell_rawCoef_le_two_uStar D] with ω hB hC hP hcoef k
  exact bundle_uDens_bundleGeometry_le_two_uStar D ω k hB hC hP hcoef

end Coupling

end MatedCRTHarmonic.BundleSec4
