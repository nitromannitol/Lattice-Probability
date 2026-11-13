/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.HypothesisTransferGMS at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.HypothesisTransfer
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid
import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedMeasurable
import Mathlib.Util.AssertNoSorry

/-!
# The hypothesis transfer at GMS's coding

`HypothesisTransfer` takes the properties of the coding `codeMap` as explicit hypotheses.  This file
discharges those already proved:

* `hmeas` — `measurable_codeMap` (`CodeMeasurable`);
* `hgood` — `measurableSet_lineConnected` (`LineConnectedMeasurable`);
* `hinv` — `lineConnected_iff_of_isSimilar` (`LineConnectedPoint`);
* `hvalid` — `validGeneral_codeMap`, from `CellConfig.validGeneral_code` (`CodingValid`);
* `hsim` — `isSimilarity_codes`, from `CellConfig.generalLaws_isSimilarity`;
* `hdensPi`, `hdensPiStar` — `rootedRowEnergyDensity_id_code_le` and
  `rootedRowEnergyDensity_inv_code_le`: when the rooted half of the (FE) integrand of the code is
  nonzero, `0` is off every cell frontier, so any cell `K ∋ 0` has `0` in its interior and is the
  root cell (`CellConfig.eq_of_mem_interior`); there the half is GMS's integrand at `K`
  (`CellConfig.ofReal_pi_cellEquiv`, `CellConfig.ofReal_piStar_cellEquiv`).

The `…_gms` theorems therefore carry **no** upstream hypothesis.  The only remaining input anywhere
is the measurable core `C` of `supportedOnValidGeneral_map_gms` (see `HypothesisTransfer` for why it
is needed).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GMS

open Code GeneralLaws

/-- A root read off `rootAt` is off the boundary mask and interior to its cell; no geometric
hypothesis is needed. -/
theorem rootAt_eq_some_imp {V : Type*} (F : IndexedCells V) {z : Plane} {v : V}
    (h : RootDensities.rootAt F z = some v) :
    z ∉ RootDensities.boundaryMask F ∧ z ∈ interior (F.cell v : Set Plane) := by
  classical
  unfold RootDensities.rootAt at h
  by_cases hz : z ∈ RootDensities.boundaryMask F
  · rw [dif_pos hz] at h
    cases h
  · rw [dif_neg hz] at h
    by_cases hex : ∃! w, RootDensities.IsInteriorRoot F z w
    · rw [dif_pos hex] at h
      have hspec := hex.exists.choose_spec
      rw [Option.some_inj.mp h] at hspec
      exact ⟨hz, hspec⟩
    · rw [dif_neg hex] at h
      cases h

/-- **The code of a line-connected configuration is a general environment.** -/
theorem validGeneral_codeMap : ∀ H : GMSSpace, H.1.LineConnected → ValidGeneral H.1.code :=
  fun H hL => CellConfig.validGeneral_code H.2 hL

/-- **GMS similarity of configurations is general similarity of their codes.** -/
theorem isSimilarity_codes : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace)
    (hL : H.1.LineConnected) (hL' : H'.1.LineConnected), IsSimilar s u hs H H' →
      GeneralLaws.IsSimilarity s u hs ⟨H.1.code, validGeneral_codeMap H hL⟩
        ⟨H'.1.code, validGeneral_codeMap H' hL'⟩ :=
  fun s u hs H _ _ _ hHH' =>
    CellConfig.generalLaws_isSimilarity s u hs H.2 rfl (congrArg CellConfig.code hHH')

/-- Line connectivity is invariant under `H ↦ C(H − z)`, in the shape `HypothesisTransfer` takes. -/
theorem lineConnected_iff_isSimilar : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace),
    IsSimilar s u hs H H' → (H.1.LineConnected ↔ H'.1.LineConnected) :=
  fun _ _ _ _ _ h => lineConnected_iff_of_isSimilar h

/-- The area of a cell of a configuration is positive. -/
theorem area_pos_of_mem {H : GMSSpace} {K : Cell} (hK : K ∈ H.1.cells) :
    0 < CellConfig.area K :=
  ENNReal.toReal_pos
    ((isOpen_interior.measure_pos volume (H.2.interior_nonempty K hK)).trans_le
      (measure_mono interior_subset)).ne'
    K.isCompact.measure_lt_top.ne

/-- A half of the rooted (FE) integrand of the code is bounded by GMS's integrand at any cell
containing `0`, given the identification `hq` of the conductance row with GMS's quantity `q`. -/
theorem rootedRowEnergyDensity_code_le {φ : ℝ → ℝ} {q : Cell → ℝ} (H : GMSSpace)
    (hq : ∀ v : Vertex H.1.code, ENNReal.ofReal (q (cell H.1.code v)) =
      ∑' w, ENNReal.ofReal (φ ((rawConfig H.1.code (CellConfig.rawAdmissible_code H.2)).c v w)))
    (hL : H.1.LineConnected) (K : Cell) (hK : K ∈ H.1.cells) (h0 : (0 : Plane) ∈ (K : Set Plane)) :
    rootedRowEnergyDensity φ (config ⟨H.1.code, validGeneral_codeMap H hL⟩) 0 ≤
      ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K * q K) := by
  unfold rootedRowEnergyDensity
  cases hr : RootDensities.rootAt (config ⟨H.1.code, validGeneral_codeMap H hL⟩).cellsOnly 0 with
  | none => exact zero_le
  | some v =>
    obtain ⟨hmask, hint⟩ := rootAt_eq_some_imp _ hr
    -- the vertex of `K`
    let w : Vertex H.1.code := (CellConfig.cellEquiv H.2).symm ⟨K, hK⟩
    have hw : cell H.1.code w = K := CellConfig.cell_cellEquiv_symm H.2 ⟨K, hK⟩
    have hKint : (0 : Plane) ∈ interior (K : Set Plane) := by
      have hfr : (0 : Plane) ∉ frontier (K : Set Plane) := by
        intro hf
        apply hmask
        refine Or.inl (mem_iUnion.mpr ⟨w, ?_⟩)
        show (0 : Plane) ∈ frontier (cell H.1.code w : Set Plane)
        rw [hw]
        exact hf
      rw [frontier, K.isCompact.isClosed.closure_eq] at hfr
      exact Classical.byContradiction fun hn => hfr ⟨h0, hn⟩
    have hKv : cell H.1.code v = K :=
      CellConfig.eq_of_mem_interior H.2 (CellConfig.cell_mem_cells H.2 v) hK hint hKint
    subst hKv
    have hA := area_pos_of_mem hK
    rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) hA.le), ENNReal.ofReal_div_of_pos hA, hq v]
    exact le_rfl

/-- **`hdensPi` at GMS's coding.** -/
theorem rootedRowEnergyDensity_id_code_le (H : GMSSpace) (hL : H.1.LineConnected) (K : Cell)
    (hK : K ∈ H.1.cells) (h0 : (0 : Plane) ∈ (K : Set Plane)) :
    rootedRowEnergyDensity id (config ⟨H.1.code, validGeneral_codeMap H hL⟩) 0 ≤
      ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K * H.1.pi K) :=
  rootedRowEnergyDensity_code_le H (fun v => CellConfig.ofReal_pi_cellEquiv H.2 v) hL K hK h0

/-- **`hdensPiStar` at GMS's coding.** -/
theorem rootedRowEnergyDensity_inv_code_le (H : GMSSpace) (hL : H.1.LineConnected) (K : Cell)
    (hK : K ∈ H.1.cells) (h0 : (0 : Plane) ∈ (K : Set Plane)) :
    rootedRowEnergyDensity (fun x : ℝ => x⁻¹) (config ⟨H.1.code, validGeneral_codeMap H hL⟩) 0 ≤
      ENNReal.ofReal (Metric.diam (K : Set Plane) ^ 2 / CellConfig.area K * H.1.piStar K) :=
  rootedRowEnergyDensity_code_le H (fun v => CellConfig.ofReal_piStar_cellEquiv H.2 v) hL K hK h0

/-! ### The transfer theorems at GMS's coding -/

section Instances

variable {μ : Measure GMSSpace} [IsProbabilityMeasure μ]

/-- `SupportedOnValidGeneral (μ.map codeMap)` from a measurable core. -/
theorem supportedOnValidGeneral_map_gms (hL : ConnectedAlongLines μ) {C : Set RawCode}
    (hC : MeasurableSet C) (hCval : ∀ r ∈ C, ValidGeneral r)
    (hCgood : ∀ H : GMSSpace, H.1.LineConnected → codeMap H ∈ C) :
    SupportedOnValidGeneral (μ.map codeMap) :=
  supportedOnValidGeneral_map measurable_codeMap hL hC hCval hCgood

/-- `SupportedOnValidGeneral (μ.map codeMap)` from Borel measurability of the set of GMS codes
(`Code.ValidGMS`, the codes satisfying Definition 1.15 with GMS's segment condition), which contains
the code of every line-connected configuration (`CellConfig.validGMS_code`). -/
theorem supportedOnValidGeneral_map_of_measurableSet_validGMS (hL : ConnectedAlongLines μ)
    (hGMS : MeasurableSet {r : RawCode | ValidGMS r}) :
    SupportedOnValidGeneral (μ.map codeMap) :=
  supportedOnValidGeneral_map_gms hL hGMS (fun _ hr => validGeneral_of_validGMS hr)
    (fun H hH => CellConfig.validGMS_code H.2 hH)

/-- **Mass transport** of `generalLaw (μ.map codeMap) hP` from GMS's mass transport. -/
theorem massTransport_generalLaw_gms
    (hL : ConnectedAlongLines μ) (hP : SupportedOnValidGeneral (μ.map codeMap))
    (hMT : MassTransport μ) :
    GeneralLaws.MassTransport (generalLaw (μ.map codeMap) hP) :=
  massTransport_generalLaw validGeneral_codeMap measurable_codeMap measurableSet_lineConnected
    lineConnected_iff_isSimilar isSimilarity_codes hL hP hMT

/-- **(FE)** for `generalLaw (μ.map codeMap) hP` from GMS's finite-expectation hypothesis. -/
theorem finiteEnergyMoment_generalLaw_gms
    (hL : ConnectedAlongLines μ) (hP : SupportedOnValidGeneral (μ.map codeMap))
    (hFE : FiniteExpectation μ) :
    GeneralLaws.FiniteEnergyMoment (generalLaw (μ.map codeMap) hP) :=
  finiteEnergyMoment_generalLaw validGeneral_codeMap measurable_codeMap measurableSet_lineConnected
    rootedRowEnergyDensity_id_code_le rootedRowEnergyDensity_inv_code_le hL hP hFE

/-- **Ergodicity modulo scaling** of `generalLaw (μ.map codeMap) hP` from GMS's ergodicity. -/
theorem environmentErgodic_generalLaw_gms
    (hL : ConnectedAlongLines μ) (hP : SupportedOnValidGeneral (μ.map codeMap))
    (hErg : ErgodicModuloScaling μ) :
    GeneralLaws.EnvironmentErgodic (generalLaw (μ.map codeMap) hP) :=
  environmentErgodic_generalLaw validGeneral_codeMap measurable_codeMap measurableSet_lineConnected
    lineConnected_iff_isSimilar isSimilarity_codes hL hP hErg

/-- **Pull-back** of `validLaw`-almost-sure statements to `μ`. -/
theorem ae_of_ae_validLaw_gms (hV : EnvironmentLaws.SupportedOnValid (μ.map codeMap))
    {p : Env → Prop} (h : ∀ᵐ e ∂EnvironmentLaws.validLaw (μ.map codeMap) hV, p e) :
    ∀ᵐ H ∂μ, ∃ hv : Valid H.1.code, p ⟨H.1.code, hv⟩ :=
  ae_of_ae_validLaw measurable_codeMap hV h

end Instances

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.rootAt_eq_some_imp
assert_no_sorry ReflectedGMS.GMS.validGeneral_codeMap
assert_no_sorry ReflectedGMS.GMS.isSimilarity_codes
assert_no_sorry ReflectedGMS.GMS.rootedRowEnergyDensity_id_code_le
assert_no_sorry ReflectedGMS.GMS.rootedRowEnergyDensity_inv_code_le
assert_no_sorry ReflectedGMS.GMS.supportedOnValidGeneral_map_gms
assert_no_sorry ReflectedGMS.GMS.supportedOnValidGeneral_map_of_measurableSet_validGMS
assert_no_sorry ReflectedGMS.GMS.massTransport_generalLaw_gms
assert_no_sorry ReflectedGMS.GMS.finiteEnergyMoment_generalLaw_gms
assert_no_sorry ReflectedGMS.GMS.environmentErgodic_generalLaw_gms
assert_no_sorry ReflectedGMS.GMS.ae_of_ae_validLaw_gms

#print axioms ReflectedGMS.GMS.rootedRowEnergyDensity_id_code_le
#print axioms ReflectedGMS.GMS.rootedRowEnergyDensity_inv_code_le
#print axioms ReflectedGMS.GMS.supportedOnValidGeneral_map_gms
#print axioms ReflectedGMS.GMS.supportedOnValidGeneral_map_of_measurableSet_validGMS
#print axioms ReflectedGMS.GMS.massTransport_generalLaw_gms
#print axioms ReflectedGMS.GMS.finiteEnergyMoment_generalLaw_gms
#print axioms ReflectedGMS.GMS.environmentErgodic_generalLaw_gms
#print axioms ReflectedGMS.GMS.ae_of_ae_validLaw_gms
