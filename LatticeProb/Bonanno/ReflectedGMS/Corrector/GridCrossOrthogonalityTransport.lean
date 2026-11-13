/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GridCrossOrthogonalityTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedMassTransportProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.TransportAeGating
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CopyDifferenceDensitySimilarity

/-!
# Mass transport and redistribution on the coupled two-grid space

`s:prop:gridindependence` runs the manuscript's signed redistribution (`s:lem:redistribution`)
on the joint law of the environment and **two** independent grids: the variation
`φ_m² − b` lives on the blocks of the second grid, while the field `Φ¹` it is paired with is
the limiting potential of the first grid.  Every checked transport statement of the
`s:prop:projection` lane (`Corrector/MarkedMassTransportProducer`,
`Corrector/TransportAeGating`) is on the one-grid space `Env × Grid`.  This module carries the
two of them that the cross orthogonality needs over to the coupled space
`GridIndependenceCoupling.CoupledSpace = Env × Grid × Grid` with law
`ν ⊗ (gridMeasure ⊗ gridMeasure)`.

## The re-rooting datum

`coupledReRooting` is the marked re-rooting whose environment is `p.1`, whose **block grid** is
the first copy `p.2.1`, and whose shift translates the environment and both grids.  Its unit-scale
joint similarity is `CopyDifferenceDensitySimilarity.coupledSimilarity 1 w`.  The second grid
`p.2.2` is a passive mark: it is carried along by the similarity but never selects a block.

## The transport identity: average over the passive grid

The manuscript's device at tex:286 — *average the transport over the marks before applying
`s:eq:MTP`* — is applied once more, to the passive grid only.  `passiveAveraged T` is the one-grid
kernel `(e, D₁) ↦ ∫ T(e, D₁, D₂) dD₂`; it is `MarkedSimilarityCovariant` as soon as `T` is
`CoupledSimilarityCovariant`, because the grid law is invariant under the joint similarity
(`measurePreserving_gridSimilarity`), and the checked one-grid
`markedMassTransport_of_massTransport` then gives the identity.  Tonelli on the reassociated law
`(ν ⊗ gridMeasure) ⊗ gridMeasure` (`Measure.prodAssoc_prod`) turns it back into a statement on
the coupled law.  No new invariance of any law is used.

## The redistribution identity

`endpointSpreadTransport_coupledSimilarityCovariant` is tex:497 ("this has scaling degree `−2`")
for an owned edge field over `coupledReRooting`, and
`lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_coupled_ae` is `s:eq:redistribute`
on the coupled law with an almost-sure selected origin block, from `EnvironmentLaws.MassTransport ν`
alone.  The proofs are those of `MarkedMassTransportProducer` with `markedSimilarity` replaced by
`coupledSimilarity`; nothing else changes because the block grid of `coupledReRooting` transforms
by exactly the grid action of `markedSimilarity`.

**This file proves no main theorem**: it supplies the transport half of the cross orthogonality;
the ownership, the block orthogonality and the passage to the limit are separate modules.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GridCrossOrthogonalityTransport

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open EnvironmentLaws DyadicGridLaw DyadicGridTranslation UniformGridDilationInvariance
open ActualMarkedBlockTransport MarkedMassTransportProducer
open GridIndependenceCoupling CopyDifferenceDensitySimilarity

/-! ### The coupled re-rooting -/

/-- **The coupled marked re-rooting.**  Environment `p.1`, block grid the first copy `p.2.1`,
and the shift translates the environment and both grid copies.  The second copy `p.2.2` is a
passive mark. -/
noncomputable def coupledReRooting : MarkedReRooting CoupledSpace where
  env p := p.1
  grid p := p.2.1
  shift w p := (translateEnv w p.1, translate w p.2.1, translate w p.2.2)
  measurable_shift := by
    have h1 : Measurable fun q : CoupledSpace × Plane => translateEnv q.2 q.1.1 := by
      simpa only [Function.comp_def] using
        measurable_translateEnv.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun q : CoupledSpace × Plane => translate q.2 q.1.2.1 := by
      simpa only [Function.comp_def] using
        measurable_translate.comp
          ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    have h3 : Measurable fun q : CoupledSpace × Plane => translate q.2 q.1.2.2 := by
      simpa only [Function.comp_def] using
        measurable_translate.comp
          ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    exact h1.prodMk (h2.prodMk h3)
  shift_zero p := by
    show (translateEnv 0 p.1, translate 0 p.2.1, translate 0 p.2.2) = p
    rw [translateEnv_zero, translate_zero, translate_zero]
  shift_shift w z p := by
    show (translateEnv z (translateEnv w p.1), translate z (translate w p.2.1),
        translate z (translate w p.2.2))
      = (translateEnv (w + z) p.1, translate (w + z) p.2.1, translate (w + z) p.2.2)
    rw [translateEnv_translateEnv, translate_translate, translate_translate]

@[simp] theorem coupledReRooting_env (p : CoupledSpace) : coupledReRooting.env p = p.1 := rfl

@[simp] theorem coupledReRooting_grid (p : CoupledSpace) : coupledReRooting.grid p = p.2.1 :=
  rfl

@[simp] theorem coupledReRooting_shift (w : Plane) (p : CoupledSpace) :
    coupledReRooting.shift w p = (translateEnv w p.1, translate w p.2.1, translate w p.2.2) :=
  rfl

theorem measurable_coupledEnv : Measurable coupledReRooting.env := measurable_fst

theorem measurable_coupledGrid : Measurable coupledReRooting.grid :=
  measurable_fst.comp measurable_snd

/-! ### `s:eq:Tcov` on the coupled space -/

/-- **`s:eq:Tcov` for a coupled transport**: degree `−2` homogeneity under every joint similarity
of the environment and both grid copies. -/
def CoupledSimilarityCovariant (T : CoupledSpace → Plane → Plane → ℝ≥0∞) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (p : CoupledSpace) (w z : Plane),
    T (coupledSimilarity s u hs p) (positiveSimilarity s u w) (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * T p w z

/-! ### Averaging over the passive grid -/

/-- The transport averaged over the passive second grid: a one-grid marked transport. -/
noncomputable def passiveAveraged (T : CoupledSpace → Plane → Plane → ℝ≥0∞)
    (q : Env × Grid) (w z : Plane) : ℝ≥0∞ :=
  ∫⁻ D : Grid, T (q.1, q.2, D) w z ∂gridMeasure

theorem measurable_passiveAveraged (T : CoupledSpace → Plane → Plane → ℝ≥0∞)
    (hT : Measurable fun x : CoupledSpace × Plane × Plane => T x.1 x.2.1 x.2.2) :
    Measurable fun x : (Env × Grid) × Plane × Plane =>
      passiveAveraged T x.1 x.2.1 x.2.2 := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hmap : Measurable fun y : ((Env × Grid) × Plane × Plane) × Grid =>
      (((y.1.1.1, y.1.1.2, y.2), y.1.2.1, y.1.2.2) : CoupledSpace × Plane × Plane) :=
    ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have h : Measurable fun y : ((Env × Grid) × Plane × Plane) × Grid =>
      T (y.1.1.1, y.1.1.2, y.2) y.1.2.1 y.1.2.2 := hT.comp hmap
  exact h.lintegral_prod_right'

/-- **The passive average of a coupled-covariant transport is marked-covariant**: the joint
similarity moves the passive grid by the grid action, and the grid law is invariant under it. -/
theorem passiveAveraged_covariant (T : CoupledSpace → Plane → Plane → ℝ≥0∞)
    (hT : Measurable fun x : CoupledSpace × Plane × Plane => T x.1 x.2.1 x.2.2)
    (hcov : CoupledSimilarityCovariant T) :
    MarkedSimilarityCovariant (passiveAveraged T) := by
  intro s u hs q w z
  have hmap' : Measurable fun D : Grid =>
      (((q.1, q.2, D), (w, z)) : CoupledSpace × Plane × Plane) :=
    (measurable_const.prodMk (measurable_const.prodMk measurable_id)).prodMk measurable_const
  have hmeas' : Measurable fun D : Grid => T (q.1, q.2, D) w z := hT.comp hmap'
  have hmap : Measurable fun D : Grid =>
      (((similarityTargetEnv s u hs q.1, dilate s hs (translate u q.2), D),
        (positiveSimilarity s u w, positiveSimilarity s u z)) : CoupledSpace × Plane × Plane) :=
    (measurable_const.prodMk (measurable_const.prodMk measurable_id)).prodMk measurable_const
  have hmeas : Measurable fun D : Grid =>
      T (similarityTargetEnv s u hs q.1, dilate s hs (translate u q.2), D)
        (positiveSimilarity s u w) (positiveSimilarity s u z) := hT.comp hmap
  have hswap : (∫⁻ D, T (similarityTargetEnv s u hs q.1, dilate s hs (translate u q.2), D)
        (positiveSimilarity s u w) (positiveSimilarity s u z) ∂gridMeasure)
      = ∫⁻ D, T (similarityTargetEnv s u hs q.1, dilate s hs (translate u q.2),
          dilate s hs (translate u D)) (positiveSimilarity s u w) (positiveSimilarity s u z)
            ∂gridMeasure :=
    ((measurePreserving_gridSimilarity s u hs).lintegral_comp hmeas).symm
  have hpt : ∀ D : Grid,
      T (similarityTargetEnv s u hs q.1, dilate s hs (translate u q.2),
          dilate s hs (translate u D)) (positiveSimilarity s u w) (positiveSimilarity s u z)
        = ENNReal.ofReal ((s ^ 2)⁻¹) * T (q.1, q.2, D) w z :=
    fun D => hcov s u hs (q.1, q.2, D) w z
  show (∫⁻ D, T (similarityTargetEnv s u hs q.1, dilate s hs (translate u q.2), D)
      (positiveSimilarity s u w) (positiveSimilarity s u z) ∂gridMeasure)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * ∫⁻ D, T (q.1, q.2, D) w z ∂gridMeasure
  rw [hswap]
  simp_rw [hpt]
  exact lintegral_const_mul _ hmeas'

/-! ### The coupled transport identity -/

/-- Tonelli on the reassociated coupled law: a coupled `lintegral` is the one-grid `lintegral` of
the passive average, with the plane integral innermost. -/
theorem lintegral_coupled_eq_lintegral_passive (ν : Measure Env) [SFinite ν]
    (S : CoupledSpace → Plane → ℝ≥0∞) (hS : Measurable fun x : CoupledSpace × Plane => S x.1 x.2) :
    (∫⁻ p, ∫⁻ z : Plane, S p z ∂volume ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ q, ∫⁻ z : Plane, ∫⁻ D : Grid, S (q.1, q.2, D) z ∂gridMeasure ∂volume
          ∂(ν.prod gridMeasure) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hassoc : ν.prod (gridMeasure.prod gridMeasure)
      = Measure.map MeasurableEquiv.prodAssoc ((ν.prod gridMeasure).prod gridMeasure) :=
    Measure.prodAssoc_prod.symm
  have hinner : Measurable fun p : CoupledSpace => ∫⁻ z : Plane, S p z ∂volume :=
    hS.lintegral_prod_right'
  rw [hassoc, lintegral_map_equiv]
  have hmeas2 : Measurable fun y : (Env × Grid) × Grid =>
      ∫⁻ z : Plane, S (MeasurableEquiv.prodAssoc y) z ∂volume :=
    hinner.comp MeasurableEquiv.prodAssoc.measurable
  rw [lintegral_prod _ hmeas2.aemeasurable]
  refine lintegral_congr fun q => ?_
  have hf : Measurable (Function.uncurry fun (D : Grid) (z : Plane) => S (q.1, q.2, D) z) :=
    hS.comp ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
      measurable_snd)
  exact lintegral_lintegral_swap (μ := gridMeasure) (ν := (volume : Measure Plane))
    hf.aemeasurable

/-- **Mass transport on the coupled space from `s:eq:MTP` alone.**  Every jointly measurable
nonnegative coupled transport of degree `−2` under the joint similarity satisfies the
mass-transport identity on `ν ⊗ (gridMeasure ⊗ gridMeasure)`.  The passive grid is averaged out
first; nothing about the environment law beyond `EnvironmentLaws.MassTransport ν` is used. -/
theorem coupledMassTransport_of_massTransport (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (T : CoupledSpace → Plane → Plane → ℝ≥0∞)
    (hT : Measurable fun x : CoupledSpace × Plane × Plane => T x.1 x.2.1 x.2.2)
    (hcov : CoupledSimilarityCovariant T) :
    (∫⁻ p, ∫⁻ z : Plane, T p 0 z ∂volume ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ p, ∫⁻ z : Plane, T p z 0 ∂volume ∂(ν.prod (gridMeasure.prod gridMeasure)) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hT' := measurable_passiveAveraged T hT
  have h := markedMassTransport_of_massTransport ν hν (passiveAveraged T) hT'
    (passiveAveraged_covariant T hT hcov)
  have hL := lintegral_coupled_eq_lintegral_passive ν (fun p z => T p 0 z)
    (hT.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  have hR := lintegral_coupled_eq_lintegral_passive ν (fun p z => T p z 0)
    (hT.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
  calc (∫⁻ p, ∫⁻ z : Plane, T p 0 z ∂volume ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ q, ∫⁻ z : Plane, ∫⁻ D : Grid, T (q.1, q.2, D) 0 z ∂gridMeasure ∂volume
          ∂(ν.prod gridMeasure) := hL
    _ = ∫⁻ q, ∫⁻ z : Plane, ∫⁻ D : Grid, T (q.1, q.2, D) z 0 ∂gridMeasure ∂volume
          ∂(ν.prod gridMeasure) := h
    _ = ∫⁻ p, ∫⁻ z : Plane, T p z 0 ∂volume ∂(ν.prod (gridMeasure.prod gridMeasure)) :=
        hR.symm

/-! ### Degree `−2` homogeneity of the redistribution kernel on the coupled space -/

/-- **`s:eq:Tcov` at the level of an owned edge field over the coupled re-rooting**: the
similarity relabels the raw labels by a bijection `σ`, carries every cell and every owner block
along, multiplies the coefficient by `s²` and the owner-block area by `s²`.  This is
`MarkedMassTransportProducer.SimilarityCovariantField` with `markedSimilarity` replaced by
`coupledSimilarity`. -/
def CoupledCovariantField {m : ℝ} (Q : OwnedEdgeField coupledReRooting m) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (p : CoupledSpace), ∃ σ : ℕ ≃ ℕ,
    (∀ n : ℕ, positiveSimilarity s u ⁻¹'
        labelCell (similarityTargetEnv s u hs p.1) (σ n) = labelCell p.1 n) ∧
      (∀ q : ℕ × ℕ, Q.weight (coupledSimilarity s u hs p) (σ q.1, σ q.2)
        = ENNReal.ofReal (s ^ 2) * Q.weight p q) ∧
      (∀ q : ℕ × ℕ, positiveSimilarity s u ⁻¹'
        Q.ownerSet (coupledSimilarity s u hs p) (σ q.1, σ q.2) = Q.ownerSet p q) ∧
      (∀ q : ℕ × ℕ, Q.ownerArea (coupledSimilarity s u hs p) (σ q.1, σ q.2)
        = ENNReal.ofReal (s ^ 2) * Q.ownerArea p q)

/-- **"This has scaling degree `−2`"** (tex:497) on the coupled space.  The proof is that of
`MarkedMassTransportProducer.endpointSpreadTransport_markedSimilarityCovariant`, verbatim, with the
environment of the transformed configuration being `similarityTargetEnv s u hs p.1` in both
cases. -/
theorem endpointSpreadTransport_coupledSimilarityCovariant {m : ℝ}
    (Q : OwnedEdgeField coupledReRooting m) (hcov : CoupledCovariantField Q) :
    CoupledSimilarityCovariant Q.endpointSpreadTransport := by
  intro s u hs p w z
  obtain ⟨σ, hcell, hwt, hset, harea⟩ := hcov s u hs p
  have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
  have hc0 : ENNReal.ofReal (s ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hs2).ne'
  have hctop : ENNReal.ofReal (s ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hcinv : ENNReal.ofReal ((s ^ 2)⁻¹) = (ENNReal.ofReal (s ^ 2))⁻¹ :=
    ENNReal.ofReal_inv_of_pos hs2
  have hcc : ENNReal.ofReal (s ^ 2) * ENNReal.ofReal ((s ^ 2)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hs2.le, mul_inv_cancel₀ hs2.ne', ENNReal.ofReal_one]
  have hreindex := Equiv.tsum_eq (Equiv.prodCongr σ σ)
    (fun q : ℕ × ℕ => Q.weight (coupledSimilarity s u hs p) q / 2 *
      spread (similarityTargetEnv s u hs p.1) q.1 (positiveSimilarity s u w) *
      Q.ownerSpread (coupledSimilarity s u hs p) q (positiveSimilarity s u z))
  have hterm : ∀ q : ℕ × ℕ,
      Q.weight (coupledSimilarity s u hs p) (σ q.1, σ q.2) / 2 *
        spread (similarityTargetEnv s u hs p.1) (σ q.1) (positiveSimilarity s u w) *
        Q.ownerSpread (coupledSimilarity s u hs p) (σ q.1, σ q.2) (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) *
        (Q.weight p q / 2 * spread p.1 q.1 w * Q.ownerSpread p q z) := by
    intro q
    have hvol : volume (labelCell (similarityTargetEnv s u hs p.1) (σ q.1))
        = ENNReal.ofReal (s ^ 2) * volume (labelCell p.1 q.1) := by
      have himg : positiveSimilarity s u '' labelCell p.1 q.1
          = labelCell (similarityTargetEnv s u hs p.1) (σ q.1) := by
        rw [← hcell q.1, Set.image_preimage_eq _ (surjective_positiveSimilarity u hs)]
      rw [← himg, Spatial.volume_image_positiveSimilarity]
    have hsp : spread (similarityTargetEnv s u hs p.1) (σ q.1) (positiveSimilarity s u w)
        = ENNReal.ofReal ((s ^ 2)⁻¹) * spread p.1 q.1 w := by
      unfold spread
      rw [indicator_preimage_comp, preimage_positiveSimilarity_interior u hs, hcell q.1, hvol,
        ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), ← hcinv, indicator_const_mul_apply]
    have hos : Q.ownerSpread (coupledSimilarity s u hs p) (σ q.1, σ q.2)
          (positiveSimilarity s u z)
        = ENNReal.ofReal ((s ^ 2)⁻¹) * Q.ownerSpread p q z := by
      unfold ownerSpread
      rw [indicator_preimage_comp, hset q, harea q,
        ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), ← hcinv, indicator_const_mul_apply]
    have hw2 : Q.weight (coupledSimilarity s u hs p) (σ q.1, σ q.2) / 2
        = ENNReal.ofReal (s ^ 2) * (Q.weight p q / 2) := by
      rw [hwt q, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    rw [hw2, hsp, hos]
    calc ENNReal.ofReal (s ^ 2) * (Q.weight p q / 2) *
          (ENNReal.ofReal ((s ^ 2)⁻¹) * spread p.1 q.1 w) *
          (ENNReal.ofReal ((s ^ 2)⁻¹) * Q.ownerSpread p q z)
        = ENNReal.ofReal (s ^ 2) * ENNReal.ofReal ((s ^ 2)⁻¹) *
            (ENNReal.ofReal ((s ^ 2)⁻¹) *
              (Q.weight p q / 2 * spread p.1 q.1 w * Q.ownerSpread p q z)) := by ring
      _ = ENNReal.ofReal ((s ^ 2)⁻¹) *
            (Q.weight p q / 2 * spread p.1 q.1 w * Q.ownerSpread p q z) := by
          rw [hcc, one_mul]
  calc Q.endpointSpreadTransport (coupledSimilarity s u hs p) (positiveSimilarity s u w)
        (positiveSimilarity s u z)
      = ∑' q : ℕ × ℕ, Q.weight (coupledSimilarity s u hs p) (σ q.1, σ q.2) / 2 *
          spread (similarityTargetEnv s u hs p.1) (σ q.1) (positiveSimilarity s u w) *
          Q.ownerSpread (coupledSimilarity s u hs p) (σ q.1, σ q.2)
            (positiveSimilarity s u z) := hreindex.symm
    _ = ∑' q : ℕ × ℕ, ENNReal.ofReal ((s ^ 2)⁻¹) *
          (Q.weight p q / 2 * spread p.1 q.1 w * Q.ownerSpread p q z) := tsum_congr hterm
    _ = ENNReal.ofReal ((s ^ 2)⁻¹) * Q.endpointSpreadTransport p w z := ENNReal.tsum_mul_left

/-! ### `s:eq:redistribute` on the coupled space -/

/-- **The single-kernel mass-transport identity for the endpoint-spread transport of a
coupled-covariant owned edge field**, from `s:eq:MTP` alone. -/
theorem coupledMassTransport_endpointSpreadTransport {m : ℝ}
    (Q : OwnedEdgeField coupledReRooting m) (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hweight : ∀ q : ℕ × ℕ, Measurable fun p : CoupledSpace => Q.weight p q)
    (howner : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {p : CoupledSpace | Q.owner p q = some c})
    (hcov : CoupledCovariantField Q) :
    (∫⁻ p, ∫⁻ z : Plane, Q.endpointSpreadTransport p 0 z ∂volume
        ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ p, ∫⁻ z : Plane, Q.endpointSpreadTransport p z 0 ∂volume
        ∂(ν.prod (gridMeasure.prod gridMeasure)) :=
  coupledMassTransport_of_massTransport ν hν Q.endpointSpreadTransport
    (MeasurableEndpointTransport.measurable_endpointSpreadTransport Q measurable_coupledEnv
      measurable_coupledGrid hweight howner)
    (endpointSpreadTransport_coupledSimilarityCovariant Q hcov)

end ReflectedGMS.GridCrossOrthogonalityTransport
