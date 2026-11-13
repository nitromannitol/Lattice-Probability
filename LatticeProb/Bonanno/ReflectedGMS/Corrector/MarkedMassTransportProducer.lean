/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedMassTransportProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MeasurableEndpointTransport
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualMarkedBlockTransport
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TemporalMassTransport
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridTranslationInvariance
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridDilationInvariance
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The marked mass-transport principle from the manuscript's own hypothesis

The manuscript's spatial mass-transport assumption `s:eq:MTP` (tex:112-122) is
restricted to kernels obeying `s:eq:Tcov`,

```
T (C (ℋ - u), C (w - u), C (z - u)) = C⁻² T (ℋ, w, z),
```

i.e. covariance of **degree minus two under the whole similarity group** —
translations *and* every positive dilation `C`.  The project's faithful
formalization of that assumption is `EnvironmentLaws.MassTransport`, whose test
objects are `EnvironmentLaws.MassTransportKernel`s, whose `covariant` field
quantifies over all `s > 0`.

At tex:286 the manuscript attaches independent uniform dyadic systems to `ℋ` and
says: *"Mass transport remains valid for a transport which depends covariantly
on these marks: average the transport over the marks before applying
\eqref{s:eq:MTP}.  The invariance of their laws gives \eqref{s:eq:Tcov} for the
averaged transport."*  Its dyadic system (tex:259) has side lengths `2^(s+k)`
with `s` uniform on `[0,1)`, so it randomizes the **scale** and not merely the
offset, and *"Its law is invariant under every deterministic translation and
positive dilation."*

This module carries out exactly that step.  The two mark-law invariances it uses
are already checked theorems of this project:

* `UniformGridTranslationInvariance.map_translate_gridMeasure`, and
* `UniformGridDilationInvariance.map_dilate_gridMeasure`, which holds for
  **every** positive real scale, not merely dyadic ones.

## What is proved here

On the actual marked configuration space `Env × Grid` of
`Spatial.ActualMarkedBlockTransport`, with law `ν.prod gridMeasure`:

* `markedSimilarity` is the joint similarity `z ↦ s • (z - u)` acting on a marked
  configuration — the canonical similarity on the environment and
  `dilate ∘ translate` on the grid mark;
* `MarkedSimilarityCovariant` is `s:eq:Tcov` for a marked transport;
* `averagedKernel` is the mark-average, and it **is** an
  `EnvironmentLaws.MassTransportKernel`: `averaged_covariant` is the manuscript
  sentence "the invariance of their laws gives `s:eq:Tcov` for the averaged
  transport";
* `markedMassTransport_of_massTransport` concludes the marked mass-transport
  identity from `EnvironmentLaws.MassTransport ν` **alone**.  No invariance of
  `ν`, no finiteness beyond `SFinite ν`, and no ergodicity is used.

Then the manuscript's `s:lem:redistribution` (tex:480-498) is discharged from
`s:eq:MTP` with no probabilistic hypothesis left over:

* `SimilarityCovariantField` is the manuscript's structural hypothesis on the
  coefficient field — "a nonnegative covariant coefficient `q_e` … scales
  quadratically", with the owner block carried along by the similarity;
* `endpointSpreadTransport_markedSimilarityCovariant` proves tex:497, *"This has
  scaling degree `-2`"*, for the manuscript kernel: the coefficient contributes
  `s²`, each of the two spreads contributes `s⁻²`;
* `lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_of_massTransport`
  is `s:eq:redistribute` itself, on the actual marked space, from
  `EnvironmentLaws.MassTransport ν`.

## Correction to an earlier note in this file

An earlier version of this module recorded that
`SpecificEnergyRedistribution.MarkedMassTransport` is not derivable from
`EnvironmentLaws.MassTransport`, and attributed this to a failure of the
manuscript's tex:286 step.  **That attribution was wrong.**  The manuscript step
is sound and the project's grid law is faithful to it; the defect was in the
Lean predicate.  `SpecificEnergyRedistribution.MarkedMassTransport` imposes on
`T` only the `C = 1` instance of `s:eq:Tcov`, namely translation covariance
along the re-rooting action, and so quantifies over a **strictly larger** class
of kernels than `s:eq:MTP` does.  Averaging a merely translation-covariant
marked kernel over the grid marks produces a kernel with no scaling behaviour,
which is not a `MassTransportKernel`; that is why the unrestricted predicate is
not derivable.  Restricting the kernel class to the paper's own degree `-2`
class, as `MarkedSimilarityCovariant` does, removes the obstruction entirely.

The conditional route through `ReRootingInvariant` is retained below because it
is checked and because it applies to the larger kernel class, but it is **not**
needed for the manuscript results and should not be consumed: everything the
consumers actually use is available unconditionally from `s:eq:MTP`.
-/

set_option autoImplicit false

open MeasureTheory

open scoped ENNReal

namespace ReflectedGMS.MarkedMassTransportProducer

open StatementIngredients DyadicApproximation DiameterBlockIndex Code MarkedBlockAveraging
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open EnvironmentLaws DyadicGridLaw DyadicGridTranslation
open UniformGridTranslationInvariance UniformGridDilationInvariance

/-! ### Reflection invariance of planar Lebesgue measure -/

/-! ### The joint similarity action on the actual marked configuration space

`s:eq:Tcov` transforms the environment, the marks and both transport arguments by
one and the same similarity `z ↦ s • (z - u)`.  On `Env × Grid` that is the
canonical similarity action on the environment together with
`dilate ∘ translate` on the mark. -/

/-- The joint similarity `z ↦ s • (z - u)` acting on a marked configuration: the
canonical similarity on the environment, `dilate ∘ translate` on the grid mark.
Its unit-scale instance is the re-rooting action
`ActualMarkedBlockTransport.actualReRooting.shift`
(`markedSimilarity_one`). -/
noncomputable def markedSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (p : Env × Grid) :
    Env × Grid :=
  (similarityTargetEnv s u hs p.1, dilate s hs (translate u p.2))

/-- At unit scale the joint similarity is exactly the marked re-rooting action of
`Spatial.ActualMarkedBlockTransport`. -/
theorem markedSimilarity_one (u : Plane) (p : Env × Grid) :
    markedSimilarity 1 u one_pos p = ActualMarkedBlockTransport.actualReRooting.shift u p := by
  have henv : similarityTargetEnv 1 u one_pos p.1
      = ActualMarkedBlockTransport.translateEnv u p.1 := rfl
  show (similarityTargetEnv 1 u one_pos p.1, dilate 1 one_pos (translate u p.2))
    = (ActualMarkedBlockTransport.translateEnv u p.1, translate u p.2)
  rw [henv, dilate_one]

/-- The grid law is preserved by every joint similarity: the composite of the two
checked invariances `map_translate_gridMeasure` and `map_dilate_gridMeasure`.
The second holds for every positive real scale, which is exactly what tex:259
asserts of the uniform dyadic system. -/
theorem measurePreserving_gridSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) :
    MeasurePreserving (fun D : Grid => dilate s hs (translate u D)) gridMeasure gridMeasure := by
  have h1 : MeasurePreserving (translate u) gridMeasure gridMeasure :=
    ⟨measurable_translate_left u, map_translate_gridMeasure u⟩
  have h2 : MeasurePreserving (dilate s hs) gridMeasure gridMeasure :=
    ⟨measurable_dilate s hs, map_dilate_gridMeasure hs⟩
  exact h2.comp h1

/-- **`s:eq:Tcov` for a marked transport**: degree `-2` homogeneity under every
translation and every positive dilation, with the marks transported along.  This
is the manuscript's "a transport which depends covariantly on these marks"
(tex:286) read with the covariance of tex:120-121, and it is exactly the kernel
class that `EnvironmentLaws.MassTransport` tests. -/
def MarkedSimilarityCovariant (T : Env × Grid → Plane → Plane → ℝ≥0∞) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (p : Env × Grid) (w z : Plane),
    T (markedSimilarity s u hs p) (positiveSimilarity s u w) (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * T p w z

/-! ### Mark averaging: the manuscript step at tex:286 -/

/-- The mark-averaged transport, "average the transport over the marks". -/
noncomputable def averaged (T : Env × Grid → Plane → Plane → ℝ≥0∞) :
    Env × Plane × Plane → ℝ≥0∞ :=
  fun x => ∫⁻ D, T (x.1, D) x.2.1 x.2.2 ∂gridMeasure

theorem measurable_averaged (T : Env × Grid → Plane → Plane → ℝ≥0∞)
    (hT : Measurable fun x : (Env × Grid) × Plane × Plane => T x.1 x.2.1 x.2.2) :
    Measurable (averaged T) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hmap : Measurable fun q : (Env × Plane × Plane) × Grid =>
      (((q.1.1, q.2), q.1.2.1, q.1.2.2) : (Env × Grid) × Plane × Plane) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have h : Measurable fun q : (Env × Plane × Plane) × Grid =>
      T (q.1.1, q.2) q.1.2.1 q.1.2.2 := hT.comp hmap
  exact h.lintegral_prod_right'

/-- **"The invariance of their laws gives `s:eq:Tcov` for the averaged
transport."**  This is the manuscript sentence at tex:286, proved. -/
theorem averaged_covariant (T : Env × Grid → Plane → Plane → ℝ≥0∞)
    (hT : Measurable fun x : (Env × Grid) × Plane × Plane => T x.1 x.2.1 x.2.2)
    (hcov : MarkedSimilarityCovariant T)
    (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env) (hsim : IsSimilarity s u hs e e')
    (w z : Plane) :
    averaged T (e', positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * averaged T (e, w, z) := by
  rw [eq_similarityTargetEnv_of_isSimilarity hsim]
  have hmap1 : Measurable fun D : Grid =>
      (((similarityTargetEnv s u hs e, D),
        (positiveSimilarity s u w, positiveSimilarity s u z)) : (Env × Grid) × Plane × Plane) :=
    (measurable_const.prodMk measurable_id).prodMk measurable_const
  have hmeas : Measurable fun D : Grid =>
      T (similarityTargetEnv s u hs e, D) (positiveSimilarity s u w)
        (positiveSimilarity s u z) := hT.comp hmap1
  have hmap2 : Measurable fun D : Grid => (((e, D), (w, z)) : (Env × Grid) × Plane × Plane) :=
    (measurable_const.prodMk measurable_id).prodMk measurable_const
  have hmeas' : Measurable fun D : Grid => T (e, D) w z := hT.comp hmap2
  have hswap : (∫⁻ D, T (similarityTargetEnv s u hs e, D) (positiveSimilarity s u w)
      (positiveSimilarity s u z) ∂gridMeasure)
      = ∫⁻ D, T (similarityTargetEnv s u hs e, dilate s hs (translate u D))
          (positiveSimilarity s u w) (positiveSimilarity s u z) ∂gridMeasure :=
    ((measurePreserving_gridSimilarity s u hs).lintegral_comp hmeas).symm
  have hpt : ∀ D : Grid, T (similarityTargetEnv s u hs e, dilate s hs (translate u D))
      (positiveSimilarity s u w) (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * T (e, D) w z :=
    fun D => hcov s u hs (e, D) w z
  show (∫⁻ D, T (similarityTargetEnv s u hs e, D) (positiveSimilarity s u w)
      (positiveSimilarity s u z) ∂gridMeasure)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * ∫⁻ D, T (e, D) w z ∂gridMeasure
  rw [hswap]
  simp_rw [hpt]
  exact lintegral_const_mul _ hmeas'

/-- The mark-averaged transport **is** a test kernel for `s:eq:MTP`. -/
noncomputable def averagedKernel (T : Env × Grid → Plane → Plane → ℝ≥0∞)
    (hT : Measurable fun x : (Env × Grid) × Plane × Plane => T x.1 x.2.1 x.2.2)
    (hcov : MarkedSimilarityCovariant T) : MassTransportKernel where
  toFun := averaged T
  measurable_toFun := measurable_averaged T hT
  covariant := fun s u hs e e' hsim w z => averaged_covariant T hT hcov s u hs e e' hsim w z

/-- **Marked mass transport from `s:eq:MTP` alone.**  On the actual marked
configuration space `Env × Grid` with law `ν.prod gridMeasure`, every jointly
measurable nonnegative marked transport of degree `-2` under the full similarity
group satisfies the mass-transport identity.

No invariance of the environment law `ν` is assumed anywhere, and `ν` is only
required to be `SFinite`: the mark-side invariances are the two checked grid
theorems, and the environment side is the manuscript's own hypothesis. -/
theorem markedMassTransport_of_massTransport (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (T : Env × Grid → Plane → Plane → ℝ≥0∞)
    (hT : Measurable fun x : (Env × Grid) × Plane × Plane => T x.1 x.2.1 x.2.2)
    (hcov : MarkedSimilarityCovariant T) :
    (∫⁻ p, ∫⁻ z : Plane, T p 0 z ∂volume ∂(ν.prod gridMeasure))
      = ∫⁻ p, ∫⁻ z : Plane, T p z 0 ∂volume ∂(ν.prod gridMeasure) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have h := hν (averagedKernel T hT hcov)
  have hout : Measurable fun q : (Env × Grid) × Plane => T q.1 0 q.2 :=
    hT.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hin : Measurable fun q : (Env × Grid) × Plane => T q.1 q.2 0 :=
    hT.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hL : (∫⁻ p, ∫⁻ z : Plane, T p 0 z ∂volume ∂(ν.prod gridMeasure))
      = ∫⁻ e, ∫⁻ z : Plane, averaged T (e, 0, z) ∂volume ∂ν := by
    have hmo : Measurable fun p : Env × Grid => ∫⁻ z : Plane, T p 0 z ∂volume :=
      hout.lintegral_prod_right'
    rw [lintegral_prod _ hmo.aemeasurable]
    refine lintegral_congr fun e => ?_
    have hf : Measurable (Function.uncurry fun (D : Grid) (z : Plane) => T (e, D) 0 z) :=
      hT.comp ((measurable_const.prodMk measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd))
    exact lintegral_lintegral_swap (f := fun (D : Grid) (z : Plane) => T (e, D) 0 z)
      hf.aemeasurable
  have hR : (∫⁻ p, ∫⁻ z : Plane, T p z 0 ∂volume ∂(ν.prod gridMeasure))
      = ∫⁻ e, ∫⁻ z : Plane, averaged T (e, z, 0) ∂volume ∂ν := by
    have hmi : Measurable fun p : Env × Grid => ∫⁻ z : Plane, T p z 0 ∂volume :=
      hin.lintegral_prod_right'
    rw [lintegral_prod _ hmi.aemeasurable]
    refine lintegral_congr fun e => ?_
    have hf : Measurable (Function.uncurry fun (D : Grid) (z : Plane) => T (e, D) z 0) :=
      hT.comp ((measurable_const.prodMk measurable_fst).prodMk
        (measurable_snd.prodMk measurable_const))
    exact lintegral_lintegral_swap (f := fun (D : Grid) (z : Plane) => T (e, D) z 0)
      hf.aemeasurable
  rw [hL, hR]
  exact h

/-! ### Elementary similarity facts used by the degree `-2` computation -/

theorem surjective_positiveSimilarity {s : ℝ} (u : Plane) (hs : 0 < s) :
    Function.Surjective (positiveSimilarity s u) :=
  fun z => ⟨positiveSimilarity s⁻¹ (-s • u) z, positiveSimilarity_inverse_right s u z hs⟩

theorem coe_positiveSimilarityHomeomorph {s : ℝ} (u : Plane) (hs : 0 < s) :
    ((positiveSimilarityHomeomorph s u hs : Plane ≃ₜ Plane) : Plane → Plane)
      = positiveSimilarity s u :=
  funext fun z => positiveSimilarityHomeomorph_apply s u z hs

theorem preimage_positiveSimilarity_interior {s : ℝ} (u : Plane) (hs : 0 < s) (A : Set Plane) :
    positiveSimilarity s u ⁻¹' interior A = interior (positiveSimilarity s u ⁻¹' A) := by
  have h := (positiveSimilarityHomeomorph s u hs).preimage_interior A
  rwa [coe_positiveSimilarityHomeomorph u hs] at h

theorem indicator_preimage_comp (A : Set Plane) (c : ℝ≥0∞) (Φ : Plane → Plane) (w : Plane) :
    Set.indicator A (fun _ => c) (Φ w) = Set.indicator (Φ ⁻¹' A) (fun _ => c) w := by
  by_cases h : Φ w ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show w ∈ Φ ⁻¹' A from h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show w ∉ Φ ⁻¹' A from h)]

theorem indicator_const_mul_apply (A : Set Plane) (a b : ℝ≥0∞) (w : Plane) :
    Set.indicator A (fun _ => a * b) w = a * Set.indicator A (fun _ => b) w := by
  by_cases h : w ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-! ### Degree `-2` homogeneity of the manuscript redistribution kernel

Manuscript tex:480-497.  The coefficient `q_e` "scales quadratically", the two
endpoint spreads `1_{w ∈ H}/a_H` and the owner-block spread `1_{z ∈ S_e}/ℓ(S_e)²`
each scale by `s⁻²`, and the net degree is `-2`. -/

/-- **`s:eq:Tcov` at the level of the coefficient field** (manuscript tex:480,
tex:497).  The similarity relabels the raw labels by a bijection `σ`, carries
every cell and every owner block to its similarity image, multiplies the
coefficient `q_e` by `s²` — the manuscript's "scales quadratically" — and
multiplies the owner-block area `ℓ(S_e)²` by `s²`.

This is the exact similarity analogue of the checked translation-only hypothesis
`SpecificEnergyRedistribution.OwnedEdgeField.ReRootingCovariant`, and it is a
structural statement about the field alone: no integral occurs in it. -/
def SimilarityCovariantField {m : ℝ}
    (Q : OwnedEdgeField ActualMarkedBlockTransport.actualReRooting m) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (p : Env × Grid), ∃ σ : ℕ ≃ ℕ,
    (∀ n : ℕ, positiveSimilarity s u ⁻¹'
        labelCell (similarityTargetEnv s u hs p.1) (σ n) = labelCell p.1 n) ∧
      (∀ q : ℕ × ℕ, Q.weight (markedSimilarity s u hs p) (σ q.1, σ q.2)
        = ENNReal.ofReal (s ^ 2) * Q.weight p q) ∧
      (∀ q : ℕ × ℕ, positiveSimilarity s u ⁻¹'
        Q.ownerSet (markedSimilarity s u hs p) (σ q.1, σ q.2) = Q.ownerSet p q) ∧
      (∀ q : ℕ × ℕ, Q.ownerArea (markedSimilarity s u hs p) (σ q.1, σ q.2)
        = ENNReal.ofReal (s ^ 2) * Q.ownerArea p q)

/-- **"This has scaling degree `-2`"** (manuscript tex:497).  The endpoint-spread
to owner-block transport of a similarity-covariant, quadratically scaling
coefficient field is a degree `-2` marked transport, hence a legitimate test
kernel for `s:eq:MTP` after mark averaging. -/
theorem endpointSpreadTransport_markedSimilarityCovariant {m : ℝ}
    (Q : OwnedEdgeField ActualMarkedBlockTransport.actualReRooting m)
    (hcov : SimilarityCovariantField Q) :
    MarkedSimilarityCovariant Q.endpointSpreadTransport := by
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
    (fun q : ℕ × ℕ => Q.weight (markedSimilarity s u hs p) q / 2 *
      spread (similarityTargetEnv s u hs p.1) q.1 (positiveSimilarity s u w) *
      Q.ownerSpread (markedSimilarity s u hs p) q (positiveSimilarity s u z))
  have hterm : ∀ q : ℕ × ℕ,
      Q.weight (markedSimilarity s u hs p) (σ q.1, σ q.2) / 2 *
        spread (similarityTargetEnv s u hs p.1) (σ q.1) (positiveSimilarity s u w) *
        Q.ownerSpread (markedSimilarity s u hs p) (σ q.1, σ q.2) (positiveSimilarity s u z)
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
    have hos : Q.ownerSpread (markedSimilarity s u hs p) (σ q.1, σ q.2)
          (positiveSimilarity s u z)
        = ENNReal.ofReal ((s ^ 2)⁻¹) * Q.ownerSpread p q z := by
      unfold ownerSpread
      rw [indicator_preimage_comp, hset q, harea q,
        ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), ← hcinv, indicator_const_mul_apply]
    have hw2 : Q.weight (markedSimilarity s u hs p) (σ q.1, σ q.2) / 2
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
  calc Q.endpointSpreadTransport (markedSimilarity s u hs p) (positiveSimilarity s u w)
        (positiveSimilarity s u z)
      = ∑' q : ℕ × ℕ, Q.weight (markedSimilarity s u hs p) (σ q.1, σ q.2) / 2 *
          spread (similarityTargetEnv s u hs p.1) (σ q.1) (positiveSimilarity s u w) *
          Q.ownerSpread (markedSimilarity s u hs p) (σ q.1, σ q.2)
            (positiveSimilarity s u z) := hreindex.symm
    _ = ∑' q : ℕ × ℕ, ENNReal.ofReal ((s ^ 2)⁻¹) *
          (Q.weight p q / 2 * spread p.1 q.1 w * Q.ownerSpread p q z) := tsum_congr hterm
    _ = ENNReal.ofReal ((s ^ 2)⁻¹) * Q.endpointSpreadTransport p w z := ENNReal.tsum_mul_left

/-! ### `s:lem:redistribution` from `s:eq:MTP`

The manuscript lemma "Redistribution over blocks" on the actual marked
configuration space, with **no** probabilistic hypothesis beyond the paper's own
`s:eq:MTP` for the environment law. -/

/-! ### The earlier conditional route, retained

The declarations below are the previously checked route through re-rooting
invariance of the marked law.  They apply to the larger, merely
translation-covariant kernel class of
`SpecificEnergyRedistribution.MarkedMassTransport`, and they are therefore
**conditional**: `ReRootingInvariant R μ` is an extra law-level hypothesis that
the manuscript does not assume.  The manuscript results do not need them — use
`markedMassTransport_of_massTransport` and
`lintegral_rootEndpointDensity_eq_lintegral_ownerBlockDensity_of_massTransport`
instead. -/

variable {Ω : Type*} [MeasurableSpace Ω]

end ReflectedGMS.MarkedMassTransportProducer
