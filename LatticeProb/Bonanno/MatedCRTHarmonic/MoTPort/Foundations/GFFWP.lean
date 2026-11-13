/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.GFFWP at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFFMod
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2H

/-!
# The whole-plane GFF modulo `rℤ`

IG4 = Miller–Sheffield, *Imaginary geometry IV*, arXiv:1302.4738: to sample a whole-plane GFF modulo `rℤ`
(`r = 2πχ`), sample `h` modulo `ℝ`, then an independent uniform `U ∈ [0,r)`, and fix the additive
constant so that `(h, φ₀) ∈ U + rℤ`, for a fixed `φ₀ ∈ C_c^∞` with `∫ φ₀ = 1`.

* `IsWPGFFMod r X P`: `X = X₀ + U` with `X₀` a whole-plane GFF normalized by `(X₀, φ₀) = 0`
  (`LQGMetric.IsWholePlaneGFF`) and `U` independent, uniform on `[0,r)`. So `X` is the normalized
  representative of its class (`normMod r X = X` a.s.).
* `isWPGFFMod_iff`: canonical form (`X₀ = X − (X, φ₀)`, `U = (X, φ₀)`).
* `exists_isWPGFFMod`: existence on `Ω × ℝ` from LQGMetric's whole-plane GFF
  (`GFFExist.exists_wholePlaneGFF`) and an independent uniform variable (mathlib `indepFun_prod`).
* `IsWPGFFMod.map_eq`: uniqueness of the law (LQGMetric `GFFLaw.map_eq_of_normalized` for `X₀`,
  independence for the pair).
* invariance: `IsWPGFFMod.ae_normMod_eq`, `IsWPGFFMod.map_normMod_addConst_intMul` (the law of
  `normMod r (X + r k)` is the law of `X` for every `k : Ω → ℤ`), `IsWPGFFMod.congr_ae`,
  `IsWPGFFMod.normMod_addConst_intMul` (`normMod r (X + r k)` is again `IsWPGFFMod r`).

The unnormalized shift statement (`IsWPGFFMod r X P → IsWPGFFMod r (X + r k) P`) is
false for `k ≠ 0` under the normalized-representative definition (`(X + r k, φ₀) = U + r k ∉ [0,r)`); the correct
statement is about the class, i.e. `normMod r (X + r k)`, proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ProbabilityTheory

namespace MatedCRTHarmonic.MoTPort

open LQGMetric NormMod

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- **whole-plane GFF modulo `rℤ`** (IG4 L1103–1108), represented by its normalized
representative `(X, φ₀) = U ∈ [0,r)`: `X = X₀ + U` with `X₀` a whole-plane GFF normalized by
`(X₀, φ₀) = 0` and `U` an independent uniform constant in `[0,r)`. -/
def IsWPGFFMod (r : ℝ) (X : Ω → Field) (P : Measure Ω) : Prop :=
  ∃ (X₀ : Ω → Field) (U : Ω → ℝ), IsWholePlaneGFF X₀ P ∧ (∀ ω, X₀ ω φ₀ = 0) ∧
    P.map U = volume[|Ico 0 r] ∧ IndepFun X₀ U P ∧ ∀ ω, X ω = addConst (X₀ ω) (U ω)

namespace WPGFFMod

lemma addConst_neg_apply_φ₀ (g : Field) : addConst g (-(g φ₀)) φ₀ = 0 := by
  rw [addConst_apply_φ₀, add_neg_cancel]

lemma addConst_addConst_neg (g : Field) : addConst (addConst g (-(g φ₀))) (g φ₀) = g := by
  rw [addConst_addConst, neg_add_cancel, NormMod.addConst_zero]

lemma measurable_recenter : Measurable fun g : Field => addConst g (-(g φ₀)) :=
  measurable_addConst_prod.comp (measurable_id.prodMk (measurable_distOn_apply φ₀).neg)

lemma isProbabilityMeasure_unif {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (volume[|Ico (0 : ℝ) r]) :=
  cond_isProbabilityMeasure_of_finite (by simp [hr]) (by simp)

lemma aemeasurable_of_map_eq_unif {r : ℝ} (hr : 0 < r) {P : Measure Ω} {U : Ω → ℝ}
    (hU : P.map U = volume[|Ico 0 r]) : AEMeasurable U P := by
  have := isProbabilityMeasure_unif hr
  by_contra h
  by_cases hP : P = 0
  · rw [hP, Measure.map_zero] at hU
    exact (IsProbabilityMeasure.ne_zero (volume[|Ico (0 : ℝ) r])) hU.symm
  · rw [Measure.map_of_not_aemeasurable_of_ne_zero h hP] at hU
    have h1 := congrArg (fun μ : Measure ℝ => μ {Classical.ofNonempty}) hU
    simp only [Measure.dirac_apply_of_mem (mem_singleton _)] at h1
    rw [cond_apply measurableSet_Ico, measure_mono_null inter_subset_right
      Real.volume_singleton, mul_zero] at h1
    exact one_ne_zero h1

end WPGFFMod

open WPGFFMod
/-- canonical form: `X₀ = X − (X, φ₀)` and `U = (X, φ₀)` -/
theorem isWPGFFMod_iff {r : ℝ} {X : Ω → Field} {P : Measure Ω} :
    IsWPGFFMod r X P ↔ IsWholePlaneGFF (fun ω => addConst (X ω) (-(X ω φ₀))) P ∧
      P.map (fun ω => X ω φ₀) = volume[|Ico 0 r] ∧
      IndepFun (fun ω => addConst (X ω) (-(X ω φ₀))) (fun ω => X ω φ₀) P := by
  constructor
  · rintro ⟨X₀, U, h0, hn, hU, hi, hX⟩
    have hU' : (fun ω => X ω φ₀) = U := funext fun ω => by
      rw [hX, addConst_apply_φ₀, hn, zero_add]
    have hX0 : (fun ω => addConst (X ω) (-(X ω φ₀))) = X₀ := funext fun ω => by
      rw [hX, addConst_apply_φ₀, hn, zero_add, addConst_addConst, add_neg_cancel,
        NormMod.addConst_zero]
    rw [hU', hX0]
    exact ⟨h0, hU, hi⟩
  · rintro ⟨h0, hU, hi⟩
    exact ⟨_, _, h0, fun ω => addConst_neg_apply_φ₀ (X ω), hU, hi,
      fun ω => (addConst_addConst_neg (X ω)).symm⟩

namespace IsWPGFFMod

variable {r : ℝ} {X : Ω → Field} {P : Measure Ω}

/-- the representative lies in the transversal `(X, φ₀) ∈ [0,r)` almost surely -/
theorem ae_apply_φ₀_mem (hr : 0 < r) (hX : IsWPGFFMod r X P) : ∀ᵐ ω ∂P, X ω φ₀ ∈ Ico 0 r := by
  obtain ⟨-, hU, -⟩ := isWPGFFMod_iff.1 hX
  have hm := aemeasurable_of_map_eq_unif hr hU
  have hc : volume[|Ico (0 : ℝ) r] (Ico 0 r)ᶜ = 0 := by
    rw [cond_apply measurableSet_Ico, inter_compl_self, measure_empty, mul_zero]
  rw [← hU] at hc
  exact ae_of_ae_map hm (measure_eq_zero_iff_ae_notMem.1 hc |>.mono fun _ h => by simpa using h)

/-- the representative is its own normalized representative, a.s. -/
theorem ae_normMod_eq (hr : 0 < r) (hX : IsWPGFFMod r X P) :
    ∀ᵐ ω ∂P, normMod r (X ω) = X ω := by
  filter_upwards [hX.ae_apply_φ₀_mem hr] with ω h using normMod_eq_self hr h

/-- the law of the class: `normMod r ∘ X` has the law of `X` -/
theorem map_normMod (hr : 0 < r) (hX : IsWPGFFMod r X P) :
    P.map (fun ω => normMod r (X ω)) = P.map X :=
  Measure.map_congr (hX.ae_normMod_eq hr)

/-- **invariance under adding `r ℤ`**: for any `k : Ω → ℤ`,
the class of `X + r k` has the law of `X` -/
theorem map_normMod_addConst_intMul (hr : 0 < r) (hX : IsWPGFFMod r X P) (k : Ω → ℤ) :
    P.map (fun ω => normMod r (addConst (X ω) (r * k ω))) = P.map X := by
  simp_rw [normMod_addConst_intMul hr.ne']
  exact hX.map_normMod hr

/-- modification on a null set (keeping measurability of the recentred field) -/
theorem congr_ae (hX : IsWPGFFMod r X P) {Y : Ω → Field}
    (hY : Measurable fun ω => addConst (Y ω) (-(Y ω φ₀))) (hXY : ∀ᵐ ω ∂P, Y ω = X ω) :
    IsWPGFFMod r Y P := by
  obtain ⟨h0, hU, hi⟩ := isWPGFFMod_iff.1 hX
  have e0 : (fun ω => addConst (Y ω) (-(Y ω φ₀))) =ᵐ[P]
      fun ω => addConst (X ω) (-(X ω φ₀)) := by
    filter_upwards [hXY] with ω h; rw [h]
  have e1 : (fun ω => Y ω φ₀) =ᵐ[P] fun ω => X ω φ₀ := by
    filter_upwards [hXY] with ω h; rw [h]
  refine isWPGFFMod_iff.2 ⟨DFGPS.L217.isWholePlaneGFF_of_map_eq hY h0 (Measure.map_congr e0),
    by rw [Measure.map_congr e1, hU], hi.congr e0.symm e1.symm⟩

/-- **invariance under adding `r ℤ`**, process form: `normMod r (X + r k)` is again a whole-plane
GFF modulo `rℤ` (for measurable `X`) -/
theorem normMod_addConst_intMul (hr : 0 < r) (hX : IsWPGFFMod r X P) (hXm : Measurable X)
    (k : Ω → ℤ) : IsWPGFFMod r (fun ω => normMod r (addConst (X ω) (r * k ω))) P := by
  simp_rw [NormMod.normMod_addConst_intMul hr.ne']
  exact hX.congr_ae (measurable_recenter.comp ((measurable_normMod r).comp hXm))
    (hX.ae_normMod_eq hr)

/-- **uniqueness of the law** of a whole-plane GFF modulo `rℤ` -/
theorem map_eq (hr : 0 < r) [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : Ω' → Field} (hX : IsWPGFFMod r X P) (hX' : IsWPGFFMod r X' P') :
    P.map X = P'.map X' := by
  obtain ⟨X₀, U, h0, hn, hU, hi, hXe⟩ := hX
  obtain ⟨X₀', U', h0', hn', hU', hi', hXe'⟩ := hX'
  have hUm := aemeasurable_of_map_eq_unif hr hU
  have hU'm := aemeasurable_of_map_eq_unif hr hU'
  have hlaw0 : P.map X₀ = P'.map X₀' :=
    GFFLaw.map_eq_of_normalized integral_φ₀ (measurable_distOn_apply φ₀)
      (fun g c => addConst_apply_φ₀ g c) h0 h0' (ae_of_all _ hn) (ae_of_all _ hn')
  have hpair : P.map (fun ω => (X₀ ω, U ω)) = P'.map (fun ω => (X₀' ω, U' ω)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map h0.measurable.aemeasurable hUm).1 hi,
      (indepFun_iff_map_prod_eq_prod_map_map h0'.measurable.aemeasurable hU'm).1 hi', hlaw0,
      hU, hU']
  have hX : X = (fun p : Field × ℝ => addConst p.1 p.2) ∘ fun ω => (X₀ ω, U ω) :=
    funext hXe
  have hX' : X' = (fun p : Field × ℝ => addConst p.1 p.2) ∘ fun ω => (X₀' ω, U' ω) :=
    funext hXe'
  rw [hX, hX', ← AEMeasurable.map_map_of_aemeasurable measurable_addConst_prod.aemeasurable
      (h0.measurable.aemeasurable.prodMk hUm),
    ← AEMeasurable.map_map_of_aemeasurable measurable_addConst_prod.aemeasurable
      (h0'.measurable.aemeasurable.prodMk hU'm), hpair]

end IsWPGFFMod

end MatedCRTHarmonic.MoTPort
