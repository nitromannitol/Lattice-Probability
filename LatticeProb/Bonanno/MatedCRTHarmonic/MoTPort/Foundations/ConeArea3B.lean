/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea3B at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# C.area-exist for the cone field, input (b1): the cone field off the origin

The cone field `coneField (lateralPartC x) a Q` (DMS Def. 4.10) is `x` plus the function
`g(z) = Q(−log|z|) + a(−log|z|) − R(|z|)`, where `R` is a version of the radial process
`r ↦ x_r(0)` (`radialFun`) continuous on `(0,∞)`; `g` is continuous on `ℂ \ {0}`. By the Ding–Gwynne density-change statement
(`ConeArea3.isVagueLimitOn_areaApproxC_add_ofFunC`), a vague limit of `areaApproxC γ x` on
`ℂ \ {0}` gives one of `areaApproxC γ (cone field)` there, with density `e^{γ g}`:

* `ofFunC_congr_ae`: `ofFunC` only depends on the a.e. class;
* `coneField_eq_add_ofFunC`: the decomposition `coneField (lateralPartC x) a Q = x + ofFunC g`;
* **`isVagueLimitOn_coneField_punctured`**: the deterministic form of (b1);
* `ae_hasCircleAvgs`: a whole-plane GFF a.s. has circle averages (as limits of mollified averages)
  at a.e. point and every dyadic scale (LM `CircleAvg.ae_tendsto_mollAvg` and Fubini);
* `ae_isVagueLimitOn_coneField_punctured_of`: (b1) for the cone data from (R1) the whole-plane
  area limit off `0`, (R2) a radial version continuous on `(0,∞)`, (R3) local integrability of
  the radial part of the cone.

Own elementary glue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort

namespace ConeArea3

open LQGMetric

/-- `ofFunC` only depends on the a.e. class of the function -/
lemma ofFunC_congr_ae {f f' : ℂ → ℝ} (h : f =ᵐ[volume] f') : ofFunC f = ofFunC f' := by
  classical
  refine DFunLike.ext _ _ fun φ => ?_
  rw [ofFunC, ofFunC, Distribution.ofFun_apply_eq_ite, Distribution.ofFun_apply_eq_ite]
  simp only [TopologicalSpace.Opens.coe_top, locallyIntegrableOn_univ]
  by_cases hf : LocallyIntegrable f volume
  · rw [if_pos hf, if_pos (hf.congr h)]
    exact integral_congr_ae (h.mono fun x hx => by simp only [hx])
  · rw [if_neg hf, if_neg fun h' => hf (h'.congr h.symm)]

/-- the radial part of the cone field written through a version `R` of `r ↦ x_r(0)` -/
def coneShift (a : ℝ → ℝ) (Q : ℝ) (R : ℝ → ℝ) : ℂ → ℝ :=
  fun z => Q * (-Real.log ‖z‖) + a (-Real.log ‖z‖) - R ‖z‖

/-- **`coneField (lateralPartC x) a Q = x + ofFunC g`** with `g = Q(−log|·|) + a(−log|·|) − R(|·|)`,
for any version `R(|·|)` of `radialFun x` -/
theorem coneField_eq_add_ofFunC {x : Field} {a : ℝ → ℝ} {Q : ℝ} {R : ℝ → ℝ}
    (hxR : radialFun x =ᵐ[volume] fun z => R ‖z‖)
    (hRl : LocallyIntegrable (fun z : ℂ => R ‖z‖) volume)
    (hAl : LocallyIntegrable (fun z : ℂ => Q * (-Real.log ‖z‖) + a (-Real.log ‖z‖)) volume) :
    coneField (lateralPartC x) a Q = x + ofFunC (coneShift a Q R) := by
  have hgl : LocallyIntegrable (coneShift a Q R) volume := hAl.sub hRl
  refine DFunLike.ext _ _ fun φ => ?_
  have hφc : Continuous fun z => φ z := φ.continuous
  have hφs : HasCompactSupport fun z => φ z := φ.hasCompactSupport
  have i1 : Integrable (fun z => φ z * (Q * (-Real.log ‖z‖) + a (-Real.log ‖z‖))) volume :=
    hAl.integrable_smul_left_of_hasCompactSupport hφc hφs
  have i2 : Integrable (fun z => φ z * R ‖z‖) volume :=
    hRl.integrable_smul_left_of_hasCompactSupport hφc hφs
  simp only [coneField, lateralPartC, add_apply, sub_apply]
  rw [ofFunC_congr_ae hxR, ConeCirc.ofFunC_apply' hRl, ConeCirc.ofFunC_apply' hAl,
    ConeCirc.ofFunC_apply' hgl]
  have e : (fun z => φ z * coneShift a Q R z) =
      fun z => φ z * (Q * (-Real.log ‖z‖) + a (-Real.log ‖z‖)) - φ z * R ‖z‖ := by
    funext z; simp only [coneShift]; ring
  rw [e, integral_sub i1 i2]
  ring

/-- the cone shift is continuous off the origin -/
lemma continuousOn_coneShift {a : ℝ → ℝ} (ha : Continuous a) (Q : ℝ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Ioi 0)) : ContinuousOn (coneShift a Q R) (univ \ {0}) := by
  have hn : ContinuousOn (fun z : ℂ => ‖z‖) (univ \ {0}) := continuous_norm.continuousOn
  have hlog : ContinuousOn (fun z : ℂ => -Real.log ‖z‖) (univ \ {0}) :=
    (Real.continuousOn_log.comp hn fun z hz => by
      simpa using hz.2).neg
  refine ((continuousOn_const.mul hlog).add (ha.comp_continuousOn hlog)).sub
    (hR.comp hn fun z hz => ?_)
  simpa [norm_pos_iff] using hz.2

lemma measurable_coneShift {a : ℝ → ℝ} (ha : Measurable a) (Q : ℝ) {R : ℝ → ℝ}
    (hR : Measurable R) : Measurable (coneShift a Q R) := by
  unfold coneShift
  have hl : Measurable fun z : ℂ => -Real.log ‖z‖ := (Real.measurable_log.comp measurable_norm).neg
  exact ((measurable_const.mul hl).add (ha.comp hl)).sub (hR.comp measurable_norm)

/-- **(b1), deterministic form**: a vague limit of `areaApproxC γ x` on `ℂ \ {0}` gives one of the
approximations of the cone field `coneField (lateralPartC x) a Q`, with density `e^{γ g}`
(`g = coneShift a Q R`), as soon as the circle averages of `x` exist a.e., `R(|·|)` is a version
of `radialFun x` continuous on `(0,∞)`, and the radial pieces are locally integrable -/
theorem isVagueLimitOn_coneField_punctured {γ Q : ℝ} {x : Field} {a : ℝ → ℝ}
    (ha : Continuous a) {R : ℝ → ℝ} (hRc : ContinuousOn R (Ioi 0)) (hRm : Measurable R)
    (hxR : radialFun x =ᵐ[volume] fun z => R ‖z‖)
    (hRl : LocallyIntegrable (fun z : ℂ => R ‖z‖) volume)
    (hAl : LocallyIntegrable (fun z : ℂ => Q * (-Real.log ‖z‖) + a (-Real.log ‖z‖)) volume)
    (hc : ConeArea.HasCircleAvgs x) {μ : Measure ℂ}
    (hx : QuantumZipper.IsVagueLimitOn (univ \ {0}) (areaApproxC γ x) μ) :
    QuantumZipper.IsVagueLimitOn (univ \ {0}) (areaApproxC γ (coneField (lateralPartC x) a Q))
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * coneShift a Q R z))) := by
  rw [coneField_eq_add_ofFunC hxR hRl hAl]
  exact isVagueLimitOn_areaApproxC_add_ofFunC (isOpen_univ.sdiff isClosed_singleton) hx hc
    (measurable_coneShift ha.measurable Q hRm) (hAl.sub hRl) (continuousOn_coneShift ha Q hRc)

/-- `(x, z) ↦ ⟨x, ψ_n * σ_{z,r}⟩` is jointly measurable (LM `measurable_circleAvg`, one level) -/
lemma measurable_mollAvg (n : ℕ) (r : ℝ) :
    Measurable fun p : Field × ℂ => CircleAvg.mollAvg p.1 n p.2 r := by
  have hm : Measurable fun q : (Field × ℂ) × ℝ => q.1.1 (bumpTest n (circleMap q.1.2 r q.2)) := by
    have hc : Measurable fun q : (Field × ℂ) × ℝ => circleMap q.1.2 r q.2 := by
      simp only [circleMap]; fun_prop
    exact (measurable_apply_bumpTest n).comp
      (f := fun q : (Field × ℂ) × ℝ => (q.1.1, circleMap q.1.2 r q.2))
      ((measurable_fst.comp measurable_fst).prodMk hc)
  have := (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).const_smul (2 * Real.pi)⁻¹
  convert this.measurable using 1
  funext p
  simp only [CircleAvg.mollAvg, Real.circleAverage_def,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rfl

/-- **a whole-plane GFF a.s. has circle averages at a.e. point and every dyadic scale** -/
theorem ae_hasCircleAvgs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Field} (hX : IsWholePlaneGFF X P) : ∀ᵐ ω ∂P, ConeArea.HasCircleAvgs (X ω) := by
  unfold ConeArea.HasCircleAvgs
  rw [ae_all_iff]
  intro k
  have hS : MeasurableSet {p : Ω × ℂ | ∃ a, Tendsto
      (fun n => CircleAvg.mollAvg (X p.1) n p.2 (QuantumZipper.radius k)) atTop (𝓝 a)} :=
    measurableSet_exists_tendsto
      (f := fun n (p : Ω × ℂ) => CircleAvg.mollAvg (X p.1) n p.2 (QuantumZipper.radius k))
      fun n => ((measurable_mollAvg n _).comp
        ((hX.measurable.comp measurable_fst).prodMk measurable_snd))
  rw [Measure.ae_ae_comm hS]
  exact ae_of_all _ fun z => CircleAvg.ae_tendsto_mollAvg hX z (QuantumZipper.radius_pos k)

/-- **(b1) for the cone data, from the three remaining inputs**:
(R1) a.s. vague limit of the whole-plane approximations of `X` on `ℂ \ {0}` (DS Prop. 1.1 for the
whole-plane GFF), (R2) a.s. a version of `r ↦ X_r(0)` continuous on `(0,∞)` (LM
`exists_continuous_version_circleAvg` + polar Fubini), (R3) a.s. local integrability of
`Q(−log|·|) + A_{−log|·|}` -/
theorem ae_isVagueLimitOn_coneField_punctured_of {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Field} {A : ℝ → Ω → ℝ} {γ α Q : ℝ}
    (hX : IsWholePlaneGFF X P) (hA : IsConeProcess α Q A P)
    (hR1 : ∀ᵐ ω ∂P, ∃ μ, QuantumZipper.IsVagueLimitOn (univ \ {0}) (areaApproxC γ (X ω)) μ)
    (hR2 : ∀ᵐ ω ∂P, ∃ R : ℝ → ℝ, ContinuousOn R (Ioi 0) ∧ Measurable R ∧
      radialFun (X ω) =ᵐ[volume] (fun z => R ‖z‖) ∧
      LocallyIntegrable (fun z : ℂ => R ‖z‖) volume)
    (hR3 : ∀ᵐ ω ∂P,
      LocallyIntegrable (fun z : ℂ => Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖) ω) volume) :
    ∀ᵐ ω ∂P, ∃ μ, QuantumZipper.IsVagueLimitOn (univ \ {0})
      (areaApproxC γ (coneField (lateralPartC (X ω)) (fun t => A t ω) Q)) μ := by
  filter_upwards [hR1, hR2, hR3, ae_hasCircleAvgs hX, (ConeMeas2.aemeasurable_conePath hA).2]
    with ω ⟨μ, hμ⟩ ⟨R, hRc, hRm, hxR, hRl⟩ hAl hc hAc
  exact ⟨_, isVagueLimitOn_coneField_punctured hAc hRc hRm hxR hRl hAl hc hμ⟩

end ConeArea3

end MatedCRTHarmonic.MoTPort
