/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.LFPPMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Adapter
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Measurability of LFPP distances of a continuous random field

Needed for the Fubini–Markov step of DG Lemma 2.5 (DG:747–770: "`E[δ^{ξ̃²/2} D̃ | h] ≤ …`. We now
conclude by means of Markov's inequality."), which DG do not spell out. Own argument:
* for an admissible path `γ`, `f ↦ ∫₀¹ e^{ξ f(γ t)} |γ'(t)| dt` is continuous on `C(ℂ,ℝ)`
  (compact-open topology; dominated convergence);
* hence `f ↦ D^ξ(f) = inf_γ (…)` is upper semicontinuous, so Borel measurable;
* a process with a.e.-measurable marginals and continuous paths is an a.e.-measurable `C(ℂ,ℝ)`-valued
  map (mathlib `ContinuousMap.measurable_iff_eval` on the completion, `NullMeasurable.aemeasurable`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Interval

namespace LQGMetric
namespace DG

/-- The LFPP length of an admissible path is continuous in the field `f ∈ C(ℂ,ℝ)`. -/
lemma continuous_lfppLength (ξ : ℝ) {γ : ℝ → ℂ} (hγ : LQGDimension.IsAdmissiblePath γ) :
    Continuous fun f : C(ℂ, ℝ) => LQGDimension.lfppLength ξ f γ := by
  rw [continuous_iff_continuousAt]
  intro f0
  have hK : IsCompact (γ '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hγ.continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn f0.continuous.continuousOn
  have hN : {f : C(ℂ, ℝ) | MapsTo f (γ '' Icc 0 1) (Ioo (-(M + 1)) (M + 1))} ∈ 𝓝 f0 := by
    refine (ContinuousMap.isOpen_setOfPred_mapsTo hK isOpen_Ioo).mem_nhds ?_
    intro x hx
    have := hM x hx
    rw [Real.norm_eq_abs, abs_le] at this
    exact ⟨by linarith, by linarith⟩
  have hD := LQGDimension.LowerAsm.deriv_intervalIntegrable' hγ
  have hIoc : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun t => Real.exp (|ξ| * (M + 1)) * ‖deriv γ t‖)
  · refine Eventually.of_forall fun f => ?_
    rw [hIoc]
    have hc : ContinuousOn (fun t => Real.exp (ξ * f (γ t))) (Ioc 0 1) :=
      (Real.continuous_exp.comp_continuousOn ((continuous_const.mul f.continuous).comp_continuousOn
        (hγ.continuousOn.mono Ioc_subset_Icc_self)))
    exact (hc.aestronglyMeasurable measurableSet_Ioc).mul
      (measurable_deriv γ).norm.aestronglyMeasurable
  · filter_upwards [hN] with f hf
    refine Eventually.of_forall fun t ht => ?_
    rw [hIoc] at ht
    have hft := hf (mem_image_of_mem γ (Ioc_subset_Icc_self ht))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_norm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have : |f (γ t)| ≤ M + 1 := abs_le.2 ⟨hft.1.le, hft.2.le⟩
    calc ξ * f (γ t) ≤ |ξ * f (γ t)| := le_abs_self _
      _ = |ξ| * |f (γ t)| := abs_mul _ _
      _ ≤ |ξ| * (M + 1) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  · exact (hD.norm.const_mul _)
  · refine Eventually.of_forall fun t _ => ?_
    exact ((Real.continuous_exp.comp (continuous_const.mul
      (continuous_eval_const (γ t)))).mul continuous_const).continuousAt

/-- `f ↦ D^ξ(f)` is Borel measurable on `C(ℂ,ℝ)` (it is upper semicontinuous). -/
lemma measurable_lfppDistance (ξ : ℝ) :
    Measurable fun f : C(ℂ, ℝ) => LQGDimension.lfppDistance ξ f := by
  have : Nonempty {γ : ℝ → ℂ // LQGDimension.IsAdmissiblePath γ} :=
    ⟨⟨_, LQGDimension.LowerAsm.admissible_ofReal⟩⟩
  refine measurable_of_Iio fun c => ?_
  have : (fun f : C(ℂ, ℝ) => LQGDimension.lfppDistance ξ f) ⁻¹' Iio c =
      ⋃ γ : {γ : ℝ → ℂ // LQGDimension.IsAdmissiblePath γ},
        (fun f : C(ℂ, ℝ) => LQGDimension.lfppLength ξ f γ.1) ⁻¹' Iio c := by
    ext f
    simp only [mem_preimage, mem_Iio, mem_iUnion, LQGDimension.lfppDistance]
    exact ciInf_lt_iff (bddBelow_ld ξ f)
  rw [this]
  exact (isOpen_iUnion fun γ => isOpen_Iio.preimage (continuous_lfppLength ξ γ.2)).measurableSet

/-- A process with a.e.-measurable marginals and continuous paths, as a `C(ℂ,ℝ)`-valued map. -/
def toContMap {Ω : Type*} (Y : ℂ → Ω → ℝ) (hc : ∀ ω, Continuous fun z => Y z ω) (ω : Ω) :
    C(ℂ, ℝ) :=
  ⟨fun z => Y z ω, hc ω⟩

lemma aemeasurable_toContMap {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Y : ℂ → Ω → ℝ)
    (hm : ∀ z, AEMeasurable (Y z) μ) (hc : ∀ ω, Continuous fun z => Y z ω) :
    AEMeasurable (toContMap Y hc) μ := by
  have key : @Measurable (NullMeasurableSpace Ω μ) C(ℂ, ℝ) _ _ (toContMap Y hc) := by
    refine (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω μ)).2 fun z => ?_
    have h1 : NullMeasurable (Y z) μ := (hm z).nullMeasurable
    exact fun s hs => h1 hs
  have h2 : NullMeasurable (toContMap Y hc) μ := fun s hs => key hs
  exact h2.aemeasurable

/-- The LFPP distance of such a process is a.e.-measurable. -/
lemma aemeasurable_lfppDistance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (ξ : ℝ)
    (Y : ℂ → Ω → ℝ) (hm : ∀ z, AEMeasurable (Y z) μ) (hc : ∀ ω, Continuous fun z => Y z ω) :
    AEMeasurable (fun ω => LQGDimension.lfppDistance ξ (fun z => Y z ω)) μ := by
  have h := (measurable_lfppDistance ξ).comp_aemeasurable (aemeasurable_toContMap Y hm hc)
  have e : ((fun f : C(ℂ, ℝ) => LQGDimension.lfppDistance ξ f) ∘ toContMap Y hc) =
      fun ω => LQGDimension.lfppDistance ξ (fun z => Y z ω) := by
    funext ω; simp only [Function.comp_apply, toContMap, ContinuousMap.coe_mk]
  rwa [e] at h

end DG
end LQGMetric
