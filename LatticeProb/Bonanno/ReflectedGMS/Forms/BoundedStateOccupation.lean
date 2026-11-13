/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.BoundedStateOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialSupermartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.ProcessOccupationLaplace
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Adapted occupation of a bounded state observable

The literal time integral of a state observable need not visibly be measurable
in the uncompleted natural filtration.  As for vertex occupation, we first cap
the path at the deterministic horizon and use its canonical dyadic version.
For right-regular paths this version agrees with the literal integral at every
horizon, and boundedness makes its sample paths continuous.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- The path capped at the horizon used to construct bounded occupation. -/
private def boundedOccupationCappedProcess (PF : ProcessFamily V) (t : ℝ≥0) :
    ℝ≥0 → PF.Ω → Option V :=
  fun s ω ↦ PF.X (min s t) ω

private theorem measurable_boundedOccupationCappedProcess
    (PF : ProcessFamily V) (t s : ℝ≥0) :
    Measurable[PF.naturalFiltration t] (boundedOccupationCappedProcess PF t s) := by
  change Measurable[pastSigma PF.X t] (PF.X (min s t))
  intro A hA
  apply measurableSet_pastSigma_iff.mpr
  refine ⟨{p | p ⟨min s t, show min s t ≤ t from min_le_right _ _⟩ ∈ A}, ?_, rfl⟩
  exact hA.preimage (measurable_pi_apply _)

/-- The canonical natural-filtration version of the occupation integral of a
state observable over `[0,t]`.  The value of `f none` is retained unchanged. -/
noncomputable def boundedStateOccupationVersion
    (PF : ProcessFamily V) (f : Option V → ℝ) (t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  ∫ r : ℝ in Icc 0 (t : ℝ),
    f (dyadicLimit (boundedOccupationCappedProcess PF t) (Real.toNNReal r) ω)

/-- At each horizon, canonical bounded-state occupation is strongly measurable
in the actual, uncompleted natural filtration. -/
theorem stronglyMeasurable_boundedStateOccupationVersion
    (PF : ProcessFamily V) (f : Option V → ℝ) (t : ℝ≥0) :
    StronglyMeasurable[PF.naturalFiltration t]
      (boundedStateOccupationVersion PF f t) := by
  let F : PF.Ω → ℝ → ℝ := fun ω r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator (fun r ↦
      f (dyadicLimit (boundedOccupationCappedProcess PF t)
        (Real.toNNReal r) ω)) r
  have hcap : ∀ s, Measurable[PF.naturalFiltration t]
      (boundedOccupationCappedProcess PF t s) :=
    measurable_boundedOccupationCappedProcess PF t
  have hjoint :
      @Measurable (PF.Ω × ℝ) ℝ
        (MeasurableSpace.prod (PF.naturalFiltration t) Real.measurableSpace)
        Real.measurableSpace (Function.uncurry F) := by
    dsimp only [F]
    apply Measurable.indicator
    · exact (measurable_of_countable f).comp
        (measurable_swap_toNNReal (mΩ := PF.naturalFiltration t)
          (measurable_uncurry_dyadicLimit
            (mΩ := PF.naturalFiltration t) hcap))
    · exact measurable_snd measurableSet_Icc
  change StronglyMeasurable[PF.naturalFiltration t]
    (fun ω ↦ ∫ r : ℝ in Icc 0 (t : ℝ),
      f (dyadicLimit (boundedOccupationCappedProcess PF t)
        (Real.toNNReal r) ω))
  letI : MeasurableSpace PF.Ω := PF.naturalFiltration t
  have hjoint' : Measurable (Function.uncurry F) := hjoint
  simpa only [F, integral_indicator measurableSet_Icc] using
    hjoint'.stronglyMeasurable.integral_prod_right

/-- Canonical bounded-state occupation is strongly adapted to the actual
natural filtration. -/
theorem stronglyAdapted_boundedStateOccupationVersion
    (PF : ProcessFamily V) (f : Option V → ℝ) :
    StronglyAdapted PF.naturalFiltration
      (boundedStateOccupationVersion PF f) := by
  intro t
  exact stronglyMeasurable_boundedStateOccupationVersion PF f t

private theorem dyadicLimit_boundedOccupationCappedProcess_eq_dyadic_of_lt
    (PF : ProcessFamily V) (t s : ℝ≥0) (ω : PF.Ω)
    (hst : s < t) :
    dyadicLimit (boundedOccupationCappedProcess PF t) s ω = dyadicLimit PF.X s ω := by
  have hε : 0 < t - s := tsub_pos_of_lt hst
  have hev : ∀ᶠ k in Filter.atTop, dyadicCeil k s < t := by
    filter_upwards [eventually_dyadicCeil_mem_Ico s hε] with k hk
    simpa [add_tsub_cancel_of_le hst.le] using hk.2
  have hversion : dyadicLimit (boundedOccupationCappedProcess PF t) s ω =
      dyadicLimit PF.X s ω := by
    refine option_eq_of_forall_some_iff fun x => ?_
    rw [dyadicLimit_eq_some_iff, dyadicLimit_eq_some_iff]
    constructor
    · intro hx
      filter_upwards [hx, hev] with k hk hkt
      simpa [boundedOccupationCappedProcess, min_eq_left hkt.le] using hk
    · intro hx
      filter_upwards [hx, hev] with k hk hkt
      simpa [boundedOccupationCappedProcess, min_eq_left hkt.le] using hk
  exact hversion

/-- Capping at the horizon changes no dyadic occupation value below it.
The endpoint is negligible for Lebesgue integration. -/
theorem boundedStateOccupationVersion_eq_dyadicIntegral
    (PF : ProcessFamily V) (f : Option V → ℝ) (t : ℝ≥0) (ω : PF.Ω) :
    boundedStateOccupationVersion PF f t ω =
      ∫ r : ℝ in Icc 0 (t : ℝ), f (dyadicLimit PF.X (Real.toNNReal r) ω) := by
  unfold boundedStateOccupationVersion
  rw [integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ico]
  apply setIntegral_congr_fun measurableSet_Ico
  intro r hr
  have hr0 : 0 ≤ r := hr.1
  have hrt : Real.toNNReal r < t := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal r hr0]
    exact hr.2
  change f (dyadicLimit (boundedOccupationCappedProcess PF t)
    (Real.toNNReal r) ω) = f (dyadicLimit PF.X (Real.toNNReal r) ω)
  rw [dyadicLimit_boundedOccupationCappedProcess_eq_dyadic_of_lt
    PF t (Real.toNNReal r) ω hrt]

private theorem boundedStateOccupationVersion_eq_of_rightRegular
    (PF : ProcessFamily V) (f : Option V → ℝ) (t : ℝ≥0) (ω : PF.Ω)
    (hω : RightRegularAt PF.X ω) :
    boundedStateOccupationVersion PF f t ω =
      ∫ r : ℝ in Icc 0 (t : ℝ), f (PF.X (Real.toNNReal r) ω) := by
  rw [boundedStateOccupationVersion_eq_dyadicIntegral]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r _
  change f (dyadicLimit PF.X (Real.toNNReal r) ω) = f (PF.X (Real.toNNReal r) ω)
  rw [dyadicLimit_eq_of_rightRegular hω]

/-- The canonical occupation of a bounded state observable has continuous
paths for every sample, before choosing any starting law. -/
theorem continuous_boundedStateOccupationVersion
    (PF : ProcessFamily V) (f : Option V → ℝ) {C : ℝ}
    (hf : ∀ q, |f q| ≤ C) (ω : PF.Ω) :
    Continuous (fun t ↦ boundedStateOccupationVersion PF f t ω) := by
  let g : ℝ → ℝ := fun r ↦
    f (dyadicLimit PF.X (Real.toNNReal r) ω)
  have hstate : Measurable (fun r : ℝ ↦
      dyadicLimit PF.X (Real.toNNReal r) ω) :=
    measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω
  have hg : Measurable g := (measurable_of_countable f).comp hstate
  have hC : 0 ≤ C := (abs_nonneg (f none)).trans (hf none)
  have hc : Continuous (fun _ : ℝ ↦ C) := continuous_const
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    constructor
    · apply (hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mono'
      · exact hg.aestronglyMeasurable
      filter_upwards [] with r
      simpa [g, Real.norm_eq_abs, abs_of_nonneg hC] using
        hf (dyadicLimit PF.X (Real.toNNReal r) ω)
    · apply (hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mono'
      · exact hg.aestronglyMeasurable
      filter_upwards [] with r
      simpa [g, Real.norm_eq_abs, abs_of_nonneg hC] using
        hf (dyadicLimit PF.X (Real.toNNReal r) ω)
  have hprimitive : Continuous (fun b : ℝ ↦ ∫ r in (0 : ℝ)..b, g r) :=
    intervalIntegral.continuous_primitive hgi 0
  have heq : (fun t : ℝ≥0 ↦ boundedStateOccupationVersion PF f t ω) =
      fun t : ℝ≥0 ↦ ∫ r in (0 : ℝ)..(t : ℝ), g r := by
    funext t
    rw [boundedStateOccupationVersion_eq_dyadicIntegral,
      intervalIntegral.integral_of_le t.coe_nonneg, integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact hprimitive.comp continuous_subtype_val

/-- Joint time/sample measurability of canonical bounded occupation. -/
theorem measurable_uncurry_boundedStateOccupationVersion
    (PF : ProcessFamily V) (f : Option V → ℝ) {C : ℝ}
    (hf : ∀ q, |f q| ≤ C) :
    Measurable (Function.uncurry (boundedStateOccupationVersion PF f)) :=
  measurable_uncurry_of_continuous_of_measurable
    (continuous_boundedStateOccupationVersion PF f hf)
    (fun t ↦ ((stronglyMeasurable_boundedStateOccupationVersion PF f t).mono
      (PF.naturalFiltration.le t)).measurable)

/-- Under an actual reflected law, one full-probability event simultaneously
identifies every canonical occupation value with the literal raw-path integral
and gives a continuous occupation path. -/
theorem boundedStateOccupationVersion_ae_eq_all_and_continuous
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (f : Option V → ℝ) {C : ℝ} (hf : ∀ q, |f q| ≤ C) (z : V) :
    ∀ᵐ ω ∂PF.P z,
      (∀ t : ℝ≥0,
        boundedStateOccupationVersion PF f t ω =
          ∫ r : ℝ in Icc 0 (t : ℝ), f (PF.X (Real.toNNReal r) ω)) ∧
      Continuous (fun t ↦ boundedStateOccupationVersion PF f t ω) := by
  filter_upwards [ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hω
  exact ⟨fun t ↦ boundedStateOccupationVersion_eq_of_rightRegular
      PF f t ω hω,
    continuous_boundedStateOccupationVersion PF f hf ω⟩

end ReflectedGMS
