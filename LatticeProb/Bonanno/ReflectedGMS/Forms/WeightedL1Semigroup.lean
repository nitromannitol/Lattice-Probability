/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.WeightedL1Semigroup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedSemigroupAction
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationarySpeedMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Weighted `L¹(m)` action of the reflected semigroup

The existing probability kernel acts on every function integrable for the
atomic speed measure.  Detailed balance upgrades the almost-everywhere row
integrability supplied by stationarity to every starting vertex.  Stationarity
then gives preservation of integrability and the `L¹` contraction.  The final
lemmas transfer the row action to the actual reflected one-time law.
-/

set_option autoImplicit false

open scoped ENNReal NNReal ProbabilityTheory BigOperators
open MeasureTheory ProbabilityTheory

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [DecidableEq V] [Nontrivial V]

namespace FullNetworkForm

/-- The pointwise action of the full-form probability kernel on a real
function. -/
noncomputable def weightedL1SemigroupAction
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (g : V → ℝ) (x : V) : ℝ :=
  ∫ y, g y ∂semigroupProbabilityKernel G m hm hmsum t x

/-- The kernel action of a speed-integrable function is itself
speed-integrable. -/
theorem integrable_weightedL1SemigroupAction
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (g : V → ℝ)
    (hg : Integrable g (vertexSpeedMeasure m)) :
    Integrable (weightedL1SemigroupAction G m hm hmsum t g)
      (vertexSpeedMeasure m) := by
  let K := semigroupProbabilityKernel G m hm hmsum t
  have hcomp : Integrable g (K ∘ₘ vertexSpeedMeasure m) := by
    rw [semigroupProbabilityKernel_comp_vertexSpeedMeasure]
    exact hg
  have hnorm := Measure.integrable_integral_norm_of_integrable_comp hcomp
  apply Integrable.mono hnorm (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with x
  change ‖∫ y, g y ∂K x‖ ≤ ‖∫ y, ‖g y‖ ∂K x‖
  calc
    ‖∫ y, g y ∂K x‖ ≤ ∫ y, ‖g y‖ ∂K x :=
      norm_integral_le_integral_norm g
    _ = ‖∫ y, ‖g y‖ ∂K x‖ := (Real.norm_of_nonneg
      (integral_nonneg_of_ae (ae_of_all _ fun y ↦ norm_nonneg (g y)))).symm

/-- The full-form probability kernel is an `L¹(m)` contraction. -/
theorem integral_norm_weightedL1SemigroupAction_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (g : V → ℝ)
    (hg : Integrable g (vertexSpeedMeasure m)) :
    (∫ x, ‖weightedL1SemigroupAction G m hm hmsum t g x‖
        ∂vertexSpeedMeasure m) ≤
      ∫ x, ‖g x‖ ∂vertexSpeedMeasure m := by
  let K := semigroupProbabilityKernel G m hm hmsum t
  have hcomp : Integrable g (K ∘ₘ vertexSpeedMeasure m) := by
    rw [semigroupProbabilityKernel_comp_vertexSpeedMeasure]
    exact hg
  have hnorm := Measure.integrable_integral_norm_of_integrable_comp hcomp
  have hiterated :
      (∫ x, (∫ y, ‖g y‖ ∂K x) ∂vertexSpeedMeasure m) =
        ∫ y, ‖g y‖ ∂(K ∘ₘ vertexSpeedMeasure m) := by
    rw [Measure.comp_eq_comp_const_apply]
    exact (Kernel.integral_comp
      (κ := Kernel.const Unit (vertexSpeedMeasure m)) (η := K) (a := ())
      hcomp.norm).symm
  calc
    (∫ x, ‖weightedL1SemigroupAction G m hm hmsum t g x‖
        ∂vertexSpeedMeasure m) ≤
        ∫ x, (∫ y, ‖g y‖ ∂K x) ∂vertexSpeedMeasure m := by
      apply integral_mono_ae
      · exact (integrable_weightedL1SemigroupAction G m hm hmsum t g hg).norm
      · exact hnorm
      · filter_upwards with x
        simpa only [weightedL1SemigroupAction, K] using
          (norm_integral_le_integral_norm (μ := K x) g)
    _ = ∫ x, ‖g x‖ ∂(K ∘ₘ vertexSpeedMeasure m) := hiterated
    _ = ∫ x, ‖g x‖ ∂vertexSpeedMeasure m := by
      rw [semigroupProbabilityKernel_comp_vertexSpeedMeasure]

/-- The stationary two-time measure is symmetric, as a measure-level form of
detailed balance. -/
theorem map_swap_vertexSpeedMeasure_compProd_semigroupProbabilityKernel
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) :
    (vertexSpeedMeasure m ⊗ₘ semigroupProbabilityKernel G m hm hmsum t).map
        Prod.swap =
      vertexSpeedMeasure m ⊗ₘ semigroupProbabilityKernel G m hm hmsum t := by
  let K := semigroupProbabilityKernel G m hm hmsum t
  apply Measure.ext_of_singleton
  rintro ⟨x, y⟩
  rw [Measure.map_apply measurable_swap (measurableSet_singleton (x, y))]
  have hjoint (a b : V) :
      (vertexSpeedMeasure m ⊗ₘ K) {(a, b)} =
        ENNReal.ofReal (m a) * ENNReal.ofReal (semigroupKernel G m t a b) := by
    rw [Measure.compProd_apply (measurableSet_singleton (a, b)),
      lintegral_countable']
    simp only [vertexSpeedMeasure_singleton]
    rw [tsum_eq_single a]
    · have hpre : Prod.mk a ⁻¹' ({(a, b)} : Set (V × V)) = {b} := by
        ext q
        simp
      rw [hpre]
      simp only [K, semigroupProbabilityKernel_apply_singleton]
      exact mul_comm (ENNReal.ofReal (semigroupKernel G m t a b))
        (ENNReal.ofReal (m a))
    · intro z hza
      have hpre : Prod.mk z ⁻¹' ({(a, b)} : Set (V × V)) = ∅ := by
        ext q
        simp [hza]
      rw [hpre, measure_empty, zero_mul]
  rw [show Prod.swap ⁻¹' ({(x, y)} : Set (V × V)) = {(y, x)} by
    ext ⟨a, b⟩
    simp [Prod.swap, and_comm]]
  rw [hjoint y x, hjoint x y, ← ENNReal.ofReal_mul (hm y).le,
    ← ENNReal.ofReal_mul (hm x).le,
    semigroupKernel_detailedBalance G m hm t y x]

/-- Reversibility extends from `L²(m)` to the pairing of a bounded test with
an arbitrary speed-integrable function. -/
theorem integral_mul_weightedL1SemigroupAction_comm
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (g v : V → ℝ)
    (hg : Integrable g (vertexSpeedMeasure m)) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ x, ‖v x‖ ≤ C) :
    (∫ x, v x * weightedL1SemigroupAction G m hm hmsum t g x
        ∂vertexSpeedMeasure m) =
      ∫ x, g x * weightedL1SemigroupAction G m hm hmsum t v x
        ∂vertexSpeedMeasure m := by
  let K := semigroupProbabilityKernel G m hm hmsum t
  let μ := vertexSpeedMeasure m
  let F : V × V → ℝ := fun p ↦ v p.1 * g p.2
  have hgcomp : Integrable g (K ∘ₘ μ) := by
    change Integrable g
      (semigroupProbabilityKernel G m hm hmsum t ∘ₘ vertexSpeedMeasure m)
    rw [semigroupProbabilityKernel_comp_vertexSpeedMeasure]
    exact hg
  have hgsnd : Integrable (fun p : V × V ↦ g p.2) (μ ⊗ₘ K) :=
    (Measure.integrable_compProd_snd_iff hgcomp.aestronglyMeasurable).2 hgcomp
  have hF : Integrable F (μ ⊗ₘ K) := by
    apply Integrable.mono (hgsnd.const_mul C)
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with p
    simp only [F, norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hv p.1) (abs_nonneg _)
  have hsym : (μ ⊗ₘ K).map Prod.swap = μ ⊗ₘ K := by
    exact map_swap_vertexSpeedMeasure_compProd_semigroupProbabilityKernel
      G m hm hmsum t
  have hFmap : Integrable F ((μ ⊗ₘ K).map Prod.swap) := by
    rw [hsym]
    exact hF
  have hFswap : Integrable (fun p : V × V ↦ v p.2 * g p.1) (μ ⊗ₘ K) := by
    have hi := (integrable_map_measure hFmap.aestronglyMeasurable
      measurable_swap.aemeasurable).1 hFmap
    apply hi.congr
    filter_upwards with p
    rcases p with ⟨a, b⟩
    rfl
  calc
    (∫ x, v x * weightedL1SemigroupAction G m hm hmsum t g x ∂μ) =
        ∫ p, F p ∂(μ ⊗ₘ K) := by
      rw [Measure.integral_compProd hF]
      simp only [F, weightedL1SemigroupAction, K]
      simp_rw [integral_const_mul]
    _ = ∫ p, F p ∂(μ ⊗ₘ K).map Prod.swap := by rw [hsym]
    _ = ∫ p, F (Prod.swap p) ∂(μ ⊗ₘ K) :=
      integral_map measurable_swap.aemeasurable hFmap.aestronglyMeasurable
    _ = ∫ p, v p.2 * g p.1 ∂(μ ⊗ₘ K) := by
      apply integral_congr_ae
      filter_upwards with p
      rcases p with ⟨a, b⟩
      rfl
    _ = ∫ x, g x * weightedL1SemigroupAction G m hm hmsum t v x ∂μ := by
      rw [Measure.integral_compProd hFswap]
      simp only [weightedL1SemigroupAction, K]
      simp_rw [integral_mul_const, mul_comm]

end FullNetworkForm

/-- The actual reflected expectation equals the weighted `L¹(m)` kernel
action, with no `L²` or boundedness hypothesis. -/
theorem integral_reflected_at_time_eq_weightedL1SemigroupAction
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (x : V) (g : V → ℝ)
    (_hg : Integrable g (vertexSpeedMeasure m)) :
    (∫ ω, (PF.X t ω).elim 0 g ∂PF.P x) =
      weightedL1SemigroupAction G m hm hmsum t g x := by
  let g₀ : Option V → ℝ := fun z ↦ z.elim 0 g
  have hg₀ : Measurable g₀ := measurable_of_countable _
  have hsome : Measurable (some : V → Option V) := measurable_of_countable _
  calc
    (∫ ω, (PF.X t ω).elim 0 g ∂PF.P x) =
        ∫ z, g₀ z ∂(PF.P x).map (PF.X t) := by
      simpa only [g₀, Function.comp_apply] using
        (integral_map (PF.measurable_X t).aemeasurable
          hg₀.aestronglyMeasurable).symm
    _ = ∫ z, g₀ z ∂(semigroupProbabilityKernel G m hm hmsum t x).map
          (some : V → Option V) := by
      exact congrArg (fun μ : Measure (Option V) ↦ ∫ z, g₀ z ∂μ)
        (reflected_transitionLaw_eq_semigroupProbabilityKernel
          h hG hm hmsum t x)
    _ = ∫ z, g z ∂semigroupProbabilityKernel G m hm hmsum t x := by
      simpa only [g₀, Function.comp_apply, Option.elim_some] using
        integral_map hsome.aemeasurable hg₀.aestronglyMeasurable
    _ = weightedL1SemigroupAction G m hm hmsum t g x := rfl

end ReflectedGMS
