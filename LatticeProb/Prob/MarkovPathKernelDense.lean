import Mathlib
import LatticeProb.Prob.ExtendedMappingAE
import LatticeProb.Prob.MarkovStepShiftedPath

/-!
# The Markov property of a continuous family of path laws on a dense set of times and starting points

Let `K : E → Prob C(ℝ≥0, E)` be a continuous family of path laws (weak topology, compact-open topology
on paths).  The family has the Markov property at `(z, t)` if, for a path `x` sampled from `K z`, the
conditional law of the shifted path `x (t + ·)` given the stopped path `x (· ∧ t)` is `K (x t)`; in test
function form, for every bounded continuous `g` on pairs of paths,
`E g (x (· ∧ t), x (t + ·)) = E ∫ g (x (· ∧ t), w) d(K (x t)) (w)`.

* `LatticeProb.continuous_integral_of_continuous_measure`: if `μ : τ → Prob X` is continuous and `G` is
  bounded continuous on `X × τ`, then `a ↦ ∫ G (x, a) dμ a (x)` is continuous (extended continuous mapping).
* `LatticeProb.MarkovAt`: the Markov property at `(z, t)` in test function form.
* `LatticeProb.markovAt_of_dense`: for a continuous family, the Markov property on a dense set of
  `(z, t)` implies it for all `(z, t)`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

/-- **Joint continuity of integrals against a continuous family of laws.**  If `μ : τ → Prob X` is
continuous and `G` is bounded and continuous on `X × τ`, then `a ↦ ∫ G (x, a) d(μ a)(x)` is
continuous. -/
theorem continuous_integral_of_continuous_measure
    {X τ : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] [PseudoMetricSpace τ] [MeasurableSpace τ] [OpensMeasurableSpace τ]
    [SecondCountableTopology τ] {μ : τ → ProbabilityMeasure X} (hμ : Continuous μ)
    {G : X × τ → ℝ} (hG : Continuous G) {C : ℝ} (hC : ∀ p, ‖G p‖ ≤ C) :
    Continuous fun a => ∫ x, G (x, a) ∂(μ a : Measure X) := by
  classical
  rw [continuous_iff_seqContinuous]
  intro a a₀ ha
  let Gb : (X × τ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup G hG C hC
  have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    ((hμ.tendsto a₀).comp ha)
  have hconst : ∀ b : τ, Measurable fun x : X => (x, b) := fun b =>
    measurable_id.prodMk measurable_const
  refine tendsto_integral_comp_of_ae_locally_uniform (E := X) (T := X × τ) (μ a₀ : Measure X)
    (fun n => (μ (a n) : Measure X)) hlim (fun x => (x, a₀)) (fun n x => (x, a n))
    (fun n => hconst (a n)) (hconst a₀) ?_ Gb
  refine Filter.Eventually.of_forall fun x ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ha ε hε
  refine ⟨ε, hε, N, fun n hn y hy => ?_⟩
  rw [Prod.dist_eq]
  exact max_le hy.le (hN n hn).le

variable {E : Type*}

attribute [local instance] dUnifMetricSpace

section Dense

variable [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

/-- **The Markov property of a family of path laws at `(z, t)`** in test function form: for every
bounded continuous `g` on pairs of paths,
`∫ g (x (· ∧ t), x (t + ·)) d(K z)(x) = ∫ ∫ g (x (· ∧ t), w) d(K (x t))(w) d(K z)(x)`. -/
def MarkovAt (K : E → ProbabilityMeasure C(ℝ≥0, E)) (z : E) (t : ℝ≥0) : Prop :=
  ∀ g : (C(ℝ≥0, E) × C(ℝ≥0, E)) →ᵇ ℝ,
    ∫ x, g (stopPath x t, pathShift x t) ∂(K z : Measure C(ℝ≥0, E)) =
      ∫ x, ∫ w, g (stopPath x t, w) ∂(K (x t) : Measure C(ℝ≥0, E)) ∂(K z : Measure C(ℝ≥0, E))

/-- The integral of a function bounded by `C` against a probability measure is bounded by `C`. -/
private theorem norm_integral_le_of_bound {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (f : α → ℝ) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) : ‖∫ x, f x ∂ν‖ ≤ C := by
  simpa using norm_integral_le_of_norm_le_const (μ := ν) (f := f) (C := C)
    (Filter.Eventually.of_forall hC)

/-- **Extension of the Markov property from a dense set.**  If `K : E → Prob C(ℝ≥0, E)` is continuous
and has the Markov property at all `(z, t)` of a dense subset of `E × ℝ≥0`, then it has it everywhere. -/
theorem markovAt_of_dense {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K)
    {Q : Set (E × ℝ≥0)} (hQ : Dense Q) (h : ∀ q ∈ Q, MarkovAt K q.1 q.2) :
    ∀ z t, MarkovAt K z t := by
  classical
  intro z t g
  have hKp : Continuous fun p : E × ℝ≥0 => K p.1 := hK.comp continuous_fst
  have hstop : Continuous fun q : C(ℝ≥0, E) × (E × ℝ≥0) => stopPath q.1 q.2.2 :=
    continuous_stopPath_uncurry.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hshift : Continuous fun q : C(ℝ≥0, E) × (E × ℝ≥0) => pathShift q.1 q.2.2 :=
    continuous_pathShift_uncurry.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  -- left side
  have hL : Continuous fun p : E × ℝ≥0 =>
      ∫ x, g (stopPath x p.2, pathShift x p.2) ∂(K p.1 : Measure C(ℝ≥0, E)) :=
    continuous_integral_of_continuous_measure hKp
      (G := fun q : C(ℝ≥0, E) × (E × ℝ≥0) => g (stopPath q.1 q.2.2, pathShift q.1 q.2.2))
      (g.continuous.comp (hstop.prodMk hshift)) (C := ‖g‖) fun q => g.norm_coe_le_norm _
  -- inner integral, jointly continuous in `(x, t)`
  have hev : Continuous fun q : C(ℝ≥0, E) × ℝ≥0 => q.1 q.2 :=
    ContinuousEval.continuous_eval
  have hKev : Continuous fun q : C(ℝ≥0, E) × ℝ≥0 => K (q.1 q.2) := hK.comp hev
  have hstop2 : Continuous fun q : C(ℝ≥0, E) × (C(ℝ≥0, E) × ℝ≥0) => stopPath q.2.1 q.2.2 :=
    continuous_stopPath_uncurry.comp continuous_snd
  have hφ : Continuous fun a : C(ℝ≥0, E) × ℝ≥0 =>
      ∫ w, g (stopPath a.1 a.2, w) ∂(K (a.1 a.2) : Measure C(ℝ≥0, E)) :=
    continuous_integral_of_continuous_measure hKev
      (G := fun q : C(ℝ≥0, E) × (C(ℝ≥0, E) × ℝ≥0) => g (stopPath q.2.1 q.2.2, q.1))
      (g.continuous.comp (hstop2.prodMk continuous_fst)) (C := ‖g‖) fun q => g.norm_coe_le_norm _
  have hφb : ∀ a : C(ℝ≥0, E) × ℝ≥0,
      ‖∫ w, g (stopPath a.1 a.2, w) ∂(K (a.1 a.2) : Measure C(ℝ≥0, E))‖ ≤ ‖g‖ :=
    fun a => norm_integral_le_of_bound (K (a.1 a.2) : Measure C(ℝ≥0, E)) _ ‖g‖
      fun w => g.norm_coe_le_norm _
  have hR : Continuous fun p : E × ℝ≥0 =>
      ∫ x, ∫ w, g (stopPath x p.2, w) ∂(K (x p.2) : Measure C(ℝ≥0, E))
        ∂(K p.1 : Measure C(ℝ≥0, E)) :=
    continuous_integral_of_continuous_measure hKp
      (G := fun q : C(ℝ≥0, E) × (E × ℝ≥0) =>
        ∫ w, g (stopPath q.1 q.2.2, w) ∂(K (q.1 q.2.2) : Measure C(ℝ≥0, E)))
      (hφ.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))) (C := ‖g‖)
      fun q => hφb (q.1, q.2.2)
  have hext := Continuous.ext_on hQ hL hR (fun q hq => h q hq g)
  exact congrFun hext (z, t)

end Dense

end LatticeProb
