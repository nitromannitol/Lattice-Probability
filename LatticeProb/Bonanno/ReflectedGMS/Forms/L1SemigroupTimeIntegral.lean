/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.L1SemigroupTimeIntegral at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.WeightedL1Semigroup
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1StateTimeIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite-time integrals of the weighted L1 semigroup

The actual reflected process supplies time measurability of the pointwise
weighted semigroup action.  Its L1 contraction then gives product
integrability on finite time intervals and permits an ordinary Fubini
interchange against bounded state tests.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm ReflectedWalk.Theorem16

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [DecidableEq V] [Nontrivial V]

namespace FullNetworkForm

/-- The weighted semigroup action, viewed jointly in real time and state;
negative real times are sent to time zero. -/
noncomputable def weightedL1SemigroupTimeState
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (g : V → ℝ) (p : ℝ × V) : ℝ :=
  weightedL1SemigroupAction G m hm hmsum (Real.toNNReal p.1) g p.2

/-- Finite-time occupation operator for the weighted semigroup. -/
noncomputable def weightedL1SemigroupTimeIntegral
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) (g : V → ℝ) (x : V) : ℝ :=
  ∫ r in Icc 0 (t : ℝ),
    weightedL1SemigroupAction G m hm hmsum (Real.toNNReal r) g x

theorem weightedL1SemigroupAction_eq_integral_dyadicStateObservable
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {g : V → ℝ}
    (hg : Integrable g (vertexSpeedMeasure m)) (r : ℝ) (x : V) :
    weightedL1SemigroupAction G m hm hmsum (Real.toNNReal r) g x =
      ∫ ω, dyadicStateObservable PF g ω r ∂PF.P x := by
  rw [← integral_reflected_at_time_eq_weightedL1SemigroupAction
    h hG hm hmsum (Real.toNNReal r) x g hg]
  apply integral_congr_ae
  filter_upwards [ae_dyadicLimit_eq (h x).2.2.1 (h x).2.2.2.1] with ω hω
  simp only [dyadicStateObservable]
  rw [hω (Real.toNNReal r)]

/-- The finite-time weighted semigroup integrand is jointly measurable in
real time and the countable state space. -/
theorem measurable_weightedL1SemigroupTimeState
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {g : V → ℝ}
    (hg : Integrable g (vertexSpeedMeasure m)) :
    Measurable (weightedL1SemigroupTimeState G m hm hmsum g) := by
  apply measurable_from_prod_countable_left
  intro x
  have hmeas : Measurable (fun r : ℝ ↦
      ∫ ω, dyadicStateObservable PF g ω r ∂PF.P x) :=
    (measurable_uncurry_dyadicStateObservable PF g).stronglyMeasurable
      |>.integral_prod_left.measurable
  rw [show (fun r : ℝ ↦
      weightedL1SemigroupTimeState G m hm hmsum g (r, x)) =
      (fun r : ℝ ↦ ∫ ω, dyadicStateObservable PF g ω r ∂PF.P x) by
    funext r
    exact weightedL1SemigroupAction_eq_integral_dyadicStateObservable
      h hG hm hmsum hg r x]
  exact hmeas

/-- The weighted semigroup integrand is integrable for finite time times the
speed measure. -/
theorem integrable_weightedL1SemigroupTimeState
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {g : V → ℝ}
    (hg : Integrable g (vertexSpeedMeasure m)) (t : ℝ≥0) :
    Integrable (weightedL1SemigroupTimeState G m hm hmsum g)
      ((volume.restrict (Icc 0 (t : ℝ))).prod (vertexSpeedMeasure m)) := by
  let μt : Measure ℝ := volume.restrict (Icc 0 (t : ℝ))
  let F := weightedL1SemigroupTimeState G m hm hmsum g
  have hF : Measurable F :=
    measurable_weightedL1SemigroupTimeState h hG hm hmsum hg
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun r ↦
    integrable_weightedL1SemigroupAction G m hm hmsum
      (Real.toNNReal r) g hg), ?_⟩
  have hinner : StronglyMeasurable (fun r ↦
      ∫ x, ‖F (r, x)‖ ∂vertexSpeedMeasure m) :=
    hF.norm.stronglyMeasurable.integral_prod_right
  apply Integrable.mono (integrable_const
    (μ := μt) (∫ x, ‖g x‖ ∂vertexSpeedMeasure m))
    hinner.aestronglyMeasurable
  filter_upwards with r
  rw [Real.norm_of_nonneg (integral_nonneg_of_ae
      (ae_of_all _ fun x ↦ norm_nonneg (F (r, x)))),
    Real.norm_of_nonneg (integral_nonneg_of_ae
      (ae_of_all _ fun x ↦ norm_nonneg (g x)))]
  exact integral_norm_weightedL1SemigroupAction_le
    G m hm hmsum (Real.toNNReal r) g hg

/-- The finite-time occupation operator maps speed-L1 functions to
speed-L1 functions. -/
theorem integrable_weightedL1SemigroupTimeIntegral
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {g : V → ℝ}
    (hg : Integrable g (vertexSpeedMeasure m)) (t : ℝ≥0) :
    Integrable (weightedL1SemigroupTimeIntegral G m hm hmsum t g)
      (vertexSpeedMeasure m) := by
  exact (integrable_weightedL1SemigroupTimeState
    h hG hm hmsum hg t).integral_prod_right

/-- Fubini for the finite-time occupation operator against a bounded state
test. -/
theorem integral_mul_weightedL1SemigroupTimeIntegral
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {g : V → ℝ}
    (hg : Integrable g (vertexSpeedMeasure m)) (t : ℝ≥0)
    (v : V → ℝ) (C : ℝ) (hC : 0 ≤ C) (hv : ∀ x, ‖v x‖ ≤ C) :
    (∫ x, v x * weightedL1SemigroupTimeIntegral G m hm hmsum t g x
        ∂vertexSpeedMeasure m) =
      ∫ r in Icc 0 (t : ℝ), ∫ x, v x *
        weightedL1SemigroupAction G m hm hmsum (Real.toNNReal r) g x
          ∂vertexSpeedMeasure m := by
  let μt : Measure ℝ := volume.restrict (Icc 0 (t : ℝ))
  let F := weightedL1SemigroupTimeState G m hm hmsum g
  have hF := integrable_weightedL1SemigroupTimeState h hG hm hmsum hg t
  have hvmeas : Measurable v := measurable_of_countable _
  have hprod : Integrable (fun p : ℝ × V ↦ v p.2 * F p)
      (μt.prod (vertexSpeedMeasure m)) := by
    apply Integrable.mono (hF.norm.const_mul C)
      ((hvmeas.comp measurable_snd).mul
        (measurable_weightedL1SemigroupTimeState h hG hm hmsum hg)).aestronglyMeasurable
    filter_upwards with p
    simpa only [Pi.mul_apply, Function.comp_apply, norm_mul, norm_norm,
      Real.norm_of_nonneg hC] using
        (mul_le_mul_of_nonneg_right (hv p.2) (norm_nonneg (F p)))
  rw [integral_integral_swap hprod]
  apply integral_congr_ae
  filter_upwards with x
  simp only [weightedL1SemigroupTimeIntegral]
  rw [integral_const_mul]

end FullNetworkForm
end ReflectedGMS
