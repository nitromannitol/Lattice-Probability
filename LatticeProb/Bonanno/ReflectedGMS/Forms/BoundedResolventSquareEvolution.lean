/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.BoundedResolventSquareEvolution at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedResolventSquareGenerator
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1SquareDynkin

/-!
# Pointwise square evolution for bounded resolvent inputs

The full-domain weak square-generator identity for the one-resolvent of a
bounded input is upgraded to pointwise speed-`L¹` semigroup evolution.  The
square-generator is only assumed through its proved speed-`L¹` summability.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace NNReal
open MeasureTheory

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [DecidableEq V] [Nontrivial V]

/-- Pointwise Dynkin evolution for the square of the one-resolvent of an
arbitrary bounded input.  The right-hand side uses the weighted `L¹(m)`
semigroup and requires no speed-`L²` membership of the square-generator. -/
theorem boundedResolventSquare_l1_dynkin
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (f : V → ℝ) {A : ℝ}
    (hfBound : ∀ z, |f z| ≤ A) (t : ℝ≥0) (x : V) :
    let hfL2 := hasSpeedL2_of_abs_le hm hmsum hfBound
    let u := oneResolventFunction G m (weightedValue m f hfL2)
    let g2 := boundedResolventSquareGenerator G m f hfL2
    weightedL1SemigroupAction G m hm hmsum t (u ^ 2) x - (u x) ^ 2 =
      weightedL1SemigroupTimeIntegral G m hm hmsum t g2 x := by
  classical
  dsimp only
  let hfL2 : HasSpeedL2 m f := hasSpeedL2_of_abs_le hm hmsum hfBound
  let u : V → ℝ := oneResolventFunction G m (weightedValue m f hfL2)
  let uSq : V → ℝ := u ^ 2
  let g2 : V → ℝ := boundedResolventSquareGenerator G m f hfL2
  obtain ⟨N, huBound⟩ := boundedInput_oneResolvent_bounded
    G m hm hmsum f hfBound
  have huBound' (z : V) : |u z| ≤ max N 0 :=
    (huBound z).trans (le_max_left N 0)
  have huSqBound (z : V) : |uSq z| ≤ (max N 0) ^ 2 := by
    dsimp only [uSq]
    rw [Pi.pow_apply, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg (u z)) (huBound' z) 2
  let huSqL2 : HasSpeedL2 m uSq :=
    hasSpeedL2_of_abs_le hm hmsum huSqBound
  have huE : G.HasFiniteEnergy u := by
    exact boundedInput_oneResolvent_hasFiniteEnergy G m hm hmsum f hfBound
  have huSqE : G.HasFiniteEnergy uSq := by
    simpa only [uSq, pow_two] using
      hasFiniteEnergy_mul_of_bounded G huBound' huBound' huE huE
  have huSq : Integrable uSq (vertexSpeedMeasure m) := by
    haveI : IsFiniteMeasure (vertexSpeedMeasure m) :=
      vertexSpeedMeasure_isFinite m hmsum
    apply Integrable.mono (integrable_const ((max N 0) ^ 2))
      (measurable_of_countable _).aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (max N 0))]
    exact huSqBound z
  have hg2sum : Summable (fun z ↦ m z * g2 z) := by
    exact summable_speed_mul_boundedResolventSquareGenerator
      G m hm hmsum f hfBound
  have hg2 : Integrable g2 (vertexSpeedMeasure m) :=
    integrable_vertexSpeedMeasure_of_summable_speed_mul m hm g2 hg2sum
  have hweakTests : ∀ {beta : ℝ}, 0 < beta → ∀ (s : ℝ≥0) (a : V),
      ⟪vertexOccupationPotentialValue G m beta a,
        fullFormSemigroup G m s (weightedValue m uSq huSqL2) -
          weightedValue m uSq huSqL2⟫_ℝ =
        ∫ r : ℝ in (0 : ℝ)..(s : ℝ),
          ∑' z : V, m z * g2 z *
            unweight m (fullFormSemigroup G m (Real.toNNReal r)
              (vertexOccupationPotentialValue G m beta a)) z := by
    intro beta hb s a
    refine fullEnergyFunction_weak_dynkin G m hm hmsum
      uSq g2 huSqL2 huSqE ?_ hb s a
    intro v B hvBound hvE
    simpa only [uSq, u, g2, hfL2] using
      boundedResolvent_squareGenerator_weak
        G m hm hmsum f hfBound v hvBound hvE
  have hevolution := l1_dynkin_of_vertexResolvent_weak_dynkin
    h hG hm hmsum uSq g2 huSqL2 huSq hg2 hweakTests t x
  simpa only [uSq, u, g2, hfL2, Pi.pow_apply] using hevolution

end ReflectedGMS
