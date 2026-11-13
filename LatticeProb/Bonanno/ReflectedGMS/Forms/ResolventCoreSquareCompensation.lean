/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreSquareCompensation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreInput
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreSquareAlgebra

/-!
# Square compensation on the countable resolvent core

The bounded-input square martingale identifies the auxiliary square process
for a finite rational resolvent coordinate.  The generic square-compensation
assembly then combines that auxiliary martingale with the pathwise square
cancellation and martingale--occupation pairing.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

theorem stronglyAdapted_rawResolventCoreSquareCompensation
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : CountableResolventCoreIndex V) (z : V) :
    StronglyAdapted PF.naturalFiltration (fun t ω ↦
      (rawResolventCoreMartingale PF G m q t ω) ^ 2 -
        adaptedJumpOccupation PF G m
          (countableResolventCoreFeature G m q) t ω) := by
  intro t
  exact (((rawResolventCoreMartingale_isMartingale
    h hG hm hmsum q z).stronglyMeasurable t).pow 2).sub
      (stronglyAdapted_adaptedJumpOccupation PF G m
        (countableResolventCoreFeature G m q) t)

theorem integrable_rawResolventCoreSquareCompensation
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : CountableResolventCoreIndex V)
    (t : ℝ≥0) (z : V) :
    Integrable (fun ω ↦
      (rawResolventCoreMartingale PF G m q t ω) ^ 2 -
        adaptedJumpOccupation PF G m
          (countableResolventCoreFeature G m q) t ω) (PF.P z) := by
  apply Integrable.sub
  · apply Integrable.of_bound
      ((((rawResolventCoreMartingale_isMartingale
        h hG hm hmsum q z).stronglyMeasurable t).pow 2).mono
          (PF.naturalFiltration.le t)).aestronglyMeasurable
      ((countableResolventCoreBound q +
        (t : ℝ) * (2 * countableResolventCoreBound q)) ^ 2)
    filter_upwards [] with ω
    change ‖(rawResolventCoreMartingale PF G m q t ω) ^ 2‖ ≤ _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_rawResolventCoreMartingale_le PF G m hm q (le_refl t) ω) 2
  · exact integrable_adaptedJumpOccupation h hG hm hmsum
      (countableResolventCoreFeature_hasFiniteEnergy G m q) t z

/-- The algebraic auxiliary process is exactly the bounded-input square
martingale for the rational core coordinate. -/
theorem resolventCoreSquareAuxiliary_eq_boundedResolventSquareMartingale
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m)
    (q : CountableResolventCoreIndex V) :
    resolventCoreSquareAuxiliary PF G m q =
      boundedResolventSquareMartingale PF G m (fun x ↦ (q x : ℝ))
        (countableResolventCoreIndex_hasSpeedL2 hm hmsum q) := by
  have hfeature :=
    countableResolventCoreFeature_eq_oneResolventFunction G m hm hmsum q
  have hdrift : resolventCoreSquareDrift G m q =
      boundedResolventSquareDrift G m (fun y ↦ (q y : ℝ))
        (countableResolventCoreIndex_hasSpeedL2 hm hmsum q) := by
    funext p
    cases p with
    | none => simp [resolventCoreSquareDrift, boundedResolventSquareDrift,
        rawResolventCorePotential, resolventCoreDrift]
    | some y =>
        simpa [resolventCoreSquareDrift, rawResolventCorePotential,
          resolventCoreDrift] using
          (boundedResolventSquareDrift_eq_countableResolventCore
            G m hm hmsum q y).symm
  funext t ω
  unfold resolventCoreSquareAuxiliary boundedResolventSquareMartingale
    boundedResolventSquareCompensator
  simp only [rawResolventCorePotential]
  rw [hdrift, hfeature]
  ring

/-- Every raw countable-resolvent-core Dynkin martingale has the exact adapted
ordinary-edge square compensation. -/
theorem rawResolventCoreSquareCompensation_isMartingale
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : CountableResolventCoreIndex V) (z : V) :
    Martingale (fun t ω ↦
      (rawResolventCoreMartingale PF G m q t ω) ^ 2 -
        adaptedJumpOccupation PF G m
          (countableResolventCoreFeature G m q) t ω)
      PF.naturalFiltration (PF.P z) := by
  let N : ℝ≥0 → PF.Ω → ℝ := fun t ω ↦
    (rawResolventCoreMartingale PF G m q t ω) ^ 2 -
      adaptedJumpOccupation PF G m
        (countableResolventCoreFeature G m q) t ω
  let Q := resolventCoreSquareAuxiliary PF G m q
  let K : ℝ≥0 → PF.Ω → ℝ := fun t ω ↦
    rawResolventCoreMartingale PF G m q t ω *
      boundedStateOccupationVersion PF (resolventCoreDrift G m q) t ω
  let J : ℝ≥0 → ℝ≥0 → PF.Ω → ℝ := fun s t ω ↦
    ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
      rawResolventCoreMartingale PF G m q r.toNNReal ω *
        resolventCoreDrift G m q (PF.X r.toNNReal ω)
  have hNa : StronglyAdapted PF.naturalFiltration N :=
    stronglyAdapted_rawResolventCoreSquareCompensation h hG hm hmsum q z
  have hNi (t : ℝ≥0) : Integrable (N t) (PF.P z) :=
    integrable_rawResolventCoreSquareCompensation h hG hm hmsum q t z
  have hQ : Martingale Q PF.naturalFiltration (PF.P z) := by
    change Martingale (resolventCoreSquareAuxiliary PF G m q)
      PF.naturalFiltration (PF.P z)
    rw [resolventCoreSquareAuxiliary_eq_boundedResolventSquareMartingale
      PF G m hm hmsum q]
    exact countableResolventCoreSquareMartingale_isMartingale
      h hG hm hmsum q z
  have hKi (t : ℝ≥0) : Integrable (K t) (PF.P z) :=
    integrable_rawResolventCoreMartingale_mul_occupation
      h hG hm hmsum q z t t
  change Martingale N PF.naturalFiltration (PF.P z)
  exact martingale_of_squareCompensation_increment h z N Q K J hNa hNi hQ hKi
    (fun {_ _} hst ↦ resolventCore_square_cancellation_ae h hm q z hst)
    (fun {_ _} hst {_} hE ↦
      rawResolventCoreMartingale_occupation_product_increment
        h hG hm hmsum q z hst hE)

end ReflectedGMS
