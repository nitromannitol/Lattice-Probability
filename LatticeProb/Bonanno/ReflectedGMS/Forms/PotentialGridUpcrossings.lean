/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.PotentialGridUpcrossings at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialSupermartingale
import Mathlib.Probability.Martingale.Upcrossing

/-!
# Upcrossing bounds for sampled vertex potentials

Deterministic monotone sampling preserves the supermartingale property.  Applying
Doob's discrete upcrossing inequality to the negative discounted vertex
potential gives a bound independent of both the sample and the horizon.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

/-- The filtration obtained by observing `ℱ` at deterministic monotone times. -/
def sampledFiltration {Ω ι κ : Type*} [Preorder ι] [Preorder κ]
    {m0 : MeasurableSpace Ω} (ℱ : Filtration ι m0) (τ : κ → ι)
    (hτ : Monotone τ) : Filtration κ m0 where
  seq n := ℱ (τ n)
  mono' _ _ hnm := ℱ.mono (hτ hnm)
  le' n := ℱ.le (τ n)

/-- A supermartingale remains a supermartingale after deterministic monotone
sampling, with the correspondingly sampled filtration. -/
theorem Supermartingale.comp_monotone_time
    {Ω ι κ E : Type*} [Preorder ι] [Preorder κ]
    {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LE E]
    {f : ι → Ω → E} {ℱ : Filtration ι m0}
    (hf : Supermartingale f ℱ μ) (τ : κ → ι) (hτ : Monotone τ) :
    Supermartingale (fun n ↦ f (τ n)) (sampledFiltration ℱ τ hτ) μ := by
  refine ⟨fun n ↦ hf.stronglyAdapted (τ n), ?_, fun n ↦ hf.integrable (τ n)⟩
  intro i j hij
  exact hf.condExp_ae_le (hτ hij)

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- The negative discounted vertex potential, sampled at arbitrary deterministic
monotone times, is a discrete submartingale. -/
theorem reflected_vertexOccupationPotential_sampled_submartingale [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y z : V)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    Submartingale
      (fun n ω ↦ -(Real.exp (-alpha * (τ n : ℝ)) *
        (PF.X (τ n) ω).elim 0 (vertexOccupationPotential G m alpha · y)))
      (sampledFiltration PF.naturalFiltration τ hτ) (PF.P z) := by
  have hsuper := reflected_vertexOccupationPotential_supermartingale
    h hG hm hmsum ha y z
  change Submartingale
    (-fun n ω ↦ Real.exp (-alpha * (τ n : ℝ)) *
      (PF.X (τ n) ω).elim 0 (vertexOccupationPotential G m alpha · y))
    (sampledFiltration PF.naturalFiltration τ hτ) (PF.P z)
  exact (ReflectedGMS.Supermartingale.comp_monotone_time hsuper τ hτ).neg

/-- Uniform finite-grid Doob bound for the negative discounted vertex
potential.  The right side depends only on the lower crossing level. -/
theorem reflected_vertexOccupationPotential_sampled_upcrossings_le [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y z : V)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (a b : ℝ) (N : ℕ) :
    (b - a) * ∫ ω, (upcrossingsBefore a b
      (fun n ω ↦ -(Real.exp (-alpha * (τ n : ℝ)) *
        (PF.X (τ n) ω).elim 0 (vertexOccupationPotential G m alpha · y)))
      N ω : ℝ) ∂PF.P z ≤ (-a)⁺ := by
  let Y : ℕ → PF.Ω → ℝ := fun n ω ↦
    -(Real.exp (-alpha * (τ n : ℝ)) *
      (PF.X (τ n) ω).elim 0 (vertexOccupationPotential G m alpha · y))
  have hY : Submartingale Y (sampledFiltration PF.naturalFiltration τ hτ) (PF.P z) := by
    simpa only [Y] using reflected_vertexOccupationPotential_sampled_submartingale
      h hG hm hmsum ha y z τ hτ
  refine (hY.mul_integral_upcrossingsBefore_le_integral_pos_part a b N).trans ?_
  have hbound : ∀ ω, (Y N ω - a)⁺ ≤ (-a)⁺ := by
    intro ω
    apply posPart_mono
    simp only [Y]
    have hz : 0 ≤ Real.exp (-alpha * (τ N : ℝ)) *
        (PF.X (τ N) ω).elim 0 (vertexOccupationPotential G m alpha · y) := by
      cases hx : PF.X (τ N) ω with
      | none => simp
      | some x =>
          exact mul_nonneg (Real.exp_nonneg _)
            (vertexOccupationPotential_nonneg G m hm ha x y)
    linarith
  calc
    (∫ ω, (Y N ω - a)⁺ ∂PF.P z) ≤ ∫ _ω, (-a)⁺ ∂PF.P z := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun ω ↦ posPart_nonneg _
      · exact integrable_const _
      · exact Filter.Eventually.of_forall hbound
    _ = (-a)⁺ := by simp

end ReflectedGMS
