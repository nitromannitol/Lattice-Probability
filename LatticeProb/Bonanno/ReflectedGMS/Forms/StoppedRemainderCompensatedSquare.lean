/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedRemainderCompensatedSquare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedRemainderVanishing
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergySquareCompensation

/-!
# Bracket atom 2 on the fast clock: the stopped compensated square is a martingale

**The fast-side content of `DiagonalCompensatedSquares`** (`Limit/BracketClausesScalarReduction`),
in the shape of the drift elimination
`StoppedFormAssociationFastStopped.martingale_stopped_fullEnergyPath_exit_completed`: for a
bounded full-domain vector `U` spatially harmonic on `A` and the actual spatial exit time
`τ = exitHitting PF A`,

`(P^τ)² − ⟨U⟩^τ`  is a martingale of the completed fast filtration,

where `P` is the full-energy path of `U` and `⟨U⟩ = adaptedJumpOccupation PF G m u` is the
canonical ordinary-edge occupation (the predictable square compensator of the Fukushima
martingale `M`, `fullEnergyMartingaleLimit_squareCompensation_isMartingale`).

The proof is exactly the manuscript's: `M² − ⟨U⟩` is a martingale, stopping preserves this, and
`P^τ = M^τ` by the stopped zero-energy statement
`StoppedRemainder.ae_forall_stopped_fullEnergyPath_eq_martingale_exitHitting`.  Everything is
on the summable fast speed; the transfer to the area clock is the clock change of
`StoppedFormAssociationOptionalSampling`, as for atom 1.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS.StoppedRemainder

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open ReflectedGMS.StoppedFormAssociation ReflectedGMS.MartingaleLimit

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default z : V) (U : hilbertDomain G m) (A : Set V)
  {enc : Option V → ℕ} (henc : Function.Injective enc)
  (X' : ℝ≥0 → PF.Ω → ℕ) (hX'e : ∀ t ω, X' t ω = enc (PF.X t ω))
  (hX' : ∀ t, Measurable (X' t))

include h hG hm hmsum

/-- The compensated square `M² − ⟨U⟩` has almost surely right-continuous paths. -/
theorem ae_isRightContinuous_compensatedSquare :
    ∀ᵐ ω ∂PF.P z, IsRightContinuous (fun t ↦
      (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 -
        adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)) t ω) := by
  filter_upwards [fullEnergyMartingaleLimit_ae_cadlag_and_uniform h hG hm hmsum default U z,
    adaptedJumpOccupation_ae_zero_continuous_boundedVariation h hG hm hmsum
      (hilbertDomain_hasFiniteEnergy G m U) z] with ω hM hA
  intro a
  exact ((hM.1.isRightContinuous a).pow 2).sub hA.2.1.continuousAt.continuousWithinAt

include henc hX'e

/-- **`M² − ⟨U⟩` is a martingale of the completed fast filtration.** -/
theorem martingale_compensatedSquare_completed :
    Martingale (fun t (ω : NullMeasurableSpace PF.Ω (PF.P z)) ↦
        (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 -
          adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)) t ω)
      (ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX') (PF.P z).completion := by
  have hK := fullEnergyMartingaleLimit_squareCompensation_isMartingale h hG hm hmsum default U z
  have hFeq := rightCont_natural_enc_eq_naturalFiltration_rightCont henc X' hX'e hX'
  refine martingale_completedNaturalFiltration_of_rightCont_setIntegral hX'
    (Y := fun t ω ↦ (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 -
      adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)) t ω)
    (fun t ↦ hK.integrable t) ?_ (ae_isRightContinuous_compensatedSquare h hG hm hmsum default z U)
    ?_
  · intro t
    rw [hFeq t]
    exact (hK.stronglyMeasurable t).aestronglyMeasurable
  · intro s t hst B hB
    rw [hFeq s] at hB
    exact (hK.setIntegral_eq hst hB).symm

/-- **Bracket atom 2 on the fast clock.**  For `U` bounded and spatially harmonic on `A`, the
stopped full-energy path `P^τ` and the stopped canonical occupation `⟨U⟩^τ` at the actual exit
time `τ = exitHitting PF A` satisfy: `(P^τ)² − ⟨U⟩^τ` is a martingale of the completed fast
filtration under the completed starting law. -/
theorem martingale_stopped_fullEnergyPath_compensatedSquare_exit_completed {C : ℝ}
    (hPb : ∀ z : V, ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ C)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0) :
    Martingale (fun t (ω : NullMeasurableSpace PF.Ω (PF.P z)) ↦
        (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
          (exitHitting PF A) t ω) ^ 2 -
          stoppedProcess (adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)))
            (exitHitting PF A) t ω)
      (ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX') (PF.P z).completion := by
  have hK := martingale_compensatedSquare_completed h hG hm hmsum default z U henc X' hX'e hX'
  have hτ := isStoppingTime_completed_exitHitting h z A henc X' hX'e hX'
  have hrc : ∀ᵐ ω : NullMeasurableSpace PF.Ω (PF.P z) ∂(PF.P z).completion,
      IsRightContinuous (fun t ↦ (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 -
        adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)) t ω) :=
    ae_completion_of_ae (ae_isRightContinuous_compensatedSquare h hG hm hmsum default z U)
  -- the stopped compensated square of `M`
  have hS := ProcessFiltration.stoppedProcess_martingale_completedNaturalFiltration (PF.P z) X' hX'
    hK hτ hrc
  -- identification with the stopped compensated square of `P`
  have hae : ∀ t, (fun ω : NullMeasurableSpace PF.Ω (PF.P z) ↦
      stoppedProcess (fun t ω ↦ (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 -
        adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)) t ω)
        (exitHitting PF A) t ω) =ᵐ[(PF.P z).completion]
      fun ω ↦ (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
          (exitHitting PF A) t ω) ^ 2 -
          stoppedProcess (adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)))
            (exitHitting PF A) t ω := by
    intro t
    refine ae_completion_of_ae ?_
    filter_upwards [ae_forall_stopped_fullEnergyPath_eq_martingale_exitHitting
      h hG hm hmsum default U A hPb hU z] with ω hω
    simp only [stoppedProcess]
    have := hω t
    simp only [stoppedProcess] at this
    rw [this]
  refine hS.congr (fun t ↦ ?_) hae
  exact LocalMartingaleCombination.stronglyMeasurable_of_ae_eq_of_null_events
    ((ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX').le t)
    (ProcessFiltration.measurableSet_completedNaturalFiltration_of_null (PF.P z) X' hX' t)
    (hS.stronglyMeasurable t) (hae t)

/-- Bracket atom 2 on the fast clock for a globally bounded vector. -/
theorem martingale_stopped_fullEnergyPath_compensatedSquare_exit_completed_of_bounded {C : ℝ}
    (hC : ∀ x, |unweight m (valueInclusion G m U) x| ≤ C)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    :
    Martingale (fun t (ω : NullMeasurableSpace PF.Ω (PF.P z)) ↦
        (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
          (exitHitting PF A) t ω) ^ 2 -
          stoppedProcess (adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)))
            (exitHitting PF A) t ω)
      (ProcessFiltration.completedNaturalFiltration (PF.P z) X' hX') (PF.P z).completion :=
  martingale_stopped_fullEnergyPath_compensatedSquare_exit_completed h hG hm hmsum default z U A
    henc X' hX'e hX' (fun z ↦ stoppedPath_bound_of_bounded h hG hm hmsum default U A hC z) hU

end ReflectedGMS.StoppedRemainder
