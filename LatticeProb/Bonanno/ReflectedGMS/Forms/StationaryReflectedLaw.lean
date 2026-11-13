/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryReflectedLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationarySpeedMeasure
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedIdentification

/-! Starting the actual reflected process with its finite speed measure gives
the same speed marginal at every time.  This identifies the mean ordinary-edge
jump rate for every full finite-energy function. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- Existing starting laws regarded as a kernel on the countable vertex set. -/
noncomputable def reflectedStartKernel (PF : ProcessFamily V) : Kernel V PF.Ω :=
  Kernel.ofFunOfCountable PF.P

instance reflectedStartKernel_isMarkov (PF : ProcessFamily V) :
    IsMarkovKernel (reflectedStartKernel PF) :=
  ⟨fun _ => by change IsProbabilityMeasure (PF.P _); infer_instance⟩

/-- The finite, unnormalized law obtained by mixing starting vertices with speed mass. -/
noncomputable def reflectedSpeedLaw (PF : ProcessFamily V) (m : V → ℝ) : Measure PF.Ω :=
  reflectedStartKernel PF ∘ₘ vertexSpeedMeasure m

theorem reflectedSpeedLaw_isFinite (PF : ProcessFamily V) (m : V → ℝ)
    (hmsum : Summable m) : IsFiniteMeasure (reflectedSpeedLaw PF m) := by
  letI := vertexSpeedMeasure_isFinite m hmsum
  unfold reflectedSpeedLaw
  infer_instance

theorem reflectedSpeedLaw_map_position
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (t : ℝ≥0) :
    (reflectedSpeedLaw PF m).map (PF.X t) =
      (vertexSpeedMeasure m).map (some : V → Option V) := by
  have hs : Measurable (some : V → Option V) := measurable_of_countable _
  have hk : (reflectedStartKernel PF).map (PF.X t) =
      (semigroupProbabilityKernel G m hm hmsum t).map (some : V → Option V) := by
    apply DFunLike.ext
    intro z
    rw [Kernel.map_apply _ (PF.measurable_X t), Kernel.map_apply _ hs]
    exact reflected_transitionLaw_eq_semigroupProbabilityKernel h hG hm hmsum t z
  rw [reflectedSpeedLaw, Measure.map_comp _ _ (PF.measurable_X t), hk,
    ← Measure.map_comp _ _ hs, semigroupProbabilityKernel_comp_vertexSpeedMeasure]

end ReflectedGMS
