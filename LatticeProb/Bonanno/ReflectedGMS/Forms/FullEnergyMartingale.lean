/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergyMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyMartingaleLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreL2Cauchy
import LatticeProb.Bonanno.ReflectedGMS.Forms.L2CauchyAELimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactVertexDynkin
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinSquareCompensation
import LatticeProb.Bonanno.ReflectedGMS.Forms.PredictableJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Process.MartingaleIngredients

/-! The full-domain path limit is an actual L2 martingale under every fixed
vertex starting law. This does not yet identify its full-energy compensator. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V) (U : hilbertDomain G m) (z : V)

include h hG hm hmsum

theorem fullEnergyMartingaleLimit_memLp_and_L2_convergence (t : ℝ≥0) :
    MemLp (fullEnergyMartingaleLimit G m hm PF default U t) 2 (PF.P z) ∧
      Tendsto (fun n ↦ eLpNorm
        (fullEnergyMartingaleApprox G m hm PF default U n t -
          fullEnergyMartingaleLimit G m hm PF default U t) 2 (PF.P z)) atTop (𝓝 0) := by
  have hF := fun n ↦ fullEnergyMartingaleApprox_memLp_two
    h hG hm hmsum default U (PF.P z) n t
  apply memLp_two_and_tendsto_eLpNorm_of_cauchySeq_of_tendsto_ae hF
  · exact countableResolventCore_centeredMartingale_toLp_cauchySeq h hG hm hmsum
      default z U (fullEnergyCoreIndex G m hm U) (fullEnergyCoreIndex_bound G m hm U) t
  · filter_upwards [fullEnergyMartingaleLimit_ae_cadlag_and_uniform
      h hG hm hmsum default U z] with ω hω
    obtain ⟨T, ht⟩ := exists_nat_ge t
    exact (hω.2 T).tendsto_at ⟨zero_le, ht⟩

theorem fullEnergyMartingaleLimit_isMartingale :
    Martingale (fullEnergyMartingaleLimit G m hm PF default U)
      PF.naturalFiltration.rightCont (PF.P z) := by
  apply martingale_of_tendsto_eLpNorm_two
    (fun n ↦ fullEnergyMartingaleApprox_isMartingale h hG hm hmsum default U z n)
    (stronglyAdapted_fullEnergyMartingaleLimit h hG hm hmsum default U)
  · intro t
    exact (fullEnergyMartingaleLimit_memLp_and_L2_convergence
      h hG hm hmsum default U z t).1.integrable (by norm_num)
  · intro t
    exact (fullEnergyMartingaleLimit_memLp_and_L2_convergence
      h hG hm hmsum default U z t).2

end ReflectedGMS
