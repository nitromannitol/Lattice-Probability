/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTraceHoldingDivergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.HoldingDivergence
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnPairProcessLaw
import Mathlib.Data.Fintype.Pigeonhole

/-! The true finite-target trace cannot accumulate infinitely many retained
holding times before a finite clock time. Reuse the exponential holding-kernel
divergence theorem; finite support supplies an infinitely recurring vertex. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16
open TargetReturnPairProcessLaw

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

omit [Nontrivial V] in
/-- Finite support suffices for holding divergence; no irreducibility input is
required because every infinite sequence in a finite set repeats a vertex. -/
theorem holdingKernel_ae_tsum_eq_top_of_finite_range
    {w : V → ℝ} (hw : ∀ x, 0 < w x) (A : Finset V)
    (Y : ℕ → V) (hY : ∀ n, Y n ∈ A) :
    ∀ᵐ T ∂holdingKernel w Y, ∑' n, ENNReal.ofReal (T n) = ⊤ := by
  classical
  let f : ℕ → {v // v ∈ A} := fun n => ⟨Y n, hY n⟩
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber f
  have hi : (f ⁻¹' {v}).Infinite := Set.infinite_coe_iff.mp hv
  apply holdingKernel_ae_tsum_ofReal_eq_top hw (z' := v.1)
  intro N
  obtain ⟨k, hk, hNk⟩ := hi.exists_gt N
  exact ⟨k, hNk, congrArg Subtype.val hk⟩

/-- Divergence under the actual finite induced-chain/holding joint law. -/
theorem inducedChainHolding_ae_tsum_eq_top
    (G : ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    {A : Finset V} (hA : A.Nonempty) {x : V} (hx : x ∈ A)
    {w : V → ℝ} (hw : ∀ v, 0 < w v) :
    ∀ᵐ p ∂(MarkovChain.chainLaw (G.inducedKernel hG hA) x ⊗ₘ holdingKernel w),
      ∑' n, ENNReal.ofReal (p.2 n) = ⊤ := by
  have hm : MeasurableSet
      {p : (ℕ → V) × (ℕ → ℝ) | ∑' n, ENNReal.ofReal (p.2 n) = ⊤} :=
    (Measurable.tsum fun n => ENNReal.measurable_ofReal.comp
      ((measurable_pi_apply n).comp measurable_snd)) (measurableSet_singleton ⊤)
  refine Measure.ae_compProd_of_ae_ae hm ?_
  filter_upwards [G.inducedChainLaw_ae_mem hG hA hx] with Y hY
  exact holdingKernel_ae_tsum_eq_top_of_finite_range hw A Y hY

/-- The retained holds extracted from the original reflected walk diverge. -/
theorem targetReturnHolding_ae_tsum_eq_top
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ v, 0 < w v)
    {A : Finset V} (hA : A.Nonempty) {x : V} (hx : x ∈ A) :
    ∀ᵐ ω ∂PF.P x,
      ∑' n, ENNReal.ofReal (targetReturnHoldingSeq PF.X A ω n) = ⊤ := by
  have hd := inducedChainHolding_ae_tsum_eq_top G hG hA hx hw
  rw [← map_targetReturnPair h hG hw hA hx] at hd
  exact ae_of_ae_map (aemeasurable_targetReturnPair h hG hA hx) hd

end ReflectedGMS
