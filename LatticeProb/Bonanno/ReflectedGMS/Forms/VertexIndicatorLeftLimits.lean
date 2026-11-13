/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexIndicatorLeftLimits at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceHoldingDivergence
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnClockCompatibility
import Mathlib.Topology.Order.Cadlag

/-!
# Left limits of the vertex-indicator coordinates

Finite-target return times decompose every bounded time interval into retained
holding intervals and excursions outside the target.  Divergence of the
retained holding clock prevents those intervals from accumulating at a finite
time.  Taking the target to contain the initial and tested vertices therefore
makes each tested vertex indicator locally constant immediately to the left of
every positive time.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16
open TargetReturnRecursion TargetReturnPairProcessLaw
open TargetReturnClockCompatibility

universe u

variable {V Ω : Type u} [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- A finite-target return decomposition with positive retained holds and
divergent retained clock makes every target-vertex indicator locally constant
immediately to the left of each positive time. -/
theorem exists_vertexIndicator_leftLimit_of_targetReturns [DecidableEq V]
    {X : ℝ≥0 → Ω → Option V} {A : Finset V} {ω : Ω} {y default : V}
    (hy : y ∈ A)
    (hfin : ∀ n, targetReturnTime X A n ω ≠ ⊤)
    (hreturn : ∀ n,
      stoppedValue X (targetReturnTime X A n) ω ∈ some '' (A : Set V))
    (hpos : ∀ n, 0 < exitAfter X (targetReturnTime X A n) ω -
      targetReturnTime X A n ω)
    (hdiv : ∑' n, ENNReal.ofReal ((targetReturnPair X A default ω).2 n) = ⊤)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ, Tendsto (fun s => if X s ω = some y then (1 : ℝ) else 0)
      (𝓝[<] t) (𝓝 l) := by
  have hstrict (n : ℕ) :
      targetReturnAt X A n ω < targetExitAt X A n ω := by
    rw [← WithTop.coe_lt_coe, coe_targetReturnAt (hfin n),
      coe_targetExitAt (targetExit_ne_top (hfin (n + 1)))]
    exact (tsub_pos_iff_lt).1 (hpos n)
  obtain ⟨n, hnt, htnext⟩ :=
    exists_targetReturn_interval (default := default) hfin hreturn hdiv t
  rcases hnt.lt_or_eq with hnt | hnt
  · by_cases hte : t ≤ targetExitAt X A n ω
    · refine ⟨if stoppedValue X (targetReturnTime X A n) ω = some y then 1 else 0,
        tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hnt] with s hs
      rw [eq_stoppedValue_of_mem_target_hold hfin hs.1.le (hs.2.trans_le hte)]
    · have het : targetExitAt X A n ω < t := lt_of_not_ge hte
      refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT het] with s hs
      have hsout := notMem_target_of_between_exit_return hfin hs.1.le
        (hs.2.trans htnext)
      have hsne : X s ω ≠ some y := by
        intro hsy
        exact hsout ⟨y, Finset.mem_coe.2 hy, hsy.symm⟩
      simp [hsne]
  · have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exfalso
        rw [targetReturnAt_zero] at hnt
        exact (ne_of_gt ht) hnt.symm
      · exact hn
    let m := n - 1
    have hmn : m + 1 = n := by
      dsimp [m]
      omega
    have hexit_le : targetExitAt X A m ω ≤ t := by
      rw [← hnt, ← hmn]
      exact targetExitAt_le_succ hfin
    rcases hexit_le.lt_or_eq with hexit | hexit
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hexit] with s hs
      have hsout := notMem_target_of_between_exit_return (n := m) hfin hs.1.le ?_
      · have hsne : X s ω ≠ some y := by
          intro hsy
          exact hsout ⟨y, Finset.mem_coe.2 hy, hsy.symm⟩
        simp [hsne]
      · rw [hmn, hnt]
        exact hs.2
    · have hmret : targetReturnAt X A m ω < t := (hstrict m).trans_eq hexit
      refine ⟨if stoppedValue X (targetReturnTime X A m) ω = some y then 1 else 0,
        tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hmret] with s hs
      rw [eq_stoppedValue_of_mem_target_hold (n := m) hfin hs.1.le]
      exact hs.2.trans_le hexit.ge

/-- Under the actual reflected-walk law, one full-probability event gives a
left limit for every vertex indicator at every positive time. -/
theorem reflected_vertexIndicators_ae_tendsto_nhdsLT [DecidableEq V]
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ v, 0 < w v) (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ y : V, ∀ t : ℝ≥0, 0 < t →
      ∃ l : ℝ, Tendsto
        (fun s => if PF.X s ω = some y then (1 : ℝ) else 0)
        (𝓝[<] t) (𝓝 l) := by
  rw [ae_all_iff]
  intro y
  let A : Finset V := {z, y}
  have hA : A.Nonempty := ⟨z, by simp [A]⟩
  have hzA : z ∈ A := by simp [A]
  have hyA : y ∈ A := by simp [A]
  filter_upwards
    [ae_forall_targetReturnTime_finite_mem h hG hA hzA,
      ae_forall_targetHolding_pos h hG hw hA hzA,
      targetReturnHolding_ae_tsum_eq_top h hG hw hA hzA] with ω hret hpos hdiv
  intro t ht
  exact exists_vertexIndicator_leftLimit_of_targetReturns
    (default := z) hyA (fun n => (hret n).1) (fun n => (hret n).2)
      hpos hdiv t ht

end ReflectedGMS
