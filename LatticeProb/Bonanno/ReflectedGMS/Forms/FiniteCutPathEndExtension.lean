/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteCutPathEndExtension at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexIndicatorLeftLimits
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexIndicatorRightContinuity
import LatticeProb.Bonanno.ReflectedGMS.Forms.EndLabelConstruction

/-!
# Finite-cut exclusion at nonvertex times

Actual reflected paths avoid every finite vertex cut on a two-sided
neighborhood of each nonvertex time. The return decomposition supplies the
left side; the ordinary exit law rules out a nonvertex at a holding endpoint.
Component stabilization across cut-free excursions remains a separate step
before `EndLabelConstruction` can be applied.
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.FiniteCutPathEndExtension
open ReflectedWalk ReflectedWalk.Theorem16
open TargetReturnRecursion TargetReturnPairProcessLaw TargetReturnClockCompatibility
open TargetReturnConditional

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]
variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- The ordinary exit following a finite stopped vertex is again a vertex. -/
theorem ae_exitAfter_defined_on_stopEvent
    (h : IsReflectedWalk G w hmin PF) (hG : G.toSimpleGraph.Connected) (z x : V)
    {τ : PF.Ω → WithTop ℝ≥0} (hτm : AEMeasurable τ (PF.P z))
    (hτ : IsAEStoppingTime PF.naturalFiltration (PF.P z) τ) :
    ∀ᵐ ω ∂PF.P z, ω ∈ stopEvent PF.X τ x →
      ∃ v, stoppedValue PF.X (exitAfter PF.X τ) ω = some v := by
  classical
  let ρ := hitAfter PF.X {s : Option V | s ≠ some x} τ
  let K := stopEvent PF.X τ x
  let J : V → Set PF.Ω := fun v => K ∩ stopEvent PF.X ρ v
  have hii := (h z).2.2.1
  have hR := (h z).2.2.2.1
  have hρm : AEMeasurable ρ (PF.P z) :=
    aemeasurable_hitAfter PF.measurable_X hii hR (admissibleTarget_ne x) hτm
  have hnull (σ : PF.Ω → WithTop ℝ≥0) (hσ : AEMeasurable σ (PF.P z)) (v : V) :
      NullMeasurableSet (stopEvent PF.X σ v) (PF.P z) := by
    refine (nullMeasurableSet_stopEvent PF.measurable_X hii hR hσ.measurable_mk v).congr ?_
    filter_upwards [hσ.ae_eq_mk] with ω hω
    simp only [stopEvent, Set.mem_setOf_eq, stoppedValue, hω]
  have hJ (v : V) : NullMeasurableSet (J v) (PF.P z) :=
    (hnull τ hτm x).inter (hnull ρ hρm v)
  have hJJ : ∀ ⦃v v' : V⦄, v ≠ v' → AEDisjoint (PF.P z) (J v) (J v') := by
    intro v v' hvv'
    apply Disjoint.aedisjoint
    exact Set.disjoint_left.2 fun ω hv hv' =>
      hvv' (Option.some.inj (hv.2.2.symm.trans hv'.2.2))
  have hmeasureJ (v : V) : PF.P z (J v) =
      PF.P z K * ENNReal.ofReal (G.c x v / G.pi x) := by
    have hm := measure_exitPair_completed h hG z hτm hτ
      (aemeasurableSetStopped_univ hτ) (A := {x}) (x := x) (by simp) (by simp)
      MeasurableSet.univ v
    rw [map_toWithTop_expMeasure_univ h x, one_mul] at hm
    simpa [J, K, ρ] using hm
  have hmeasureJU : PF.P z (⋃ v, J v) = PF.P z K := by
    rw [measure_iUnion₀ hJJ hJ]
    simp_rw [hmeasureJ]
    rw [ENNReal.tsum_mul_left, tsum_ofReal_step hG x, mul_one]
  have hsub : (⋃ v, J v) ⊆ K := by
    intro ω hω
    obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hω
    exact hv.1
  have heq : (⋃ v, J v) =ᵐ[PF.P z] K :=
    ae_eq_of_subset_of_measure_ge hsub hmeasureJU.ge
      (NullMeasurableSet.iUnion hJ) (measure_ne_top _ _)
  filter_upwards [heq] with ω hω hx
  have hj : ω ∈ ⋃ v, J v := by rwa [hω]
  obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hj
  refine ⟨v, ?_⟩
  have he : exitAfter PF.X τ ω = ρ ω := by rw [exitAfter, hx.2]
  simpa only [stoppedValue, he] using hv.2.2

/-- All exits of the finite-target return decomposition are vertex-valued. -/
theorem ae_targetExitAt_defined
    (h : IsReflectedWalk G w hmin PF) (hG : G.toSimpleGraph.Connected)
    {A : Finset V} (hA : A.Nonempty) {z : V} (hz : z ∈ A) :
    ∀ᵐ ω ∂PF.P z, ∀ n, ∃ v, PF.X (targetExitAt PF.X A n ω) ω = some v := by
  have hall := ae_forall_targetReturnTime_finite_mem h hG hA hz
  have hex : ∀ᵐ ω ∂PF.P z, ∀ n x,
      ω ∈ stopEvent PF.X (targetReturnTime PF.X A n) x →
      ∃ v, stoppedValue PF.X (exitAfter PF.X (targetReturnTime PF.X A n)) ω = some v := by
    exact ae_all_iff.2 fun n => ae_all_iff.2 fun x =>
      ae_exitAfter_defined_on_stopEvent h hG z x
        (aemeasurable_targetReturnTime h hG hA hz n)
        (isAEStoppingTime_targetReturnTime h hG hA hz n)
  filter_upwards [hall, hex] with ω hret hex n
  obtain ⟨x, -, hx⟩ := (hret n).2
  obtain ⟨v, hv⟩ := hex n x ⟨(hret n).1, hx.symm⟩
  exact ⟨v, hv⟩

/-- A nonvertex time lies strictly inside a target-free excursion. -/
theorem eventually_notMem_finiteCut_of_targetReturns
    {Ω : Type u} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → Option V}
    {A : Finset V} {ω : Ω} {default : V}
    (hfin : ∀ n, targetReturnTime X A n ω ≠ ⊤)
    (hreturn : ∀ n, stoppedValue X (targetReturnTime X A n) ω ∈ some '' (A : Set V))
    (hexit : ∀ n, ∃ v, X (targetExitAt X A n ω) ω = some v)
    (hdiv : ∑' n, ENNReal.ofReal ((targetReturnPair X A default ω).2 n) = ⊤)
    {t : ℝ≥0} (ht : X t ω = none) :
    ∀ᶠ s in 𝓝 t, X s ω ∉ some '' (A : Set V) := by
  obtain ⟨n, hnt, htnext⟩ := exists_targetReturn_interval hfin hreturn hdiv t
  have hte : targetExitAt X A n ω < t := by
    by_contra hte
    rcases (le_of_not_gt hte).lt_or_eq with hlt | heq
    · have he := eq_stoppedValue_of_mem_target_hold hfin hnt hlt
      obtain ⟨v, -, hv⟩ := hreturn n
      rw [ht] at he
      have hfalse := he.trans hv.symm
      cases hfalse
    · obtain ⟨v, hv⟩ := hexit n
      rw [← heq, ht] at hv
      contradiction
  filter_upwards [Ioo_mem_nhds hte htnext] with s hs
  exact notMem_target_of_between_exit_return hfin hs.1.le hs.2

/-- One event of full probability gives two-sided avoidance of every finite
cut at every nonvertex time of the actual reflected path. -/
theorem reflected_ae_eventually_notMem_finiteCut
    (h : IsReflectedWalk G w hmin PF) (hG : G.toSimpleGraph.Connected)
    (hw : ∀ v, 0 < w v) (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ t, PF.X t ω = none → ∀ K : Finset V,
      ∀ᶠ s in 𝓝 t, PF.X s ω ∉ some '' (K : Set V) := by
  classical
  have hcut : ∀ K : Finset V, ∀ᵐ ω ∂PF.P z, ∀ t, PF.X t ω = none →
      ∀ᶠ s in 𝓝 t, PF.X s ω ∉ some '' (K : Set V) := by
    intro K
    let A := insert z K
    have hz : z ∈ A := by simp [A]
    have hA : A.Nonempty := ⟨z, hz⟩
    filter_upwards [ae_forall_targetReturnTime_finite_mem h hG hA hz,
      ae_targetExitAt_defined h hG hA hz,
      targetReturnHolding_ae_tsum_eq_top h hG hw hA hz] with ω hret hex hdiv t ht
    filter_upwards [eventually_notMem_finiteCut_of_targetReturns
      (default := z) (fun n => (hret n).1) (fun n => (hret n).2) hex hdiv ht] with s hs
    intro hmem
    apply hs
    obtain ⟨v, hv, hvx⟩ := hmem
    exact ⟨v, Finset.mem_insert_of_mem hv, hvx⟩
  filter_upwards [ae_all_iff.2 hcut] with ω hω t ht K
  exact hω K t ht

end ReflectedGMS.FiniteCutPathEndExtension
