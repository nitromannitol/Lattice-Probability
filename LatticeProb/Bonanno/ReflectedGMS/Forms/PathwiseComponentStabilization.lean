/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.PathwiseComponentStabilization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CutFreeComponentStabilization
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteCutPathEndExtension

/-! # Finite-cut components along actual reflected paths -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.PathwiseComponentStabilization

open ReflectedWalk ReflectedWalk.Theorem16
open TargetReturnKernelLaw TargetReturnRecursion TargetReturnPairProcessLaw
open TargetReturnClockCompatibility TargetReturnConditional

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]
variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- Every successive retained return respects each component outside a cut
retained in the target. This is a consequence of the actual process law. -/
theorem ae_targetReturn_no_component_switch
    (h : IsReflectedWalk G w hmin PF) (hG : G.toSimpleGraph.Connected)
    {A K : Finset V} (hA : A.Nonempty) (hKA : K ⊆ A) {z : V} (hz : z ∈ A) :
    ∀ᵐ ω ∂PF.P z, ∀ n (C : G.toSimpleGraph.ComponentCompl (K : Set V)) (x y : V),
      stoppedValue PF.X (targetReturnTime PF.X A n) ω = some x →
      stoppedValue PF.X (targetReturnTime PF.X A (n + 1)) ω = some y →
      x ∈ C → y ∉ K → y ∈ C := by
  classical
  haveI : Countable (G.toSimpleGraph.ComponentCompl (K : Set V)) := by
    unfold SimpleGraph.ComponentCompl SimpleGraph.ConnectedComponent
    infer_instance
  have hpair : ∀ᵐ ω ∂PF.P z, ∀ n (C : G.toSimpleGraph.ComponentCompl (K : Set V))
      (x y : V), x ∈ A → y ∈ A → x ∈ C → y ∉ K → y ∉ C →
      ¬ (ω ∈ stopEvent PF.X (targetReturnTime PF.X A n) x ∧
        ω ∈ stopEvent PF.X (targetReturnTime PF.X A (n + 1)) y) := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun C =>
      ae_all_iff.2 fun x => ae_all_iff.2 fun y => ?_
    by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · by_cases hxC : x ∈ C
        · by_cases hyK : y ∉ K
          · by_cases hyC : y ∉ C
            · have hτ := isAEStoppingTime_targetReturnTime h hG hA hz n
              have hm := measure_targetReturn_completed h hG z
                (aemeasurable_targetReturnTime h hG hA hz n) hτ
                (aemeasurableSetStopped_univ hτ) hA hxA hyA MeasurableSet.univ
              rw [CutFreeComponentStabilization.inducedTransProb_eq_zero_of_separated
                G hG hA hKA C hxA hyA hxC hyK hyC] at hm
              have hzero : PF.P z {ω | ω ∈ stopEvent PF.X (targetReturnTime PF.X A n) x ∧
                  ω ∈ stopEvent PF.X (targetReturnTime PF.X A (n + 1)) y} = 0 := by
                simpa [targetReturnTime, stopEvent, Set.setOf_and] using hm
              have hae : ∀ᵐ ω ∂PF.P z,
                  ¬ (ω ∈ stopEvent PF.X (targetReturnTime PF.X A n) x ∧
                    ω ∈ stopEvent PF.X (targetReturnTime PF.X A (n + 1)) y) := by
                simpa only [ae_iff, not_not] using hzero
              exact hae.mono fun _ hω _ _ _ _ _ => hω
            · exact Filter.Eventually.of_forall fun _ _ _ _ _ hbad => (hyC hbad).elim
          · exact Filter.Eventually.of_forall fun _ _ _ _ hbad => (hyK hbad).elim
        · exact Filter.Eventually.of_forall fun _ _ _ hbad => (hxC hbad).elim
      · exact Filter.Eventually.of_forall fun _ _ hbad => (hyA hbad).elim
    · exact Filter.Eventually.of_forall fun _ hbad => (hxA hbad).elim
  filter_upwards [hpair, ae_forall_targetReturnTime_finite_mem h hG hA hz]
    with ω hpair hret n C x y hx hy hxC hyK
  by_contra hyC
  obtain ⟨x', hxA, hx'⟩ := (hret n).2
  obtain ⟨y', hyA, hy'⟩ := (hret (n + 1)).2
  have hxx : x' = x := Option.some.inj (hx'.trans hx)
  have hyy : y' = y := Option.some.inj (hy'.trans hy)
  subst x'
  subst y'
  exact hpair n C x y hxA hyA hxC hyK hyC ⟨⟨(hret n).1, hx⟩, ⟨(hret (n + 1)).1, hy⟩⟩


/-- On a cut-free interval, finite induction over retained return indices
transports component membership between its vertex-valued endpoints. -/
theorem component_of_cut_free_interval_of_targetReturns
    {Ω : Type u} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → Option V}
    {A K : Finset V} {ω : Ω} {default : V}
    (hfin : ∀ n, targetReturnTime X A n ω ≠ ⊤)
    (hreturn : ∀ n, stoppedValue X (targetReturnTime X A n) ω ∈ some '' (A : Set V))
    (hdiv : ∑' n, ENNReal.ofReal ((targetReturnPair X A default ω).2 n) = ⊤)
    (hswitch : ∀ n (C : G.toSimpleGraph.ComponentCompl (K : Set V)) (x y : V),
      stoppedValue X (targetReturnTime X A n) ω = some x →
      stoppedValue X (targetReturnTime X A (n + 1)) ω = some y →
      x ∈ C → y ∉ K → y ∈ C)
    {s t : ℝ≥0} (hst : s ≤ t) {x y : V} (hxA : x ∈ A) (hyA : y ∈ A)
    (hx : X s ω = some x) (hy : X t ω = some y)
    (hcut : ∀ u ∈ Icc s t, X u ω ∉ some '' (K : Set V))
    (C : G.toSimpleGraph.ComponentCompl (K : Set V)) (hxC : x ∈ C) : y ∈ C := by
  obtain ⟨i, his, hsi⟩ := exists_targetReturn_interval hfin hreturn hdiv s
  obtain ⟨j, hjt, htj⟩ := exists_targetReturn_interval hfin hreturn hdiv t
  have hsExit : s < targetExitAt X A i ω := by
    by_contra hn
    exact notMem_target_of_between_exit_return hfin (le_of_not_gt hn) hsi
      ⟨x, hxA, hx.symm⟩
  have htExit : t < targetExitAt X A j ω := by
    by_contra hn
    exact notMem_target_of_between_exit_return hfin (le_of_not_gt hn) htj
      ⟨y, hyA, hy.symm⟩
  have hxi : stoppedValue X (targetReturnTime X A i) ω = some x :=
    (eq_stoppedValue_of_mem_target_hold hfin his hsExit).symm.trans hx
  have hyj : stoppedValue X (targetReturnTime X A j) ω = some y :=
    (eq_stoppedValue_of_mem_target_hold hfin hjt htExit).symm.trans hy
  have hij : i ≤ j := by
    by_contra hn
    have hji : j + 1 ≤ i := Nat.lt_iff_add_one_le.1 (lt_of_not_ge hn)
    exact (not_lt_of_ge ((targetReturnAt_mono hfin hji).trans (his.trans hst))) htj
  have hprop : ∀ k, i ≤ k → k ≤ j → ∀ v,
      stoppedValue X (targetReturnTime X A k) ω = some v → v ∈ C := by
    intro k hik
    induction k, hik using Nat.le_induction with
    | base =>
        intro _ v hv
        have hvx : v = x := Option.some.inj (hv.symm.trans hxi)
        simpa only [hvx] using hxC
    | succ k hik ih =>
        intro hkj v hv
        obtain ⟨a, _, ha⟩ := hreturn k
        have haC : a ∈ C := ih (Nat.le_trans (Nat.le_succ k) hkj) a ha.symm
        have hsv : s ≤ targetReturnAt X A (k + 1) ω :=
          hsi.le.trans (targetReturnAt_mono hfin (Nat.add_le_add_right hik 1))
        have hvt : targetReturnAt X A (k + 1) ω ≤ t :=
          (targetReturnAt_mono hfin hkj).trans hjt
        have hvK : v ∉ K := by
          intro hvK
          exact hcut _ ⟨hsv, hvt⟩ ⟨v, hvK, hv.symm⟩
        exact hswitch k C a v ha.symm hv haC hvK
  exact hprop j hij le_rfl y hyj


/-- Simultaneously for all finite cuts and all real interval endpoints, the
actual reflected path cannot change complement components without hitting the cut. -/
theorem ae_component_of_cut_free_interval
    (h : IsReflectedWalk G w hmin PF) (hG : G.toSimpleGraph.Connected)
    (hw : ∀ v, 0 < w v) (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ (K : Finset V) (x y : V) (s t : ℝ≥0)
      (C : G.toSimpleGraph.ComponentCompl (K : Set V)),
      s ≤ t → PF.X s ω = some x → PF.X t ω = some y →
      (∀ u ∈ Icc s t, PF.X u ω ∉ some '' (K : Set V)) → x ∈ C → y ∈ C := by
  classical
  refine ae_all_iff.2 fun K => ae_all_iff.2 fun x => ae_all_iff.2 fun y => ?_
  let A := insert z (insert x (insert y K))
  have hz : z ∈ A := by simp [A]
  have hA : A.Nonempty := ⟨z, hz⟩
  have hxA : x ∈ A := by simp [A]
  have hyA : y ∈ A := by simp [A]
  have hKA : K ⊆ A := by intro v hv; simp [A, hv]
  filter_upwards [ae_forall_targetReturnTime_finite_mem h hG hA hz,
    targetReturnHolding_ae_tsum_eq_top h hG hw hA hz,
    ae_targetReturn_no_component_switch h hG hA hKA hz]
    with ω hret hdiv hswitch s t C hst hx hy hcut hxC
  exact component_of_cut_free_interval_of_targetReturns (default := z)
    (fun n => (hret n).1) (fun n => (hret n).2) hdiv hswitch
    hst hxA hyA hx hy hcut C hxC

/-- A single event of full probability supplies the finite-cut stabilization
premise used by the end-label construction, from the actual reflected-walk law. -/
theorem reflected_ae_hasFiniteCutStabilization
    (F : IndexedCells V) {hminF : F.graph.EnergyMinimizer}
    (h : IsReflectedWalk F.graph w hminF PF) (hG : F.graph.toSimpleGraph.Connected)
    (hw : ∀ v, 0 < w v) (z : V) :
    ∀ᵐ ω ∂PF.P z, EndLabelConstruction.HasFiniteCutStabilization F (fun t => PF.X t ω) := by
  have hgrid : ∀ᵐ ω ∂PF.P z, ∀ q : ℚ,
      ∃ v, PF.X (Real.toNNReal (q : ℝ)) ω = some v := by
    exact ae_all_iff.2 fun q => ((h z).2.1 (Real.toNNReal (q : ℝ))).mono fun _ hq => hq.1
  have hrat : DenseRange (fun q : ℚ => Real.toNNReal (q : ℝ)) := by
    have hsurj : Function.Surjective Real.toNNReal := by
      intro t
      exact ⟨(t : ℝ), NNReal.eq (Real.coe_toNNReal (t : ℝ) t.property)⟩
    simpa only [Function.comp_def] using
      hsurj.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal
  filter_upwards [ae_component_of_cut_free_interval h hG hw z,
    FiniteCutPathEndExtension.reflected_ae_eventually_notMem_finiteCut h hG hw z,
    hgrid] with ω hpath havoid hgrid
  have hdense : Dense {s | ∃ v, PF.X s ω = some v} := by
    apply hrat.mono
    rintro s ⟨q, rfl⟩
    exact hgrid q
  intro t ht K
  obtain ⟨a, b, _, hI, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (havoid t ht K)
  obtain ⟨s, ⟨x, hx⟩, hsI⟩ := hdense.inter_nhds_nonempty hI
  have hxK : x ∉ (K : Set V) := by
    intro hxK
    exact hsub hsI ⟨x, hxK, hx.symm⟩
  let C := F.graph.toSimpleGraph.componentComplMk hxK
  refine ⟨C, ?_⟩
  filter_upwards [hI] with r hrI y hy
  rcases le_total s r with hsr | hrs
  · exact hpath K x y s r C hsr hx hy
      (fun u hu => hsub ⟨hsI.1.trans hu.1, hu.2.trans hrI.2⟩)
      (F.graph.toSimpleGraph.componentComplMk_mem hxK)
  · have hyK : y ∉ (K : Set V) := by
      intro hyK
      exact hsub hrI ⟨y, hyK, hy.symm⟩
    let D := F.graph.toSimpleGraph.componentComplMk hyK
    have hxD : x ∈ D := hpath K y x r s D hrs hy hx
      (fun u hu => hsub ⟨hrI.1.trans hu.1, hu.2.trans hsI.2⟩)
      (F.graph.toSimpleGraph.componentComplMk_mem hyK)
    have hCD : C = D := hxD.choose_spec
    exact hCD.symm ▸ F.graph.toSimpleGraph.componentComplMk_mem hyK

end ReflectedGMS.PathwiseComponentStabilization
