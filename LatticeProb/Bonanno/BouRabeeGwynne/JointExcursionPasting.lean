/- Adapted from Leonardo Bonanno’s lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.JointExcursionPasting at commit fdb5cad; imports are relocated. -/
import LatticeProb.Bonanno.BouRabeeGwynne.SelectedExcursionOscillation
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSkeletonPrefix
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonPrefix

/-! A pointwise comparison under the actual joint excursion law. Compatibility,
initial starts, and whole-excursion oscillations are transferred from its exact
original-process marginals, without lifting to a joint original-path space. -/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Metric
open scoped unitInterval ENNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem walkBrownianJointLaw_ae_pasted_dist_le (N : FiniteConductanceNetwork V)
    (hd : 1 ≤ d) (pos : V → Euc d) (hinj : Function.Injective pos)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
    (hE : ∀ n k, MeasurableSet (E n k))
    (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc d) {K : ℕ} (P : TimePartition K) {R a S : ℝ}
    (hdiam : ∀ i ≤ K, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (pos v) z ≤ a)
    (hwrange : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ n,
      ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 ∈
        curveOscillationLe R)
    (hbrange : ∀ᵐ ω ∂μ, ∀ n,
      (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) n ω).2 ∈
        curveOscillationLe S) :
    ∀ᵐ p ∂N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE initial v z,
      (∀ i ≤ K, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a) → ∀ t,
        dist (P.concatenate (ExcursionTrajectory.prefixChain K d
          (fun i => ClockedWalkExcursion.curve (p.1 i).2)) t)
          (P.concatenate (ExcursionTrajectory.prefixChain K d (fun i => (p.2 i).2)) t) ≤
            R + a + S := by
  let WS : Set (ℕ → Bool × ClockedWalkExcursion d) := {w |
    (fun i => ClockedWalkExcursion.curve (w i).2) ∈ ExcursionTrajectory.compatiblePaths K d ∧
      ClockedWalkExcursion.start (w 0).2 = pos v ∧
        ∀ n, ClockedWalkExcursion.curve (w n).2 ∈ curveOscillationLe R}
  let BS : Set (ℕ → Bool × C(unitInterval, Euc d)) := {b |
    (fun i => (b i).2) ∈ ExcursionTrajectory.compatiblePaths K d ∧
      (b 0).2 0 = z ∧ ∀ n, (b n).2 ∈ curveOscillationLe S}
  have hWS : MeasurableSet WS := by
    have hr : MeasurableSet {w : ℕ → Bool × ClockedWalkExcursion d |
        ∀ n, ClockedWalkExcursion.curve (w n).2 ∈ curveOscillationLe R} := by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun n =>
        (ClockedWalkExcursion.measurable_curve.comp (measurable_pi_apply n).snd)
          (measurableSet_curveOscillationLe R)
    exact ((ExcursionTrajectory.measurableSet_compatiblePaths K d).preimage
      (Measurable.of_eval fun n => ClockedWalkExcursion.measurable_curve.comp
        (measurable_pi_apply n).snd)).inter
      ((measurableSet_eq_fun (ClockedWalkExcursion.measurable_start.comp
        (measurable_pi_apply 0).snd) measurable_const).inter hr)
  have hBS : MeasurableSet BS := by
    have hr : MeasurableSet {b : ℕ → Bool × C(unitInterval, Euc d) |
        ∀ n, (b n).2 ∈ curveOscillationLe S} := by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun n =>
        (measurable_pi_apply n).snd (measurableSet_curveOscillationLe S)
    exact ((ExcursionTrajectory.measurableSet_compatiblePaths K d).preimage
      (Measurable.of_eval fun n => (measurable_pi_apply n).snd)).inter
      ((measurableSet_eq_fun ((ContinuousMap.measurable_eval 0).comp
        (measurable_pi_apply 0).snd) measurable_const).inter hr)
  have hwactual : ∀ᵐ ω ∂N.trajectoryLaw A hA v,
      actualWalkExcursionSequence pos B initial select ω ∈ WS := by
    filter_upwards [N.actualWalkStage_ae_all_clocks_finite pos B hBA hA haccess initial
      (fun n v => select n (pos v)) v, N.trajectoryLaw_ae_start A hA v, hwrange]
      with ω hf hstart hr
    refine ⟨actualWalkStage_compatiblePaths pos B initial (fun n v => select n (pos v))
      K ω (hf K), ?_, hr⟩
    simpa only [actualWalkExcursionSequence, actualWalkStage, ClockedWalkExcursion.start_ofWalk]
      using congrArg pos hstart
  have hbstart : ∀ᵐ ω ∂μ,
      (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) 0 ω).2 0 = z := by
    exact ae_of_ae_map (measurable_stoppedBrownianRepresentative (hU initial) z).aemeasurable
      (brownianExcursionKernel_ae_start (hU initial) μ hμ z)
  have hbactual : ∀ᵐ ω ∂μ,
      (fun n => brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) n ω) ∈ BS := by
    filter_upwards [standardBrownianLaw_ae_finiteSkeletonClock hd hμ U hU hUb z initial
      (fun n => hs (n - 1)) K, hbstart, hbrange] with ω hf hstart hr
    refine ⟨?_, hstart, hr⟩
    have hchain := brownianSkeletonPhysicalKnots_chain_apply U z initial
      (brownianSelectorForWalk select) K ω hf
    intro i j hij
    change (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) i.val ω).2 1 =
      (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) j.val ω).2 0
    rw [← hchain i, ← hchain j]
    exact ((brownianSkeletonPhysicalKnots U z initial (brownianSelectorForWalk select) K ω hf).chain
      z ω).property i j hij
  have hm := N.walkBrownianJointLaw_marginals pos hinj B hB U hU μ select hs m E hE hdE
    hd hμ hUb hBA hA haccess initial v z
  have hwlaw : ∀ᵐ w ∂(N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE
      initial v z).fst, w ∈ WS := by
    rw [hm.1]
    exact (ae_map_iff (measurable_actualWalkExcursionSequence pos B initial select).aemeasurable
      hWS).mpr hwactual
  have hblaw : ∀ᵐ b ∂(N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE
      initial v z).snd, b ∈ BS := by
    rw [hm.2]
    exact (ae_map_iff (Measurable.of_eval fun n => measurable_brownianSkeletonExcursion U hU z
      initial (fun n => hs (n - 1)) n).aemeasurable hBS).mpr hbactual
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hwlaw,
    ae_of_ae_map measurable_snd.aemeasurable hblaw] with p hw hb
  intro hgood t
  exact goodExcursionPair_pasted_pointwise_dist_le pos P m E hdiam p.1 p.2 hw.1 hb.1 hgood
    (by rw [hw.2.1, hb.2.1]; exact hnear)
    (fun i _ => hw.2.2 i) (fun i _ => hb.2.2 i) t

end BouRabeeGwynne.FiniteConductanceNetwork
