/- Adapted from the lean-formalizations of Leonardo Bonanno (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.SelectedExcursionOscillation at commit fdb5cad; imports and selected declarations are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionOscillation
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSkeletonLaw
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonLaw

/-! Whole-excursion oscillation bounds along the original selected processes.
The walk's one-ball input is the actual enlarged-ball kernel bound. -/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Metric Preorder
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

variable {d : ℕ}

lemma constant_mem_curveOscillationLe (x : Euc d) {R : ℝ} (hR : 0 ≤ R) :
    ContinuousMap.const unitInterval x ∈ curveOscillationLe R := by
  intro t
  simpa only [ContinuousMap.const_apply, dist_self] using hR

lemma clockedConstant_mem_curveOscillationLe (x : Euc d) {R : ℝ} (hR : 0 ≤ R) :
    ClockedWalkExcursion.curve (ClockedWalkExcursion.constant x) ∈ curveOscillationLe R := by
  simpa only [ClockedWalkExcursion.curve, ClockedWalkExcursion.constant,
    polygonalCurve_zero, id_eq] using constant_mem_curveOscillationLe x hR

namespace FiniteConductanceNetwork

variable {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem trajectoryLaw_walkSkeleton_ae_oscillation (N : FiniteConductanceNetwork V)
    (pos : V → Euc d) (hinj : Function.Injective pos)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ j v, v ∈ B j → ∀ᵐ e ∂N.clockedWalkExcursionKernel pos (B j) (hB j) v,
      ClockedWalkExcursion.curve e ∈ curveOscillationLe R)
    (hselect : ∀ n v j, select n (pos v) = some j → v ∈ B j)
    (initial : J) (v : V) (hv : v ∈ B initial) :
    ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ n,
      ClockedWalkExcursion.curve (actualWalkExcursionSequence pos B initial select ω n).2 ∈
        curveOscillationLe R := by
  have hm : MeasurableSet {q : Bool × ClockedWalkExcursion d |
      ClockedWalkExcursion.curve q.2 ∈ curveOscillationLe R} :=
    (ClockedWalkExcursion.measurable_curve.comp measurable_snd)
      (measurableSet_curveOscillationLe R)
  have hinit : ∀ᵐ q ∂N.walkSkeletonInitialLaw pos B hB initial v,
      ClockedWalkExcursion.curve q.2 ∈ curveOscillationLe R :=
    (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hm).mpr
      (hball initial v hv)
  have hstep (n : ℕ) (h : Finset.Iic n → Bool × ClockedWalkExcursion d) :
      ∀ᵐ q ∂N.walkSkeletonHistoryKernel pos hinj B hB select hs n h,
        ClockedWalkExcursion.curve q.2 ∈ curveOscillationLe R := by
    apply absorbingExcursionKernel_ae_oscillation
      (fun j => N.spatialClockedExcursionKernel pos hinj (B j) (hB j))
      ClockedWalkExcursion.endPoint ClockedWalkExcursion.measurable_endPoint
      ClockedWalkExcursion.constant ClockedWalkExcursion.measurable_constant (select n) (hs n)
      ClockedWalkExcursion.curve ClockedWalkExcursion.measurable_curve R
      (fun x => clockedConstant_mem_curveOscillationLe x hR) ?_
      (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    intro j x hx
    by_cases hgraph : x ∈ Set.range pos
    · obtain ⟨w, rfl⟩ := hgraph
      rw [N.spatialClockedExcursionKernel_vertex]
      exact hball j w (hselect n w j hx)
    · change ∀ᵐ e ∂finiteVertexKernelExtension pos hinj
        (N.clockedWalkExcursionKernel pos (B j) (hB j)) ClockedWalkExcursion.constant
        ClockedWalkExcursion.measurable_constant x, _
      rw [finiteVertexKernelExtension_apply_off_graph pos hinj _ _ _ hgraph]
      exact (ae_dirac_iff (ClockedWalkExcursion.measurable_curve
        (measurableSet_curveOscillationLe R))).mpr
          (clockedConstant_mem_curveOscillationLe x hR)
  have hall := trajMeasure_ae_curveOscillation (N.walkSkeletonInitialLaw pos B hB initial v)
    (N.walkSkeletonHistoryKernel pos hinj B hB select hs)
    (fun q => ClockedWalkExcursion.curve q.2)
    (ClockedWalkExcursion.measurable_curve.comp measurable_snd) R hinit hstep
  rw [← N.trajectoryLaw_walkSkeleton_map pos hinj B hBA hA hB haccess initial select hs v] at hall
  exact ae_of_ae_map (measurable_actualWalkExcursionSequence pos B initial select).aemeasurable hall

end FiniteConductanceNetwork
theorem standardBrownianLaw_skeleton_ae_oscillation {J : Type*}
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) (centers : J → Euc d) {r : ℝ} (hr : 0 < r)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (hselect : ∀ n x j, select n x = some j → x ∈ ball (centers j) r)
    (initial : J) (z : Euc d) (hz : z ∈ ball (centers initial) r) :
    ∀ᵐ ω ∂μ, ∀ n,
      (brownianSkeletonExcursion (fun j => ball (centers j) r) z initial
        (brownianSelectorForWalk select) n ω).2 ∈ curveOscillationLe (2 * r) := by
  let U := fun j => ball (centers j) r
  have hm : MeasurableSet {q : Bool × C(unitInterval, Euc d) |
      q.2 ∈ curveOscillationLe (2 * r)} :=
    measurable_snd (measurableSet_curveOscillationLe (2 * r))
  have hinit : ∀ᵐ q ∂brownianSkeletonInitialLaw U (fun _ => isOpen_ball) μ z initial,
      q.2 ∈ curveOscillationLe (2 * r) :=
    (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hm).mpr
      (brownianExcursionKernel_ae_oscillation hd μ hμ hr hz)
  have hstep (n : ℕ) (h : Finset.Iic n → Bool × C(unitInterval, Euc d)) :
      ∀ᵐ q ∂brownianSkeletonKernel U (fun _ => isOpen_ball) μ
        (brownianSelectorForWalk select) (fun n => hs (n - 1)) n h,
        q.2 ∈ curveOscillationLe (2 * r) := by
    change ∀ᵐ q ∂absorbingExcursionKernel (fun j => brownianExcursionKernel
        (U := U j) isOpen_ball μ) (fun c => c 1) (ContinuousMap.measurable_eval 1)
        (ContinuousMap.const unitInterval) (by
          apply ContinuousMap.measurable_iff_eval.mpr
          intro t
          exact measurable_id)
        (brownianSelectorForWalk select (n + 1)) (hs ((n + 1) - 1))
        (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩), _
    apply absorbingExcursionKernel_ae_oscillation _ _ _ _ _ _ _ id measurable_id (2 * r)
      (fun x => constant_mem_curveOscillationLe x (by positivity)) ?_
    intro j x hx
    exact brownianExcursionKernel_ae_oscillation hd μ hμ hr
      (hselect n x j (by simpa only [brownianSelectorForWalk_succ] using hx))
  have hall := trajMeasure_ae_curveOscillation
    (brownianSkeletonInitialLaw U (fun _ => isOpen_ball) μ z initial)
    (brownianSkeletonKernel U (fun _ => isOpen_ball) μ
      (brownianSelectorForWalk select) (fun n => hs (n - 1)))
    Prod.snd measurable_snd (2 * r) hinit hstep
  rw [← standardBrownianLaw_skeleton_map hd hμ U (fun _ => isOpen_ball)
    (fun _ => isBounded_ball) z initial (brownianSelectorForWalk select)
    (fun n => hs (n - 1))] at hall
  exact ae_of_ae_map (Measurable.of_eval fun n => measurable_brownianSkeletonExcursion U
    (fun _ => isOpen_ball) z initial (fun n => hs (n - 1)) n).aemeasurable hall

end BouRabeeGwynne
