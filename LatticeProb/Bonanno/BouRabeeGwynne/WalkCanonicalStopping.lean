/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkCanonicalStopping at commit fdb5cad; imports are relocated and later exports are omitted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionTrajectory
import LatticeProb.Bonanno.BouRabeeGwynne.ClockedWalkExitParameter
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSkeletonPrefix
import LatticeProb.Bonanno.BouRabeeGwynne.WalkReconstructionLaw
import LatticeProb.Bonanno.BouRabeeGwynne.MonotoneStoppedPrefixes
import LatticeProb.Bonanno.BouRabeeGwynne.PolygonalVertexExitGeometry
import LatticeProb.Bonanno.BouRabeeGwynne.WalkStoppedReconstruction
import LatticeProb.Bonanno.BouRabeeGwynne.UnitCurveExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianBoundaryExcursion

/-! The measurable curve obtained by pasting a finite prefix of walk excursions, and its canonical stopping support. -/

open MeasureTheory Set
open scoped unitInterval

namespace BouRabeeGwynne

noncomputable def pastedWalkCurve {d n : ℕ} (P : TimePartition n)
    (e : ℕ → Bool × ClockedWalkExcursion d) : C(unitInterval, Euc d) :=
  P.concatenate (ExcursionTrajectory.prefixChain n d
    (fun k => ClockedWalkExcursion.curve (e k).2))

lemma measurable_pastedWalkCurve {d n : ℕ} (P : TimePartition n) :
    Measurable (pastedWalkCurve (d := d) P) :=
  P.measurable_concatenate.comp ((ExcursionTrajectory.measurable_prefixChain n d).comp
    (Measurable.of_eval fun k => ClockedWalkExcursion.measurable_curve.comp
      (measurable_pi_apply k).snd))

def canonicalWalkStoppingSupport {d n : ℕ} (U : Set (Euc d)) (δ : ℝ) (P : TimePartition n) :
    Set (ℕ → Bool × ClockedWalkExcursion d) :=
  {e | let f := pastedWalkCurve P e
       let a := ClockedWalkExcursion.pastedVertexExitParameter U P e
       CurveSpace.project (prefixUnitCurve f a) = reconstructedVertexStoppedCurve U n e ∧
       f a ∉ U ∧ (a = 0 ∨ prefixUnitCurve f a ∈ curveRangeEvent (Metric.cthickening δ U))}

lemma measurableSet_canonicalWalkStoppingSupport {d n : ℕ} {U : Set (Euc d)}
    (hU : MeasurableSet U) (δ : ℝ) (P : TimePartition n) :
    MeasurableSet (canonicalWalkStoppingSupport U δ P) := by
  have hf := measurable_pastedWalkCurve (d := d) P
  have ha := ClockedWalkExcursion.measurable_pastedVertexExitParameter hU P
  have hp := measurable_prefixUnitCurve.comp (hf.prodMk ha)
  have heval : Measurable (fun p : C(unitInterval, Euc d) × unitInterval => p.1 p.2) :=
    (by fun_prop : Continuous (fun p : C(unitInterval, Euc d) × unitInterval => p.1 p.2)).measurable
  exact (measurableSet_eq_fun (CurveSpace.continuous_project.measurable.comp hp)
      (measurable_reconstructedVertexStoppedCurve hU n)).inter
    ((hU.compl.preimage (heval.comp (hf.prodMk ha))).inter
      ((measurableSet_eq_fun ha measurable_const).union
        ((isClosed_curveRangeEvent Metric.isClosed_cthickening).measurableSet.preimage hp)))

lemma canonicalWalkStoppingSupport_pre {d n : ℕ} {U : Set (Euc d)} {δ : ℝ}
    {P : TimePartition n} {e : ℕ → Bool × ClockedWalkExcursion d}
    (he : e ∈ canonicalWalkStoppingSupport U δ P) :
    ∀ t < ClockedWalkExcursion.pastedVertexExitParameter U P e,
      pastedWalkCurve P e t ∈ Metric.cthickening δ U := by
  intro t ht
  rcases he.2.2 with hz | hrange
  · rw [hz] at ht
    exact False.elim ((not_lt_of_ge (show (0 : unitInterval) ≤ t from t.property.1)) ht)
  · let a := ClockedWalkExcursion.pastedVertexExitParameter U P e
    have ha : (0 : ℝ) < a := lt_of_le_of_lt t.property.1 ht
    let u : unitInterval := ⟨(t : ℝ) / a, div_nonneg t.property.1 ha.le,
      (div_le_one ha).mpr ht.le⟩
    have heq : a * u = t := by
      apply Subtype.ext
      change (a : ℝ) * ((t : ℝ) / a) = t
      rw [mul_comm, div_mul_cancel₀ _ ha.ne']
    have h := hrange u
    change pastedWalkCurve P e (a * u) ∈ Metric.cthickening δ U at h
    rw [heq] at h
    exact h

private lemma polygonalCurve_prefix_of_scaled_vertex {d : ℕ} {V : Type*}
    (pos : V → Euc d) (ω : ℕ → V) {M m : ℕ} (hmM : m ≤ M)
    (b : unitInterval) (hb : (M : ℝ) * (b : ℝ) = m) :
    prefixUnitCurve (polygonalCurve pos ω M) b = polygonalCurve pos ω m := by
  apply ContinuousMap.ext
  intro u
  change polygonalCurve pos ω M (b * u) = polygonalCurve pos ω m u
  simpa only [Nat.zero_add] using polygonalCurve_shift_of_scaled_time pos ω
    (a := 0) (m := m) (M := M) (by simpa only [Nat.zero_add] using hmM) u (b * u)
    (by
      rw [Set.Icc.coe_mul, Nat.cast_zero, zero_add, ← mul_assoc, hb])

namespace FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

lemma prefixTimeData_actualWalkStage (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) (ω : ℕ → V)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) :
    (ClockedWalkExcursion.prefixTimeData (n := n)
      (fun k => (actualWalkStage pos B initial select k ω).2)).val =
      actualWalkStage_times pos B initial select n ω := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · change (ClockedWalkExcursion.concatenate
        (fun j => (actualWalkStage pos B initial select j ω).2.2) k.val).1 = _
    rw [concatenate_actualWalkStage pos B initial select ω k.val
      (actualWalkStage_clock_finite_of_le pos B initial select ω (by omega) hfinite)]
    exact Nat.sub_zero _

lemma pastedWalkCurve_actual_eq_comp_canonical (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → Euc d → Option J) (n : ℕ) (ω : ℕ → V)
    (hfinite : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1 ≠ ⊤)
    (P : TimePartition n) :
    pastedWalkCurve P (actualWalkExcursionSequence pos B initial select ω) =
      (polygonalCurve pos ω
        ((actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1.untopD 0)).comp
      (P.weakClock ((ClockedWalkExcursion.prefixTimeData
        (actualWalkExcursionSequence pos B initial select ω)).knots P)) := by
  let s := fun i v => select i (pos v)
  let D := ClockedWalkExcursion.prefixTimeData (n := n)
    (actualWalkExcursionSequence pos B initial select ω)
  have hD : D.val = actualWalkStage_times pos B initial s n ω :=
    prefixTimeData_actualWalkStage pos B initial s n ω hfinite
  have hM : D.duration = (actualWalkStage pos B initial s n ω).1.untopD 0 :=
    congrFun hD (Fin.last (n + 1))
  have hQ (i : Fin (n + 2)) :
      (((actualWalkStage pos B initial s n ω).1.untopD 0 : ℕ) : ℝ) *
        ((D.knots P).knots i : ℝ) = (actualWalkStage_times pos B initial s n ω i : ℝ) := by
    rw [← hM, ← hD]
    exact D.knots_scaled P i
  have hchain := clockedWalkSegments_eq_restrictChain (D.knots P) pos ω
    (actualWalkStage_times pos B initial s n ω)
    (actualWalkStage_times_monotone pos B initial s n ω hfinite) rfl hQ
    (ExcursionTrajectory.prefixChain n d
      (fun k => ClockedWalkExcursion.curve (actualWalkStage pos B initial s k ω).2.2))
    (by
      intro i
      rw [ExcursionTrajectory.prefixChain_apply
        (actualWalkStage_compatiblePaths pos B initial s n ω hfinite)]
      exact congrArg ClockedWalkExcursion.curve
        (actualWalkStage_eq_segment_times pos B initial s n ω hfinite i))
  change P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k => ClockedWalkExcursion.curve (actualWalkStage pos B initial s k ω).2.2)) =
    (polygonalCurve pos ω ((actualWalkStage pos B initial s n ω).1.untopD 0)).comp
      (P.weakClock (D.knots P))
  rw [hchain, WeakTimeKnots.concatenate_restrictChain]
  rfl

theorem canonicalWalkStoppingSupport_actual (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → Euc d → Option J) (U : Set (Euc d))
    (n : ℕ) (ω : ℕ → V) (δ : ℝ)
    (hfinite : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1 ≠ ⊤)
    (hexit : exitTime (pos ⁻¹' U) ω ≤
      (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1)
    (hedge : ∀ k < (exitTime (pos ⁻¹' U) ω).untopD 0,
      dist (pos (ω (k + 1))) (pos (ω k)) ≤ δ) (P : TimePartition n) :
    actualWalkExcursionSequence pos B initial select ω ∈ canonicalWalkStoppingSupport U δ P := by
  let s := fun i v => select i (pos v)
  let e := actualWalkExcursionSequence pos B initial select ω
  let D := ClockedWalkExcursion.prefixTimeData (n := n) e
  let M := (actualWalkStage pos B initial s n ω).1.untopD 0
  have hclock : (actualWalkStage pos B initial s n ω).1 = (M : WithTop ℕ) := by
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfinite
    dsimp only [M]
    rw [← hk]
    rfl
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top hfinite hexit)
  have hmM : m ≤ M := WithTop.coe_le_coe.mp (hm.trans_le (hexit.trans_eq hclock))
  have hconcat : ClockedWalkExcursion.concatenate (fun k => (e k).2) n =
      clockedWalkSegment pos ω 0 M :=
    concatenate_actualWalkStage pos B initial s ω n hfinite
  have hduration : D.duration = M := by
    change (ClockedWalkExcursion.concatenate (fun k => (e k).2) n).1 = M
    rw [hconcat]
    exact Nat.sub_zero M
  have he : exitTime U (ClockedWalkExcursion.concatenate (fun k => (e k).2) n).2 =
      exitTime (pos ⁻¹' U) ω := by
    rw [hconcat, ← exitTime_map pos U ω]
    apply exitTime_congr_prefix_of_le U (M := M)
    · intro k hk
      change pos (ω (0 + min k (M - 0))) = pos (ω k)
      simp only [Nat.sub_zero, Nat.zero_add, min_eq_left hk]
    · rw [exitTime_map]
      exact hexit.trans_eq hclock
  have hindex : ClockedWalkExcursion.concatenatedExitIndex (n := n) U e = m := by
    change min ((exitTime U (ClockedWalkExcursion.concatenate (fun k => (e k).2) n).2).untopD 0)
      D.duration = m
    rw [he, ← hm, WithTop.untopD_coe, hduration, min_eq_left hmM]
  let a := ClockedWalkExcursion.pastedVertexExitParameter U P e
  let b := D.vertexTime m
  let f := pastedWalkCurve P e
  have hab : P.weakClock (D.knots P) a = b := by
    simpa only [hindex] using ClockedWalkExcursion.pastedVertexExitParameter_clock U P e
  have hb : (M : ℝ) * (b : ℝ) = m := by
    simpa only [hduration, min_eq_left hmM] using D.vertexTime_scaled m
  have hcomp : f = (polygonalCurve pos ω M).comp (P.weakClock (D.knots P)) :=
    pastedWalkCurve_actual_eq_comp_canonical pos B initial select n ω hfinite P
  have hinside : ∀ k < m, pos (ω k) ∈ U := by
    intro k hk
    change ω k ∈ pos ⁻¹' U
    apply mem_of_lt_exitTime
    rw [← hm]
    exact WithTop.coe_lt_coe.mpr hk
  have hout : pos (ω m) ∉ U := by
    have h := exitTime_mem_compl_of_ne_top (ne_top_of_le_ne_top hfinite hexit)
    rw [← hm] at h
    exact h
  have hstep : ∀ k < m, dist (pos (ω (k + 1))) (pos (ω k)) ≤ δ := by
    simpa only [← hm, WithTop.untopD_coe] using hedge
  have hfa : f a = pos (ω m) := by
    rw [hcomp, ContinuousMap.comp_apply, hab]
    exact polygonalCurve_at_scaled_vertex pos ω hmM b hb
  refine ⟨?_, hfa ▸ hout, ?_⟩
  · change CurveSpace.project (prefixUnitCurve f a) = reconstructedVertexStoppedCurve U n e
    rw [hcomp, curveSpace_project_prefix_comp_monotone _ _
      (P.weakClock_monotone _) (P.weakClock_zero _) a b hab,
      polygonalCurve_prefix_of_scaled_vertex pos ω hmM b hb,
      reconstructedVertexStoppedCurve_actual pos B initial select U ω n hfinite hexit]
    simp only [stoppedPolygonalCurve, ← hm, WithTop.untopD_coe]
  · by_cases hmzero : m = 0
    · left
      change D.exitParameter P (ClockedWalkExcursion.concatenatedExitIndex (n := n) U e) = 0
      rw [hindex, hmzero, WalkPrefixTimeData.exitParameter_zero]
    · right
      intro u
      change f (a * u) ∈ Metric.cthickening δ U
      rw [hcomp, ContinuousMap.comp_apply]
      apply polygonalCurve_mem_cthickening_before_vertex pos ω (Nat.pos_of_ne_zero hmzero)
        hmM hinside hstep
      calc
        (M : ℝ) * (P.weakClock (D.knots P) (a * u) : ℝ) ≤
            (M : ℝ) * (P.weakClock (D.knots P) a : ℝ) :=
          mul_le_mul_of_nonneg_left ((P.weakClock_monotone _) (show a * u ≤ a from
            mul_le_of_le_one_right a.property.1 u.property.2)) (Nat.cast_nonneg M)
        _ = m := by rw [hab]; exact hb

/-- The support needed by the joint comparison is measurable on the rich walk
marginal. A prefix which is still active is left for the separate tail bound. -/
theorem trajectoryLaw_map_ae_canonicalWalkStoppingSupport (N : FiniteConductanceNetwork V)
    (pos : V → Euc d) {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (select : ℕ → Euc d → Option J) (U : Set (Euc d))
    (hU : MeasurableSet U) (hselect : ∀ i x, select i x = none → x ∉ U)
    (v : V) (n : ℕ) (δ : ℝ)
    (hsteps : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ k,
      dist (pos (ω k)) (pos (ω (k + 1))) ≤ δ) (P : TimePartition n) :
    ∀ᵐ e ∂(N.trajectoryLaw A hA v).map (actualWalkExcursionSequence pos B initial select),
      (e n).1 = false ∨ e ∈ canonicalWalkStoppingSupport U δ P := by
  have hflag : MeasurableSet {e : ℕ → Bool × ClockedWalkExcursion d | (e n).1 = false} :=
    measurableSet_eq_fun (measurable_pi_apply n).fst measurable_const
  apply (ae_map_iff (measurable_actualWalkExcursionSequence pos B initial select).aemeasurable
    (hflag.union (measurableSet_canonicalWalkStoppingSupport hU δ P))).mpr
  filter_upwards [hsteps, N.actualWalkStage_ae_all_clocks_finite pos B hBA hA haccess initial
    (fun i v => select i (pos v)) v] with ω hω hfinite
  by_cases hactive : (actualWalkExcursionSequence pos B initial select ω n).1 = false
  · exact Or.inl hactive
  right
  have hstopped : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).2.1 = true :=
    Bool.eq_true_of_not_eq_false hactive
  apply canonicalWalkStoppingSupport_actual pos B initial select U n ω δ (hfinite n)
    (actualWalkStage_exit_le_of_stopped pos B initial (fun i v => select i (pos v))
      (pos ⁻¹' U) (fun i v hv => hselect i (pos v) hv) ω n (hfinite n) hstopped) ?_ P
  intro k _
  simpa only [dist_comm] using hω k

end FiniteConductanceNetwork

end BouRabeeGwynne
