/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ExcursionOscillation at commit fdb5cad; local import paths and a deprecated proof name are updated; one unused hypothesis is renamed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianGoodEvent
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionTrajectory
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionKernel

/-! Whole-excursion range bounds and literal pointwise comparison of the
two actual representatives pasted on the same fixed time partition. -/

open MeasureTheory ProbabilityTheory Set Metric Preorder
open scoped unitInterval

namespace BouRabeeGwynne

variable {d : ℕ}

def curveOscillationLe (R : ℝ) : Set C(unitInterval, Euc d) :=
  {c | ∀ t, dist (c t) (c 0) ≤ R}

lemma isClosed_curveOscillationLe (R : ℝ) : IsClosed (curveOscillationLe (d := d) R) := by
  simp only [curveOscillationLe, Set.ofPred_forall]
  exact isClosed_iInter fun t => isClosed_le
    ((continuous_eval_const t).dist (continuous_eval_const 0)) continuous_const

lemma measurableSet_curveOscillationLe (R : ℝ) :
    MeasurableSet (curveOscillationLe (d := d) R) :=
  (isClosed_curveOscillationLe R).measurableSet

lemma mem_curveOscillationLe_of_closedBall {c : C(unitInterval, Euc d)}
    {x : Euc d} {R S : ℝ} (hrange : ∀ t, c t ∈ closedBall x R)
    (hstart : c 0 ∈ closedBall x S) : c ∈ curveOscillationLe (R + S) := by
  intro t
  exact (dist_triangle (c t) x (c 0)).trans
    (add_le_add (hrange t) (by simpa only [dist_comm] using (mem_closedBall.mp hstart)))

lemma absorbingExcursionKernel_ae_oscillation {X S J : Type*}
    [MeasurableSpace X] [MeasurableSpace S] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (κ : J → Kernel X S) (endpoint : S → X) (hend : Measurable endpoint)
    (constantState : X → S) (hconstant : Measurable constantState)
    (select : X → Option J) (hs : Measurable select)
    (curve : S → C(unitInterval, Euc d)) (hcurve : Measurable curve) (R : ℝ)
    (hconst : ∀ x, curve (constantState x) ∈ curveOscillationLe R)
    (hactive : ∀ j x, select x = some j → ∀ᵐ e ∂κ j x,
      curve e ∈ curveOscillationLe R) (p : Bool × S) :
    ∀ᵐ q ∂absorbingExcursionKernel κ endpoint hend constantState hconstant select hs p,
      curve q.2 ∈ curveOscillationLe R := by
  have hm : MeasurableSet {q : Bool × S | curve q.2 ∈ curveOscillationLe R} :=
    (hcurve.comp measurable_snd) (measurableSet_curveOscillationLe R)
  rcases p with ⟨flag, e⟩
  cases flag with
  | true =>
    rw [absorbingExcursionKernel_true]
    exact (ae_dirac_iff hm).mpr (hconst _)
  | false =>
    cases hsel : select (endpoint e) with
    | none =>
      rw [absorbingExcursionKernel_false_none κ endpoint hend constantState hconstant select hs e hsel]
      exact (ae_dirac_iff hm).mpr (hconst _)
    | some j =>
      rw [absorbingExcursionKernel_false_some κ endpoint hend constantState hconstant select hs e j hsel]
      exact (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hm).mpr
        (hactive j (endpoint e) hsel)

theorem trajMeasure_ae_curveOscillation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (κ n)]
    (curve : X → C(unitInterval, Euc d)) (hcurve : Measurable curve) (R : ℝ)
    (hinit : ∀ᵐ x ∂μ, curve x ∈ curveOscillationLe R)
    (hstep : ∀ n h, ∀ᵐ x ∂κ n h, curve x ∈ curveOscillationLe R) :
    ∀ᵐ ω ∂Kernel.trajMeasure (X := fun _ => X) μ κ,
      ∀ n, curve (ω n) ∈ curveOscillationLe R := by
  have hm : MeasurableSet {h : Finset.Iic 0 → X |
      curve (h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∈ curveOscillationLe R} :=
    (hcurve.comp (measurable_pi_apply _)) (measurableSet_curveOscillationLe R)
  have hi : ∀ᵐ h ∂μ.map (fun x => fun _ : Finset.Iic 0 => x),
      curve (h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∈ curveOscillationLe R :=
    (ae_map_iff (by fun_prop) hm).mpr hinit
  rw [← TrajectoryCoupling.prefix_zero μ κ] at hi
  have hzero : ∀ᵐ ω ∂Kernel.trajMeasure (X := fun _ => X) μ κ,
      curve (ω 0) ∈ curveOscillationLe R :=
    ae_of_ae_map (measurable_frestrictLe 0).aemeasurable hi
  apply ae_all_iff.mpr
  intro n
  cases n with
  | zero => exact hzero
  | succ n =>
    exact TrajectoryCoupling.ae_next_relation μ κ n
      (fun p => curve p.2 ∈ curveOscillationLe R)
      ((hcurve.comp measurable_snd) (measurableSet_curveOscillationLe R)) (hstep n)

lemma brownianExcursionKernel_ae_oscillation (hd : 1 ≤ d)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) {x z : Euc d} {r : ℝ} (_hr : 0 < r)
    (hz : z ∈ ball x r) :
    ∀ᵐ c ∂brownianExcursionKernel (U := ball x r) isOpen_ball μ z,
      c ∈ curveOscillationLe (2 * r) := by
  filter_upwards [brownianExcursionKernel_ae_mem_closure hd isOpen_ball isBounded_ball μ hμ hz,
    brownianExcursionKernel_ae_start isOpen_ball μ hμ z] with c hc hstart
  have hc' : ∀ t, c t ∈ closedBall x r := by
    exact fun t => closure_minimal ball_subset_closedBall isClosed_closedBall (hc t)
  have h0 : c 0 ∈ closedBall x r := by
    rw [hstart]
    exact mem_closedBall.mpr (mem_ball.mp hz).le
  simpa only [two_mul] using mem_curveOscillationLe_of_closedBall hc' h0

namespace TimePartition

/-- The common fixed partition gives a pointwise bound with the identity
clock, preserving the exact representatives needed for subsequent stopping. -/
theorem concatenate_pointwise_dist_le {K : ℕ} (P : TimePartition K)
    (c e : ExcursionChain K d) {R a S : ℝ}
    (hc : ∀ i, c.val i ∈ curveOscillationLe R)
    (he : ∀ i, e.val i ∈ curveOscillationLe S)
    (hstarts : ∀ i, dist (c.val i 0) (e.val i 0) ≤ a) (t : unitInterval) :
    dist (P.concatenate c t) (P.concatenate e t) ≤ R + a + S := by
  obtain ⟨i, hi⟩ := P.exists_interval t
  rw [P.concatenate_apply c i hi, P.concatenate_apply e i hi]
  calc
    _ ≤ dist (c.val i (P.localTime i t)) (e.val i 0) +
        dist (e.val i 0) (e.val i (P.localTime i t)) := dist_triangle _ _ _
    _ ≤ dist (c.val i (P.localTime i t)) (c.val i 0) +
        dist (c.val i 0) (e.val i 0) + dist (e.val i 0) (e.val i (P.localTime i t)) :=
      add_le_add (dist_triangle _ _ _) le_rfl
    _ ≤ R + a + S := add_le_add (add_le_add (hc i _) (hstarts i))
      (by simpa only [dist_comm] using he i (P.localTime i t))

end TimePartition

/-- Matched valid endpoints at preceding stages, together with the actual
start support, control every point of the two pasted full excursion prefixes. -/
theorem goodExcursionPair_pasted_pointwise_dist_le {V : Type*} (pos : V → Euc d)
    {K : ℕ} (P : TimePartition K) (m : ℕ → ℕ) {R a S : ℝ}
    (E : ∀ i, Fin (m i) → Set (Euc d)) (hdiam : ∀ i ≤ K, ∀ k,
      ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (w : ℕ → Bool × ClockedWalkExcursion d)
    (b : ℕ → Bool × C(unitInterval, Euc d))
    (hw : (fun i => ClockedWalkExcursion.curve (w i).2) ∈
      ExcursionTrajectory.compatiblePaths K d)
    (hb : (fun i => (b i).2) ∈ ExcursionTrajectory.compatiblePaths K d)
    (hgood : ∀ i ≤ K, (w i, b i) ∈ goodExcursionPair pos (E i) a)
    (hstart : dist (ClockedWalkExcursion.start (w 0).2) ((b 0).2 0) ≤ a)
    (hwrange : ∀ i ≤ K, ClockedWalkExcursion.curve (w i).2 ∈ curveOscillationLe R)
    (hbrange : ∀ i ≤ K, (b i).2 ∈ curveOscillationLe S) (t : unitInterval) :
    dist (P.concatenate (ExcursionTrajectory.prefixChain K d
        (fun i => ClockedWalkExcursion.curve (w i).2)) t)
      (P.concatenate (ExcursionTrajectory.prefixChain K d (fun i => (b i).2)) t) ≤
        R + a + S := by
  apply P.concatenate_pointwise_dist_le
  · intro i
    rw [ExcursionTrajectory.prefixChain_apply hw]
    exact hwrange i.val (Nat.le_of_lt_succ i.isLt)
  · intro i
    rw [ExcursionTrajectory.prefixChain_apply hb]
    exact hbrange i.val (Nat.le_of_lt_succ i.isLt)
  · intro i
    rw [ExcursionTrajectory.prefixChain_apply hw, ExcursionTrajectory.prefixChain_apply hb]
    cases hi : i.val with
    | zero => simpa only [hi, ClockedWalkExcursion.curve_start] using hstart
    | succ j =>
      have hj : j < K + 1 := by omega
      have heq : (⟨j, hj⟩ : Fin (K + 1)).succ = i.castSucc := Fin.ext (by simpa using hi.symm)
      have hw' := hw ⟨j, hj⟩ i heq
      have hb' := hb ⟨j, hj⟩ i heq
      simp only [hi] at hw' hb'
      rw [← hw', ← hb', ClockedWalkExcursion.curve_endPoint]
      have hjK : j ≤ K := Nat.le_of_lt_succ hj
      exact goodExcursionPair_dist_le pos (E j) (hdiam j hjK)
        (p := (w j, b j)) (hgood j hjK)

end BouRabeeGwynne
