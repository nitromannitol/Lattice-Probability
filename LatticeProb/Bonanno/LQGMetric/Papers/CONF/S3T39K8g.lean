/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8g at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8f

/-!
# CONF Theorem 3.9, packet J6d, node O2: Effros-measurability of the centre and of `t39jGoodAct`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1586. The inputs `hCtr`, `hGood` of `t39k5_fields_at` (S3T39K5i), in exactly that shape,
from the uniform local accessibility of Jordan frontiers `T39K8LocAccess` (S3T39K8b):

* **`k8_hCtr`**: `(K, J) ↦ t39jCtr K J r` agrees, on closed bounded `K` with Jordan frontier and
  `J ⊆ ∂K`, with an Effros-measurable map (`k8_lexMin_meas` for the centre set, whose hit events
  are `k8CtrHit`, `k8CtrHit_iff`, or for `∂K`, `k8FrHit_iff`);
* **`k8_hGood`**: likewise the event `t39jGoodAct K J q R` (the open radius `ρ < ε R` is replaced
  by rational closed radii, then `k8_disc_iff`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory

namespace LQGMetric.CONF

attribute [local instance] effrosSigma

theorem k8_hit1_meas {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet {x : Set ℂ × Set ℂ | (x.1 ∩ V).Nonempty} :=
  measurable_fst (t39j_hit_open hV)

theorem k8_hit2_meas {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet {x : Set ℂ × Set ℂ | (x.2 ∩ V).Nonempty} :=
  measurable_snd (t39j_hit_open hV)

theorem k8BallSub_meas (p : ℂ) (ρ : ℝ) :
    MeasurableSet {x : Set ℂ × Set ℂ | k8BallSub x.1 p ρ} := by
  unfold k8BallSub
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun i => k8_hit1_meas isOpen_ball

theorem k8FrHit_meas (U : Set ℂ) : MeasurableSet {x : Set ℂ × Set ℂ | k8FrHit x.1 U} := by
  unfold k8FrHit
  simp only [ofPred_exists, ofPred_and]
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun ρ =>
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      ((k8_hit1_meas isOpen_ball).inter (k8BallSub_meas _ _).compl))

theorem k8Disc_comp_meas {Ψ : Set ℂ × Set ℂ → ℂ} (hΨ : Measurable Ψ) (a : ℝ) :
    MeasurableSet {x : Set ℂ × Set ℂ | k8Disc x.1 x.2 (Ψ x) a} :=
  (measurable_id.prodMk hΨ) (k8Disc_meas a)

theorem k8CtrHit_meas (r : ℝ) (U : Set ℂ) :
    MeasurableSet {x : Set ℂ × Set ℂ | k8CtrHit x.1 x.2 r U} := by
  unfold k8CtrHit
  simp only [ofPred_exists, ofPred_and, ofPred_forall]
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun ρ =>
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter (MeasurableSet.iInter fun j =>
      MeasurableSet.iUnion fun c' => (MeasurableSet.const _).inter ((k8FrHit_meas _).inter
        (k8Disc_comp_meas measurable_const _))))

theorem k8_frontier_nonempty {K : Set ℂ} (hJor : JordanMap.IsJordanCurve (frontier K)) :
    (frontier K).Nonempty := by
  obtain ⟨γ, -, -, h⟩ := hJor
  rw [← h]
  exact (NormedSpace.sphere_nonempty.2 zero_le_one).image _

open Classical in
/-- the set whose lexicographic minimum is the centre -/
def k8F (r : ℝ) (x : Set ℂ × Set ℂ) : Set ℂ :=
  if (t39jCtrSet x.1 x.2 r).Nonempty then t39jCtrSet x.1 x.2 r else frontier x.1

/-- the centre lies on the frontier -/
theorem k8_ctr_mem {K J : Set ℂ} (hKb : Bornology.IsBounded K)
    (hJor : JordanMap.IsJordanCurve (frontier K)) (r : ℝ) : t39jCtr K J r ∈ frontier K := by
  unfold t39jCtr
  split_ifs with h
  · exact t39jCtrSet_subset K J r (t39jLexMin_mem (t39j_isCompact_ctrSet hKb J r) h)
  · exact t39jLexMin_mem (t39j_isCompact_frontier hKb) (k8_frontier_nonempty hJor)

end LQGMetric.CONF
