/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8c at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8b
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J2

/-!
# CONF Theorem 3.9, packet J6d, node O2: measurability of the countable disconnection condition

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1586. The countable condition `k8Disc K J c a` (S3T39K8b; equivalent to
`DisconnectsFromInfty K (closedBall c a) J` for Jordan `K`, `k8_disc_iff`) is a measurable set of
`((K, J), c)` for the Effros σ-algebras on `K`, `J` and the Borel σ-algebra on `c`
(**`k8Disc_meas`**): it only involves hit events of open sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory

namespace LQGMetric.CONF

attribute [local instance] effrosSigma

theorem k8_imp {α : Type*} [MeasurableSpace α] {A B : α → Prop} (hA : MeasurableSet {x | A x})
    (hB : MeasurableSet {x | B x}) : MeasurableSet {x | A x → B x} := by
  have : {x | A x → B x} = {x | A x}ᶜ ∪ {x | B x} := by ext; simp [imp_iff_not_or]
  rw [this]; exact hA.compl.union hB

/-- the space of `((K, J), c)` -/
abbrev K8X := (Set ℂ × Set ℂ) × ℂ

theorem k8_hitK_meas {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet {p : K8X | (p.1.1 ∩ V).Nonempty} :=
  (measurable_fst.comp measurable_fst) (t39j_hit_open hV)

theorem k8_hitJ_meas {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet {p : K8X | (p.1.2 ∩ V).Nonempty} :=
  (measurable_snd.comp measurable_fst) (t39j_hit_open hV)

theorem k8Good_meas (a : ℝ) (b : K8B) : MeasurableSet {p : K8X | k8Good p.1.1 p.2 a b} := by
  unfold k8Good
  simp only [ofPred_and, ofPred_exists]
  refine (MeasurableSet.const _).inter (MeasurableSet.inter ?_ ?_)
  · exact MeasurableSet.iUnion fun j : ℕ => (k8_hitK_meas isOpen_ball).compl
  · exact measurableSet_lt measurable_const
      ((continuous_const.dist continuous_id).measurable.comp measurable_snd)

theorem k8W_meas (a : ℝ) (n : ℕ) (q : ℂ) : MeasurableSet {p : K8X | k8W p.1.1 p.2 a n q} := by
  have : {p : K8X | k8W p.1.1 p.2 a n q} = ⋃ l : List K8B,
      (⋂ b ∈ {b | b ∈ l}, {p : K8X | k8Good p.1.1 p.2 a b}) ∩
        {_p | ∃ y : ℂ, (n : ℝ) < ‖y‖ ∧ k8G q l y} := by
    ext p; simp [k8W]
  rw [this]
  exact MeasurableSet.iUnion fun l => (MeasurableSet.biInter (Set.to_countable _)
    fun b _ => k8Good_meas a b).inter (MeasurableSet.const _)

/-- **the countable disconnection condition is measurable** -/
theorem k8Disc_meas (a : ℝ) : MeasurableSet {p : K8X | k8Disc p.1.1 p.1.2 p.2 a} := by
  unfold k8Disc
  simp only [ofPred_exists, ofPred_and, ofPred_forall]
  refine MeasurableSet.iUnion fun n => (k8_hitK_meas ?_).compl.inter
    (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun k => MeasurableSet.iInter fun q =>
      k8_imp (k8W_meas a n _) (k8_imp (k8_hitJ_meas isOpen_ball) ?_))
  · exact isOpen_lt continuous_const continuous_norm
  · exact measurableSet_le ((continuous_const.dist continuous_id).measurable.comp measurable_snd)
      measurable_const

end LQGMetric.CONF
