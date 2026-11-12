/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.WedgeShiftHit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeLawRef
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability

/-!
# WEDGE-SHIFT (1): a measurable first hitting time and re-centred path on path space

Input of the translation step `F1.WedgeShiftLawStmt` of B4(c) (Duplantier–Miller–Sheffield,
*Liouville quantum gravity as a mating of trees*, arXiv:1409.7055, proof of Prop. 4.7(i), p. 77:
the radial part is re-centred at the first time it hits a level; Sheffield, arXiv:1012.4797,
§1.6).

The hitting time `T(a) = inf {s ≥ 0 : a s ≤ -c}` and the re-centred path `a(T(a) + ·) + c` are
not measurable for the product σ-algebra on `ℝ → ℝ`. We build measurable functions `hitT c`,
`shiftPath c` on `ℝ → ℝ` that read `a` only through countably many values and agree with them
on **every continuous** path (`hitT_eq_of_continuous`, `shiftPath_eq_of_continuous`):

* `hitT c a = inf {t > 0 : ∀ j, ∃ q ∈ ℚ ∩ [0, t], a q < -c + 1/(j+1)}` (an up-closed set of
  positive reals, `LQGMeas.measurable_sInf_upClosed`); for continuous `a` its members are the
  `t > 0` with `min_{[0,t]} a ≤ -c`;
* `shiftPath c a t = extP a (hitT c a + t) + c` (`WedgeLaw.extP`, the dyadic read-off).

Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1

/-- The countable-data hitting set: `t > 0` such that `a` comes within every `1/(j+1)` of the
level `-c` at some rational time in `[0, t]`. -/
def hitS (c : ℝ) (a : ℝ → ℝ) : Set ℝ :=
  {t | 0 < t ∧ ∀ j : ℕ, ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t ∧ a q < -c + 1 / ((j : ℝ) + 1)}

/-- The measurable first hitting time of `(-∞, -c]` (junk `0` if the path never gets there). -/
def hitT (c : ℝ) (a : ℝ → ℝ) : ℝ := sInf (hitS c a)

theorem measurable_hitT (c : ℝ) : Measurable (hitT c) := by
  refine LQGMeas.measurable_sInf_upClosed (hitS c) (fun q₀ => ?_) ?_ ?_
  · refine measurableSet_setOfPred.2 ((measurable_const).and (Measurable.forall fun j =>
      Measurable.exists fun q => (measurable_const.and (measurable_const.and ?_))))
    exact measurableSet_setOfPred.1 (measurableSet_lt (measurable_pi_apply _) measurable_const)
  · rintro a s t ⟨hs, h⟩ hst
    exact ⟨hs.trans_le hst, fun j => (h j).imp fun q hq => ⟨hq.1, hq.2.1.trans hst, hq.2.2⟩⟩
  · rintro a s ⟨hs, -⟩
    exact hs

/-- For a continuous path and `t > 0`: membership in `hitS` is `min_{[0,t]} a ≤ -c`. -/
theorem mem_hitS_iff {c : ℝ} {a : ℝ → ℝ} (ha : Continuous a) {t : ℝ} (ht : 0 < t) :
    t ∈ hitS c a ↔ ∃ s ∈ Icc (0 : ℝ) t, a s ≤ -c := by
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 ht.le) ha.continuousOn
    refine ⟨s₀, hs₀, le_of_forall_pos_lt_add fun ε hε => ?_⟩
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    obtain ⟨q, hq0, hqt, hq⟩ := h j
    have : a s₀ ≤ a q := hmin (show (q : ℝ) ∈ Icc (0 : ℝ) t from ⟨hq0, hqt⟩)
    linarith
  · rintro ⟨s, ⟨hs0, hst⟩, hs⟩
    refine ⟨ht, fun j => ?_⟩
    have hj : a s < -c + 1 / ((j : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
      (ha.continuousAt.eventually (gt_mem_nhds hj))
    have hlt : max 0 (s - δ) < min t (s + δ) :=
      max_lt (lt_min ht (by linarith)) (lt_min (by linarith) (by linarith))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    refine ⟨q, (le_max_left _ _).trans hq1.le, (hq2.le.trans (min_le_left _ _)), hball ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_right 0 (s - δ)]
    · linarith [min_le_right t (s + δ)]

/-- **`hitT` is the first hitting time on continuous paths.** -/
theorem hitT_eq_of_continuous {c : ℝ} {a : ℝ → ℝ} (ha : Continuous a) :
    hitT c a = sInf {s | 0 ≤ s ∧ a s ≤ -c} := by
  set Hs : Set ℝ := {s | 0 ≤ s ∧ a s ≤ -c} with hHs
  unfold hitT
  rcases Hs.eq_empty_or_nonempty with he | hne
  · have : hitS c a = ∅ := by
      ext t
      simp only [mem_empty_iff_false, iff_false]
      intro ht
      obtain ⟨s, ⟨hs0, -⟩, hs⟩ := (mem_hitS_iff ha ht.1).1 ht
      exact (he ▸ (show s ∈ Hs from ⟨hs0, hs⟩) : s ∈ (∅ : Set ℝ))
    rw [this, he]
  · have hcl : IsClosed Hs := isClosed_Ici.inter (isClosed_le ha continuous_const)
    have hbdd : BddBelow Hs := ⟨0, fun s hs => hs.1⟩
    have hT := hcl.csInf_mem hne hbdd
    set T := sInf Hs
    have e : hitS c a = {t | 0 < t ∧ T ≤ t} := by
      ext t
      constructor
      · intro ht
        obtain ⟨s, ⟨hs0, hst⟩, hs⟩ := (mem_hitS_iff ha ht.1).1 ht
        exact ⟨ht.1, (csInf_le hbdd ⟨hs0, hs⟩).trans hst⟩
      · rintro ⟨ht, hTt⟩
        exact (mem_hitS_iff ha ht).2 ⟨T, ⟨hT.1, hTt⟩, hT.2⟩
    rw [e]
    refine IsGLB.csInf_eq ⟨fun t ht => ht.2, fun b hb => ?_⟩ ⟨T + 1, by linarith [hT.1], by
      linarith⟩
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have := hb (show T + ε / 2 ∈ {t | 0 < t ∧ T ≤ t} from ⟨by linarith [hT.1], by linarith⟩)
    linarith

/-- The re-centred path `a(T(a) + ·) + c`, read through dyadic values. -/
def shiftPath (c : ℝ) (a : ℝ → ℝ) : ℝ → ℝ := fun t => WedgeLaw.extP a (hitT c a + t) + c

theorem measurable_shiftPath (c : ℝ) : Measurable (shiftPath c) :=
  measurable_pi_iff.2 fun t =>
    (WedgeLaw.measurable_extP.comp
      (measurable_id.prodMk ((measurable_hitT c).add_const t))).add_const c

theorem shiftPath_eq_of_continuous {c : ℝ} {a : ℝ → ℝ} (ha : Continuous a) :
    shiftPath c a = fun t => a (hitT c a + t) + c := by
  funext t
  simp only [shiftPath, WedgeLaw.extP_of_continuous ha]

theorem shiftPath_eq_of_continuous' {c : ℝ} {a : ℝ → ℝ} (ha : Continuous a) :
    shiftPath c a = fun t => a (sInf {s | 0 ≤ s ∧ a s ≤ -c} + t) + c := by
  rw [shiftPath_eq_of_continuous ha, hitT_eq_of_continuous ha]

end F1
end QuantumZipper
