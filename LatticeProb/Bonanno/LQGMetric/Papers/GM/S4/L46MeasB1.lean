/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasB1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasDet
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBasic
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStop
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4a
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventLength

/-!
# GM Lemma 4.6 (a), measurability: filled balls read on a dense sequence (task P2-E3b)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.6, l. 1701–1706. GM do not discuss measurability; decision D30 (events
quantified over paths are universally measurable, Lusin) is the convention. Own elementary
arguments (plane topology, dense sequences):

* `gm_notMem_filledBall_iff`: `z ∉ 𝓑^•_t(𝕫; d)` iff for every `n` some path from `z` to a point
  of norm `≥ n` stays a positive distance away from the dense-sequence points of `𝓑_t(𝕫; d)`
  (the unbounded component of `ℂ ∖ cl 𝓑_t` is open, hence path connected);
* `gm_uMeasurableSet_notMem_filledBall`: hence `{(d,t) | z ∉ 𝓑^•_t(𝕫; d)}` is analytic in the
  sense of D30 (universally measurable);
* `gm_infDist_frontier_filledBall`: for `z ∉ 𝓑^•_t`, `dist(z, ∂𝓑^•_t) = dist(z, 𝓑_t)`, and
  `gm_measurable_infDist_ballM`: the latter is Borel in `(d, t)`;
* `gm_filledBall_subset_ball_iff`: on `lenSet`, `𝓑^•_s ⊆ B_R(𝕫)` is read on the dense sequence,
  so that the exit time `τ_R` agrees on `lenSet` with the Borel function `gmTauB`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- the dense-sequence points of `𝓑_t(𝕫; d)` stay at distance `≥ 1/(m+1)` from the path `η` -/
def gmAvoid (d : ContMetric) (𝕫 : ℂ) (t : ℝ) (η : C(unitInterval, ℂ)) (m : ℕ) : Prop :=
  ∀ i, t ≤ d.1 (𝕫, qd i) ∨ ∀ s, 1 / ((m : ℝ) + 1) ≤ ‖η s - qd i‖

lemma gm_avoid_notMem {d : ContMetric} {𝕫 : ℂ} {t : ℝ} {η : C(unitInterval, ℂ)} {m : ℕ}
    (hav : gmAvoid d 𝕫 t η m) (s : unitInterval) : η s ∉ closure (ballM d 𝕫 t) := by
  intro hs
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hs _ isOpen_ball (mem_ball_self hpos)
  obtain ⟨i, hi1, hi2⟩ := denseRange_qd.exists_mem_open (isOpen_ball.inter (jb_isOpen_ballM d 𝕫 t))
    ⟨y, hy1, hy2⟩
  rcases hav i with h | h
  · exact absurd hi2 (not_lt.2 h)
  · have := h s
    rw [mem_ball, dist_eq_norm, ← norm_neg, neg_sub] at hi1
    linarith

/-- **path characterization of the complement of a filled ball** -/
theorem gm_notMem_filledBall_iff (d : ContMetric) (𝕫 z : ℂ) (t : ℝ) :
    z ∉ filledBall d 𝕫 t ↔ ∀ n : ℕ, ∃ η : C(unitInterval, ℂ), η 0 = z ∧ (n : ℝ) ≤ ‖η 1‖ ∧
      ∃ m : ℕ, gmAvoid d 𝕫 t η m := by
  set C := closure (ballM d 𝕫 t)
  have hCo : IsOpen Cᶜ := isClosed_closure.isOpen_compl
  constructor
  · intro hz n
    simp only [filledBall, mem_union, mem_ofPred_eq, not_or, not_and] at hz
    obtain ⟨hzC, hzb⟩ := hz
    have hub := hzb hzC
    set Z := connectedComponentIn Cᶜ z
    have hZo : IsOpen Z := hCo.connectedComponentIn
    have hZc : IsConnected Z := isConnected_connectedComponentIn_iff.2 hzC
    have hZp : IsPathConnected Z := hZo.isConnected_iff_isPathConnected.1 hZc
    obtain ⟨w, hwZ, hwn⟩ : ∃ w ∈ Z, (n : ℝ) ≤ ‖w‖ := by
      by_contra hcon
      push_neg at hcon
      exact hub ((isBounded_closedBall (x := (0 : ℂ)) (r := n)).subset fun w hw => by
        rw [mem_closedBall, dist_zero_right]; exact (hcon w hw).le)
    have hj := hZp.joinedIn z (mem_connectedComponentIn hzC) w hwZ
    set γ := hj.somePath
    let η : C(unitInterval, ℂ) := γ.toContinuousMap
    have hηZ : ∀ s, η s ∈ Z := hj.somePath_mem
    have hsub : range η ⊆ Cᶜ := by
      rintro _ ⟨s, rfl⟩; exact connectedComponentIn_subset _ _ (hηZ s)
    obtain ⟨δ, hδ, hδs⟩ := (isCompact_range η.continuous).exists_cthickening_subset_open hCo hsub
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨η, γ.source, by rw [show η 1 = w from γ.target]; exact hwn, m, fun i => ?_⟩
    by_cases hi : t ≤ d.1 (𝕫, qd i)
    · exact Or.inl hi
    · refine Or.inr fun s => ?_
      by_contra hlt
      push_neg at hlt
      have hmem : qd i ∈ cthickening δ (range η) :=
        mem_cthickening_of_dist_le (qd i) (η s) δ _ ⟨s, rfl⟩
          (by rw [dist_eq_norm, ← norm_neg, neg_sub]; linarith)
      exact hδs hmem (subset_closure (show d.1 (𝕫, qd i) < t from not_le.1 hi))
  · intro H
    obtain ⟨η, hη0, -, m, hav⟩ := H 0
    have hzC : z ∉ C := hη0 ▸ gm_avoid_notMem hav 0
    simp only [filledBall, mem_union, mem_ofPred_eq, not_or, not_and]
    refine ⟨hzC, fun _ hb => ?_⟩
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    obtain ⟨n, hn⟩ := exists_nat_gt M
    obtain ⟨η', hη'0, hη'n, m', hav'⟩ := H n
    have hsub : range η' ⊆ connectedComponentIn Cᶜ z := by
      refine (isPreconnected_range η'.continuous).subset_connectedComponentIn ⟨0, hη'0⟩ ?_
      rintro _ ⟨s, rfl⟩; exact gm_avoid_notMem hav' s
    have := hM (hsub ⟨1, rfl⟩)
    rw [mem_closedBall, dist_zero_right] at this
    linarith

/-- **`{(d,t) | z ∉ 𝓑^•_t(𝕫; d)}` is universally measurable** (an intersection of analytic sets) -/
theorem gm_uMeasurableSet_notMem_filledBall (𝕫 z : ℂ) :
    UMeasurableSet {p : ContMetric × ℝ | z ∉ filledBall p.1 𝕫 p.2} := by
  have hS : ∀ n : ℕ, MeasurableSet {q : (ContMetric × ℝ) × C(unitInterval, ℂ) |
      q.2 0 = z ∧ (n : ℝ) ≤ ‖q.2 1‖ ∧ ∃ m : ℕ, gmAvoid q.1.1 𝕫 q.1.2 q.2 m} := by
    intro n
    have hc0 : Continuous fun η : C(unitInterval, ℂ) => η 0 := continuous_eval_const 0
    have hc1 : Continuous fun η : C(unitInterval, ℂ) => η 1 := continuous_eval_const 1
    have h3 : MeasurableSet {q : (ContMetric × ℝ) × C(unitInterval, ℂ) |
        ∃ m : ℕ, gmAvoid q.1.1 𝕫 q.1.2 q.2 m} := by
      have e3 : {q : (ContMetric × ℝ) × C(unitInterval, ℂ) | ∃ m : ℕ, gmAvoid q.1.1 𝕫 q.1.2 q.2 m} =
          ⋃ m : ℕ, ⋂ i : ℕ, ({q : (ContMetric × ℝ) × C(unitInterval, ℂ) | q.1.2 ≤ q.1.1.1 (𝕫, qd i)} ∪
            Prod.snd ⁻¹' {η : C(unitInterval, ℂ) | ∀ s, 1 / ((m : ℝ) + 1) ≤ ‖η s - qd i‖}) := by
        ext q; simp [gmAvoid]
      rw [e3]
      refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun i => MeasurableSet.union ?_ ?_
      · exact measurableSet_le (measurable_snd.comp measurable_fst)
          ((measurable_apply _).comp (measurable_fst.comp measurable_fst))
      · have hcl : IsClosed {η : C(unitInterval, ℂ) | ∀ s, 1 / ((m : ℝ) + 1) ≤ ‖η s - qd i‖} := by
          simp only [ofPred_forall]
          exact isClosed_iInter fun s => isClosed_le continuous_const
            ((continuous_eval_const s).sub continuous_const).norm
        exact hcl.measurableSet.preimage measurable_snd
    exact ((isClosed_eq hc0 continuous_const).measurableSet.preimage measurable_snd).inter
      (((isClosed_le continuous_const hc1.norm).measurableSet.preimage measurable_snd).inter h3)
  have e : {p : ContMetric × ℝ | z ∉ filledBall p.1 𝕫 p.2} =
      ⋂ n : ℕ, {p | ∃ η, (p, η) ∈ {q : (ContMetric × ℝ) × C(unitInterval, ℂ) |
        q.2 0 = z ∧ (n : ℝ) ≤ ‖q.2 1‖ ∧ ∃ m : ℕ, gmAvoid q.1.1 𝕫 q.1.2 q.2 m}} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    exact gm_notMem_filledBall_iff p.1 𝕫 z p.2
  rw [e]
  exact UMeasurableSet.iInter fun n => UMeasurableSet.setOf_exists (hS n)

/-- for `z ∉ 𝓑^•_t`, `dist(z, ∂𝓑^•_t) = dist(z, 𝓑_t)` (bounded balls) -/
theorem gm_infDist_frontier_filledBall {d : ContMetric} {𝕫 z : ℂ} {t : ℝ}
    (hbd : Bornology.IsBounded (ballM d 𝕫 t)) (hz : z ∉ filledBall d 𝕫 t) :
    infDist z (frontier (filledBall d 𝕫 t)) = infDist z (ballM d 𝕫 t) := by
  have hfr := jb_frontier_subset_closure hbd
  have hBK : ballM d 𝕫 t ⊆ filledBall d 𝕫 t := subset_closure.trans subset_union_left
  rcases (ballM d 𝕫 t).eq_empty_or_nonempty with he | hne
  · rw [he, closure_empty, subset_empty_iff] at hfr
    rw [hfr, he]
  obtain ⟨y, hy⟩ := hne
  have hfne : (frontier (filledBall d 𝕫 t)).Nonempty := by
    obtain ⟨x, -, hx⟩ := jb_inter_frontier_nonempty (gm_filledBall_isClosed d 𝕫 t)
      isPreconnected_univ (mem_univ z) hz (mem_univ y) (hBK hy)
    exact ⟨x, hx⟩
  refine le_antisymm ?_ ?_
  · refine (le_infDist ⟨y, hy⟩).2 fun x hx => gm_infDist_frontier_le_dist hz (hBK hx)
  · rw [← infDist_closure (s := ballM d 𝕫 t)]
    exact infDist_le_infDist_of_subset hfr hfne

/-- `dist(z, 𝓑_t(𝕫; d))` is Borel in `(d, t)` -/
theorem gm_measurable_infDist_ballM (𝕫 z : ℂ) :
    Measurable fun p : ContMetric × ℝ => infDist z (ballM p.1 𝕫 p.2) := by
  have key : ∀ p : ContMetric × ℝ, infEDist z (ballM p.1 𝕫 p.2) =
      ⨅ i, if p.1.1 (𝕫, qd i) < p.2 then edist z (qd i) else ⊤ := by
    intro p
    have hcl : closure (ballM p.1 𝕫 p.2) = closure (ballM p.1 𝕫 p.2 ∩ range qd) :=
      le_antisymm (closure_minimal (denseRange_qd.open_subset_closure_inter
        (jb_isOpen_ballM p.1 𝕫 p.2)) isClosed_closure) (closure_mono inter_subset_left)
    rw [← infEDist_closure, hcl, infEDist_closure]
    refine le_antisymm (le_iInf fun i => ?_) (le_infEDist.2 ?_)
    · split_ifs with hi
      · exact infEDist_le_edist_of_mem ⟨hi, i, rfl⟩
      · exact le_top
    · rintro _ ⟨hy, i, rfl⟩
      refine iInf_le_of_le i ?_
      exact (if_pos hy).le
  have hm : Measurable fun p : ContMetric × ℝ =>
      ⨅ i, if p.1.1 (𝕫, qd i) < p.2 then edist z (qd i) else (⊤ : ℝ≥0∞) :=
    Measurable.iInf fun i => Measurable.ite
      (measurableSet_lt ((measurable_apply _).comp measurable_fst) measurable_snd)
      measurable_const measurable_const
  have e : (fun p : ContMetric × ℝ => infDist z (ballM p.1 𝕫 p.2)) =
      fun p => (⨅ i, if p.1.1 (𝕫, qd i) < p.2 then edist z (qd i) else (⊤ : ℝ≥0∞)).toReal := by
    funext p
    rw [← key]
    rfl
  rw [e]
  exact hm.ennreal_toReal

/-- on `lenSet` the closure of a metric ball is compact -/
theorem gm_isCompact_closure_ballM {d : ContMetric} (hd : d ∈ lenSet) (𝕫 : ℂ) (s : ℝ) :
    IsCompact (closure (ballM d 𝕫 s)) := by
  refine bcpt_of_mem_lenSet hd _ isClosed_closure ⟨2 * s, fun u hu v hv => ?_⟩
  have h1 := gm_closure_ballM_subset d 𝕫 s hu
  have h2 := gm_closure_ballM_subset d 𝕫 s hv
  simp only [mem_ofPred_eq] at h1 h2
  have := d.2.triangle u 𝕫 v
  rw [d.2.symm u 𝕫] at this
  linarith

/-- the dense-sequence form of `𝓑_s(𝕫; d) ⊆ B_{R - 1/(m+1)}(𝕫)` -/
def gmGoodB (𝕫 : ℂ) (R : ℝ) (d : ContMetric) (s : ℝ) : Prop :=
  ∃ m : ℕ, ∀ i, s ≤ d.1 (𝕫, qd i) ∨ ‖qd i - 𝕫‖ ≤ R - 1 / ((m : ℝ) + 1)

/-- on `lenSet`: `𝓑^•_s(𝕫; d) ⊆ B_R(𝕫)` iff `gmGoodB` -/
theorem gm_filledBall_subset_ball_iff {d : ContMetric} (hd : d ∈ lenSet) (𝕫 : ℂ) (R s : ℝ) :
    filledBall d 𝕫 s ⊆ ball 𝕫 R ↔ gmGoodB 𝕫 R d s := by
  set C := closure (ballM d 𝕫 s)
  constructor
  · intro hK
    have hCK : C ⊆ ball 𝕫 R := subset_union_left.trans hK
    rcases C.eq_empty_or_nonempty with he | hne
    · refine ⟨0, fun i => Or.inl ?_⟩
      by_contra hi
      have : qd i ∈ C := subset_closure (show d.1 (𝕫, qd i) < s from not_le.1 hi)
      rw [he] at this
      exact this
    obtain ⟨x₀, hx₀, hmax⟩ := (gm_isCompact_closure_ballM hd 𝕫 s).exists_isMaxOn hne
      (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
      (f := fun w : ℂ => ‖w - 𝕫‖)
    have hx₀R : ‖x₀ - 𝕫‖ < R := by
      have := hCK hx₀; rwa [mem_ball, dist_eq_norm] at this
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hx₀R)
    refine ⟨m, fun i => ?_⟩
    by_cases hi : s ≤ d.1 (𝕫, qd i)
    · exact Or.inl hi
    · right
      have hq : qd i ∈ C := subset_closure (show d.1 (𝕫, qd i) < s from not_le.1 hi)
      have := isMaxOn_iff.1 hmax _ hq
      linarith
  · rintro ⟨m, hm⟩
    set R' := R - 1 / ((m : ℝ) + 1)
    have hR' : R' < R := by simp only [R']; linarith [show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity]
    have hC : C ⊆ closedBall 𝕫 R' := by
      refine closure_minimal ((denseRange_qd.open_subset_closure_inter
        (jb_isOpen_ballM d 𝕫 s)).trans (closure_minimal ?_ isClosed_closedBall)) isClosed_closedBall
      rintro _ ⟨hy, i, rfl⟩
      rcases hm i with h | h
      · exact absurd hy (not_lt.2 h)
      · rw [mem_closedBall, dist_eq_norm]; exact h
    intro x hx
    by_contra hxR
    rw [mem_ball, dist_eq_norm, not_lt] at hxR
    set A : Set ℂ := (fun w => w + 𝕫) '' {w : ℂ | R' < ‖w‖}
    have hA : IsPreconnected A := (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R').image _
      (continuous_id.add continuous_const).continuousOn
    have hxA : x ∈ A := ⟨x - 𝕫, show R' < ‖x - 𝕫‖ by linarith, sub_add_cancel x 𝕫⟩
    have hAC : A ⊆ Cᶜ := by
      rintro _ ⟨w, hw, rfl⟩ hwC
      have := hC hwC
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right] at this
      exact absurd hw (not_lt.2 this)
    have hxC : x ∉ C := hAC hxA
    rcases hx with hx | ⟨-, hb⟩
    · exact hxC hx
    · have hAb := hb.subset (hA.subset_connectedComponentIn hxA hAC)
      obtain ⟨M, hM⟩ := hAb.subset_closedBall 0
      refine jb_not_isBounded_lt_norm R' ((isBounded_closedBall (x := (0 : ℂ))
        (r := M + ‖𝕫‖)).subset fun w hw => ?_)
      have := hM ⟨w, hw, rfl⟩
      rw [mem_closedBall, dist_zero_right] at this ⊢
      have := norm_add_le (w + 𝕫) (-𝕫)
      rw [add_neg_cancel_right, norm_neg] at this
      linarith

/-- the Borel exit time read on the dense sequence -/
def gmTauB (𝕫 : ℂ) (R : ℝ) (d : ContMetric) : ℝ :=
  sInf {s | 0 < s ∧ ¬ gmGoodB 𝕫 R d s}

theorem gm_tauD_eq_tauB {d : ContMetric} (hd : d ∈ lenSet) (𝕫 : ℂ) (R : ℝ) :
    tauD d 𝕫 R = gmTauB 𝕫 R d := by
  unfold tauD gmTauB
  congr 1
  ext s
  simp only [mem_ofPred_eq, gm_filledBall_subset_ball_iff hd]

lemma gm_goodB_anti {𝕫 : ℂ} {R : ℝ} {d : ContMetric} {s s' : ℝ} (h : gmGoodB 𝕫 R d s)
    (hs : s' ≤ s) : gmGoodB 𝕫 R d s' := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun i => (hm i).imp_left hs.trans⟩

lemma gm_measurableSet_goodB (𝕫 : ℂ) (R s : ℝ) : MeasurableSet {d | gmGoodB 𝕫 R d s} := by
  simp only [gmGoodB, ofPred_exists, ofPred_forall, ofPred_or]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun i =>
    MeasurableSet.union (measurableSet_le measurable_const (measurable_apply _)) ?_
  by_cases h : ‖qd i - 𝕫‖ ≤ R - 1 / ((m : ℝ) + 1)
  · simp only [h, ofPred_true, MeasurableSet.univ]
  · simp only [h, ofPred_false, MeasurableSet.empty]

theorem gm_measurable_tauB (𝕫 : ℂ) (R : ℝ) : Measurable (gmTauB 𝕫 R) := by
  refine measurable_of_Iio fun u => ?_
  have e : gmTauB 𝕫 R ⁻¹' Iio u = ({d | 0 < u} ∩ ⋂ q : ℚ, {d | 0 < (q : ℝ) → gmGoodB 𝕫 R d q}) ∪
      ⋃ q : ℚ, {d | 0 < (q : ℝ) ∧ (q : ℝ) < u ∧ ¬ gmGoodB 𝕫 R d q} := by
    ext d
    simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_ofPred_eq, mem_iInter,
      mem_iUnion]
    set A := {s | 0 < s ∧ ¬ gmGoodB 𝕫 R d s}
    have hbdd : BddBelow A := ⟨0, fun s hs => hs.1.le⟩
    constructor
    · intro hu
      rcases A.eq_empty_or_nonempty with he | hne
      · left
        have h0 : gmTauB 𝕫 R d = 0 := by show sInf A = 0; rw [he, Real.sInf_empty]
        refine ⟨by rwa [h0] at hu, fun q hq => ?_⟩
        by_contra hg
        have : (q : ℝ) ∈ A := ⟨hq, hg⟩
        rw [he] at this; exact this
      · right
        obtain ⟨s, ⟨hs0, hs⟩, hsu⟩ := exists_lt_of_csInf_lt hne hu
        obtain ⟨q, hsq, hqu⟩ := exists_rat_btwn hsu
        exact ⟨q, hs0.trans hsq, hqu, fun hg => hs (gm_goodB_anti hg hsq.le)⟩
    · rintro (⟨hu, hall⟩ | ⟨q, hq0, hqu, hq⟩)
      · have he : A = ∅ := by
          refine eq_empty_iff_forall_notMem.2 fun s ⟨hs0, hs⟩ => ?_
          obtain ⟨q, hsq⟩ := exists_rat_gt s
          exact hs (gm_goodB_anti (hall q (hs0.trans hsq)) hsq.le)
        show sInf A < u
        rwa [he, Real.sInf_empty]
      · exact lt_of_le_of_lt (csInf_le hbdd ⟨hq0, hq⟩) hqu
  rw [e]
  refine MeasurableSet.union (MeasurableSet.inter ?_ (MeasurableSet.iInter fun q => ?_))
    (MeasurableSet.iUnion fun q => ?_)
  · by_cases h : 0 < u
    · simp only [h, ofPred_true, MeasurableSet.univ]
    · simp only [h, ofPred_false, MeasurableSet.empty]
  · by_cases h : 0 < (q : ℝ)
    · simp only [h, forall_const]; exact gm_measurableSet_goodB 𝕫 R q
    · simp only [h, false_imp_iff, ofPred_true, MeasurableSet.univ]
  · by_cases h : 0 < (q : ℝ) ∧ (q : ℝ) < u
    · simp only [h, true_and]; exact (gm_measurableSet_goodB 𝕫 R q).compl
    · simp only [← and_assoc, h, false_and, ofPred_false, MeasurableSet.empty]

end LQGMetric.GM
