/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasE1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD2

/-!
# The filled metric ball is Borel in `(d, s, x)` (task P2-E3d, decision D65 (i))

Source: GM = Gwynne–Miller, arXiv:1905.00383v3; the filled ball `𝓑^•_s(𝕫; d)` (GM l. 846,
`Blueprint.filledBall`). GM do not discuss measurability; own descriptive-set-theory argument.

For every continuous metric `d` (no length assumption):
* `w ∈ closure (ballM d 𝕫 s)` iff points `qd i` of the dense sequence of ℂ close to `w` lie in
  `ballM` (`gmE_mem_closure_open_iff`);
* a compact nonempty `S` avoids `closure (ballM d 𝕫 s)` iff a uniform neighbourhood of it does,
  tested on `qd` (`gmE_subset_compl_closure_iff`);
* the connected component of `x` in an open `O ⊆ ℂ` is unbounded iff for each `N` a rational
  ball around `x` and a path of the dense sequence `gmPth` of `C([0,1], ℂ)`, both in `O`, reach
  norm `> N` (`gmE_unbounded_iff`).
Hence `{(d, s, x) | x ∈ 𝓑^•_s(𝕫; d)}` is Borel (`gmE_measurableSet_filledBall`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- a dense sequence of paths `[0,1] → ℂ` -/
def gmPth : ℕ → C(unitInterval, ℂ) := TopologicalSpace.denseSeq C(unitInterval, ℂ)

lemma gmE_continuous_dist0 (d : ContMetric) (𝕫 : ℂ) : Continuous fun w : ℂ => d.1 (𝕫, w) :=
  d.1.continuous.comp (continuous_const.prodMk continuous_id)

lemma gmE_isOpen_ballM (d : ContMetric) (𝕫 : ℂ) (s : ℝ) : IsOpen (ballM d 𝕫 s) :=
  isOpen_lt (gmE_continuous_dist0 d 𝕫) continuous_const

/-- closure of an open set through the dense sequence `qd` -/
lemma gmE_mem_closure_open_iff {V : Set ℂ} (hV : IsOpen V) (w : ℂ) :
    w ∈ closure V ↔ ∀ m : ℕ, ∃ i : ℕ, dist (qd i) w < 1 / ((m : ℝ) + 1) ∧ qd i ∈ V := by
  constructor
  · intro hw m
    obtain ⟨b, hb, hbw⟩ := Metric.mem_closure_iff.1 hw (1 / ((m : ℝ) + 1)) (by positivity)
    obtain ⟨i, hi⟩ := denseRange_qd.exists_mem_open (hV.inter isOpen_ball)
      ⟨b, hb, by rw [mem_ball, dist_comm]; exact hbw⟩
    exact ⟨i, hi.2, hi.1⟩
  · intro H
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨i, hi, hd⟩ := H m
    exact ⟨qd i, hd, by rw [dist_comm]; linarith⟩

/-- a compact nonempty set avoids `closure (ballM d 𝕫 s)` iff a uniform neighbourhood avoids
`ballM`, tested on `qd` -/
lemma gmE_subset_compl_closure_iff (d : ContMetric) (𝕫 : ℂ) (s : ℝ) {S : Set ℂ}
    (hS : IsCompact S) (hne : S.Nonempty) :
    S ⊆ (closure (ballM d 𝕫 s))ᶜ ↔
      ∃ m : ℕ, ∀ i : ℕ, infDist (qd i) S < 1 / ((m : ℝ) + 1) → s ≤ d.1 (𝕫, qd i) := by
  constructor
  · intro h
    obtain ⟨δ, hδ, hδS⟩ := hS.exists_thickening_subset_open isClosed_closure.isOpen_compl h
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun i hi => ?_⟩
    have h1 : qd i ∈ thickening δ S := (mem_thickening_iff_infDist_lt hne).2 (hi.trans hm)
    by_contra hlt
    exact hδS h1 (subset_closure (show qd i ∈ ballM d 𝕫 s from not_le.1 hlt))
  · rintro ⟨m, hm⟩ w hwS hw
    obtain ⟨i, hi, hd⟩ := (gmE_mem_closure_open_iff (gmE_isOpen_ballM d 𝕫 s) w).1 hw m
    have := hm i ((infDist_le_dist_of_mem hwS).trans_lt hi)
    exact absurd hd (not_lt.2 this)

/-- **unbounded components of open sets**, countable form -/
lemma gmE_unbounded_iff {O : Set ℂ} (hO : IsOpen O) {x : ℂ} (hx : x ∈ O) :
    ¬ Bornology.IsBounded (connectedComponentIn O x) ↔
      ∀ N : ℕ, ∃ j n k : ℕ, dist x (qd j) < 1 / ((n : ℝ) + 1) ∧
        closedBall (qd j) (1 / ((n : ℝ) + 1)) ⊆ O ∧
        dist (gmPth k 0) (qd j) < 1 / ((n : ℝ) + 1) ∧ range (gmPth k) ⊆ O ∧
        (N : ℝ) < ‖gmPth k 1‖ := by
  constructor
  · intro H N
    have hw : ∃ w ∈ connectedComponentIn O x, (N : ℝ) + 1 < ‖w‖ := by
      by_contra hcon
      push Not at hcon
      exact H (isBounded_iff_forall_norm_le.2 ⟨_, hcon⟩)
    obtain ⟨w, hwC, hwN⟩ := hw
    have hCo : IsOpen (connectedComponentIn O x) := hO.connectedComponentIn
    have hCc : IsConnected (connectedComponentIn O x) := isConnected_connectedComponentIn_iff.2 hx
    have hpc := (hCo.isConnected_iff_isPathConnected).1 hCc
    have hj := hpc.joinedIn x (mem_connectedComponentIn hx) w hwC
    set γ := hj.somePath
    have hγO : range γ ⊆ O := by
      rintro _ ⟨t, rfl⟩; exact connectedComponentIn_subset _ _ (hj.somePath_mem t)
    obtain ⟨δ, hδ, hδO⟩ := (isCompact_range γ.continuous).exists_thickening_subset_open hO hγO
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hδ)
    set ρ : ℝ := 1 / ((n : ℝ) + 1)
    have hρ : 0 < ρ := by positivity
    obtain ⟨j, hj'⟩ := denseRange_qd.exists_dist_lt x hρ
    set e : ℝ := min (ρ - dist x (qd j)) (min δ 1)
    have he : 0 < e := lt_min (by linarith) (lt_min hδ one_pos)
    obtain ⟨k, hk⟩ := (TopologicalSpace.denseRange_denseSeq C(unitInterval, ℂ)).exists_dist_lt
      γ.toContinuousMap he
    have hk' : ∀ t, dist (gmPth k t) (γ t) < e := fun t => by
      rw [dist_comm] at hk
      exact (ContinuousMap.dist_apply_le_dist (f := gmPth k) (g := γ.toContinuousMap) t).trans_lt hk
    have hγ0 : γ 0 = x := γ.source
    have hγ1 : γ 1 = w := γ.target
    refine ⟨j, n, k, hj', fun v hv => hδO ?_, ?_, fun _ ⟨t, ht⟩ => hδO ?_, ?_⟩
    · refine mem_thickening_iff.2 ⟨x, ⟨0, hγ0⟩, ?_⟩
      have := dist_triangle v (qd j) x
      rw [mem_closedBall] at hv
      rw [dist_comm (qd j) x] at this
      linarith
    · have h1 := dist_triangle (gmPth k 0) x (qd j)
      have h2 := hk' 0
      rw [hγ0] at h2
      have : e ≤ ρ - dist x (qd j) := min_le_left _ _
      linarith
    · rw [← ht]
      exact mem_thickening_iff.2 ⟨γ t, ⟨t, rfl⟩, (hk' t).trans_le
        ((min_le_right _ _).trans (min_le_left _ _))⟩
    · have h1 := hk' 1
      rw [hγ1] at h1
      have h2 : e ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
      have h3 := norm_sub_norm_le w (gmPth k 1)
      rw [← dist_eq_norm, dist_comm] at h3
      linarith
  · intro H hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
    obtain ⟨j, n, k, hxj, hball, hk0, hkO, hkN⟩ := H ⌈R⌉₊
    set ρ : ℝ := 1 / ((n : ℝ) + 1)
    have hS : IsPreconnected (closedBall (qd j) ρ ∪ range (gmPth k)) :=
      (convex_closedBall _ _).isPreconnected.union (gmPth k 0)
        (mem_closedBall.2 hk0.le) ⟨0, rfl⟩ (isPreconnected_range (gmPth k).continuous)
    have hsub := hS.subset_connectedComponentIn (Or.inl (mem_closedBall.2 hxj.le))
      (union_subset hball hkO)
    have := hR _ (hsub (Or.inr ⟨1, rfl⟩))
    have := Nat.le_ceil R
    linarith

/-- the complement of the filled ball, countable form -/
def gmOutF (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (x : ℂ) : Prop :=
  (∃ m : ℕ, ∀ i : ℕ, dist (qd i) x < 1 / ((m : ℝ) + 1) → s ≤ d.1 (𝕫, qd i)) ∧
  ∀ N : ℕ, ∃ j n k : ℕ, dist x (qd j) < 1 / ((n : ℝ) + 1) ∧
    (∃ m : ℕ, ∀ i : ℕ, infDist (qd i) (closedBall (qd j) (1 / ((n : ℝ) + 1))) <
      1 / ((m : ℝ) + 1) → s ≤ d.1 (𝕫, qd i)) ∧
    dist (gmPth k 0) (qd j) < 1 / ((n : ℝ) + 1) ∧
    (∃ m : ℕ, ∀ i : ℕ, infDist (qd i) (range (gmPth k)) < 1 / ((m : ℝ) + 1) →
      s ≤ d.1 (𝕫, qd i)) ∧ (N : ℝ) < ‖gmPth k 1‖

lemma gmE_notMem_closure_iff (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (x : ℂ) :
    x ∉ closure (ballM d 𝕫 s) ↔
      ∃ m : ℕ, ∀ i : ℕ, dist (qd i) x < 1 / ((m : ℝ) + 1) → s ≤ d.1 (𝕫, qd i) := by
  rw [gmE_mem_closure_open_iff (gmE_isOpen_ballM d 𝕫 s)]
  push Not
  simp only [ballM, mem_ofPred_eq, not_lt]

/-- **the complement of the filled ball** in countable form -/
theorem gmE_notMem_filledBall_iff (d : ContMetric) (𝕫 : ℂ) (s : ℝ) (x : ℂ) :
    x ∉ filledBall d 𝕫 s ↔ gmOutF d 𝕫 s x := by
  set O := (closure (ballM d 𝕫 s))ᶜ
  have hO : IsOpen O := isClosed_closure.isOpen_compl
  have e1 : x ∉ filledBall d 𝕫 s ↔ x ∈ O ∧ ¬ Bornology.IsBounded (connectedComponentIn O x) := by
    simp only [filledBall, mem_union, mem_ofPred_eq, not_or, not_and, O, mem_compl_iff]
    tauto
  have hball : ∀ c ρ, 0 < ρ → (closedBall c ρ ⊆ O ↔ ∃ m : ℕ, ∀ i : ℕ,
      infDist (qd i) (closedBall c ρ) < 1 / ((m : ℝ) + 1) → s ≤ d.1 (𝕫, qd i)) :=
    fun c ρ hρ => gmE_subset_compl_closure_iff d 𝕫 s (isCompact_closedBall c ρ)
      (nonempty_closedBall.2 hρ.le)
  have hrange : ∀ k, (range (gmPth k) ⊆ O ↔ ∃ m : ℕ, ∀ i : ℕ,
      infDist (qd i) (range (gmPth k)) < 1 / ((m : ℝ) + 1) → s ≤ d.1 (𝕫, qd i)) :=
    fun k => gmE_subset_compl_closure_iff d 𝕫 s (isCompact_range (gmPth k).continuous)
      (range_nonempty _)
  rw [e1, gmOutF, ← gmE_notMem_closure_iff]
  constructor
  · rintro ⟨hx, hu⟩
    refine ⟨hx, fun N => ?_⟩
    obtain ⟨j, n, k, h1, h2, h3, h4, h5⟩ := (gmE_unbounded_iff hO hx).1 hu N
    exact ⟨j, n, k, h1, (hball _ _ (by positivity)).1 h2, h3, (hrange k).1 h4, h5⟩
  · rintro ⟨hx, H⟩
    refine ⟨hx, (gmE_unbounded_iff hO hx).2 fun N => ?_⟩
    obtain ⟨j, n, k, h1, h2, h3, h4, h5⟩ := H N
    exact ⟨j, n, k, h1, (hball _ _ (by positivity)).2 h2, h3, (hrange k).2 h4, h5⟩

lemma gmE_measurable_le_dist (𝕫 w : ℂ) :
    Measurable fun p : ContMetric × ℝ × ℂ => p.2.1 ≤ p.1.1 (𝕫, w) :=
  measurableSet_setOfPred.1 (measurableSet_le (measurable_fst.comp measurable_snd)
    ((measurable_apply (𝕫, w)).comp measurable_fst))

/-- **the filled ball is Borel in `(d, s, x)`** -/
theorem gmE_measurableSet_outF (𝕫 : ℂ) :
    MeasurableSet {p : ContMetric × ℝ × ℂ | gmOutF p.1 𝕫 p.2.1 p.2.2} := by
  have hx : Measurable fun p : ContMetric × ℝ × ℂ => p.2.2 := measurable_snd.comp measurable_snd
  have hdx : ∀ (w : ℂ) (c : ℝ), Measurable fun p : ContMetric × ℝ × ℂ => dist w p.2.2 < c :=
    fun w c => measurableSet_setOfPred.1 (measurableSet_lt (measurable_const.dist hx) measurable_const)
  have hxd : ∀ (w : ℂ) (c : ℝ), Measurable fun p : ContMetric × ℝ × ℂ => dist p.2.2 w < c :=
    fun w c => measurableSet_setOfPred.1 (measurableSet_lt (hx.dist measurable_const) measurable_const)
  refine measurableSet_setOfPred.2 ((Measurable.exists fun m => Measurable.forall fun i =>
    (hdx _ _).imp (gmE_measurable_le_dist _ _)).and (Measurable.forall fun N =>
      Measurable.exists fun j => Measurable.exists fun n => Measurable.exists fun k =>
        (hxd _ _).and ((Measurable.exists fun m => Measurable.forall fun i =>
          measurable_const.imp (gmE_measurable_le_dist _ _)).and (measurable_const.and
          ((Measurable.exists fun m => Measurable.forall fun i =>
            measurable_const.imp (gmE_measurable_le_dist _ _)).and measurable_const)))))

theorem gmE_measurableSet_filledBall (𝕫 : ℂ) :
    MeasurableSet {p : ContMetric × ℝ × ℂ | p.2.2 ∈ filledBall p.1 𝕫 p.2.1} := by
  have e : {p : ContMetric × ℝ × ℂ | p.2.2 ∈ filledBall p.1 𝕫 p.2.1} =
      {p : ContMetric × ℝ × ℂ | gmOutF p.1 𝕫 p.2.1 p.2.2}ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, ← gmE_notMem_filledBall_iff, not_not]
  rw [e]
  exact (gmE_measurableSet_outF 𝕫).compl

end LQGMetric.GM
