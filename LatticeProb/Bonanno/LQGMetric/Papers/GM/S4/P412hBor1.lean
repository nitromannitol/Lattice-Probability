/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412hBor1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hDef
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE1

/-!
# Borel tests for a random closed set (D98 §2, packet P-L414Borel, part 1)

Source: decision D98 §2 (decisions/DEC-98.md): the selection criteria of `gd` are Borel "by the
method of `gmE_unbounded_iff` / `gmE_mem_closure_open_iff`" (L46MeasE1, D65 (i)). GM do not
discuss measurability; own descriptive-set-theory arguments.

A *regular random closed set* `K : X → Set ℂ` (`P412hRC`): Borel point events `{w ∈ K x}`, `K x`
closed and `K x ⊆ cl(int K x)` (true for filled balls: `cl(ballM)` and the bounded components are
in `cl(int)`). Then:
* `p412h_meas_disj`: `{x | Disjoint S (K x)}` is Borel for compact `S` (test on `qd`);
* `p412h_mem_cc_iff`: `u ∈ cc(O, y₀)` for open `O` in countable form (one dense path, two balls);
* `p412h_rat_near`: points of rational angle are dense in each arc of `∂B ∖ K`;
* **`p412h_meas_arc`**: `{x | u ∈ cc(∂B_r(c) ∖ K x, y₀)}` is Borel (through the open set
  `{z ≠ c | rproj z ∉ K x}`, whose components meet the circle in the arcs).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Topology Bornology
open LQGMetric.Topo.Crosscut LQGMetric.LocalEvent

namespace LQGMetric.GM

/-- a regular random closed set -/
structure P412hRC {X : Type} [MeasurableSpace X] (K : X → Set ℂ) : Prop where
  mem : ∀ w, MeasurableSet {x | w ∈ K x}
  closed : ∀ x, IsClosed (K x)
  reg : ∀ x, K x ⊆ closure (interior (K x))

variable {X : Type} [MeasurableSpace X] {K : X → Set ℂ}

theorem p412h_disj_iff {K : Set ℂ} (hK : IsClosed K) (hreg : K ⊆ closure (interior K))
    {S : Set ℂ} (hS : IsCompact S) (hne : S.Nonempty) :
    Disjoint S K ↔ ∃ m : ℕ, ∀ i : ℕ, infDist (qd i) S < 1 / ((m : ℝ) + 1) → qd i ∉ K := by
  constructor
  · intro h
    obtain ⟨δ, hδ, hδS⟩ := hS.exists_thickening_subset_open hK.isOpen_compl
      (fun z hz hzK => h.ne_of_mem hz hzK rfl)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    exact ⟨m, fun i hi => hδS ((mem_thickening_iff_infDist_lt hne).2 (hi.trans hm))⟩
  · rintro ⟨m, hm⟩
    refine Set.disjoint_left.2 fun w hwS hwK => ?_
    obtain ⟨b, hb, hbw⟩ := Metric.mem_closure_iff.1 (hreg hwK) (1 / ((m : ℝ) + 1)) (by positivity)
    obtain ⟨i, hi⟩ := denseRange_qd.exists_mem_open (isOpen_interior.inter isOpen_ball)
      ⟨b, hb, by rw [mem_ball, dist_comm]; exact hbw⟩
    have hd : dist (qd i) w < 1 / ((m : ℝ) + 1) := by
      have := hi.2; rw [mem_ball] at this
      linarith [dist_triangle (qd i) b w, dist_comm b w]
    exact hm i ((infDist_le_dist_of_mem hwS).trans_lt hd) (interior_subset hi.1)

/-- **avoidance of a compact set is Borel** -/
theorem p412h_meas_disj (hK : P412hRC K) {S : Set ℂ} (hS : IsCompact S) :
    MeasurableSet {x | Disjoint S (K x)} := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [empty_disjoint, setOf_true, MeasurableSet.univ]
  have e : {x | Disjoint S (K x)} = ⋃ m : ℕ, ⋂ i : ℕ,
      {x | infDist (qd i) S < 1 / ((m : ℝ) + 1) → qd i ∉ K x} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, mem_iInter]
    exact p412h_disj_iff (hK.closed x) (hK.reg x) hS hne
  rw [e]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun i => ?_
  by_cases hi : infDist (qd i) S < 1 / ((m : ℝ) + 1)
  · simp only [hi, true_implies]; exact (hK.mem _).compl
  · simp only [hi, false_implies, setOf_true, MeasurableSet.univ]

/-- **components of an open set**, countable form -/
theorem p412h_mem_cc_iff {O : Set ℂ} (hO : IsOpen O) {y₀ u : ℂ} (hy₀ : y₀ ∈ O) :
    u ∈ connectedComponentIn O y₀ ↔ ∃ n k : ℕ, closedBall y₀ (1 / ((n : ℝ) + 1)) ⊆ O ∧
      closedBall u (1 / ((n : ℝ) + 1)) ⊆ O ∧ range (gmPth k) ⊆ O ∧
      dist (gmPth k 0) y₀ < 1 / ((n : ℝ) + 1) ∧ dist (gmPth k 1) u < 1 / ((n : ℝ) + 1) := by
  constructor
  · intro hu
    have hCo : IsOpen (connectedComponentIn O y₀) := hO.connectedComponentIn
    have hCc : IsConnected (connectedComponentIn O y₀) := isConnected_connectedComponentIn_iff.2 hy₀
    have hpc := (hCo.isConnected_iff_isPathConnected).1 hCc
    have hj := hpc.joinedIn y₀ (mem_connectedComponentIn hy₀) u hu
    set γ := hj.somePath
    have hγO : range γ ⊆ O := by
      rintro _ ⟨t, rfl⟩; exact connectedComponentIn_subset _ _ (hj.somePath_mem t)
    obtain ⟨δ, hδ, hδO⟩ := (isCompact_range γ.continuous).exists_thickening_subset_open hO hγO
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hδ)
    set ρ : ℝ := 1 / ((n : ℝ) + 1)
    have hρ : 0 < ρ := by positivity
    obtain ⟨k, hk⟩ := (TopologicalSpace.denseRange_denseSeq C(unitInterval, ℂ)).exists_dist_lt
      γ.toContinuousMap hρ
    have hk' : ∀ t, dist (gmPth k t) (γ t) < ρ := fun t => by
      rw [dist_comm] at hk
      exact (ContinuousMap.dist_apply_le_dist (f := gmPth k) (g := γ.toContinuousMap) t).trans_lt hk
    have hγ0 : γ 0 = y₀ := γ.source
    have hγ1 : γ 1 = u := γ.target
    refine ⟨n, k, fun v hv => hδO ?_, fun v hv => hδO ?_, fun _ ⟨t, ht⟩ => hδO ?_, ?_, ?_⟩
    · exact mem_thickening_iff.2 ⟨y₀, ⟨0, hγ0⟩, by rw [mem_closedBall] at hv; linarith⟩
    · exact mem_thickening_iff.2 ⟨u, ⟨1, hγ1⟩, by rw [mem_closedBall] at hv; linarith⟩
    · rw [← ht]
      exact mem_thickening_iff.2 ⟨γ t, ⟨t, rfl⟩, by linarith [hk' t]⟩
    · have := hk' 0; rwa [hγ0] at this
    · have := hk' 1; rwa [hγ1] at this
  · rintro ⟨n, k, h0, h1, hk, hk0, hk1⟩
    set ρ : ℝ := 1 / ((n : ℝ) + 1)
    have hS : IsPreconnected (closedBall y₀ ρ ∪ range (gmPth k) ∪ closedBall u ρ) :=
      ((convex_closedBall _ _).isPreconnected.union (gmPth k 0)
        (mem_closedBall.2 hk0.le) (mem_range_self (0 : unitInterval))
        (isPreconnected_range (gmPth k).continuous)).union
        (gmPth k 1) (Or.inr (mem_range_self (1 : unitInterval))) (mem_closedBall.2 hk1.le)
          (convex_closedBall _ _).isPreconnected
    have hsub := hS.subset_connectedComponentIn
      (Or.inl (Or.inl (mem_closedBall_self (by positivity)))) (union_subset (union_subset h0 hk) h1)
    exact hsub (Or.inr (mem_closedBall_self (by positivity)))

/-- points of rational angle are dense in each arc of `∂B_ρ(c) ∖ K` -/
theorem p412h_rat_near {K : Set ℂ} (hK : IsClosed K) {c u : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hu : u ∈ sphere c ρ) (huK : u ∉ K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ : ℚ, p412hPt c ρ θ ∈ connectedComponentIn (sphere c ρ \ K) u ∧
      dist (p412hPt c ρ θ) u < δ := by
  obtain ⟨δ', hδ', hsub⟩ : ∃ δ' > 0, ball u δ' ∩ sphere c ρ ⊆
      connectedComponentIn (sphere c ρ \ K) u := by
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · refine ⟨1, one_pos, ?_⟩
      rw [diff_empty, (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) c ρ
        ).connectedComponentIn hu]
      exact inter_subset_right
    · exact cc_sphere_open hK hKne hρ hu huK
  have hcont : Continuous (p412hPt c ρ) := by unfold p412hPt; fun_prop
  have hφ : p412hPt c ρ (Complex.arg (u - c) / (2 * Real.pi)) = u := by
    have hn : ‖u - c‖ = ρ := by rw [← dist_eq_norm]; exact mem_sphere.1 hu
    have h2 : (2 * Real.pi * (Complex.arg (u - c) / (2 * Real.pi))) = Complex.arg (u - c) := by
      field_simp
    rw [p412hPt, h2, ← hn, Complex.norm_mul_exp_arg_mul_I]; ring
  obtain ⟨θ, hθ⟩ := Rat.denseRange_cast.exists_mem_open
    ((isOpen_ball (x := u) (ε := min δ δ')).preimage hcont)
    ⟨_, show p412hPt c ρ _ ∈ ball u (min δ δ') by rw [hφ]; exact mem_ball_self (lt_min hδ hδ')⟩
  have hθ' : dist (p412hPt c ρ θ) u < min δ δ' := hθ
  exact ⟨θ, hsub ⟨mem_ball.2 (hθ'.trans_le (min_le_right _ _)), p412h_pt_mem c hρ.le _⟩,
    hθ'.trans_le (min_le_left _ _)⟩

/-- the open set `{z ≠ c | rproj z ∉ K}` -/
def p412hO (K : Set ℂ) (c : ℂ) (r : ℝ) : Set ℂ := {z | z ≠ c ∧ rproj c r z ∉ K}

theorem p412h_isOpen_O {K : Set ℂ} (hK : IsClosed K) (c : ℂ) (r : ℝ) : IsOpen (p412hO K c r) :=
  (continuousOn_rproj c r).isOpen_inter_preimage isOpen_ne hK.isOpen_compl

/-- the arcs of `∂B_r(c) ∖ K` are the traces of the components of `p412hO` -/
theorem p412h_cc_sphere_iff {K : Set ℂ} {c y₀ u : ℂ} {r : ℝ} (hr : 0 < r)
    (hy₀ : y₀ ∈ sphere c r) :
    u ∈ connectedComponentIn (sphere c r \ K) y₀ ↔
      u ∈ sphere c r ∧ u ∈ connectedComponentIn (p412hO K c r) y₀ := by
  have hne : ∀ z ∈ sphere c r, z ≠ c := fun z hz h => by
    rw [h, mem_sphere, dist_self] at hz; linarith
  have hSO : sphere c r \ K ⊆ p412hO K c r := fun z hz =>
    ⟨hne z hz.1, by rw [rproj_of_mem hr hz.1]; exact hz.2⟩
  constructor
  · intro hu
    have hy₀K : y₀ ∈ sphere c r \ K := connectedComponentIn_nonempty_iff.1 ⟨u, hu⟩
    exact ⟨(connectedComponentIn_subset _ _ hu).1, (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hy₀K) ((connectedComponentIn_subset _ _).trans hSO)) hu⟩
  · rintro ⟨huS, hu⟩
    have hy₀O : y₀ ∈ p412hO K c r := connectedComponentIn_nonempty_iff.1 ⟨u, hu⟩
    have hsub : rproj c r '' connectedComponentIn (p412hO K c r) y₀ ⊆ sphere c r \ K := by
      rintro _ ⟨z, hz, rfl⟩
      have hzO := connectedComponentIn_subset _ _ hz
      exact ⟨rproj_mem_sphere hr.le hzO.1, hzO.2⟩
    have hpre : IsPreconnected (rproj c r '' connectedComponentIn (p412hO K c r) y₀) :=
      isPreconnected_connectedComponentIn.image _ ((continuousOn_rproj c r).mono fun z hz =>
        (connectedComponentIn_subset _ _ hz).1)
    have h1 := hpre.subset_connectedComponentIn ⟨y₀, mem_connectedComponentIn hy₀O,
      rproj_of_mem hr hy₀⟩ hsub
    exact h1 ⟨u, hu, rproj_of_mem hr huS⟩

/-- compact sets inside `p412hO` -/
theorem p412h_subset_O_iff {K S : Set ℂ} {c : ℂ} {r : ℝ} (hcS : c ∉ S) :
    S ⊆ p412hO K c r ↔ Disjoint (rproj c r '' S) K := by
  constructor
  · intro h
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ hzK
    exact (h hz).2 hzK
  · intro h z hz
    exact ⟨fun hzc => hcS (hzc ▸ hz), fun hzK => Set.disjoint_left.1 h ⟨z, hz, rfl⟩ hzK⟩

theorem p412h_meas_subset_O (hK : P412hRC K) {S : Set ℂ} (hS : IsCompact S) (c : ℂ) (r : ℝ) :
    MeasurableSet {x | S ⊆ p412hO (K x) c r} := by
  by_cases hcS : c ∈ S
  · have : {x | S ⊆ p412hO (K x) c r} = ∅ :=
      eq_empty_of_forall_notMem fun x hx => (hx hcS).1 rfl
    rw [this]; exact MeasurableSet.empty
  · simp only [p412h_subset_O_iff hcS]
    exact p412h_meas_disj hK (hS.image_of_continuousOn ((continuousOn_rproj c r).mono
      fun z hz hzc => hcS (hzc ▸ hz)))

/-- **arc membership is Borel** -/
theorem p412h_meas_arc (hK : P412hRC K) {c y₀ u : ℂ} {r : ℝ} (hr : 0 < r)
    (hy₀ : y₀ ∈ sphere c r) :
    MeasurableSet {x | u ∈ connectedComponentIn (sphere c r \ K x) y₀} := by
  by_cases huS : u ∈ sphere c r
  swap
  · have : {x | u ∈ connectedComponentIn (sphere c r \ K x) y₀} = ∅ :=
      eq_empty_of_forall_notMem fun x hx => huS ((p412h_cc_sphere_iff hr hy₀).1 hx).1
    rw [this]; exact MeasurableSet.empty
  have e : {x | u ∈ connectedComponentIn (sphere c r \ K x) y₀} =
      {x | y₀ ∉ K x} ∩ ⋃ n : ℕ, ⋃ k : ℕ,
        ({x | closedBall y₀ (1 / ((n : ℝ) + 1)) ⊆ p412hO (K x) c r} ∩
        {x | closedBall u (1 / ((n : ℝ) + 1)) ⊆ p412hO (K x) c r} ∩
        {x | range (gmPth k) ⊆ p412hO (K x) c r} ∩
        {_x | dist (gmPth k 0) y₀ < 1 / ((n : ℝ) + 1) ∧ dist (gmPth k 1) u < 1 / ((n : ℝ) + 1)}) := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    rw [p412h_cc_sphere_iff hr hy₀]
    have hne : y₀ ≠ c := fun h => by rw [h, mem_sphere, dist_self] at hy₀; linarith
    constructor
    · rintro ⟨-, hu⟩
      have hy₀O : y₀ ∈ p412hO (K x) c r := connectedComponentIn_nonempty_iff.1 ⟨u, hu⟩
      obtain ⟨n, k, h⟩ := (p412h_mem_cc_iff (p412h_isOpen_O (hK.closed x) c r) hy₀O).1 hu
      refine ⟨fun h' => hy₀O.2 (by rwa [rproj_of_mem hr hy₀]), n, k, ⟨⟨h.1, h.2.1⟩, h.2.2.1⟩,
        h.2.2.2⟩
    · rintro ⟨hy₀K, n, k, ⟨⟨h0, h1⟩, h2⟩, h3, h4⟩
      have hy₀O : y₀ ∈ p412hO (K x) c r := ⟨hne, by rwa [rproj_of_mem hr hy₀]⟩
      exact ⟨huS, (p412h_mem_cc_iff (p412h_isOpen_O (hK.closed x) c r) hy₀O).2
        ⟨n, k, h0, h1, h2, h3, h4⟩⟩
  rw [e]
  refine (hK.mem y₀).compl.inter (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k =>
    (((p412h_meas_subset_O hK (isCompact_closedBall _ _) c r).inter
      (p412h_meas_subset_O hK (isCompact_closedBall _ _) c r)).inter
      (p412h_meas_subset_O hK (isCompact_range (gmPth k).continuous) c r)).inter
      (MeasurableSet.const _))

end LQGMetric.GM
