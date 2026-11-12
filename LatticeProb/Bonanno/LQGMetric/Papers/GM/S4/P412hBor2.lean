/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412hBor2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412hBor1

/-!
# Borel tests for the sides of circle arcs (D98 §2, packet P-L414Borel, part 2)

Source: decision D98 §2 (method of `gmE_unbounded_iff` / `gmE_mem_closure_open_iff`, L46MeasE1);
own descriptive-set-theory arguments (GM do not discuss measurability).

* `P412hCT F` — Borel complement tests for a random closed set `F` (point events and
  `{S ⊆ (F x)ᶜ}` for compact `S`); stable under unions (`p412h_ct_union`), satisfied by regular
  random closed sets (`p412h_ct_of_rc`), constants, and by `α ∪ K` for an arc
  `α = cc(∂B_r(c) ∖ K, y₀)` (`p412h_ct_arc`, through the points of rational angle);
* `p412h_meas_dgW`, `p412h_meas_dgB`, `p412h_meas_closure` — the sides `dgW F`, `dgB F` and
  closures of open random sets;
* `p412h_meas_arcN`, `p412h_meas_arcY` — the two conditions on an arc in the family `F` of
  `p412d_GML4_14` (`α ⊆ cl dgW(B̄ ∪ K)`, `y ∈ cl dgB(α ∪ K)`);
* `p412h_bs_sub_iff` — comparison of the bounded sides of two arcs in countable form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Topology Bornology
open LQGMetric.Topo.Crosscut LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {X : Type} [MeasurableSpace X]

/-- Borel complement tests for a random closed set -/
structure P412hCT (F : X → Set ℂ) : Prop where
  mem : ∀ w, MeasurableSet {x | w ∈ F x}
  closed : ∀ x, IsClosed (F x)
  sub : ∀ S : Set ℂ, IsCompact S → MeasurableSet {x | S ⊆ (F x)ᶜ}

theorem p412h_ct_of_rc {K : X → Set ℂ} (hK : P412hRC K) : P412hCT K :=
  ⟨hK.mem, hK.closed, fun S hS => by
    simp only [subset_compl_iff_disjoint_right]; exact p412h_meas_disj hK hS⟩

theorem p412h_ct_const {A : Set ℂ} (hA : IsClosed A) : P412hCT (fun _ : X => A) :=
  ⟨fun _ => MeasurableSet.const _, fun _ => hA, fun _ _ => MeasurableSet.const _⟩

theorem p412h_ct_union {F G : X → Set ℂ} (hF : P412hCT F) (hG : P412hCT G) :
    P412hCT (fun x => F x ∪ G x) := by
  refine ⟨fun w => ?_, fun x => (hF.closed x).union (hG.closed x), fun S hS => ?_⟩
  · simp only [mem_union, setOf_or]; exact (hF.mem w).union (hG.mem w)
  · simp only [compl_union, subset_inter_iff, setOf_and]; exact (hF.sub S hS).inter (hG.sub S hS)

/-- the unbounded side -/
theorem p412h_meas_dgW {F : X → Set ℂ} (hF : P412hCT F) (w : ℂ) :
    MeasurableSet {x | w ∈ dgW (F x)} := by
  have e : {x | w ∈ dgW (F x)} = {x | w ∈ F x}ᶜ ∩ ⋂ N : ℕ, ⋃ j : ℕ, ⋃ n : ℕ, ⋃ k : ℕ,
      ({_x | dist w (qd j) < 1 / ((n : ℝ) + 1)} ∩
        {x | closedBall (qd j) (1 / ((n : ℝ) + 1)) ⊆ (F x)ᶜ} ∩
        {_x | dist (gmPth k 0) (qd j) < 1 / ((n : ℝ) + 1)} ∩ {x | range (gmPth k) ⊆ (F x)ᶜ} ∩
        {_x | (N : ℝ) < ‖gmPth k 1‖}) := by
    ext x
    simp only [dgW, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_iInter, mem_iUnion]
    constructor
    · rintro ⟨hw, hu⟩
      refine ⟨hw, fun N => ?_⟩
      obtain ⟨j, n, k, h1, h2, h3, h4, h5⟩ :=
        (gmE_unbounded_iff (hF.closed x).isOpen_compl hw).1 hu N
      exact ⟨j, n, k, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · rintro ⟨hw, H⟩
      refine ⟨hw, (gmE_unbounded_iff (hF.closed x).isOpen_compl hw).2 fun N => ?_⟩
      obtain ⟨j, n, k, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := H N
      exact ⟨j, n, k, h1, h2, h3, h4, h5⟩
  rw [e]
  refine (hF.mem w).compl.inter (MeasurableSet.iInter fun N => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k => ?_)
  exact ((((MeasurableSet.const _).inter (hF.sub _ (isCompact_closedBall _ _))).inter
    (MeasurableSet.const _)).inter (hF.sub _ (isCompact_range (gmPth k).continuous))).inter
    (MeasurableSet.const _)

/-- the bounded side -/
theorem p412h_meas_dgB {F : X → Set ℂ} (hF : P412hCT F) (w : ℂ) :
    MeasurableSet {x | w ∈ dgB (F x)} := by
  have e : {x | w ∈ dgB (F x)} = {x | w ∈ F x}ᶜ \ {x | w ∈ dgW (F x)} := by
    ext x; simp only [dgB, dgW, mem_ofPred_eq, mem_diff, mem_compl_iff]; tauto
  rw [e]; exact (hF.mem w).compl.diff (p412h_meas_dgW hF w)

/-- closures of open random sets, at a measurable point -/
theorem p412h_meas_closure {O : X → Set ℂ} (hO : ∀ x, IsOpen (O x))
    (hm : ∀ w, MeasurableSet {x | w ∈ O x}) {y : X → ℂ} (hy : Measurable y) :
    MeasurableSet {x | y x ∈ closure (O x)} := by
  have e : {x | y x ∈ closure (O x)} = ⋂ m : ℕ, ⋃ i : ℕ,
      ({x | dist (qd i) (y x) < 1 / ((m : ℝ) + 1)} ∩ {x | qd i ∈ O x}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
    exact gmE_mem_closure_open_iff (hO x) (y x)
  rw [e]
  exact MeasurableSet.iInter fun m => MeasurableSet.iUnion fun i =>
    (measurableSet_lt (measurable_const.dist hy) measurable_const).inter (hm _)

/-- compact sets off `α ∪ K`, through the points of rational angle of `α` -/
theorem p412h_sub_arcK_iff {K : Set ℂ} (hK : IsClosed K) {c y₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {S : Set ℂ} (hS : IsCompact S) (hne : S.Nonempty) :
    S ⊆ (connectedComponentIn (sphere c r \ K) y₀ ∪ K)ᶜ ↔ Disjoint S K ∧
      ∃ m : ℕ, ∀ θ : ℚ, p412hPt c r θ ∈ connectedComponentIn (sphere c r \ K) y₀ →
        1 / ((m : ℝ) + 1) ≤ infDist (p412hPt c r θ) S := by
  set α := connectedComponentIn (sphere c r \ K) y₀
  constructor
  · intro h
    refine ⟨Set.disjoint_left.2 fun z hz hzK => h hz (Or.inr hzK), ?_⟩
    have hS' : S ⊆ (closure α)ᶜ := fun z hz hzc => h hz (closure_cc_sub K c y₀ r hzc)
    obtain ⟨δ, hδ, hδS⟩ := hS.exists_thickening_subset_open isClosed_closure.isOpen_compl hS'
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun θ hθ => ?_⟩
    by_contra hlt
    exact hδS ((mem_thickening_iff_infDist_lt hne).2 ((not_le.1 hlt).trans hm))
      (subset_closure hθ)
  · rintro ⟨hdis, m, hm⟩ z hzS hz
    rcases hz with hz | hz
    · have hzK := (connectedComponentIn_subset _ _ hz)
      obtain ⟨θ, hθ, hθd⟩ := p412h_rat_near hK hr hzK.1 hzK.2 (δ := 1 / ((m : ℝ) + 1))
        (by positivity)
      rw [← connectedComponentIn_eq hz] at hθ
      exact absurd ((infDist_le_dist_of_mem hzS).trans_lt hθd) (not_lt.2 (hm θ hθ))
    · exact Set.disjoint_left.1 hdis hzS hz

/-- **`α ∪ K` has Borel complement tests** -/
theorem p412h_ct_arc {K : X → Set ℂ} (hK : P412hRC K) {c y₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hy₀ : y₀ ∈ sphere c r) :
    P412hCT (fun x => connectedComponentIn (sphere c r \ K x) y₀ ∪ K x) := by
  refine ⟨fun w => ?_, fun x => isClosed_cc_union _ (hK.closed x) c y₀ r, fun S hS => ?_⟩
  · simp only [mem_union, setOf_or]; exact (p412h_meas_arc hK hr hy₀).union (hK.mem w)
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [empty_subset, setOf_true, MeasurableSet.univ]
  have e : {x | S ⊆ (connectedComponentIn (sphere c r \ K x) y₀ ∪ K x)ᶜ} =
      {x | Disjoint S (K x)} ∩ ⋃ m : ℕ, ⋂ θ : ℚ,
        ({x | p412hPt c r θ ∈ connectedComponentIn (sphere c r \ K x) y₀}ᶜ ∪
          {_x | 1 / ((m : ℝ) + 1) ≤ infDist (p412hPt c r θ) S}) := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, mem_union, mem_compl_iff]
    rw [p412h_sub_arcK_iff (hK.closed x) hr hS hne]
    simp only [imp_iff_not_or]
  rw [e]
  exact (p412h_meas_disj hK hS).inter (MeasurableSet.iUnion fun m => MeasurableSet.iInter
    fun θ => (p412h_meas_arc hK hr hy₀).compl.union (MeasurableSet.const _))

/-- an arc lies in a closed set iff its points of rational angle do -/
theorem p412h_arc_sub_iff {K : Set ℂ} (hK : IsClosed K) {c y₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {C : Set ℂ} (hC : IsClosed C) :
    connectedComponentIn (sphere c r \ K) y₀ ⊆ C ↔
      ∀ θ : ℚ, p412hPt c r θ ∈ connectedComponentIn (sphere c r \ K) y₀ → p412hPt c r θ ∈ C := by
  refine ⟨fun h θ hθ => h hθ, fun h u hu => ?_⟩
  by_contra huC
  obtain ⟨δ, hδ, hδC⟩ := Metric.isOpen_iff.1 hC.isOpen_compl u huC
  have huK := connectedComponentIn_subset _ _ hu
  obtain ⟨θ, hθ, hθd⟩ := p412h_rat_near hK hr huK.1 huK.2 hδ
  rw [← connectedComponentIn_eq hu] at hθ
  exact hδC (mem_ball.2 hθd) (h θ hθ)

/-- condition `α ⊆ cl dgW(B̄_r(c) ∪ K)` is Borel -/
theorem p412h_meas_arcN {K : X → Set ℂ} (hK : P412hRC K) {c y₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hy₀ : y₀ ∈ sphere c r) :
    MeasurableSet {x | connectedComponentIn (sphere c r \ K x) y₀ ⊆
      closure (dgW (closedBall c r ∪ K x))} := by
  have hCT := p412h_ct_union (p412h_ct_const (X := X) (isClosed_closedBall (x := c) (ε := r)))
    (p412h_ct_of_rc hK)
  have e : {x | connectedComponentIn (sphere c r \ K x) y₀ ⊆
      closure (dgW (closedBall c r ∪ K x))} = ⋂ θ : ℚ,
        ({x | p412hPt c r θ ∈ connectedComponentIn (sphere c r \ K x) y₀}ᶜ ∪
          {x | p412hPt c r θ ∈ closure (dgW (closedBall c r ∪ K x))}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
    rw [p412h_arc_sub_iff (hK.closed x) hr isClosed_closure]
    simp only [imp_iff_not_or]
  rw [e]
  exact MeasurableSet.iInter fun θ => (p412h_meas_arc hK hr hy₀).compl.union
    (p412h_meas_closure (fun x => p412d_isOpen_dgW (hCT.closed x)) (p412h_meas_dgW hCT)
      measurable_const)

/-- condition `y ∈ cl dgB(α ∪ K)` is Borel -/
theorem p412h_meas_arcY {K : X → Set ℂ} (hK : P412hRC K) {c y₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hy₀ : y₀ ∈ sphere c r) {y : X → ℂ} (hy : Measurable y) :
    MeasurableSet {x | y x ∈ closure (dgB (connectedComponentIn (sphere c r \ K x) y₀ ∪ K x))} :=
  p412h_meas_closure (fun x => p412d_isOpen_dgB ((p412h_ct_arc hK hr hy₀).closed x))
    (p412h_meas_dgB (p412h_ct_arc hK hr hy₀)) hy

/-- comparison of bounded sides in countable form -/
theorem p412h_bs_sub_iff {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hKo : IsPreconnected Kᶜ) {c₁ c₂ y₁ y₂ : ℂ} {r : ℝ} (hr : 0 < r) (hy₁ : y₁ ∈ sphere c₁ r)
    (hy₁K : y₁ ∉ K) (hne : (p412hBs K r c₁ y₁).Nonempty) :
    p412hBs K r c₁ y₁ ⊆ p412hBs K r c₂ y₂ ↔
      (∃ k : ℕ, qd k ∈ p412hBs K r c₁ y₁ ∧ qd k ∈ p412hBs K r c₂ y₂) ∧
      ∀ θ : ℚ, p412hPt c₂ r θ ∈ connectedComponentIn (sphere c₂ r \ K) y₂ →
        p412hPt c₂ r θ ∉ p412hBs K r c₁ y₁ := by
  have hO₁ : IsOpen (p412hBs K r c₁ y₁) := p412d_isOpen_dgB (isClosed_cc_union _ hK.isClosed _ _ _)
  constructor
  · intro h
    obtain ⟨k, hk⟩ := denseRange_qd.exists_mem_open hO₁ hne
    exact ⟨⟨k, hk, h hk⟩, fun θ hθ hθ₁ => p412d_dgB_compl _ (h hθ₁) (Or.inl hθ)⟩
  · rintro ⟨⟨k, hk₁, hk₂⟩, hθ⟩
    have hpre : IsPreconnected (p412hBs K r c₁ y₁) := by
      rw [p412hBs, p412d_dgB_eq_cc hK hKc hKo hr hy₁ hy₁K hk₁]
      exact isPreconnected_connectedComponentIn
    refine p412d_sub_dgB hpre (fun z hz hzF => ?_) hk₁ hk₂
    have hzK : z ∉ K := fun h => p412d_dgB_compl _ hz (Or.inr h)
    rcases hzF with hzα | hzK'
    · obtain ⟨δ, hδ, hδB⟩ := Metric.isOpen_iff.1 hO₁ z hz
      have hzS := connectedComponentIn_subset _ _ hzα
      obtain ⟨θ, hθα, hθd⟩ := p412h_rat_near hK.isClosed hr hzS.1 hzS.2 hδ
      rw [← connectedComponentIn_eq hzα] at hθα
      exact hθ θ hθα (hδB (mem_ball.2 hθd))
    · exact hzK hzK'

end LQGMetric.GM
