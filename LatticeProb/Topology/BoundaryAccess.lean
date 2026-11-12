/-
# Boundary points of a complementary domain of a locally connected compact set are accessible

Let `K ⊆ ℂ` be compact and locally connected and `W` a component of `Kᶜ`. Every point `x` of the closure of `W` is
the endpoint of a curve `β : [0, 1] → ℂ` with `β 1 = x` and `β [0, 1) ⊆ W`. Since only finitely many components of
`W ∩ ball x r` meet `ball x (r / 4)` (`finite_connectedComponentsIn_inter_ball`), one of them accumulates at `x`;
iterating with the radii `2⁻¹ ^ n` gives nested components `V n` accumulating at `x`, and paths joining points of
consecutive ones inside `V n` concatenate to the access curve (`exists_continuousOn_Icc_of_tendsto_paths`).
-/
import LatticeProb.Topology.AnnulusFinite
import LatticeProb.Topology.PathGluing

open Set Metric Filter
open scoped Topology

namespace LatticeProb.Topology

/-- **A component accumulating at a point.** Let `K ⊆ ℂ` be compact and locally connected, `W` a component of `Kᶜ`,
`Y ⊆ W` and `x ∈ closure Y`. For `r > 0`, some component `V` of `W ∩ ball x r` has `x ∈ closure (V ∩ Y)`. -/
theorem exists_mem_connectedComponentsIn_inter_ball_mem_closure {K : Set ℂ} (hK : IsCompact K)
    (hlc : IsLocallyConnectedSet K) {W : Set ℂ} (hW : W ∈ connectedComponentsIn Kᶜ) {Y : Set ℂ}
    (hYW : Y ⊆ W) {x : ℂ} (hx : x ∈ closure Y) {r : ℝ} (hr : 0 < r) :
    ∃ V ∈ connectedComponentsIn (W ∩ ball x r), x ∈ closure (V ∩ Y) := by
  have hS := finite_connectedComponentsIn_inter_ball hK hlc hW x hr
  have hsub : Y ∩ ball x (r / 4) ⊆ ⋃ V ∈ {V ∈ connectedComponentsIn (W ∩ ball x r) |
      (V ∩ ball x (r / 4)).Nonempty}, V ∩ Y := by
    rintro y ⟨hyY, hyb⟩
    have hyWr : y ∈ W ∩ ball x r := ⟨hYW hyY, ball_subset_ball (by linarith) hyb⟩
    exact mem_iUnion₂.2 ⟨connectedComponentIn (W ∩ ball x r) y,
      ⟨⟨y, hyWr, rfl⟩, y, mem_connectedComponentIn hyWr, hyb⟩, mem_connectedComponentIn hyWr, hyY⟩
  have hx' : x ∈ closure (Y ∩ ball x (r / 4)) := by
    rw [inter_comm]
    exact isOpen_ball.inter_closure ⟨mem_ball_self (by linarith), hx⟩
  have h := closure_mono hsub hx'
  rw [hS.closure_biUnion] at h
  obtain ⟨V, hV, hxV⟩ := mem_iUnion₂.1 h
  exact ⟨V, hV.1, hxV⟩

/-- **Nested components accumulating at a point.** Let `K ⊆ ℂ` be compact and locally connected, `W` a component of
`Kᶜ`, `x ∈ closure W`, and `r n > 0` nonincreasing. There are components `V n` of `W ∩ ball x (r n)` with
`x ∈ closure (V n)` and `V (n + 1) ⊆ V n`. -/
theorem exists_nested_connectedComponentsIn_inter_ball {K : Set ℂ} (hK : IsCompact K)
    (hlc : IsLocallyConnectedSet K) {W : Set ℂ} (hW : W ∈ connectedComponentsIn Kᶜ) {x : ℂ}
    (hx : x ∈ closure W) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hrmono : ∀ n, r (n + 1) ≤ r n) :
    ∃ V : ℕ → Set ℂ, ∀ n, V n ∈ connectedComponentsIn (W ∩ ball x (r n)) ∧ x ∈ closure (V n) ∧
      V (n + 1) ⊆ V n := by
  have hstep : ∀ (n : ℕ) (Y : Set ℂ), ∃ V : Set ℂ, Y ⊆ W → x ∈ closure Y →
      V ∈ connectedComponentsIn (W ∩ ball x (r n)) ∧ x ∈ closure (V ∩ Y) := by
    intro n Y
    by_cases h : Y ⊆ W ∧ x ∈ closure Y
    · obtain ⟨V, hV, hxV⟩ :=
        exists_mem_connectedComponentsIn_inter_ball_mem_closure hK hlc hW h.1 h.2 (hr n)
      exact ⟨V, fun _ _ => ⟨hV, hxV⟩⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose f hf using hstep
  obtain ⟨V, hV0, hVs⟩ : ∃ V : ℕ → Set ℂ, V 0 = f 0 W ∧ ∀ n, V (n + 1) = f (n + 1) (V n) :=
    ⟨fun n => Nat.rec (f 0 W) (fun n Vn => f (n + 1) Vn) n, rfl, fun n => rfl⟩
  have hgood : ∀ n, V n ∈ connectedComponentsIn (W ∩ ball x (r n)) ∧ x ∈ closure (V n) := by
    intro n
    induction n with
    | zero =>
      rw [hV0]
      obtain ⟨h1, h2⟩ := hf 0 W subset_rfl hx
      exact ⟨h1, closure_mono inter_subset_left h2⟩
    | succ n ih =>
      rw [hVs]
      obtain ⟨h1, h2⟩ := hf (n + 1) (V n)
        ((subset_of_mem_connectedComponentsIn ih.1).trans inter_subset_left) ih.2
      exact ⟨h1, closure_mono inter_subset_left h2⟩
  refine ⟨V, fun n => ⟨(hgood n).1, (hgood n).2, ?_⟩⟩
  have h2 := (hf (n + 1) (V n)
    ((subset_of_mem_connectedComponentsIn (hgood n).1).trans inter_subset_left) (hgood n).2).2
  rw [← hVs] at h2
  obtain ⟨z, hz1, hz2⟩ := closure_nonempty_iff.1 ⟨x, h2⟩
  obtain ⟨y, -, hy⟩ := (hgood n).1
  have hzc : z ∈ connectedComponentIn (W ∩ ball x (r n)) y := hy ▸ hz2
  rw [← hy, connectedComponentIn_eq hzc]
  exact (isConnected_of_mem_connectedComponentsIn (hgood (n + 1)).1).isPreconnected.subset_connectedComponentIn
    hz1 ((subset_of_mem_connectedComponentsIn (hgood (n + 1)).1).trans
      (inter_subset_inter_right _ (ball_subset_ball (hrmono n))))

/-- **Accessibility of boundary points.** Let `K ⊆ ℂ` be compact and locally connected and `W` a component of `Kᶜ`.
Every `x ∈ closure W` is the endpoint `β 1` of a curve `β`, continuous on `[0, 1]`, with `β '' [0, 1) ⊆ W`. -/
theorem exists_access_curve_of_mem_closure {K : Set ℂ} (hK : IsCompact K) (hlc : IsLocallyConnectedSet K)
    {W : Set ℂ} (hW : W ∈ connectedComponentsIn Kᶜ) {x : ℂ} (hx : x ∈ closure W) :
    ∃ β : ℝ → ℂ, ContinuousOn β (Icc 0 1) ∧ β 1 = x ∧ β '' Ico 0 1 ⊆ W := by
  obtain ⟨V, hV⟩ := exists_nested_connectedComponentsIn_inter_ball hK hlc hW hx
    (r := fun n => 2⁻¹ ^ n) (fun n => by positivity)
    (fun n => by rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) (by norm_num))
  have hWo : IsOpen W := isOpen_of_mem_connectedComponentsIn_compl hK.isClosed hW
  have hVo : ∀ n, IsOpen (V n) := fun n => by
    obtain ⟨y, -, hy⟩ := (hV n).1
    rw [← hy]
    exact (hWo.inter isOpen_ball).connectedComponentIn
  have hne : ∀ n, (V n).Nonempty := fun n => closure_nonempty_iff.1 ⟨x, (hV n).2.1⟩
  choose c hc using hne
  have hj : ∀ n, JoinedIn (V n) (c n) (c (n + 1)) := fun n =>
    ((hVo n).isConnected_iff_isPathConnected.1 (isConnected_of_mem_connectedComponentsIn (hV n).1)).joinedIn
      _ (hc n) _ ((hV n).2.2 (hc (n + 1)))
  obtain ⟨β, hβc, hβ1, hβ⟩ := exists_continuousOn_Icc_of_tendsto_paths (x := x) (fun n => (hj n).somePath)
    (ρ := fun n => 2⁻¹ ^ n) (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (fun n s => mem_ball.1 (subset_of_mem_connectedComponentsIn (hV n).1 ((hj n).somePath_mem s)).2)
  refine ⟨β, hβc, hβ1, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨n, s, hs⟩ := hβ t ht
  rw [← hs]
  exact (subset_of_mem_connectedComponentsIn (hV n).1 ((hj n).somePath_mem s)).1

/-- **Accessibility of boundary points**, frontier form. -/
theorem exists_access_curve {K : Set ℂ} (hK : IsCompact K) (hlc : IsLocallyConnectedSet K)
    {W : Set ℂ} (hW : W ∈ connectedComponentsIn Kᶜ) {x : ℂ} (hx : x ∈ frontier W) :
    ∃ β : ℝ → ℂ, ContinuousOn β (Icc 0 1) ∧ β 1 = x ∧ β '' Ico 0 1 ⊆ W :=
  exists_access_curve_of_mem_closure hK hlc hW (frontier_subset_closure hx)

end LatticeProb.Topology
