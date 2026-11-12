/-
# Gluing a sequence of paths that shrinks to a point

Let `X` be a metric space, `c : ℕ → X`, and `γ n` a path from `c n` to `c (n + 1)` lying in the ball of radius `ρ n`
about a point `x`, where `ρ n → 0`. Running `γ n` on the interval `[1 - 2⁻¹ ^ n, 1 - 2⁻¹ ^ (n + 1)]` and giving the
value `x` at time `1` defines a curve that is continuous on `[0, 1]`, ends at `x`, and before time `1` only takes
values on the paths `γ n`.
-/
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Metric
open scoped Topology

namespace LatticeProb.Topology

/-- **Infinite concatenation of paths, with its time grid.** Paths `γ n` from `c n` to `c (n + 1)` inside balls
`ball x (ρ n)` with `ρ n → 0` concatenate to a curve `β`, continuous on `[0, 1]`, with `β 1 = x`, `β t` on some
`γ n` for `t ∈ [0, 1)`, and `β` running `γ n` affinely on `[1 - 2⁻¹ ^ n, 1 - 2⁻¹ ^ (n + 1)]`. -/
theorem exists_continuousOn_Icc_of_tendsto_paths_grid {X : Type*} [MetricSpace X] {x : X} {c : ℕ → X}
    (γ : ∀ n, Path (c n) (c (n + 1))) {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0))
    (hγρ : ∀ n, ∀ s, dist (γ n s) x < ρ n) :
    ∃ β : ℝ → X, ContinuousOn β (Icc 0 1) ∧ β 1 = x ∧ (∀ t ∈ Ico 0 1, ∃ n, β t ∈ range (γ n)) ∧
      ∀ n, ∀ t ∈ Icc (1 - 2⁻¹ ^ n) (1 - 2⁻¹ ^ (n + 1)),
        β t = (γ n).extend ((t - (1 - 2⁻¹ ^ n)) / 2⁻¹ ^ (n + 1)) := by
  classical
  -- the time grid `a n = 1 - 2⁻¹ ^ n`
  set a : ℕ → ℝ := fun n => 1 - 2⁻¹ ^ n with hadef
  have ha0 : a 0 = 0 := by simp [hadef]
  have hstep : ∀ n, a (n + 1) - a n = 2⁻¹ ^ (n + 1) := fun n => by simp only [hadef]; ring
  have hamono : StrictMono a := strictMono_nat_of_lt_succ fun n => by
    have h1 := hstep n
    have h2 : (0 : ℝ) < 2⁻¹ ^ (n + 1) := by positivity
    linarith
  have halt : ∀ n, a n < 1 := fun n => by
    have h2 : (0 : ℝ) < 2⁻¹ ^ n := by positivity
    simp only [hadef]
    linarith
  have hlim : ∀ t < 1, ∃ n, t < a n := by
    intro t ht
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
    obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds (sub_pos.2 ht))).exists
    exact ⟨n, by simp only [hadef]; linarith⟩
  have hcover : ∀ y : ℝ, 0 ≤ y → y < 1 → ∃ m, a m ≤ y ∧ y ≤ a (m + 1) := by
    intro y hy0 hy1
    obtain ⟨n, hn⟩ := hlim y hy1
    have hex : ∃ m, y < a (m + 1) := by
      rcases n with _ | n
      · rw [ha0] at hn
        linarith
      · exact ⟨n, hn⟩
    refine ⟨Nat.find hex, ?_, (Nat.find_spec hex).le⟩
    rcases hm : Nat.find hex with _ | j
    · rw [ha0]
      exact hy0
    · exact not_lt.1 (Nat.find_min hex (show j < Nat.find hex by omega))
  -- the glued curve, described on each interval of the grid
  obtain ⟨β, hβ1, hβI⟩ : ∃ β : ℝ → X, β 1 = x ∧ ∀ n, ∀ t ∈ Icc (a n) (a (n + 1)),
      β t = (γ n).extend ((t - a n) / (a (n + 1) - a n)) := by
    refine ⟨fun t => if h : ∃ n, t ≤ a (n + 1) then
      (γ (Nat.find h)).extend ((t - a (Nat.find h)) / (a (Nat.find h + 1) - a (Nat.find h))) else x,
      ?_, ?_⟩
    · have h : ¬ ∃ n, (1 : ℝ) ≤ a (n + 1) := fun ⟨n, hn⟩ => (halt (n + 1)).not_ge hn
      exact dite_eq_right h
    · intro n t ht
      have h : ∃ n, t ≤ a (n + 1) := ⟨n, ht.2⟩
      dsimp only
      rw [dite_eq_left h]
      have hle : Nat.find h ≤ n := Nat.find_min' h ht.2
      have hspec : t ≤ a (Nat.find h + 1) := Nat.find_spec h
      generalize Nat.find h = m at hle hspec ⊢
      rcases hle.lt_or_eq with hlt | rfl
      · have h1 : a (m + 1) ≤ a n := hamono.monotone hlt
        have htm : t = a (m + 1) := le_antisymm hspec (h1.trans ht.1)
        have hn : m + 1 = n := hamono.injective (le_antisymm h1 (ht.1.trans htm.le))
        subst hn
        rw [htm, div_self (sub_pos.2 (hamono (Nat.lt_succ_self m))).ne', sub_self, zero_div,
          Path.extend_one, Path.extend_zero]
      · rfl
  have hcontI : ∀ n, ContinuousOn β (Icc (a n) (a (n + 1))) := by
    intro n
    have hc : Continuous fun t : ℝ => (γ n).extend ((t - a n) / (a (n + 1) - a n)) :=
      (γ n).continuous_extend.comp ((continuous_id.sub continuous_const).div_const _)
    exact hc.continuousOn.congr fun t ht => hβI n t ht
  have hcont : ∀ n, ContinuousOn β (Icc 0 (a n)) := by
    intro n
    induction n with
    | zero =>
      rw [ha0, Icc_self]
      exact continuousOn_singleton _ _
    | succ n ih =>
      have h0 : 0 ≤ a n := by
        rw [← ha0]
        exact hamono.monotone (Nat.zero_le n)
      rw [← Icc_union_Icc_eq_Icc h0 (hamono.monotone n.le_succ)]
      exact ih.union_of_isClosed (hcontI n) isClosed_Icc isClosed_Icc
  have hrange : ∀ t ∈ Ico (0 : ℝ) 1, ∃ n, β t ∈ range (γ n) := by
    intro t ht
    obtain ⟨m, hm1, hm2⟩ := hcover t ht.1 ht.2
    refine ⟨m, ?_⟩
    rw [hβI m t ⟨hm1, hm2⟩, ← Path.extend_range]
    exact mem_range_self _
  refine ⟨β, ?_, hβ1, hrange, fun n t ht => ?_⟩
  swap
  · have h := hβI n t ht
    rw [hstep n] at h
    exact h
  intro t ht
  rcases ht.2.lt_or_eq with ht1 | rfl
  · obtain ⟨n, hn⟩ := hlim t ht1
    refine ((hcont n) t ⟨ht.1, hn.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio (a n), isOpen_Iio, hn, fun y hy => ⟨hy.2.1, hy.1.le⟩⟩
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hρ.eventually (gt_mem_nhds hε))
    refine ⟨1 - a N, sub_pos.2 (halt N), ?_⟩
    intro y hy hyd
    rw [hβ1]
    rcases hy.2.lt_or_eq with hy1 | rfl
    · obtain ⟨m, hm1, hm2⟩ := hcover y hy.1 hy1
      have hyN : a N < y := by
        rw [Real.dist_eq, abs_sub_lt_iff] at hyd
        linarith [hyd.2]
      have hmN : N ≤ m := by
        by_contra h
        have := hamono.monotone (show m + 1 ≤ N by omega)
        linarith
      obtain ⟨s, hs⟩ : β y ∈ range (γ m) := by
        rw [hβI m y ⟨hm1, hm2⟩, ← Path.extend_range]
        exact mem_range_self _
      rw [← hs]
      exact (hγρ m s).trans (hN m hmN)
    · rw [hβ1, dist_self]
      exact hε

/-- **Infinite concatenation of paths.** Paths `γ n` from `c n` to `c (n + 1)` inside balls `ball x (ρ n)` with
`ρ n → 0` concatenate to a curve `β`, continuous on `[0, 1]`, with `β 1 = x` and `β t` on some `γ n` for
`t ∈ [0, 1)`. -/
theorem exists_continuousOn_Icc_of_tendsto_paths {X : Type*} [MetricSpace X] {x : X} {c : ℕ → X}
    (γ : ∀ n, Path (c n) (c (n + 1))) {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (𝓝 0))
    (hγρ : ∀ n, ∀ s, dist (γ n s) x < ρ n) :
    ∃ β : ℝ → X, ContinuousOn β (Icc 0 1) ∧ β 1 = x ∧ ∀ t ∈ Ico 0 1, ∃ n, β t ∈ range (γ n) := by
  obtain ⟨β, hc, h1, hr, -⟩ := exists_continuousOn_Icc_of_tendsto_paths_grid γ hρ hγρ
  exact ⟨β, hc, h1, hr⟩

end LatticeProb.Topology
