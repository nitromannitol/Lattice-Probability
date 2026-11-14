/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.FixedBallCover at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.PaperObjects
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.Linarith

/-! Fixed balls for the finite excursion coupling. The ball radius and its
inner margin are chosen before the skeleton length and the stage partitions.
Later cell refinements preserve the same displacement bound. -/

open Set Metric

namespace BouRabeeGwynne

/-- A compact collar admits a finite cover by quarter-radius balls, with all
full closed balls in the prescribed open neighborhood and an arbitrarily
small common positive radius. -/
theorem exists_fixed_ball_cover {d : ℕ} {K W : Set (Euc d)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rmax ∧ ∃ centers : Finset (Euc d),
      (∀ c ∈ centers, c ∈ K) ∧
      (∀ z ∈ K, ∃ c ∈ centers, z ∈ ball c (r / 4)) ∧
      (∀ c ∈ centers, closedBall c r ⊆ W) := by
  classical
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  let r := min δ rmax
  have hr : 0 < r := lt_min hδ hrmax
  obtain ⟨S, hSK, hS, hcover⟩ := hK.finite_cover_balls (show 0 < r / 4 by positivity)
  refine ⟨r, hr, min_le_right _ _, hS.toFinset, ?_, ?_, ?_⟩
  · intro c hc
    exact hSK (hS.mem_toFinset.mp hc)
  · intro z hz
    obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp (hcover hz)
    exact ⟨c, hS.mem_toFinset.mpr hc, hzc⟩
  · intro c hc
    exact (closedBall_subset_cthickening (hSK (hS.mem_toFinset.mp hc)) r).trans
      ((cthickening_mono (min_le_left δ rmax) K).trans hδW)

/-- Any sufficiently small cell meeting the compact collar fits in the
half-radius part of one of the fixed balls. Only its actual pairwise distance
bound is used, so an unbounded set cannot enter through a default real diameter. -/
theorem exists_inner_ball_for_cell {d : ℕ} {K C : Set (Euc d)} {r : ℝ}
    {centers : Finset (Euc d)}
    (hcover : ∀ z ∈ K, ∃ c ∈ centers, z ∈ ball c (r / 4))
    (hCK : (C ∩ K).Nonempty)
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ r / 4) :
    ∃ c ∈ centers, C ⊆ ball c (r / 2) := by
  obtain ⟨x, hxC, hxK⟩ := hCK
  obtain ⟨c, hc, hxc⟩ := hcover x hxK
  refine ⟨c, hc, fun y hy => ?_⟩
  have hxy := hdiam y hy x hxC
  have htri := dist_triangle y x c
  have hxc' : dist x c < r / 4 := hxc
  change dist y c < r / 2
  linarith

lemma near_cover_point_mem_inner_ball {d : ℕ} {c z x : Euc d} {r : ℝ}
    (hz : z ∈ ball c (r / 4)) (hxz : dist x z ≤ r / 4) :
    x ∈ ball c (r / 2) := by
  have hzc : dist z c < r / 4 := hz
  have htri := dist_triangle x z c
  change dist x c < r / 2
  linarith

/-- The common inner margin forces every active excursion to make the same
minimum displacement, independently of all later partition refinements. -/
lemma inner_ball_exit_displacement {d : ℕ} {c x y : Euc d} {r : ℝ}
    (hx : x ∈ closedBall c (r / 2)) (hy : y ∉ ball c r) :
    r / 2 ≤ dist x y := by
  have hxc : dist x c ≤ r / 2 := hx
  have hyc : r ≤ dist y c := le_of_not_gt hy
  have htri := dist_triangle y x c
  rw [dist_comm y x] at htri
  linarith

end BouRabeeGwynne
