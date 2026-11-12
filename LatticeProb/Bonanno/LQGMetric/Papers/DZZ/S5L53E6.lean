/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53E6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeas

/-!
# DZZ Lemma 5.3, part 1: joint measurability of the tilde distance (P2-DZZ53E)

Input `hS` of `l53_far_count` (DZZ l. 2495–2502). DZZ take `𝓛₁`-measures of
`Λ_{z,far} = {z' ∈ ∂𝖡 : log D̃_{δδ̃}(z,z') ≥ …}` and probabilities of them without comment. Here
the tilde distance `D̃_δ(z,z') = D^{𝕍̃_{z,z'}}_δ(z,z')` (walled by its own box) is shown to be
jointly measurable in `(ω, z, z')`. This is our own elementary argument, reusing the rational-radius
reduction `lgdDZZ_eq_lgdRat` and `lgdRat_le_iff` of `LGDMeas` (P2-LGDMEAS). Steps:

* `isOpen_setOf_joinedIn`: `{(x, y) | x, y are joined in U}` is open for open `U ⊆ ℂ`.
* `dzzWall_ball_le_iff`: `D^K`-admissibility of a ball means `μ(B) ≤ δ²` and `B ⊆ K` (`K` closed).
* `isClosed_setOf_ball_subset_tildeBox`.
* **`measurable_lgdTilde`**: `(ω, (z, z')) ↦ D^{𝕍̃_{z,z'}}_δ[ν ω](z, z')` is measurable when the ball
  masses of `ν` are.
* **`measurableSet_l53Far`**: the far set `{((ω, z), z') | ¬ lgdLeExp … z z'}` is measurable (the
  shape of `S` in `l53_far_count`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

lemma isOpen_setOf_joinedIn {U : Set ℂ} (hU : IsOpen U) :
    IsOpen {p : ℂ × ℂ | JoinedIn U p.1 p.2} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨x, y⟩ h
  have hx : x ∈ U := h.mem.1
  have hC : IsOpen (pathComponentIn U x) := hU.pathComponentIn x
  refine Filter.mem_of_superset (prod_mem_nhds (hC.mem_nhds (mem_pathComponentIn_self hx))
    (hC.mem_nhds h)) ?_
  rintro ⟨x', y'⟩ ⟨hx', hy'⟩
  exact (JoinedIn.symm hx').trans hy'

lemma isClosed_setOf_ball_subset_tildeBox (c : ℂ) (r : ℝ) :
    IsClosed {p : ℂ × ℂ | Metric.ball c r ⊆ tildeBox p.1 p.2} := by
  have : {p : ℂ × ℂ | Metric.ball c r ⊆ tildeBox p.1 p.2} =
      ⋂ w ∈ Metric.ball c r, {p : ℂ × ℂ | w ∈ tildeBox p.1 p.2} := by
    ext p; simp [subset_def]
  rw [this]
  refine isClosed_biInter fun w _ => ?_
  show IsClosed ({p : ℂ × ℂ | |((w - (p.1 + p.2) / 2) * starRingEnd ℂ (p.2 - p.1)).re| ≤
      ‖p.2 - p.1‖ ^ 2} ∩ {p : ℂ × ℂ | |((w - (p.1 + p.2) / 2) * starRingEnd ℂ (p.2 - p.1)).im| ≤
      ‖p.2 - p.1‖ ^ 2})
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop))

variable {Ω : Type*} [MeasurableSpace Ω]

end DZZ
end LQGMetric
