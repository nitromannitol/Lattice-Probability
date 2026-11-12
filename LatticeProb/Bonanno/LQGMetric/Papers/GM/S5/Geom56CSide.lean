/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CSide at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CAux

/-!
# GM Lemma 5.6, condition (2) at one junction, with planar hypotheses (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, condition (2)
(l. 2982–2989), decisions D69 and D77.

`sepDiscNear_side`: the tube `tubeOf s (Fc ∪ sqF s r z P ∪ Fr)`, with `Fc` the grid corridor of
`exists_corridor` at `u` (half-lengths `50 s`, `2 s`), `P ∋ a, c` a preconnected set in
`cl B_{2r}(z)` (GM's `π₋ ∪ L₋`, joined to the corridor at its centre `c`), and `Fr` squares inside
a set `Y` (the rest of the tube). Four planar hypotheses suffice:
(H1) corridor points outside `B_{19 s}(u)` are at distance `≥ s` from `Y`;
(H2) `P` is at distance `≥ 4 s` from `Y`; (H3) `P` is at distance `≥ 25 s` from `u`;
(H4) `b` is off the corridor and at distance `> 3 s` from `P`.
Then `SepDiscNear` at `u` with `O_{u'}` of radius `20 s` and separation `s`.
The same theorem serves the junction at `v` (GM: "a similar argument applies"). Own elementary
argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology

namespace LQGMetric.GM
open Blueprint

/-- **condition (2) at one junction**; see the module docstring -/
theorem sepDiscNear_side {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {z c e u a b : ℂ} {P Y : Set ℂ}
    {Fc Fr : Finset (ℤ × ℤ)} (he : ‖e‖ = 1)
    (hc : ⋃ m ∈ Fc, gridSquare s m = rectC c e (50 * s) (2 * s))
    (hξ1 : 48.5 * s ≤ ((u - c) * (starRingEnd ℂ) e).re)
    (hξ2 : ((u - c) * (starRingEnd ℂ) e).re ≤ 49.5 * s)
    (hη : |((u - c) * (starRingEnd ℂ) e).im| ≤ s / 2)
    (hP : IsPreconnected P) (hPB : P ⊆ closedBall z (2 * r)) (haP : a ∈ P) (hcP : c ∈ P)
    (hFr : ⋃ m ∈ Fr, gridSquare s m ⊆ Y)
    (H1 : ∀ x ∈ rectC c e (50 * s) (2 * s), 19 * s ≤ dist x u → ∀ y ∈ Y, s ≤ dist x y)
    (H2 : ∀ p ∈ P, ∀ y ∈ Y, 4 * s ≤ dist p y) (H3 : ∀ p ∈ P, 25 * s ≤ dist p u)
    (H4 : b ∉ rectC c e (50 * s) (2 * s)) (H4' : ∀ p ∈ P, 3 * s < dist p b) :
    SepDiscNear (tubeOf s (Fc ∪ sqF s r z P ∪ Fr)) (20 * s) u a b s := by
  set Fp := sqF s r z P
  have hnear : ∀ x ∈ ⋃ m ∈ Fp, gridSquare s m, ∃ p ∈ P, dist x p ≤ 3 * s := by
    intro x hx
    rw [mem_iUnion₂] at hx
    obtain ⟨m, hm, hxm⟩ := hx
    exact exists_near_of_mem_sq hs ((mem_sqF hs hr hPB).1 hm) hxm
  rw [abs_le] at hη
  refine sepDiscNear_of_layout hs he (by positivity) (by linarith) (by linarith) hc hP
    (subset_tubeOf_of_sqF hs hr hPB (fun m hm => Finset.mem_union_left _
      (Finset.mem_union_right _ hm)))
    (subset_iUnion_sqF hs hr hPB) (fun m hm => (mem_sqF hs hr hPB).1 hm) ⟨c, hcP, ?_⟩ ?_ ?_ ?_ ?_
    haP ?_
  · refine ⟨?_, ?_⟩ <;> simp only [sub_self, zero_mul, Complex.zero_re, Complex.zero_im,
      abs_zero] <;> positivity
  · refine ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  · exact abs_lt.2 ⟨by linarith, by linarith⟩
  · filter_upwards [ball_mem_nhds u hs] with u' hu' m hm
    rw [Set.disjoint_left]
    intro x hxm hxB
    obtain ⟨p, hpP, hxp⟩ := hnear x (mem_biUnion hm hxm)
    have h3 := H3 p hpP
    have := dist_triangle p x u'
    have := dist_triangle p u' u
    rw [mem_ball] at hu' hxB
    rw [dist_comm] at hxp
    linarith
  · filter_upwards [ball_mem_nhds u hs] with u' hu'
    rintro x ⟨hx | hx, hxB⟩ y hy
    · refine H1 x hx ?_ y (hFr hy)
      rw [mem_ball, not_lt] at hxB
      rw [mem_ball] at hu'
      have := dist_triangle x u u'
      rw [dist_comm u u'] at this
      linarith
    · obtain ⟨p, hpP, hxp⟩ := hnear x hx
      have := H2 p hpP y (hFr hy)
      have := dist_triangle p x y
      rw [dist_comm] at hxp
      linarith
  · rintro (hb | hb)
    · exact H4 hb
    · obtain ⟨p, hpP, hxp⟩ := hnear b hb
      have := H4' p hpP
      rw [dist_comm] at hxp
      linarith

end LQGMetric.GM
