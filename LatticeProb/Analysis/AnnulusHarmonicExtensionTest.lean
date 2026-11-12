import LatticeProb.Analysis.AnnulusThickeningVolume
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsHarmonicExtension

/-!
# Test functions on an annulus from the discrete harmonic extension

Let `D = B_r(c) \ B̄_s(c)` with `0 < s < r` be an annulus in the plane, and let a multigraph carry a cell `H x ⊆ ℂ` at
each vertex `x`, every cell being preconnected. Let `f` be boundary data equal to `1` on the inner circle `∂B_s(c)` and
to `0` on the outer circle `∂B_r(c)`, and let `g` be the discrete harmonic extension of `f` in the sense of
Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*, (1.6) (`IsHarmonicExtension`): on the vertices
`V(D)` whose cells meet `D`, `g` is the supremum of `f` over the part of the cell on `∂D` when the cell meets `∂D`, and
is discrete harmonic otherwise.

If no cell meets both circles (for instance, if every cell has diameter less than `r - s`), the function
`annulusTestFunction` equal to `g` on `V(D)`, to `1` on the other vertices whose cells meet `B̄_s(c)`, and to `0`
elsewhere, is a test function for the condenser `(V(B̄_s(c)), V(B_r(c)))`: it is `1` on `V(B̄_s(c))`, it vanishes off
`V(B_r(c))`, and it has no increment across any pair of intersecting cells one of which does not meet `D`. Hence its
Dirichlet energy is carried by the edges inside `V(D)`, where it equals `g`.

This is the comparison between the discrete harmonic function of Berestycki–Gwynne, *Random walks on mated-CRT
planar maps and Liouville Brownian motion*, Lemma 4.3, and the discrete harmonic extension of the continuum harmonic
function on the annulus to which the energy estimate of Gwynne–Miller–Sheffield, Theorem 3.2, applies.
-/

namespace LatticeProb

open Metric Set
open MatedCRTHarmonic

/-- The inner circle of a nondegenerate annulus lies in its frontier. -/
theorem sphere_subset_frontier_ball_diff_closedBall_inner (c : ℂ) {s r : ℝ} (hs : 0 < s) (hsr : s < r) :
    sphere c s ⊆ frontier (ball c r \ closedBall c s) := by
  intro p hp
  have hD : IsOpen (ball c r \ closedBall c s) := isOpen_ball.sdiff isClosed_closedBall
  rw [hD.frontier_eq]
  have hps : dist p c = s := mem_sphere.1 hp
  have hpr : p ∈ ball c r := mem_ball.2 (by linarith)
  refine ⟨?_, fun h => h.2 (sphere_subset_closedBall hp)⟩
  have h1 : p ∈ closure (closedBall c s)ᶜ := by
    rw [closure_compl, interior_closedBall c hs.ne']
    intro h
    have := mem_ball.1 h
    linarith
  have h2 := isOpen_ball.inter_closure ⟨hpr, h1⟩
  rw [Set.sdiff_eq]
  exact h2

/-- The outer circle of a nondegenerate annulus lies in its frontier. -/
theorem sphere_subset_frontier_ball_diff_closedBall_outer (c : ℂ) {s r : ℝ} (hs : 0 ≤ s) (hsr : s < r) :
    sphere c r ⊆ frontier (ball c r \ closedBall c s) := by
  intro p hp
  have hD : IsOpen (ball c r \ closedBall c s) := isOpen_ball.sdiff isClosed_closedBall
  rw [hD.frontier_eq]
  have hpr : dist p c = r := mem_sphere.1 hp
  refine ⟨?_, fun h => ?_⟩
  · have h1 : p ∈ (closedBall c s)ᶜ := by
      intro h
      have := mem_closedBall.1 h
      linarith
    have h2 : p ∈ closure (ball c r) := by
      rw [closure_ball c (hs.trans_lt hsr).ne']
      exact sphere_subset_closedBall hp
    have h3 := isClosed_closedBall.isOpen_compl.inter_closure ⟨h1, h2⟩
    rw [Set.sdiff_eq, Set.inter_comm]
    exact h3
  · have := mem_ball.1 h.1
    linarith

/-- A preconnected set which meets `t` and its complement meets the frontier of `t`. -/
theorem isPreconnected_inter_frontier_nonempty {K t : Set ℂ} (hK : IsPreconnected K) (h1 : (K ∩ t).Nonempty)
    (h2 : (K \ t).Nonempty) : (K ∩ frontier t).Nonempty := by
  by_contra hF
  have hfr : frontier t = closure t \ interior t := rfl
  rw [hfr] at hF
  have hcov : K ⊆ interior t ∪ (closure t)ᶜ := by
    intro p hp
    by_cases hpt : p ∈ interior t
    · exact Or.inl hpt
    · exact Or.inr fun hpc => hF ⟨p, hp, hpc, hpt⟩
  have hI : (K ∩ interior t).Nonempty := by
    obtain ⟨p, hpK, hpt⟩ := h1
    exact ⟨p, hpK, by_contra fun hpi => hF ⟨p, hpK, subset_closure hpt, hpi⟩⟩
  have hC : (K ∩ (closure t)ᶜ).Nonempty := by
    obtain ⟨p, hpK, hpt⟩ := h2
    exact ⟨p, hpK, fun hpc => hF ⟨p, hpK, hpc, fun hpi => hpt (interior_subset hpi)⟩⟩
  obtain ⟨p, -, hp1, hp2⟩ := hK _ _ isOpen_interior isClosed_closure.isOpen_compl hcov hI hC
  exact hp2 (interior_subset_closure hp1)

/-- A preconnected set which does not meet the annulus `B_r(c) \ B̄_s(c)` and meets the closed disc `B̄_s(c)` lies
in that disc. -/
theorem subset_closedBall_of_not_meets_annulus {K : Set ℂ} (hK : IsPreconnected K) {c : ℂ} {s r : ℝ}
    (hsr : s < r) (hKD : ¬(K ∩ (ball c r \ closedBall c s)).Nonempty)
    (hKs : (K ∩ closedBall c s).Nonempty) : K ⊆ closedBall c s := by
  have hcov : K ⊆ closedBall c s ∪ (ball c r)ᶜ := by
    intro p hp
    by_contra h
    simp only [mem_union, mem_compl_iff, not_or, not_not] at h
    exact hKD ⟨p, hp, h.2, h.1⟩
  have hdisj : K ∩ (closedBall c s ∩ (ball c r)ᶜ) = ∅ := by
    ext p
    simp only [mem_inter_iff, mem_compl_iff, mem_closedBall, mem_ball, mem_empty_iff_false, iff_false]
    rintro ⟨-, h1, h2⟩
    exact h2 (by linarith)
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hK _ _ isClosed_closedBall
      isOpen_ball.isClosed_compl hcov hdisj with h | h
  · exact h
  · obtain ⟨p, hpK, hps⟩ := hKs
    exact absurd (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hps) hsr)) (h hpK)

/-- A set of diameter less than `r - s` does not meet both circles `∂B_s(c)` and `∂B_r(c)`. -/
theorem not_meets_both_spheres_of_diam_lt {K : Set ℂ} (hb : Bornology.IsBounded K) {c : ℂ} {s r : ℝ}
    (hd : diam K < r - s) (hKs : (K ∩ sphere c s).Nonempty) : ¬(K ∩ sphere c r).Nonempty := by
  rintro ⟨q, hqK, hq⟩
  obtain ⟨p, hpK, hp⟩ := hKs
  have h1 := dist_le_diam_of_mem hb hpK hqK
  have h2 := dist_triangle q p c
  rw [mem_sphere.1 hq, mem_sphere.1 hp, dist_comm] at h2
  linarith

variable {V E : Type*}

open Classical in
/-- The test function on the condenser `(V(B̄_s(c)), V(B_r(c)))` built from a function `g` on `V(D)`,
`D = B_r(c) \ B̄_s(c)`: it is `g` on `V(D)`, `1` on the other vertices whose cells meet `B̄_s(c)`, and `0` elsewhere. -/
noncomputable def annulusTestFunction (H : V → Set ℂ) (c : ℂ) (s r : ℝ) (g : V → ℝ) (x : V) : ℝ :=
  if x ∈ verticesMeeting H (ball c r \ closedBall c s) then g x
  else if x ∈ verticesMeeting H (closedBall c s) then 1 else 0

section HarmonicExtension

variable (G : LFMultigraph V E) {H : V → Set ℂ} {c : ℂ} {s r : ℝ} {f : ℂ → ℝ} {g : V → ℝ}

/-- On a vertex of `V(D)` whose cell meets the inner circle, the harmonic extension equals `1`. -/
theorem IsHarmonicExtension.eq_one_of_meets_inner (hs : 0 < s) (hsr : s < r)
    (hf1 : ∀ z ∈ sphere c s, f z = 1) (hf0 : ∀ z ∈ sphere c r, f z = 0)
    (hg : G.IsHarmonicExtension H (ball c r \ closedBall c s) f g) {x : V}
    (hx : x ∈ verticesMeeting H (ball c r \ closedBall c s)) (hxs : (H x ∩ sphere c s).Nonempty) :
    g x = 1 := by
  obtain ⟨p, hpH, hp⟩ := hxs
  have hpF := sphere_subset_frontier_ball_diff_closedBall_inner c hs hsr hp
  have hlub := (hg x hx).1 ⟨p, hpH, hpF⟩
  refine hlub.unique (IsGreatest.isLUB ⟨⟨p, ⟨hpH, hpF⟩, hf1 p hp⟩, ?_⟩)
  rintro _ ⟨z, ⟨-, hzF⟩, rfl⟩
  rcases frontier_ball_diff_closedBall_subset c r s hzF with hz | hz
  · rw [hf0 z hz]; norm_num
  · rw [hf1 z hz]

/-- On a vertex of `V(D)` whose cell meets the outer circle but not the inner one, the harmonic extension
equals `0`. -/
theorem IsHarmonicExtension.eq_zero_of_meets_outer (hs : 0 ≤ s) (hsr : s < r)
    (hf0 : ∀ z ∈ sphere c r, f z = 0)
    (hg : G.IsHarmonicExtension H (ball c r \ closedBall c s) f g) {x : V}
    (hx : x ∈ verticesMeeting H (ball c r \ closedBall c s)) (hxr : (H x ∩ sphere c r).Nonempty)
    (hxs : ¬(H x ∩ sphere c s).Nonempty) : g x = 0 := by
  obtain ⟨p, hpH, hp⟩ := hxr
  have hpF := sphere_subset_frontier_ball_diff_closedBall_outer c hs hsr hp
  have hlub := (hg x hx).1 ⟨p, hpH, hpF⟩
  refine hlub.unique (IsGreatest.isLUB ⟨⟨p, ⟨hpH, hpF⟩, hf0 p hp⟩, ?_⟩)
  rintro _ ⟨z, ⟨hzH, hzF⟩, rfl⟩
  rcases frontier_ball_diff_closedBall_subset c r s hzF with hz | hz
  · rw [hf0 z hz]
  · exact absurd ⟨z, hzH, hz⟩ hxs

/-- The test function equals `1` on the vertices whose cells meet the closed inner disc. -/
theorem annulusTestFunction_eq_one (hH : ∀ x, IsPreconnected (H x)) (hs : 0 < s) (hsr : s < r)
    (hf1 : ∀ z ∈ sphere c s, f z = 1) (hf0 : ∀ z ∈ sphere c r, f z = 0)
    (hg : G.IsHarmonicExtension H (ball c r \ closedBall c s) f g) {x : V}
    (hx : x ∈ verticesMeeting H (closedBall c s)) : annulusTestFunction H c s r g x = 1 := by
  unfold annulusTestFunction
  by_cases hxD : x ∈ verticesMeeting H (ball c r \ closedBall c s)
  · simp only [hxD, ↓reduceIte]
    obtain ⟨p, hpH, hpD⟩ := hxD
    have hfr := isPreconnected_inter_frontier_nonempty (hH x) hx ⟨p, hpH, hpD.2⟩
    rw [frontier_closedBall c hs.ne'] at hfr
    exact IsHarmonicExtension.eq_one_of_meets_inner G hs hsr hf1 hf0 hg ⟨p, hpH, hpD⟩ hfr
  · simp only [hxD, hx, ↓reduceIte]

/-- The test function vanishes off the vertices whose cells meet the outer disc. -/
theorem annulusTestFunction_eq_zero (hsr : s < r) {x : V} (hx : x ∉ verticesMeeting H (ball c r)) :
    annulusTestFunction H c s r g x = 0 := by
  unfold annulusTestFunction
  have hD : x ∉ verticesMeeting H (ball c r \ closedBall c s) := fun ⟨p, hpH, hp⟩ => hx ⟨p, hpH, hp.1⟩
  have hB : x ∉ verticesMeeting H (closedBall c s) := fun ⟨p, hpH, hp⟩ =>
    hx ⟨p, hpH, mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hp) hsr)⟩
  simp only [hD, hB, ↓reduceIte]

/-- The test function equals `g` on `V(D)`. -/
theorem annulusTestFunction_eq_of_mem {x : V} (hx : x ∈ verticesMeeting H (ball c r \ closedBall c s)) :
    annulusTestFunction H c s r g x = g x := by
  unfold annulusTestFunction
  simp only [hx, ↓reduceIte]

/-- Across two intersecting cells, the first of which does not meet `D`, the test function has no increment. -/
theorem annulusTestFunction_eq_of_not_mem (hH : ∀ x, IsPreconnected (H x)) (hs : 0 < s) (hsr : s < r)
    (hf1 : ∀ z ∈ sphere c s, f z = 1) (hf0 : ∀ z ∈ sphere c r, f z = 0)
    (hsep : ∀ x, (H x ∩ sphere c s).Nonempty → ¬(H x ∩ sphere c r).Nonempty)
    (hg : G.IsHarmonicExtension H (ball c r \ closedBall c s) f g) {x y : V}
    (hx : x ∉ verticesMeeting H (ball c r \ closedBall c s)) (hxy : (H x ∩ H y).Nonempty) :
    annulusTestFunction H c s r g x = annulusTestFunction H c s r g y := by
  obtain ⟨p, hpx, hpy⟩ := hxy
  by_cases hxs : x ∈ verticesMeeting H (closedBall c s)
  · have hsub := subset_closedBall_of_not_meets_annulus (hH x) hsr hx hxs
    rw [annulusTestFunction_eq_one G hH hs hsr hf1 hf0 hg hxs,
      annulusTestFunction_eq_one G hH hs hsr hf1 hf0 hg ⟨p, hpy, hsub hpx⟩]
  · have hx0 : annulusTestFunction H c s r g x = 0 := by
      unfold annulusTestFunction
      simp only [hx, hxs, ↓reduceIte]
    have hpr : p ∉ ball c r := by
      intro hp
      by_cases hps : p ∈ closedBall c s
      · exact hxs ⟨p, hpx, hps⟩
      · exact hx ⟨p, hpx, hp, hps⟩
    rw [hx0]
    by_cases hyD : y ∈ verticesMeeting H (ball c r \ closedBall c s)
    · rw [annulusTestFunction_eq_of_mem hyD]
      obtain ⟨q, hqy, hqD⟩ := hyD
      have hfr := isPreconnected_inter_frontier_nonempty (hH y) ⟨q, hqy, hqD.1⟩ ⟨p, hpy, hpr⟩
      rw [frontier_ball c (hs.trans hsr).ne'] at hfr
      exact (IsHarmonicExtension.eq_zero_of_meets_outer G hs.le hsr hf0 hg ⟨q, hqy, hqD⟩ hfr
        fun h => hsep y h hfr).symm
    · by_cases hys : y ∈ verticesMeeting H (closedBall c s)
      · have hsub := subset_closedBall_of_not_meets_annulus (hH y) hsr hyD hys
        exact absurd (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (hsub hpy)) hsr)) hpr
      · unfold annulusTestFunction
        simp only [hyD, hys, ↓reduceIte]

/-- **The test function from the harmonic extension on an annulus.** If the cells are preconnected, no cell meets
both circles, `f = 1` on `∂B_s(c)`, `f = 0` on `∂B_r(c)` and `g` is the discrete harmonic extension of `f` on
`D = B_r(c) \ B̄_s(c)`, then `annulusTestFunction H c s r g` is `1` on `V(B̄_s(c))`, vanishes off `V(B_r(c))`, equals
`g` on `V(D)`, and takes the same value at the two ends of every pair of intersecting cells not both meeting `D`. -/
theorem annulusTestFunction_spec (hH : ∀ x, IsPreconnected (H x)) (hs : 0 < s) (hsr : s < r)
    (hf1 : ∀ z ∈ sphere c s, f z = 1) (hf0 : ∀ z ∈ sphere c r, f z = 0)
    (hsep : ∀ x, (H x ∩ sphere c s).Nonempty → ¬(H x ∩ sphere c r).Nonempty)
    (hg : G.IsHarmonicExtension H (ball c r \ closedBall c s) f g) :
    (∀ x ∈ verticesMeeting H (closedBall c s), annulusTestFunction H c s r g x = 1) ∧
    (∀ x, x ∉ verticesMeeting H (ball c r) → annulusTestFunction H c s r g x = 0) ∧
    (∀ x ∈ verticesMeeting H (ball c r \ closedBall c s), annulusTestFunction H c s r g x = g x) ∧
    (∀ x y, (H x ∩ H y).Nonempty →
      (x ∉ verticesMeeting H (ball c r \ closedBall c s) ∨ y ∉ verticesMeeting H (ball c r \ closedBall c s)) →
      annulusTestFunction H c s r g x = annulusTestFunction H c s r g y) := by
  refine ⟨fun x hx => annulusTestFunction_eq_one G hH hs hsr hf1 hf0 hg hx,
    fun x hx => annulusTestFunction_eq_zero hsr hx, fun x hx => annulusTestFunction_eq_of_mem hx,
    fun x y hxy h => ?_⟩
  rcases h with h | h
  · exact annulusTestFunction_eq_of_not_mem G hH hs hsr hf1 hf0 hsep hg h hxy
  · rw [Set.inter_comm] at hxy
    exact (annulusTestFunction_eq_of_not_mem G hH hs hsr hf1 hf0 hsep hg h hxy).symm

end HarmonicExtension

end LatticeProb
