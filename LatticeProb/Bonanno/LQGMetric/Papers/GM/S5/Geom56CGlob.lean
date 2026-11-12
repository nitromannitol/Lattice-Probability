/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CGlob at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CSide

/-!
# GM Lemma 5.6: global properties of the corridor tube (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, l. 2976–2977
("Since `z − 2r, z + 2r ∈ P̃′` and `P̃′` is connected, it follows that `V_r(z)` is connected and
contains `z − 2r` and `z + 2r`").

`tube_isPreconnected`: the tube made of two corridors `Ru`, `Rv` (convex, tiled by squares), the
squares meeting `Pu`, `Pv` and `T` (preconnected), joined at `cu ∈ Pu ∩ Ru`, `u ∈ Ru ∩ T`,
`v ∈ Rv ∩ T`, `cv ∈ Pv ∩ Rv`, is preconnected. `dist_lt_two_of_mem_sq`: two points of one square
are at distance `< 2 s`. Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

lemma dist_lt_two_of_mem_sq {s : ℝ} (hs : 0 < s) {m : ℤ × ℤ} {x w : ℂ} (hx : x ∈ gridSquare s m)
    (hw : w ∈ gridSquare s m) : dist x w < 2 * s := by
  obtain ⟨a1, a2, a3, a4⟩ := hx
  obtain ⟨b1, b2, b3, b4⟩ := hw
  have h : dist x w ^ 2 < (2 * s) ^ 2 := by
    rw [dist_sq_eq]
    have e1 : (x.re - w.re) ^ 2 ≤ s ^ 2 := by apply sq_le_sq' <;> nlinarith
    have e2 : (x.im - w.im) ^ 2 ≤ s ^ 2 := by apply sq_le_sq' <;> nlinarith
    nlinarith
  exact (pow_lt_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1 h

/-- `V ∩ R` is preconnected for a closed convex `R` with nonempty interior inside `V` -/
lemma inter_convex_isPreconnected {V R : Set ℂ} (hR : Convex ℝ R) (hne : (interior R).Nonempty)
    (hV : interior R ⊆ V) : IsPreconnected (V ∩ R) := by
  refine hR.interior.isPreconnected.subset_closure (subset_inter hV interior_subset) ?_
  rw [hR.closure_interior_eq_closure_of_nonempty_interior hne]
  exact inter_subset_right.trans subset_closure

/-- a corridor glued to the squares meeting a set through a common point -/
lemma corridor_union_isPreconnected {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {z c : ℂ} {V R P : Set ℂ}
    (hR : Convex ℝ R) (hne : (interior R).Nonempty) (hRV : interior R ⊆ V)
    (hP : IsPreconnected P) (hPB : P ⊆ closedBall z (2 * r)) (hPV : P ⊆ V)
    (hQV : ∀ m ∈ sqF s r z P, interior (gridSquare s m) ⊆ V) (hcP : c ∈ P) (hcR : c ∈ R) :
    IsPreconnected ((V ∩ R) ∪ (V ∩ ⋃ m ∈ sqF s r z P, gridSquare s m)) :=
  (inter_convex_isPreconnected hR hne hRV).union' ⟨c, ⟨hPV hcP, hcR⟩, hPV hcP,
    subset_iUnion_sqF hs hr hPB hcP⟩
    (inter_squares_isPreconnected hs hP hPV (subset_iUnion_sqF hs hr hPB)
      (fun m hm => (mem_sqF hs hr hPB).1 hm) hQV)

/-- **the corridor tube is preconnected** (GM l. 2976–2977); see the module docstring -/
theorem tube_isPreconnected {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {z cu cv u v : ℂ}
    {Ru Rv Pu Pv T : Set ℂ} {Fcu Fcv : Finset (ℤ × ℤ)}
    (hcu : ⋃ m ∈ Fcu, gridSquare s m = Ru) (hcv : ⋃ m ∈ Fcv, gridSquare s m = Rv)
    (hRu : Convex ℝ Ru) (hRv : Convex ℝ Rv) (hneu : (interior Ru).Nonempty)
    (hnev : (interior Rv).Nonempty)
    (hPu : IsPreconnected Pu) (hPv : IsPreconnected Pv) (hT : IsPreconnected T)
    (hPuB : Pu ⊆ closedBall z (2 * r)) (hPvB : Pv ⊆ closedBall z (2 * r))
    (hTB : T ⊆ closedBall z (2 * r))
    (hcuP : cu ∈ Pu) (hcuR : cu ∈ Ru) (hcvP : cv ∈ Pv) (hcvR : cv ∈ Rv)
    (huR : u ∈ Ru) (huT : u ∈ T) (hvR : v ∈ Rv) (hvT : v ∈ T) :
    IsPreconnected (tubeOf s (Fcu ∪ sqF s r z Pu ∪ (Fcv ∪ sqF s r z Pv ∪ sqF s r z T))) := by
  set F := Fcu ∪ sqF s r z Pu ∪ (Fcv ∪ sqF s r z Pv ∪ sqF s r z T)
  set V := tubeOf s F
  have hsub : ∀ {G : Finset (ℤ × ℤ)}, G ⊆ F → interior (⋃ m ∈ G, gridSquare s m) ⊆ V :=
    fun hG => interior_mono (biUnion_subset_biUnion_left (fun m hm => hG hm))
  have hFcu : Fcu ⊆ F := fun m hm => by simp [F, hm]
  have hFcv : Fcv ⊆ F := fun m hm => by simp [F, hm]
  have hFpu : sqF s r z Pu ⊆ F := fun m hm => by simp [F, hm]
  have hFpv : sqF s r z Pv ⊆ F := fun m hm => by simp [F, hm]
  have hFT : sqF s r z T ⊆ F := fun m hm => by simp [F, hm]
  have hsq : ∀ {G : Finset (ℤ × ℤ)}, G ⊆ F → ∀ m ∈ G, interior (gridSquare s m) ⊆ V :=
    fun hG m hm => interior_gridSquare_subset_tubeOf (hG hm)
  have hRuV : interior Ru ⊆ V := by rw [← hcu]; exact hsub hFcu
  have hRvV : interior Rv ⊆ V := by rw [← hcv]; exact hsub hFcv
  have hPuV := subset_tubeOf_of_sqF hs hr hPuB hFpu
  have hPvV := subset_tubeOf_of_sqF hs hr hPvB hFpv
  have hTV := subset_tubeOf_of_sqF hs hr hTB hFT
  have A1 := corridor_union_isPreconnected hs hr hRu hneu hRuV hPu hPuB hPuV (hsq hFpu) hcuP hcuR
  have A3 := corridor_union_isPreconnected hs hr hRv hnev hRvV hPv hPvB hPvV (hsq hFpv) hcvP hcvR
  have A2 : IsPreconnected (V ∩ ⋃ m ∈ sqF s r z T, gridSquare s m) :=
    inter_squares_isPreconnected hs hT hTV (subset_iUnion_sqF hs hr hTB)
      (fun m hm => (mem_sqF hs hr hTB).1 hm) (hsq hFT)
  have A12 := A1.union' (t := V ∩ ⋃ m ∈ sqF s r z T, gridSquare s m) ⟨u, Or.inl ⟨hTV huT, huR⟩, hTV huT, subset_iUnion_sqF hs hr hTB huT⟩ A2
  have A123 := A12.union' (t := (V ∩ Rv) ∪ (V ∩ ⋃ m ∈ sqF s r z Pv, gridSquare s m))
    ⟨v, Or.inr ⟨hTV hvT, subset_iUnion_sqF hs hr hTB hvT⟩,
    Or.inl ⟨hTV hvT, hvR⟩⟩ A3
  convert A123 using 1
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm, hxm⟩ := mem_tubeOf_exists hx
    simp only [F, Finset.mem_union] at hm
    rcases hm with (hm | hm) | (hm | hm) | hm
    · exact Or.inl (Or.inl (Or.inl ⟨hx, hcu ▸ mem_biUnion hm hxm⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hx, mem_biUnion hm hxm⟩))
    · exact Or.inr (Or.inl ⟨hx, hcv ▸ mem_biUnion hm hxm⟩)
    · exact Or.inr (Or.inr ⟨hx, mem_biUnion hm hxm⟩)
    · exact Or.inl (Or.inr ⟨hx, mem_biUnion hm hxm⟩)
  · rintro (((h | h) | h) | (h | h)) <;> exact h.1

end LQGMetric.GM
