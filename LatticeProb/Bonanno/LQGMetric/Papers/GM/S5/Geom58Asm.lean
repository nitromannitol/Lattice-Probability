/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Asm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Junc
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Paths

/-!
# GM Lemma 5.8: toolkit for assembling `U_r^{x,y}` from squares (task P2-M2L58)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3087–3092: "`U_r^{x,y}` is the interior of a finite union of squares …
connected and contains `x, y`").

* `mem_of_mem_interior_union'`: `w ∈ int (A ∪ B)`, `w ∉ int A`, `B` closed ⇒ `w ∈ B`
  (gives `U ⊆ V ∪ X ∪ Y`).
* `subset_interior_squares`: a set `K` lies in the interior of the union of the squares meeting it.
* `mem_comp_of_square`: a point of `U` in a square meeting a preconnected `K ⊆ U ∖ B` lies in the
  component of `U ∖ B` of `K`.
Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

lemma mem_of_mem_interior_union' {A B : Set ℂ} (hB : IsClosed B) {w : ℂ}
    (hw : w ∈ interior (A ∪ B)) (hwA : w ∉ interior A) : w ∈ B := by
  by_contra hwB
  exact hwA (mem_interior_of_mem_interior_union hB hw hwB)

/-- the grid index of the square `⌊Re x/s⌋, ⌊Im x/s⌋` containing `x` -/
def gIdx (s : ℝ) (x : ℂ) : ℤ × ℤ := (⌊x.re / s⌋, ⌊x.im / s⌋)

lemma mem_gridSquare_gIdx {s : ℝ} (hs : 0 < s) (x : ℂ) : x ∈ gridSquare s (gIdx s x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Int.floor_le (x.re / s); rwa [le_div_iff₀ hs] at this
  · have := Int.lt_floor_add_one (x.re / s); rw [div_lt_iff₀ hs] at this; exact this.le
  · have := Int.floor_le (x.im / s); rwa [le_div_iff₀ hs] at this
  · have := Int.lt_floor_add_one (x.im / s); rw [div_lt_iff₀ hs] at this; exact this.le

/-- the squares near `w` -/
def nearIdx (s : ℝ) (w : ℂ) : Finset (ℤ × ℤ) :=
  Finset.Icc ((gIdx s w).1 - 1) ((gIdx s w).1 + 1) ×ˢ Finset.Icc ((gIdx s w).2 - 1) ((gIdx s w).2 + 1)

lemma gIdx_mem_nearIdx {s : ℝ} (hs : 0 < s) {w v : ℂ} (hv : dist v w < s) :
    gIdx s v ∈ nearIdx s w := by
  rw [dist_eq_norm] at hv
  have h1 := lt_of_le_of_lt (Complex.abs_re_le_norm (v - w)) hv
  have h2 := lt_of_le_of_lt (Complex.abs_im_le_norm (v - w)) hv
  rw [Complex.sub_re, abs_lt] at h1
  rw [Complex.sub_im, abs_lt] at h2
  obtain ⟨a1, a2, a3, a4⟩ := mem_gridSquare_gIdx hs v
  obtain ⟨b1, b2, b3, b4⟩ := mem_gridSquare_gIdx hs w
  have c1 : ((gIdx s w).1 : ℝ) - 1 < (gIdx s v).1 + 1 := lt_of_mul_lt_mul_right (by nlinarith) hs.le
  have c2 : ((gIdx s v).1 : ℝ) - 1 < (gIdx s w).1 + 1 := lt_of_mul_lt_mul_right (by nlinarith) hs.le
  have c3 : ((gIdx s w).2 : ℝ) - 1 < (gIdx s v).2 + 1 := lt_of_mul_lt_mul_right (by nlinarith) hs.le
  have c4 : ((gIdx s v).2 : ℝ) - 1 < (gIdx s w).2 + 1 := lt_of_mul_lt_mul_right (by nlinarith) hs.le
  have d1 : (gIdx s w).1 - 1 < (gIdx s v).1 + 1 := by exact_mod_cast c1
  have d2 : (gIdx s v).1 - 1 < (gIdx s w).1 + 1 := by exact_mod_cast c2
  have d3 : (gIdx s w).2 - 1 < (gIdx s v).2 + 1 := by exact_mod_cast c3
  have d4 : (gIdx s v).2 - 1 < (gIdx s w).2 + 1 := by exact_mod_cast c4
  simp only [nearIdx, Finset.mem_product, Finset.mem_Icc]
  omega

/-- a set lies in the interior of the union of the grid squares meeting it -/
theorem subset_interior_squares {s : ℝ} (hs : 0 < s) {K : Set ℂ} {Q : Set (ℤ × ℤ)}
    (hQ : ∀ m, (gridSquare s m ∩ K).Nonempty → m ∈ Q) :
    K ⊆ interior (⋃ m ∈ Q, gridSquare s m) := by
  classical
  intro w hw
  set C : Set ℂ := ⋃ m ∈ (nearIdx s w).filter (fun m => w ∉ gridSquare s m), gridSquare s m
  have hC : IsClosed C := isClosed_biUnion_finset (fun m _ => isClosed_gridSquare s m)
  have hwC : w ∉ C := by
    intro h
    rw [mem_iUnion₂] at h
    obtain ⟨m, hm, hwm⟩ := h
    exact (Finset.mem_filter.1 hm).2 hwm
  obtain ⟨ε, hε, hεC⟩ := Metric.isOpen_iff.1 hC.isOpen_compl w hwC
  rw [mem_interior]
  refine ⟨ball w (min ε s), fun v hv => ?_, isOpen_ball, mem_ball_self (lt_min hε hs)⟩
  rw [mem_ball] at hv
  have hvε : v ∉ C := hεC (mem_ball.2 (lt_of_lt_of_le hv (min_le_left _ _)))
  have hvs : dist v w < s := lt_of_lt_of_le hv (min_le_right _ _)
  have hwS : w ∈ gridSquare s (gIdx s v) := by
    by_contra hn
    exact hvε (mem_iUnion₂.2 ⟨gIdx s v,
      Finset.mem_filter.2 ⟨gIdx_mem_nearIdx hs hvs, hn⟩, mem_gridSquare_gIdx hs v⟩)
  exact mem_iUnion₂.2 ⟨gIdx s v, hQ _ ⟨w, hwS, hw⟩, mem_gridSquare_gIdx hs v⟩

/-- a point of `U` in a square meeting a preconnected `K ⊆ U ∖ B` lies in the component of
`U ∖ B` of any point of `K` -/
theorem mem_comp_of_square {U B K : Set ℂ} (hU : IsOpen U) {s : ℝ} (hs : 0 < s) {m : ℤ × ℤ}
    (hSU : openSq s m ⊆ U) (hK : IsPreconnected K) (hKUB : K ⊆ U \ B) {k₀ c w : ℂ}
    (hk₀ : k₀ ∈ K) (hcK : c ∈ K) (hcS : c ∈ gridSquare s m)
    (hfarc : ∀ v, dist v c < 2 * s → v ∉ B) (hwU : w ∈ U) (hwS : w ∈ gridSquare s m)
    (hfarw : ∀ v, dist v w < 2 * s → v ∉ B) : w ∈ connectedComponentIn (U \ B) k₀ := by
  have hKc : K ⊆ connectedComponentIn (U \ B) k₀ := hK.subset_connectedComponentIn hk₀ hKUB
  have h1 := openSq_subset_comp hU hs hSU hcS (hKUB hcK).1 hfarc
  have h2 := openSq_subset_comp hU hs hSU hwS hwU hfarw
  obtain ⟨o, ho, -⟩ := exists_openSq_near hs hcS one_pos
  rw [connectedComponentIn_eq (hKc hcK), connectedComponentIn_eq (h1 ho),
    ← connectedComponentIn_eq (h2 ho)]
  exact mem_connectedComponentIn ⟨hwU, hfarw w (by rw [dist_self]; positivity)⟩

end LQGMetric.GM
