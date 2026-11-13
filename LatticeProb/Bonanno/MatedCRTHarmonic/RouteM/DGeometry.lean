/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.DGeometry at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle

/-!
# Route M, the explicit drawing `D` (Proposition M2): the planar pieces

The drawing construction. This module contains the purely geometric part of
the drawing of the mated-CRT graph in the sheared strip plane of `RouteM/PsiBundle.lean` (points `w = t + iy`,
written `stripPoint t y`; the central band is `ℝ × [0,1]`):

* `drawPt ε x = ε(x − ½) + i/2`, the vertex points (centres of the rectangles `I_x × [0,1]`);
* `dChord X a b`, the chord curve `u ↦ u + i(X_a − X_u)` over `[a, b]` below the strip (TF3's `κ_L(a, b)` for the
  coordinate `X`);
* `dLowArc ε X x y p₁ p₂`, the lower edge arc `[pt x, p₁] ∪ κ(p₁, p₂) ∪ [p₂, pt y]` with bottom ports `p₁, p₂`;
* `dRefl`, the reflection `t + iy ↦ t + i(1 − y)` across the middle line of the strip, and
  `dHighArc ε X x y p₁ p₂ := dRefl ∘ dLowArc ε X x y p₁ p₂`, the upper edge arc with top ports (TF3's R-edges: its
  chord is `u ↦ u + i(1 + X_u − X_a)`, TF3's `κ_R(a, b)`).

The main facts proved here, under `LowArcData` (ports interior to their cells, a direct relation between them):

* `injective_dLowArc`: lower arcs are arcs (injective paths);
* the classification of the points of a lower arc by height (`dLowArc_im_le`, `dLowArc_im_neg`,
  `dLowArc_im_zero`, `dLowArc_im_mid`, `dLowArc_im_half`), and `dLowArc_level_eq`: two lower arcs of the same
  coordinate meet off the middle line only if their levels `X p₁` agree (TF3 §5.2: "chords at distinct heights");
* the star-segment and horizontal-segment geometry used by the drawing (`DAux.bstar_*`, `DAux.hseg_*`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped unitInterval

namespace MatedCRTHarmonic.RouteM

/-! ### Coordinates in the strip plane -/

@[simp] theorem DAux.stripPoint_re (t y : ℝ) : (stripPoint t y).re = t := rfl

@[simp] theorem DAux.stripPoint_im (t y : ℝ) : (stripPoint t y).im = y := rfl

theorem DAux.stripPoint_re_im (w : ℂ) : stripPoint w.re w.im = w := Complex.ext rfl rfl

/-- Points of a segment of `ℂ`, in real coordinates. -/
theorem DAux.mem_segment_iff {a b w : ℂ} :
    w ∈ segment ℝ a b ↔
      ∃ s ∈ Icc (0 : ℝ) 1, w.re = a.re + s * (b.re - a.re) ∧ w.im = a.im + s * (b.im - a.im) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by simp, by simp⟩
  · rintro ⟨s, hs, hre, him⟩
    exact ⟨s, hs, Complex.ext (by simp [hre]) (by simp [him])⟩

/-- Concatenating two injective paths that meet only at the junction point gives an injective path. -/
theorem DAux.trans_injective {X : Type*} [TopologicalSpace X] {x y z : X} {γ : Path x y} {γ' : Path y z}
    (hγ : Injective γ) (hγ' : Injective γ') (h : ∀ w ∈ range γ, w ∈ range γ' → w = y) :
    Injective (γ.trans γ') := by
  have key : ∀ s t, γ s = γ' t → s = 1 ∧ t = 0 := by
    intro s t hst
    have hw : γ s = y := h _ ⟨s, rfl⟩ ⟨t, hst.symm⟩
    refine ⟨hγ (hw.trans γ.target.symm), hγ' ?_⟩
    rw [← hst, hw, γ'.source]
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have := congrArg Subtype.val (hγ hst)
    simp only at this
    exact Subtype.ext (by linarith)
  · have h1 := congrArg Subtype.val (key _ _ hst).2
    simp only [Set.Icc.coe_zero] at h1
    exact absurd (by linarith : (t : ℝ) ≤ 1 / 2) ht
  · have h1 := congrArg Subtype.val (key _ _ hst.symm).2
    simp only [Set.Icc.coe_zero] at h1
    exact absurd (by linarith : (s : ℝ) ≤ 1 / 2) hs
  · have := congrArg Subtype.val (hγ' hst)
    simp only at this
    exact Subtype.ext (by linarith)

/-! ### Vertex points -/

section Points

variable (ε : ℝ)

/-- The vertex point `pt x = ε(x − ½) + i/2` of TF3 §5.2: the centre of the rectangle `I_x × [0, 1]`,
`I_x = [ε(x − 1), εx]`. -/
def drawPt (x : ℤ) : ℂ := stripPoint (ε * ((x : ℝ) - 1 / 2)) (1 / 2)

@[simp] theorem drawPt_re (x : ℤ) : (drawPt ε x).re = ε * ((x : ℝ) - 1 / 2) := rfl

@[simp] theorem drawPt_im (x : ℤ) : (drawPt ε x).im = 1 / 2 := rfl

variable {ε}

theorem drawPt_injective (hε : 0 < ε) : Injective (drawPt ε) := by
  intro x y h
  have h1 := congrArg Complex.re h
  simp only [drawPt_re] at h1
  have h2 : ((x : ℝ) - 1 / 2) = ((y : ℝ) - 1 / 2) := mul_left_cancel₀ hε.ne' h1
  exact_mod_cast (by linarith : (x : ℝ) = y)

/-- The centre of `I_x` lies in the interior of `I_x`. -/
theorem drawPt_re_mem (hε : 0 < ε) (x : ℤ) :
    (drawPt ε x).re ∈ Ioo (ε * ((x : ℝ) - 1)) (ε * x) := by
  simp only [drawPt_re, mem_Ioo]
  constructor <;> nlinarith

/-- Open cell intervals of distinct vertices are disjoint. -/
theorem DAux.eq_of_mem_Ioo (hε : 0 < ε) {v v' : ℤ} {r : ℝ} (h : r ∈ Ioo (ε * ((v : ℝ) - 1)) (ε * v))
    (h' : r ∈ Ioo (ε * ((v' : ℝ) - 1)) (ε * v')) : v = v' := by
  rcases lt_trichotomy v v' with hlt | heq | hgt
  · have hle : (v : ℝ) ≤ (v' : ℝ) - 1 := by
      have : v ≤ v' - 1 := by omega
      exact_mod_cast this
    have : ε * v ≤ ε * ((v' : ℝ) - 1) := mul_le_mul_of_nonneg_left hle hε.le
    linarith [h.2, h'.1]
  · exact heq
  · have hle : (v' : ℝ) ≤ (v : ℝ) - 1 := by
      have : v' ≤ v - 1 := by omega
      exact_mod_cast this
    have : ε * v' ≤ ε * ((v : ℝ) - 1) := mul_le_mul_of_nonneg_left hle hε.le
    linarith [h'.2, h.1]

end Points

/-! ### Star segments (from a vertex point to a bottom port) -/

section Stars

variable {ε : ℝ}

/-- Coordinates of the points of the bottom star segment `[pt v, p + 0i]`. -/
theorem DAux.bstar_coords {v : ℤ} {p : ℝ} {w : ℂ} (hw : w ∈ segment ℝ (drawPt ε v) (stripPoint p 0)) :
    ∃ s ∈ Icc (0 : ℝ) 1, w.re = ε * ((v : ℝ) - 1 / 2) + s * (p - ε * ((v : ℝ) - 1 / 2)) ∧
      w.im = 1 / 2 - s / 2 := by
  obtain ⟨s, hs, hre, him⟩ := DAux.mem_segment_iff.mp hw
  refine ⟨s, hs, by simpa using hre, ?_⟩
  simp only [drawPt_im, DAux.stripPoint_im] at him
  linarith

theorem DAux.bstar_im_mem {v : ℤ} {p : ℝ} {w : ℂ} (hw : w ∈ segment ℝ (drawPt ε v) (stripPoint p 0)) :
    0 ≤ w.im ∧ w.im ≤ 1 / 2 := by
  obtain ⟨s, hs, -, him⟩ := DAux.bstar_coords hw
  constructor <;> linarith [hs.1, hs.2]

/-- A bottom star segment stays over the open cell interval when its port does. -/
theorem DAux.bstar_re_mem (hε : 0 < ε) {v : ℤ} {p : ℝ} (hp : p ∈ Ioo (ε * ((v : ℝ) - 1)) (ε * v)) {w : ℂ}
    (hw : w ∈ segment ℝ (drawPt ε v) (stripPoint p 0)) :
    w.re ∈ Ioo (ε * ((v : ℝ) - 1)) (ε * v) := by
  obtain ⟨s, hs, hre, -⟩ := DAux.bstar_coords hw
  have hc := drawPt_re_mem hε v
  simp only [drawPt_re, mem_Ioo] at hc
  rw [hre, mem_Ioo]
  rcases le_total p (ε * ((v : ℝ) - 1 / 2)) with hpc | hpc
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 hpc), hp.1]
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.2 hpc)]
  · constructor
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.2 hpc)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 hpc), hp.2]

theorem DAux.bstar_eq_pt {v : ℤ} {p : ℝ} {w : ℂ} (hw : w ∈ segment ℝ (drawPt ε v) (stripPoint p 0))
    (him : w.im = 1 / 2) : w = drawPt ε v := by
  obtain ⟨s, -, hre, him'⟩ := DAux.bstar_coords hw
  have hs : s = 0 := by linarith
  subst hs
  exact Complex.ext (by simpa using hre) (by simpa using him)

theorem DAux.bstar_eq_port {v : ℤ} {p : ℝ} {w : ℂ} (hw : w ∈ segment ℝ (drawPt ε v) (stripPoint p 0))
    (him : w.im = 0) : w = stripPoint p 0 := by
  obtain ⟨s, -, hre, him'⟩ := DAux.bstar_coords hw
  have hs : s = 1 := by linarith
  subst hs
  exact Complex.ext (by simp [hre]) (by simpa using him)

/-- Two bottom star segments of one vertex meet below the middle line only if their ports agree. -/
theorem DAux.bstar_port_eq {v : ℤ} {p p' : ℝ} {w : ℂ} (hw : w ∈ segment ℝ (drawPt ε v) (stripPoint p 0))
    (hw' : w ∈ segment ℝ (drawPt ε v) (stripPoint p' 0)) (him : w.im < 1 / 2) : p = p' := by
  obtain ⟨s, -, hre, him1⟩ := DAux.bstar_coords hw
  obtain ⟨s', -, hre', him2⟩ := DAux.bstar_coords hw'
  have hss : s' = s := by linarith
  subst hss
  have hs : s' ≠ 0 := by
    intro h0
    rw [h0] at him1
    linarith
  have : s' * p = s' * p' := by linarith
  exact mul_left_cancel₀ hs this

end Stars

/-! ### The horizontal segment of a consecutive edge -/

section Horizontal

variable {ε : ℝ}

theorem DAux.hseg_coords (hε : 0 < ε) {x : ℤ} {w : ℂ} (hw : w ∈ segment ℝ (drawPt ε x) (drawPt ε (x + 1))) :
    w.im = 1 / 2 ∧ ε * ((x : ℝ) - 1 / 2) ≤ w.re ∧ w.re ≤ ε * ((x : ℝ) + 1 / 2) := by
  obtain ⟨s, hs, hre, him⟩ := DAux.mem_segment_iff.mp hw
  simp only [drawPt_re, drawPt_im, Int.cast_add, Int.cast_one] at hre him
  refine ⟨by linarith, ?_, ?_⟩
  · rw [hre]; nlinarith [hs.1]
  · rw [hre]; nlinarith [hs.2]

/-- A vertex point on the horizontal segment of `{x, x + 1}` is one of its two ends. -/
theorem DAux.hseg_pt (hε : 0 < ε) {x v : ℤ} (hv : drawPt ε v ∈ segment ℝ (drawPt ε x) (drawPt ε (x + 1))) :
    v = x ∨ v = x + 1 := by
  obtain ⟨-, h1, h2⟩ := DAux.hseg_coords hε hv
  simp only [drawPt_re] at h1 h2
  have h1' : (x : ℝ) ≤ v := by nlinarith
  have h2' : (v : ℝ) ≤ x + 1 := by nlinarith
  have h1'' : x ≤ v := by exact_mod_cast h1'
  have h2'' : v ≤ x + 1 := by exact_mod_cast h2'
  omega

/-- Horizontal segments of distinct consecutive edges meet only at a common vertex point. -/
theorem DAux.hseg_inter (hε : 0 < ε) {x x' : ℤ} (hxx : x < x') {w : ℂ}
    (hw : w ∈ segment ℝ (drawPt ε x) (drawPt ε (x + 1)))
    (hw' : w ∈ segment ℝ (drawPt ε x') (drawPt ε (x' + 1))) : x' = x + 1 ∧ w = drawPt ε (x + 1) := by
  obtain ⟨him, -, h2⟩ := DAux.hseg_coords hε hw
  obtain ⟨-, h1', -⟩ := DAux.hseg_coords hε hw'
  have hle : (x' : ℝ) ≤ x + 1 := by nlinarith
  have hle' : x' ≤ x + 1 := by exact_mod_cast hle
  have hx' : x' = x + 1 := by omega
  refine ⟨hx', ?_⟩
  subst hx'
  push_cast at h1'
  refine Complex.ext ?_ (by simpa using him)
  simp only [drawPt_re, Int.cast_add, Int.cast_one]
  linarith

end Horizontal

/-! ### Chords and lower arcs -/

section Arcs

variable (ε : ℝ)

/-- The chord curve `u ↦ u + i(X_a − X_u)` over `[a, b]` (TF3 §5.1, `κ_L(a, b)` for the coordinate `X`), as a path
from `a + 0i` to `b + i(X_a − X_b)` (the latter is `b + 0i` for a direct relation). -/
def dChord (X : C(ℝ, ℝ)) (a b : ℝ) : Path (stripPoint a 0) (stripPoint b (X a - X b)) where
  toFun s := stripPoint (a + (s : ℝ) * (b - a)) (X a - X (a + (s : ℝ) * (b - a)))
  continuous_toFun := by
    have h : Continuous (fun s : I => (a + (s : ℝ) * (b - a), X a - X (a + (s : ℝ) * (b - a)))) := by
      fun_prop
    exact continuous_stripPoint_pair.comp h
  source' := by simp [stripPoint]
  target' := by simp [stripPoint]

/-- The lower edge arc of TF3 §5.2: the star segment from `pt x` to the bottom port `p₁ + 0i`, the chord over
`[p₁, p₂]`, and the star segment from the bottom port `p₂ + 0i` to `pt y`. -/
def dLowArc (X : C(ℝ, ℝ)) (x y : ℤ) (p₁ p₂ : ℝ) : Path (drawPt ε x) (drawPt ε y) :=
  (Path.segment (drawPt ε x) (stripPoint p₁ 0)).trans
    ((dChord X p₁ p₂).trans (Path.segment (stripPoint p₂ (X p₁ - X p₂)) (drawPt ε y)))

/-- The data under which `dLowArc ε X x y p₁ p₂` is an arc of the drawing: `x < y`, the ports lie in the open cell
intervals `int I_x`, `int I_y`, and `X` makes a direct excursion above the level `X p₁` between them. -/
structure LowArcData (X : ℝ → ℝ) (x y : ℤ) (p₁ p₂ : ℝ) : Prop where
  lt : x < y
  mem₁ : p₁ ∈ Ioo (ε * ((x : ℝ) - 1)) (ε * x)
  mem₂ : p₂ ∈ Ioo (ε * ((y : ℝ) - 1)) (ε * y)
  rel : directRel X p₁ p₂

variable {ε}

theorem mem_range_dChord {X : C(ℝ, ℝ)} {a b : ℝ} (hab : a ≤ b) {w : ℂ} (hw : w ∈ range (dChord X a b)) :
    ∃ u ∈ Icc a b, w = stripPoint u (X a - X u) := by
  obtain ⟨s, rfl⟩ := hw
  refine ⟨a + (s : ℝ) * (b - a), ⟨?_, ?_⟩, rfl⟩
  · nlinarith [s.2.1]
  · nlinarith [s.2.2]

theorem injective_dChord {X : C(ℝ, ℝ)} {a b : ℝ} (hab : a < b) : Injective (dChord X a b) := by
  intro s t hst
  have h := congrArg Complex.re hst
  change a + (s : ℝ) * (b - a) = a + (t : ℝ) * (b - a) at h
  have : (s : ℝ) = t := mul_right_cancel₀ (sub_ne_zero.2 hab.ne') (by linarith)
  exact Subtype.ext this

/-- Points of a chord of a direct relation lie on or below the strip, and on its bottom line only at its ends. -/
theorem DAux.chord_im {X : C(ℝ, ℝ)} {a b : ℝ} (hrel : directRel X a b) {u : ℝ} (hu : u ∈ Icc a b) :
    X a - X u ≤ 0 ∧ (X a - X u = 0 → u = a ∨ u = b) := by
  obtain ⟨hab, hval, hinside⟩ := hrel
  rcases eq_or_lt_of_le hu.1 with rfl | hau
  · exact ⟨by simp, fun _ => Or.inl rfl⟩
  rcases eq_or_lt_of_le hu.2 with rfl | hub
  · exact ⟨by simp [hval], fun _ => Or.inr rfl⟩
  have := hinside u ⟨hau, hub⟩
  exact ⟨by linarith, fun h => absurd h (by linarith)⟩

theorem range_dLowArc (X : C(ℝ, ℝ)) (x y : ℤ) (p₁ p₂ : ℝ) :
    range (dLowArc ε X x y p₁ p₂) = segment ℝ (drawPt ε x) (stripPoint p₁ 0) ∪
      (range (dChord X p₁ p₂) ∪ segment ℝ (stripPoint p₂ (X p₁ - X p₂)) (drawPt ε y)) := by
  rw [dLowArc, Path.trans_range, Path.trans_range, Path.range_segment, Path.range_segment]

/-- The three pieces of a lower arc, in a form adapted to the data: the first star segment, a chord point, the
second star segment (written from `pt y`). -/
theorem dLowArc_pieces {X : C(ℝ, ℝ)} {x y : ℤ} {p₁ p₂ : ℝ} (hd : LowArcData ε X x y p₁ p₂) {w : ℂ}
    (hw : w ∈ range (dLowArc ε X x y p₁ p₂)) :
    w ∈ segment ℝ (drawPt ε x) (stripPoint p₁ 0) ∨ (∃ u ∈ Icc p₁ p₂, w = stripPoint u (X p₁ - X u)) ∨
      w ∈ segment ℝ (drawPt ε y) (stripPoint p₂ 0) := by
  rw [range_dLowArc] at hw
  rcases hw with hw | hw | hw
  · exact Or.inl hw
  · exact Or.inr (Or.inl (mem_range_dChord hd.rel.1.le hw))
  · refine Or.inr (Or.inr ?_)
    rw [segment_symm]
    have : X p₁ - X p₂ = 0 := by rw [hd.rel.2.1, sub_self]
    rwa [this] at hw

/-- Points of a lower arc lie on or below the middle line. -/
theorem dLowArc_im_le {X : C(ℝ, ℝ)} {x y : ℤ} {p₁ p₂ : ℝ} (hd : LowArcData ε X x y p₁ p₂) {w : ℂ}
    (hw : w ∈ range (dLowArc ε X x y p₁ p₂)) : w.im ≤ 1 / 2 := by
  rcases dLowArc_pieces hd hw with h | ⟨u, hu, rfl⟩ | h
  · exact (DAux.bstar_im_mem h).2
  · have := (DAux.chord_im hd.rel hu).1
    simp only [DAux.stripPoint_im]
    linarith
  · exact (DAux.bstar_im_mem h).2

/-- Below the strip, a lower arc runs along its chord: `Im w = X p₁ − X (Re w)`. -/
theorem dLowArc_im_neg {X : C(ℝ, ℝ)} {x y : ℤ} {p₁ p₂ : ℝ} (hd : LowArcData ε X x y p₁ p₂) {w : ℂ}
    (hw : w ∈ range (dLowArc ε X x y p₁ p₂)) (him : w.im < 0) : w.im = X p₁ - X w.re := by
  rcases dLowArc_pieces hd hw with h | ⟨u, hu, rfl⟩ | h
  · exact absurd (DAux.bstar_im_mem h).1 (not_le.2 him)
  · simp
  · exact absurd (DAux.bstar_im_mem h).1 (not_le.2 him)

/-- On the bottom line of the strip, a lower arc is at one of its ports, where `X` takes the level `X p₁`. -/
theorem dLowArc_im_zero {X : C(ℝ, ℝ)} {x y : ℤ} {p₁ p₂ : ℝ} (hd : LowArcData ε X x y p₁ p₂) {w : ℂ}
    (hw : w ∈ range (dLowArc ε X x y p₁ p₂)) (him : w.im = 0) : X w.re = X p₁ := by
  rcases dLowArc_pieces hd hw with h | ⟨u, hu, rfl⟩ | h
  · rw [DAux.bstar_eq_port h him]
    rfl
  · simp only [DAux.stripPoint_im] at him
    simp only [DAux.stripPoint_re]
    linarith
  · rw [DAux.bstar_eq_port h him]
    exact hd.rel.2.1.symm

/-- Strictly between the bottom line and the middle line, a lower arc runs along a star segment of one of its ends
`v`, towards a port `p ∈ int I_v` at the level `X p₁`. -/
theorem dLowArc_im_mid {X : C(ℝ, ℝ)} {x y : ℤ} {p₁ p₂ : ℝ} (hd : LowArcData ε X x y p₁ p₂) {w : ℂ}
    (hw : w ∈ range (dLowArc ε X x y p₁ p₂)) (him0 : 0 < w.im) :
    ∃ v p, (v = x ∨ v = y) ∧ p ∈ Ioo (ε * ((v : ℝ) - 1)) (ε * v) ∧ X p = X p₁ ∧
      w ∈ segment ℝ (drawPt ε v) (stripPoint p 0) := by
  rcases dLowArc_pieces hd hw with h | ⟨u, hu, rfl⟩ | h
  · exact ⟨x, p₁, Or.inl rfl, hd.mem₁, rfl, h⟩
  · have := (DAux.chord_im hd.rel hu).1
    simp only [DAux.stripPoint_im] at him0
    linarith
  · exact ⟨y, p₂, Or.inr rfl, hd.mem₂, hd.rel.2.1.symm, h⟩

/-- On the middle line, a lower arc is at one of its end points. -/
theorem dLowArc_im_half {X : C(ℝ, ℝ)} {x y : ℤ} {p₁ p₂ : ℝ} (hd : LowArcData ε X x y p₁ p₂) {w : ℂ}
    (hw : w ∈ range (dLowArc ε X x y p₁ p₂)) (him : w.im = 1 / 2) : w = drawPt ε x ∨ w = drawPt ε y := by
  rcases dLowArc_pieces hd hw with h | ⟨u, hu, rfl⟩ | h
  · exact Or.inl (DAux.bstar_eq_pt h him)
  · have := (DAux.chord_im hd.rel hu).1
    simp only [DAux.stripPoint_im] at him
    linarith
  · exact Or.inr (DAux.bstar_eq_pt h him)

/-- **Chords at distinct heights** (TF3 §5.2): two lower arcs of the same coordinate `X` that meet off the middle
line have the same level `X p₁`. -/
theorem dLowArc_level_eq (hε : 0 < ε) {X : C(ℝ, ℝ)} {x y x' y' : ℤ} {p₁ p₂ p₁' p₂' : ℝ}
    (hd : LowArcData ε X x y p₁ p₂) (hd' : LowArcData ε X x' y' p₁' p₂') {w : ℂ}
    (hw : w ∈ range (dLowArc ε X x y p₁ p₂)) (hw' : w ∈ range (dLowArc ε X x' y' p₁' p₂'))
    (him : w.im ≠ 1 / 2) : X p₁ = X p₁' := by
  have hle := dLowArc_im_le hd hw
  rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
  · have h1 := dLowArc_im_neg hd hw hneg
    have h2 := dLowArc_im_neg hd' hw' hneg
    linarith
  · rw [← dLowArc_im_zero hd hw hzero, dLowArc_im_zero hd' hw' hzero]
  · have hlt : w.im < 1 / 2 := lt_of_le_of_ne hle him
    obtain ⟨v, p, -, hp, hXp, hwv⟩ := dLowArc_im_mid hd hw hpos
    obtain ⟨v', p', -, hp', hXp', hwv'⟩ := dLowArc_im_mid hd' hw' hpos
    have hvv : v = v' :=
      DAux.eq_of_mem_Ioo hε (DAux.bstar_re_mem hε hp hwv) (DAux.bstar_re_mem hε hp' hwv')
    subst hvv
    have hpp : p = p' := DAux.bstar_port_eq hwv hwv' hlt
    rw [← hXp, ← hXp', hpp]

/-- Lower arcs are arcs: `dLowArc` is injective under `LowArcData`. -/
theorem injective_dLowArc (hε : 0 < ε) {X : C(ℝ, ℝ)} {x y : ℤ} {p₁ p₂ : ℝ} (hd : LowArcData ε X x y p₁ p₂) :
    Injective (dLowArc ε X x y p₁ p₂) := by
  have hX : X p₁ - X p₂ = 0 := by rw [hd.rel.2.1, sub_self]
  have hne₁ : drawPt ε x ≠ stripPoint p₁ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hne₂ : stripPoint p₂ (X p₁ - X p₂) ≠ drawPt ε y := by
    intro h
    have := congrArg Complex.im h
    simp only [DAux.stripPoint_im, drawPt_im, hX] at this
    norm_num at this
  -- the chord followed by the second star segment
  have hinj₂ : Injective ((dChord X p₁ p₂).trans (Path.segment (stripPoint p₂ (X p₁ - X p₂)) (drawPt ε y))) := by
    refine DAux.trans_injective (injective_dChord hd.rel.1) (Path.segment_injective_of_ne hne₂) ?_
    intro w hwc hws
    rw [Path.range_segment, segment_symm, hX] at hws
    obtain ⟨u, hu, rfl⟩ := mem_range_dChord hd.rel.1.le hwc
    have him := DAux.bstar_im_mem hws
    have hc := DAux.chord_im hd.rel hu
    simp only [DAux.stripPoint_im] at him
    have h0 : X p₁ - X u = 0 := le_antisymm hc.1 him.1
    have hre := DAux.bstar_re_mem hε hd.mem₂ hws
    simp only [DAux.stripPoint_re] at hre
    rcases hc.2 h0 with rfl | rfl
    · have := hd.mem₁.2
      have hxy : (x : ℝ) ≤ (y : ℝ) - 1 := by
        have : x ≤ y - 1 := by have := hd.lt; omega
        exact_mod_cast this
      have : ε * x ≤ ε * ((y : ℝ) - 1) := mul_le_mul_of_nonneg_left hxy hε.le
      linarith [hre.1]
    · rw [h0]
  refine DAux.trans_injective (Path.segment_injective_of_ne hne₁) hinj₂ ?_
  intro w hws hw2
  rw [Path.range_segment] at hws
  rw [Path.trans_range, Path.range_segment, segment_symm] at hw2
  have hre := DAux.bstar_re_mem hε hd.mem₁ hws
  rcases hw2 with hwc | hws2
  · obtain ⟨u, hu, rfl⟩ := mem_range_dChord hd.rel.1.le hwc
    have him := DAux.bstar_im_mem hws
    have hc := DAux.chord_im hd.rel hu
    simp only [DAux.stripPoint_im] at him
    have h0 : X p₁ - X u = 0 := le_antisymm hc.1 him.1
    exact DAux.bstar_eq_port hws (by simpa using h0)
  · rw [hX] at hws2
    have hre2 := DAux.bstar_re_mem hε hd.mem₂ hws2
    exact absurd (DAux.eq_of_mem_Ioo hε hre hre2) hd.lt.ne

end Arcs

/-! ### The reflection across the middle line, and upper arcs -/

section Reflection

variable (ε : ℝ)

/-- The reflection `t + iy ↦ t + i(1 − y)` across the middle line `y = ½` of the strip. -/
def dRefl (w : ℂ) : ℂ := stripPoint w.re (1 - w.im)

@[simp] theorem dRefl_re (w : ℂ) : (dRefl w).re = w.re := rfl

@[simp] theorem dRefl_im (w : ℂ) : (dRefl w).im = 1 - w.im := rfl

@[simp] theorem dRefl_dRefl (w : ℂ) : dRefl (dRefl w) = w := Complex.ext rfl (by simp)

theorem continuous_dRefl : Continuous dRefl := by
  have h : Continuous (fun w : ℂ => (w.re, 1 - w.im)) := by fun_prop
  exact continuous_stripPoint_pair.comp h

theorem injective_dRefl : Injective dRefl := fun w w' h => by
  rw [← dRefl_dRefl w, h, dRefl_dRefl]

theorem dRefl_drawPt (x : ℤ) : dRefl (drawPt ε x) = drawPt ε x :=
  Complex.ext rfl (by simp only [dRefl_im, drawPt_im]; norm_num)

/-- The upper edge arc: the reflection of the lower arc across the middle line (top ports `p₁ + i`, `p₂ + i`, the
chord `u ↦ u + i(1 + X_u − X_{p₁})` above the strip, TF3's `κ_R`). -/
def dHighArc (X : C(ℝ, ℝ)) (x y : ℤ) (p₁ p₂ : ℝ) : Path (drawPt ε x) (drawPt ε y) :=
  ((dLowArc ε X x y p₁ p₂).map continuous_dRefl).cast (dRefl_drawPt ε x).symm (dRefl_drawPt ε y).symm

variable {ε}

theorem mem_range_dHighArc {X : C(ℝ, ℝ)} {x y : ℤ} {p₁ p₂ : ℝ} {w : ℂ} :
    w ∈ range (dHighArc ε X x y p₁ p₂) ↔ dRefl w ∈ range (dLowArc ε X x y p₁ p₂) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by simp [dHighArc, Path.cast_coe, Path.map_coe]⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simp only [dHighArc, Path.cast_coe, Path.map_coe, comp_apply]
    rw [ht, dRefl_dRefl]

theorem injective_dHighArc (hε : 0 < ε) {X : C(ℝ, ℝ)} {x y : ℤ} {p₁ p₂ : ℝ} (hd : LowArcData ε X x y p₁ p₂) :
    Injective (dHighArc ε X x y p₁ p₂) := by
  intro s t hst
  simp only [dHighArc, Path.cast_coe, Path.map_coe, comp_apply] at hst
  exact injective_dLowArc hε hd (injective_dRefl hst)

end Reflection

end MatedCRTHarmonic.RouteM
