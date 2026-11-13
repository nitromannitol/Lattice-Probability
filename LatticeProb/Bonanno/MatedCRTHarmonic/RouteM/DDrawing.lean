/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.DDrawing at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DLevels
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj

/-!
# Route M, the explicit drawing `D` of the mated-CRT graph (Proposition M2)

The drawing construction. The drawing of `G^ε = MatedCRT.graph ε ω h` in the
sheared strip plane of `RouteM/PsiBundle.lean`:

* vertices: `drawPt ε x = ε(x − ½) + i/2`;
* a consecutive edge `{x, x + 1}`: the horizontal segment `[pt x, pt (x + 1)]` (through the side port `εx + i/2`);
* an L-edge `{x, y}`, `y ≥ x + 2`: the lower arc `[pt x, t₁] ∪ κ_L(t₁, t₂) ∪ [t₂, pt y]` with the ports
  `t₁ = ℓ⁻(εx, λ) ∈ int I_x`, `t₂ = ℓ⁺(ε(y − 1), λ) ∈ int I_y` of a level `λ = dLevel ε L x y` in the window of (1.1)
  (non-empty by G0, `SideStrict`), the levels of distinct pairs being distinct;
* an R-edge (a non-consecutive pair satisfying (1.1) for `R` but not for `L`): the same with `R`, reflected above the
  strip (top ports, chord `κ_R`); an L-and-R double edge is drawn once, as its L-edge.

`dOrdArc ε ω x y` is the arc of the ordered pair `x < y`, and `dArc ε ω x y` the arc of any pair (reversed when
`y < x`). **Proposition M2** (TF3 §5.2), proved here under G0 for every adjacent pair:

1. `drawPt_injective` (`RouteM/DGeometry.lean`) and `injective_dArc`: vertex points are distinct, each edge arc is
   an arc;
2. `dArc_inter`: arcs of different edges meet only at `pt v` for common end points `v`;
3. `eq_or_eq_of_drawPt_mem_dArc`: `pt v` lies on an arc only if `v` is an end point of the edge;
4. `shearedStripMap_drawPt_mem`, `shearedStripMap_dArc_mem`: `Ψ(pt x) ∈ H_x` and `Ψ(arc_{xy}) ⊆ H_x ∪ H_y` for the
   cells `H_x = η(I_x)`, `Ψ = shearedStripMap P` the strip map of Proposition M1.
-/

set_option autoImplicit false

noncomputable section

open Set Function

namespace MatedCRTHarmonic.RouteM

/-! ### The two coordinates as bundled continuous maps -/

/-- The L-coordinate `t ↦ L_t` as a bundled continuous map. -/
def drawL (ω : MatedCRT.Path2) : C(ℝ, ℝ) := ⟨lCoord ω, continuous_lCoord⟩

/-- The R-coordinate `t ↦ R_t` as a bundled continuous map. -/
def drawR (ω : MatedCRT.Path2) : C(ℝ, ℝ) := ⟨rCoord ω, continuous_rCoord⟩

@[simp] theorem coe_drawL (ω : MatedCRT.Path2) : ⇑(drawL ω) = lCoord ω := rfl

@[simp] theorem coe_drawR (ω : MatedCRT.Path2) : ⇑(drawR ω) = rCoord ω := rfl

/-! ### The arcs -/

section Def

variable (ε : ℝ) (ω : MatedCRT.Path2)

open Classical in
/-- The drawn arc of the ordered pair `x < y` (TF3 §5.2): the horizontal segment for `y = x + 1`; otherwise the lower
arc of the L-ports if (1.1) holds for `L`, and else the upper arc of the R-ports. -/
def dOrdArc (x y : ℤ) : Path (drawPt ε x) (drawPt ε y) :=
  if y = x + 1 then Path.segment (drawPt ε x) (drawPt ε y)
  else if MatedCRT.SideCond ε (lCoord ω) x y then
    dLowArc ε (drawL ω) x y (dPort₁ ε (lCoord ω) x y) (dPort₂ ε (lCoord ω) x y)
  else dHighArc ε (drawR ω) x y (dPort₁ ε (rCoord ω) x y) (dPort₂ ε (rCoord ω) x y)

/-- The drawn arc of a pair `x, y` of vertices: `dOrdArc ε ω x y` if `x < y`, its reverse otherwise. -/
def dArc (x y : ℤ) : Path (drawPt ε x) (drawPt ε y) :=
  if x < y then dOrdArc ε ω x y else (dOrdArc ε ω y x).symm

end Def

variable {ε : ℝ} {ω : MatedCRT.Path2}

theorem dOrdArc_succ (x : ℤ) : dOrdArc ε ω x (x + 1) = Path.segment (drawPt ε x) (drawPt ε (x + 1)) := by
  rw [dOrdArc, ite_eq_left rfl]

theorem dOrdArc_low {x y : ℤ} (hne : y ≠ x + 1) (hL : MatedCRT.SideCond ε (lCoord ω) x y) :
    dOrdArc ε ω x y = dLowArc ε (drawL ω) x y (dPort₁ ε (lCoord ω) x y) (dPort₂ ε (lCoord ω) x y) := by
  rw [dOrdArc, ite_eq_right hne, ite_eq_left hL]

theorem dOrdArc_high {x y : ℤ} (hne : y ≠ x + 1) (hL : ¬ MatedCRT.SideCond ε (lCoord ω) x y) :
    dOrdArc ε ω x y = dHighArc ε (drawR ω) x y (dPort₁ ε (rCoord ω) x y) (dPort₂ ε (rCoord ω) x y) := by
  rw [dOrdArc, ite_eq_right hne, ite_eq_right hL]

theorem dArc_of_lt {x y : ℤ} (hxy : x < y) : dArc ε ω x y = dOrdArc ε ω x y := by
  rw [dArc, ite_eq_left hxy]

theorem dArc_of_gt {x y : ℤ} (hxy : y < x) : dArc ε ω x y = (dOrdArc ε ω y x).symm := by
  rw [dArc, ite_eq_right (not_lt.2 hxy.le)]

/-- Reversing a pair reverses its arc. -/
theorem dArc_swap {x y : ℤ} (hne : x ≠ y) : dArc ε ω y x = (dArc ε ω x y).symm := by
  rcases lt_or_gt_of_ne hne with hxy | hxy
  · rw [dArc_of_gt hxy, dArc_of_lt hxy]
  · rw [dArc_of_lt hxy, dArc_of_gt hxy, Path.symm_symm]

/-! ### Adjacency in the mated-CRT map -/

/-- The kinds of the adjacent ordered pairs `x < y` of the mated-CRT map ([18] (1.1)): consecutive, an L-edge,
or an R-edge that is not also an L-edge. -/
theorem matedCRT_adj_cases {h : MatedCRT.IsLocallyFinite ε ω} {x y : ℤ} (hxy : x < y)
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) :
    y = x + 1 ∨ (x + 1 < y ∧ MatedCRT.SideCond ε (lCoord ω) x y) ∨
      (x + 1 < y ∧ ¬ MatedCRT.SideCond ε (lCoord ω) x y ∧ MatedCRT.SideCond ε (rCoord ω) x y) := by
  rw [LFMultigraph.adj, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨-, ⟨⟨⟨a, b, c⟩, hlt, hcase⟩, he1, he2⟩ | ⟨⟨⟨a, b, c⟩, hlt, _⟩, he1, he2⟩⟩
  · change a = x at he1
    change b = y at he2
    subst he1 he2
    rcases hcase with ⟨hb, -⟩ | ⟨hb, hside⟩
    · exact Or.inl hb
    · have hlt' : a + 1 < b := by
        change a < b at hlt
        change b ≠ a + 1 at hb
        omega
      by_cases hL : MatedCRT.SideCond ε (lCoord ω) a b
      · exact Or.inr (Or.inl ⟨hlt', hL⟩)
      · refine Or.inr (Or.inr ⟨hlt', hL, ?_⟩)
        cases c
        · have hs : MatedCRT.SideCond ε (fun t => (ω t).1) a b := by simpa using hside
          exact absurd hs hL
        · have hs : MatedCRT.SideCond ε (fun t => (ω t).2) a b := by simpa using hside
          exact hs
  · change a = y at he1
    change b = x at he2
    change a < b at hlt
    omega

/-- G0 for the L-coordinate: (1.1) for `L` at a non-consecutive pair holds strictly. -/
theorem DAux.dWin_lt_L (hG : SideStrict ε ω) {x y : ℤ} (hxy : x + 1 < y)
    (hL : MatedCRT.SideCond ε (lCoord ω) x y) : dWinLo ε (lCoord ω) x y < dWinHi ε (lCoord ω) x y := by
  have hf : (fun t => if (false = true) then (ω t).2 else (ω t).1) = lCoord ω := by
    funext t
    simp [lCoord]
  have := hG false x y hxy
  rw [hf] at this
  exact this hL

/-- G0 for the R-coordinate. -/
theorem DAux.dWin_lt_R (hG : SideStrict ε ω) {x y : ℤ} (hxy : x + 1 < y)
    (hR : MatedCRT.SideCond ε (rCoord ω) x y) : dWinLo ε (rCoord ω) x y < dWinHi ε (rCoord ω) x y := by
  have hf : (fun t => if (true = true) then (ω t).2 else (ω t).1) = rCoord ω := by
    funext t
    simp [rCoord]
  have := hG true x y hxy
  rw [hf] at this
  exact this hR

/-! ### Points of the ordered arcs -/

section Ordered

variable {h : MatedCRT.IsLocallyFinite ε ω}

/-- On the middle line, an ordered arc is at an end point, or is the horizontal segment of a consecutive pair. -/
theorem dOrdArc_im_half (hG : SideStrict ε ω) (hε : 0 < ε) {x y : ℤ} (hxy : x < y)
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) {w : ℂ} (hw : w ∈ range (dOrdArc ε ω x y))
    (him : w.im = 1 / 2) :
    w = drawPt ε x ∨ w = drawPt ε y ∨ (y = x + 1 ∧ w ∈ segment ℝ (drawPt ε x) (drawPt ε (x + 1))) := by
  rcases matedCRT_adj_cases hxy hadj with rfl | ⟨hlt, hL⟩ | ⟨hlt, hL, hR⟩
  · rw [dOrdArc_succ, Path.range_segment] at hw
    exact Or.inr (Or.inr ⟨rfl, hw⟩)
  · rw [dOrdArc_low (by omega) hL] at hw
    have hd := (lowArcData_dPorts continuous_lCoord hε hlt (DAux.dWin_lt_L hG hlt hL)).1
    exact (dLowArc_im_half (X := drawL ω) hd hw him).imp_right Or.inl
  · rw [dOrdArc_high (by omega) hL, mem_range_dHighArc] at hw
    have hd := (lowArcData_dPorts continuous_rCoord hε hlt (DAux.dWin_lt_R hG hlt hR)).1
    have him' : (dRefl w).im = 1 / 2 := by rw [dRefl_im, him]; norm_num
    rcases dLowArc_im_half (X := drawR ω) hd hw him' with h1 | h1
    · left
      rw [← dRefl_dRefl w, h1, dRefl_drawPt]
    · right; left
      rw [← dRefl_dRefl w, h1, dRefl_drawPt]

/-- Below the middle line, an ordered arc is the lower arc of an L-edge. -/
theorem dOrdArc_im_lt (hG : SideStrict ε ω) (hε : 0 < ε) {x y : ℤ} (hxy : x < y)
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) {w : ℂ} (hw : w ∈ range (dOrdArc ε ω x y))
    (him : w.im < 1 / 2) :
    x + 1 < y ∧ MatedCRT.SideCond ε (lCoord ω) x y ∧
      w ∈ range (dLowArc ε (drawL ω) x y (dPort₁ ε (lCoord ω) x y) (dPort₂ ε (lCoord ω) x y)) := by
  rcases matedCRT_adj_cases hxy hadj with rfl | ⟨hlt, hL⟩ | ⟨hlt, hL, hR⟩
  · rw [dOrdArc_succ, Path.range_segment] at hw
    exact absurd (DAux.hseg_coords hε hw).1 him.ne
  · rw [dOrdArc_low (by omega) hL] at hw
    exact ⟨hlt, hL, hw⟩
  · rw [dOrdArc_high (by omega) hL, mem_range_dHighArc] at hw
    have hd := (lowArcData_dPorts continuous_rCoord hε hlt (DAux.dWin_lt_R hG hlt hR)).1
    have := dLowArc_im_le (X := drawR ω) hd hw
    rw [dRefl_im] at this
    linarith

/-- Above the middle line, an ordered arc is the upper arc of an R-edge that is not an L-edge. -/
theorem dOrdArc_im_gt (hG : SideStrict ε ω) (hε : 0 < ε) {x y : ℤ} (hxy : x < y)
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) {w : ℂ} (hw : w ∈ range (dOrdArc ε ω x y))
    (him : 1 / 2 < w.im) :
    x + 1 < y ∧ ¬ MatedCRT.SideCond ε (lCoord ω) x y ∧ MatedCRT.SideCond ε (rCoord ω) x y ∧
      dRefl w ∈ range (dLowArc ε (drawR ω) x y (dPort₁ ε (rCoord ω) x y) (dPort₂ ε (rCoord ω) x y)) := by
  rcases matedCRT_adj_cases hxy hadj with rfl | ⟨hlt, hL⟩ | ⟨hlt, hL, hR⟩
  · rw [dOrdArc_succ, Path.range_segment] at hw
    exact absurd (DAux.hseg_coords hε hw).1 him.ne'
  · rw [dOrdArc_low (by omega) hL] at hw
    have hd := (lowArcData_dPorts continuous_lCoord hε hlt (DAux.dWin_lt_L hG hlt hL)).1
    have := dLowArc_im_le (X := drawL ω) hd hw
    linarith
  · rw [dOrdArc_high (by omega) hL, mem_range_dHighArc] at hw
    exact ⟨hlt, hL, hR, hw⟩

/-- **Proposition M2 (2), ordered form**: arcs of distinct adjacent ordered pairs meet only at vertex points of
common end points. -/
theorem dOrdArc_inter (hG : SideStrict ε ω) (hε : 0 < ε) {x y x' y' : ℤ} (hxy : x < y) (hxy' : x' < y')
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) (hadj' : (MatedCRT.graph ε ω h).adj.Adj x' y')
    (hne : ¬ (x = x' ∧ y = y')) {w : ℂ} (hw : w ∈ range (dOrdArc ε ω x y))
    (hw' : w ∈ range (dOrdArc ε ω x' y')) : w ∈ drawPt ε '' ({x, y} ∩ {x', y'}) := by
  rcases lt_trichotomy w.im (1 / 2) with hlt | heq | hgt
  · -- two lower arcs of L-edges: equal levels, hence equal pairs
    obtain ⟨h1, hL, hwL⟩ := dOrdArc_im_lt hG hε hxy hadj hw hlt
    obtain ⟨h1', hL', hwL'⟩ := dOrdArc_im_lt hG hε hxy' hadj' hw' hlt
    obtain ⟨hd, hlev⟩ := lowArcData_dPorts continuous_lCoord hε h1 (DAux.dWin_lt_L hG h1 hL)
    obtain ⟨hd', hlev'⟩ := lowArcData_dPorts continuous_lCoord hε h1' (DAux.dWin_lt_L hG h1' hL')
    have := dLowArc_level_eq (X := drawL ω) hε hd hd' hwL hwL' hlt.ne
    simp only [coe_drawL] at this
    rw [hlev, hlev'] at this
    exact absurd (dLevel_injective this) hne
  · rcases dOrdArc_im_half hG hε hxy hadj hw heq with h1 | h1 | ⟨hsucc, hseg⟩ <;>
      rcases dOrdArc_im_half hG hε hxy' hadj' hw' heq with h2 | h2 | ⟨hsucc', hseg'⟩
    -- vertex point against vertex point
    · exact ⟨x, ⟨Or.inl rfl, Or.inl (drawPt_injective hε (h1.symm.trans h2))⟩, h1.symm⟩
    · exact ⟨x, ⟨Or.inl rfl, Or.inr (drawPt_injective hε (h1.symm.trans h2))⟩, h1.symm⟩
    · -- vertex point of `x` on the horizontal segment of `{x', x' + 1}`
      rw [h1] at hseg'
      subst hsucc'
      exact ⟨x, ⟨Or.inl rfl, DAux.hseg_pt hε hseg'⟩, h1.symm⟩
    · exact ⟨y, ⟨Or.inr rfl, Or.inl (drawPt_injective hε (h1.symm.trans h2))⟩, h1.symm⟩
    · exact ⟨y, ⟨Or.inr rfl, Or.inr (drawPt_injective hε (h1.symm.trans h2))⟩, h1.symm⟩
    · rw [h1] at hseg'
      subst hsucc'
      exact ⟨y, ⟨Or.inr rfl, DAux.hseg_pt hε hseg'⟩, h1.symm⟩
    · rw [h2] at hseg
      subst hsucc
      exact ⟨x', ⟨DAux.hseg_pt hε hseg, Or.inl rfl⟩, h2.symm⟩
    · rw [h2] at hseg
      subst hsucc
      exact ⟨y', ⟨DAux.hseg_pt hε hseg, Or.inr rfl⟩, h2.symm⟩
    · -- two horizontal segments
      subst hsucc hsucc'
      rcases lt_trichotomy x x' with hlt' | heq' | hgt'
      · obtain ⟨hx', hpt⟩ := DAux.hseg_inter hε hlt' hseg hseg'
        exact ⟨x + 1, ⟨Or.inr rfl, Or.inl hx'.symm⟩, hpt.symm⟩
      · exact absurd ⟨heq', by rw [heq']⟩ hne
      · obtain ⟨hx', hpt⟩ := DAux.hseg_inter hε hgt' hseg' hseg
        exact ⟨x' + 1, ⟨Or.inl hx'.symm, Or.inr rfl⟩, hpt.symm⟩
  · -- two upper arcs of R-edges: reflect, equal levels, hence equal pairs
    obtain ⟨h1, -, hR, hwR⟩ := dOrdArc_im_gt hG hε hxy hadj hw hgt
    obtain ⟨h1', -, hR', hwR'⟩ := dOrdArc_im_gt hG hε hxy' hadj' hw' hgt
    obtain ⟨hd, hlev⟩ := lowArcData_dPorts continuous_rCoord hε h1 (DAux.dWin_lt_R hG h1 hR)
    obtain ⟨hd', hlev'⟩ := lowArcData_dPorts continuous_rCoord hε h1' (DAux.dWin_lt_R hG h1' hR')
    have him : (dRefl w).im ≠ 1 / 2 := by
      rw [dRefl_im]
      intro h0
      linarith
    have := dLowArc_level_eq (X := drawR ω) hε hd hd' hwR hwR' him
    simp only [coe_drawR] at this
    rw [hlev, hlev'] at this
    exact absurd (dLevel_injective this) hne

/-- **Proposition M2 (3), ordered form**: a vertex point lies on an ordered arc only at its end points. -/
theorem eq_or_eq_of_drawPt_mem_dOrdArc (hG : SideStrict ε ω) (hε : 0 < ε) {x y v : ℤ} (hxy : x < y)
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) (hv : drawPt ε v ∈ range (dOrdArc ε ω x y)) :
    v = x ∨ v = y := by
  rcases dOrdArc_im_half hG hε hxy hadj hv (drawPt_im ε v) with h1 | h1 | ⟨rfl, hseg⟩
  · exact Or.inl (drawPt_injective hε h1)
  · exact Or.inr (drawPt_injective hε h1)
  · exact DAux.hseg_pt hε hseg

/-- **Proposition M2 (1), ordered form**: the arc of an adjacent ordered pair is an arc (an injective path). -/
theorem injective_dOrdArc (hG : SideStrict ε ω) (hε : 0 < ε) {x y : ℤ} (hxy : x < y)
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) : Injective (dOrdArc ε ω x y) := by
  rcases matedCRT_adj_cases hxy hadj with rfl | ⟨hlt, hL⟩ | ⟨hlt, hL, hR⟩
  · rw [dOrdArc_succ]
    refine Path.segment_injective_of_ne fun h0 => ?_
    have := drawPt_injective hε h0
    omega
  · rw [dOrdArc_low (by omega) hL]
    exact injective_dLowArc (X := drawL ω) hε
      (lowArcData_dPorts continuous_lCoord hε hlt (DAux.dWin_lt_L hG hlt hL)).1
  · rw [dOrdArc_high (by omega) hL]
    exact injective_dHighArc (X := drawR ω) hε
      (lowArcData_dPorts continuous_rCoord hε hlt (DAux.dWin_lt_R hG hlt hR)).1

/-- The strip map on the closed central band reads the horizontal coordinate. -/
theorem DAux.shearedStripMap_of_mid {η : ℝ → ℂ} (P : Peanosphere ω η) {w : ℂ} (h0 : 0 ≤ w.im) (h1 : w.im ≤ 1) :
    shearedStripMap P w = η w.re := by
  have := shearedStripMap_stripPoint_mid P (t := w.re) h0 h1
  rwa [DAux.stripPoint_re_im] at this

/-- **Proposition M2 (4), ordered form**: the strip map sends the arc of an adjacent ordered pair `x < y` into
`H_x ∪ H_y`, `H_v = η(I_v)`. -/
theorem shearedStripMap_dOrdArc_mem {η : ℝ → ℂ} (P : Peanosphere ω η) (hG : SideStrict ε ω) (hε : 0 < ε)
    {x y : ℤ} (hxy : x < y) (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) {w : ℂ}
    (hw : w ∈ range (dOrdArc ε ω x y)) :
    shearedStripMap P w ∈ η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∪ η '' Icc (ε * ((y : ℝ) - 1)) (ε * y) := by
  -- a point of a bottom or top star segment of an end point `v`
  have hstar : ∀ {v : ℤ} {p : ℝ}, p ∈ Ioo (ε * ((v : ℝ) - 1)) (ε * v) → ∀ {u : ℂ},
      u ∈ segment ℝ (drawPt ε v) (stripPoint p 0) → ∀ {z : ℂ}, z.re = u.re → 0 ≤ z.im → z.im ≤ 1 →
        shearedStripMap P z ∈ η '' Icc (ε * ((v : ℝ) - 1)) (ε * v) := by
    intro v p hp u hu z hre h0 h1
    rw [DAux.shearedStripMap_of_mid P h0 h1]
    exact mem_image_of_mem η (Ioo_subset_Icc_self (hre ▸ DAux.bstar_re_mem hε hp hu))
  rcases matedCRT_adj_cases hxy hadj with rfl | ⟨hlt, hL⟩ | ⟨hlt, hL, hR⟩
  · rw [dOrdArc_succ, Path.range_segment] at hw
    obtain ⟨him, h1, h2⟩ := DAux.hseg_coords hε hw
    rw [DAux.shearedStripMap_of_mid P (by rw [him]; norm_num) (by rw [him]; norm_num)]
    rcases le_or_gt w.re (ε * x) with hle | hgt
    · left
      refine mem_image_of_mem η ⟨?_, hle⟩
      nlinarith
    · right
      refine mem_image_of_mem η ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast; nlinarith
  · rw [dOrdArc_low (by omega) hL] at hw
    have hd := (lowArcData_dPorts continuous_lCoord hε hlt (DAux.dWin_lt_L hG hlt hL)).1
    rcases dLowArc_pieces (X := drawL ω) hd hw with hs | ⟨u, hu, rfl⟩ | hs
    · exact Or.inl (hstar hd.mem₁ hs rfl (DAux.bstar_im_mem hs).1 (by linarith [(DAux.bstar_im_mem hs).2]))
    · left
      have := shearedStripMap_lowerChord P _ _ hd.rel hu
      simp only [coe_drawL]
      rw [this]
      exact mem_image_of_mem η (Ioo_subset_Icc_self hd.mem₁)
    · exact Or.inr (hstar hd.mem₂ hs rfl (DAux.bstar_im_mem hs).1 (by linarith [(DAux.bstar_im_mem hs).2]))
  · rw [dOrdArc_high (by omega) hL, mem_range_dHighArc] at hw
    have hd := (lowArcData_dPorts continuous_rCoord hε hlt (DAux.dWin_lt_R hG hlt hR)).1
    rcases dLowArc_pieces (X := drawR ω) hd hw with hs | ⟨u, hu, hu'⟩ | hs
    · have him := DAux.bstar_im_mem hs
      rw [dRefl_im] at him
      exact Or.inl (hstar hd.mem₁ hs (dRefl_re w).symm (by linarith) (by linarith))
    · left
      have hw' : w = stripPoint u (1 + rCoord ω u - rCoord ω (dPort₁ ε (rCoord ω) x y)) := by
        rw [← dRefl_dRefl w, hu']
        refine Complex.ext rfl ?_
        simp only [dRefl_im, DAux.stripPoint_im, coe_drawR]
        ring
      rw [hw', shearedStripMap_upperChord P _ _ hd.rel hu]
      exact mem_image_of_mem η (Ioo_subset_Icc_self hd.mem₁)
    · have him := DAux.bstar_im_mem hs
      rw [dRefl_im] at him
      exact Or.inr (hstar hd.mem₂ hs (dRefl_re w).symm (by linarith) (by linarith))

end Ordered

/-! ### Proposition M2 for the arcs of all adjacent pairs -/

section Unordered

variable {h : MatedCRT.IsLocallyFinite ε ω}

theorem range_dArc_of_lt {x y : ℤ} (hxy : x < y) : range (dArc ε ω x y) = range (dOrdArc ε ω x y) := by
  rw [dArc_of_lt hxy]

theorem range_dArc_of_gt {x y : ℤ} (hxy : y < x) : range (dArc ε ω x y) = range (dOrdArc ε ω y x) := by
  rw [dArc_of_gt hxy, Path.symm_range]

/-- **Proposition M2 (1)**: every edge arc is an arc (an injective path). -/
theorem injective_dArc (hG : SideStrict ε ω) (hε : 0 < ε) {x y : ℤ}
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) : Injective (dArc ε ω x y) := by
  rcases lt_or_gt_of_ne hadj.ne with hxy | hxy
  · rw [dArc_of_lt hxy]
    exact injective_dOrdArc hG hε hxy hadj
  · rw [dArc_of_gt hxy]
    intro s t hst
    have := injective_dOrdArc hG hε hxy hadj.symm hst
    simpa using congrArg unitInterval.symm this

/-- **Proposition M2 (2)**: two arcs of different edges meet only at `pt v` for common end points `v`. -/
theorem dArc_inter (hG : SideStrict ε ω) (hε : 0 < ε) {x y x' y' : ℤ}
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) (hadj' : (MatedCRT.graph ε ω h).adj.Adj x' y')
    (hne₁ : ¬ (x = x' ∧ y = y')) (hne₂ : ¬ (x = y' ∧ y = x')) :
    range (dArc ε ω x y) ∩ range (dArc ε ω x' y') ⊆ drawPt ε '' ({x, y} ∩ {x', y'}) := by
  rintro w ⟨hw, hw'⟩
  rcases lt_or_gt_of_ne hadj.ne with hxy | hxy <;> rcases lt_or_gt_of_ne hadj'.ne with hxy' | hxy'
  · rw [range_dArc_of_lt hxy] at hw
    rw [range_dArc_of_lt hxy'] at hw'
    exact dOrdArc_inter hG hε hxy hxy' hadj hadj' hne₁ hw hw'
  · rw [range_dArc_of_lt hxy] at hw
    rw [range_dArc_of_gt hxy'] at hw'
    have := dOrdArc_inter hG hε hxy hxy' hadj hadj'.symm (fun h0 => hne₂ ⟨h0.1, h0.2⟩) hw hw'
    rwa [pair_comm x' y']
  · rw [range_dArc_of_gt hxy] at hw
    rw [range_dArc_of_lt hxy'] at hw'
    have := dOrdArc_inter hG hε hxy hxy' hadj.symm hadj' (fun h0 => hne₂ ⟨h0.2, h0.1⟩) hw hw'
    rwa [pair_comm y x] at this
  · rw [range_dArc_of_gt hxy] at hw
    rw [range_dArc_of_gt hxy'] at hw'
    have := dOrdArc_inter hG hε hxy hxy' hadj.symm hadj'.symm (fun h0 => hne₁ ⟨h0.2, h0.1⟩) hw hw'
    rwa [pair_comm y x, pair_comm y' x'] at this

/-- **Proposition M2 (3)**: `pt v` lies on the arc of an edge only if `v` is an end point of that edge. -/
theorem eq_or_eq_of_drawPt_mem_dArc (hG : SideStrict ε ω) (hε : 0 < ε) {x y v : ℤ}
    (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) (hv : drawPt ε v ∈ range (dArc ε ω x y)) : v = x ∨ v = y := by
  rcases lt_or_gt_of_ne hadj.ne with hxy | hxy
  · rw [range_dArc_of_lt hxy] at hv
    exact eq_or_eq_of_drawPt_mem_dOrdArc hG hε hxy hadj hv
  · rw [range_dArc_of_gt hxy] at hv
    exact (eq_or_eq_of_drawPt_mem_dOrdArc hG hε hxy hadj.symm hv).symm

/-- **Proposition M2 (4), vertices**: `Ψ(pt x) ∈ H_x`. -/
theorem shearedStripMap_drawPt_mem {η : ℝ → ℂ} (P : Peanosphere ω η) (hε : 0 < ε) (x : ℤ) :
    shearedStripMap P (drawPt ε x) ∈ η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
  rw [DAux.shearedStripMap_of_mid P (by rw [drawPt_im]; norm_num) (by rw [drawPt_im]; norm_num)]
  exact mem_image_of_mem η (Ioo_subset_Icc_self (drawPt_re_mem hε x))

/-- **Proposition M2 (4), edges**: `Ψ(arc_{xy}) ⊆ H_x ∪ H_y`. -/
theorem shearedStripMap_dArc_mem {η : ℝ → ℂ} (P : Peanosphere ω η) (hG : SideStrict ε ω) (hε : 0 < ε)
    {x y : ℤ} (hadj : (MatedCRT.graph ε ω h).adj.Adj x y) (t : unitInterval) :
    shearedStripMap P (dArc ε ω x y t) ∈
      η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∪ η '' Icc (ε * ((y : ℝ) - 1)) (ε * y) := by
  have hw : dArc ε ω x y t ∈ range (dArc ε ω x y) := mem_range_self t
  rcases lt_or_gt_of_ne hadj.ne with hxy | hxy
  · rw [range_dArc_of_lt hxy] at hw
    exact shearedStripMap_dOrdArc_mem P hG hε hxy hadj hw
  · rw [range_dArc_of_gt hxy] at hw
    exact (shearedStripMap_dOrdArc_mem P hG hε hxy hadj.symm hw).symm

end Unordered

end MatedCRTHarmonic.RouteM
