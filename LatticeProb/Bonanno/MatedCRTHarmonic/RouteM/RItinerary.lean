/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.RItinerary at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RGeometry

/-!
# Route M,: template itineraries (index ranges and cell locations)

`IsTemplateWalk H z r ϑ n v α β` bundles the hypotheses that `CellularEmbedding.TemplateSeparation z r` places on
one walk `v 0, …, v n` with template intervals `[α j, β j]` (an `r/60`-itinerary of the moved polar template, TF3
§2). This module proves, in the normalized coordinates `tmplCoord z r ϑ` of `RGeometry`:

* the **radial block** (`exists_radial_block`): indices `j₀ ≤ j₁ ≤ n` with `α j₀ ∈ [1/4, 1/4 + 1/50)` and
  `β j₁ ∈ (1/2 - 1/50, 1/2]`; every index in between has `[α j, β j] ⊆ [1/4, 1/2]` (TF3's block `R`);
* the **final block** (`exists_final_start`): an index `k₀ ≤ n` with `α k₀ ∈ [3/4, 3/4 + 1/50)` (TF3's block
  `F = [k₀, n]`);
* cell locations: cells of the radial block lie in `{re > 22/25, |im| < 1/60}` (`coord_radial`), its first cell inside
  `|·| < 19/20` and its last cell outside `|·| > 21/20`; cells of the final block lie within `1/60` of the final arc
  (`coord_final_props`), the first one strictly below the real axis with argument `≤ -1/50` and the last one above
  it with argument `≥ 1/50`; every cell of the walk lies in the annulus `22/25 < |·| < 28/25` (`coord_annulus`).
-/

set_option autoImplicit false

noncomputable section

open Set Real
open MatedCRTHarmonic.Topology

namespace MatedCRTHarmonic.RouteM

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-- The hypotheses of `CellularEmbedding.TemplateSeparation z r` on one walk `v 0, …, v n` with template intervals
`[α j, β j]` (TF3 §2: an `r/60`-itinerary of the moved polar template), bundled. -/
structure IsTemplateWalk (H : CellularEmbedding G o) (z : ℂ) (r ϑ : ℝ) (n : ℕ) (v : ℕ → V) (α β : ℕ → ℝ) :
    Prop where
  adj : ∀ j < n, G.adj.Adj (v j) (v (j + 1))
  α_zero : α 0 = 0
  β_last : β n = 1
  monotone_α : Monotone α
  monotone_β : Monotone β
  overlap : ∀ j < n, α (j + 1) ≤ β j
  bounds : ∀ j ≤ n, 0 ≤ α j ∧ α j ≤ β j ∧ β j ≤ 1 ∧ β j - α j ≤ 1 / 50
  near : ∀ j ≤ n, ∀ s ∈ Set.Icc (α j) (β j), ∀ w ∈ H.cell (v j),
    ‖w - CellularEmbedding.movedTemplate z r ϑ s‖ < r / 60

namespace IsTemplateWalk

variable {H : CellularEmbedding G o} {z : ℂ} {r ϑ : ℝ} {n : ℕ} {v : ℕ → V} {α β : ℕ → ℝ}

theorem α_last_ge (hW : IsTemplateWalk H z r ϑ n v α β) : 49 / 50 ≤ α n := by
  have h := hW.bounds n le_rfl
  rw [hW.β_last] at h
  linarith [h.2.2.2]

/-- **The radial block** (TF3 §8, "Index ranges"): indices `j₀ ≤ j₁ ≤ n` with `α j₀ ∈ [1/4, 1/4 + 1/50)` and
`β j₁ ∈ (1/2 - 1/50, 1/2]`. -/
theorem exists_radial_block (hW : IsTemplateWalk H z r ϑ n v α β) :
    ∃ j₀ j₁, j₀ ≤ j₁ ∧ j₁ ≤ n ∧ 1 / 4 ≤ α j₀ ∧ α j₀ < 1 / 4 + 1 / 50 ∧ β j₁ ≤ 1 / 2 ∧
      1 / 2 - 1 / 50 < β j₁ := by
  classical
  have hex : ∃ j, 1 / 4 ≤ α j ∧ j ≤ n := ⟨n, by linarith [hW.α_last_ge], le_rfl⟩
  obtain ⟨hj₀α, hj₀n⟩ := Nat.find_spec hex
  have hj₀pos : Nat.find hex ≠ 0 := by
    intro h
    rw [h, hW.α_zero] at hj₀α
    norm_num at hj₀α
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hj₀pos
  have hmlt : m < n := by omega
  have hmα : ¬ (1 / 4 ≤ α m ∧ m ≤ n) := Nat.find_min hex (by omega)
  have hmα' : α m < 1 / 4 := by
    by_contra hcon
    exact hmα ⟨le_of_not_gt hcon, hmlt.le⟩
  have hov := hW.overlap m hmlt
  have hb := hW.bounds m hmlt.le
  have hα₀ : α (Nat.find hex) < 1 / 4 + 1 / 50 := by
    rw [hm]
    linarith [hb.2.2.2]
  have hb₀ := hW.bounds (Nat.find hex) hj₀n
  have hβj₀ : β (Nat.find hex) ≤ 1 / 2 := by linarith [hb₀.2.2.2]
  have hj₀j₁ : Nat.find hex ≤ Nat.findGreatest (fun j => β j ≤ 1 / 2) n :=
    Nat.le_findGreatest hj₀n hβj₀
  have hβj₁ : β (Nat.findGreatest (fun j => β j ≤ 1 / 2) n) ≤ 1 / 2 :=
    Nat.findGreatest_spec (P := fun j => β j ≤ 1 / 2) hj₀n hβj₀
  have hj₁n : Nat.findGreatest (fun j => β j ≤ 1 / 2) n ≤ n := Nat.findGreatest_le n
  have hj₁lt : Nat.findGreatest (fun j => β j ≤ 1 / 2) n < n := by
    rcases lt_or_eq_of_le hj₁n with h | h
    · exact h
    · rw [h, hW.β_last] at hβj₁
      norm_num at hβj₁
  have hnext : ¬ (β (Nat.findGreatest (fun j => β j ≤ 1 / 2) n + 1) ≤ 1 / 2) :=
    Nat.findGreatest_is_greatest (P := fun j => β j ≤ 1 / 2) (n := n)
      (k := Nat.findGreatest (fun j => β j ≤ 1 / 2) n + 1) (by omega) (by omega)
  have hov' := hW.overlap _ hj₁lt
  have hb' := hW.bounds (Nat.findGreatest (fun j => β j ≤ 1 / 2) n + 1) (by omega)
  refine ⟨Nat.find hex, Nat.findGreatest (fun j => β j ≤ 1 / 2) n, hj₀j₁, hj₁n, hj₀α, hα₀, hβj₁, ?_⟩
  push Not at hnext
  linarith [hb'.2.2.2]

/-- **The final block** (TF3 §8, "Index ranges"): an index `k₀ ≤ n` with `α k₀ ∈ [3/4, 3/4 + 1/50)`. -/
theorem exists_final_start (hW : IsTemplateWalk H z r ϑ n v α β) :
    ∃ k₀, k₀ ≤ n ∧ 3 / 4 ≤ α k₀ ∧ α k₀ < 3 / 4 + 1 / 50 := by
  classical
  have hex : ∃ j, 3 / 4 ≤ α j ∧ j ≤ n := ⟨n, by linarith [hW.α_last_ge], le_rfl⟩
  obtain ⟨hk₀α, hk₀n⟩ := Nat.find_spec hex
  have hk₀pos : Nat.find hex ≠ 0 := by
    intro h
    rw [h, hW.α_zero] at hk₀α
    norm_num at hk₀α
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk₀pos
  have hmlt : m < n := by omega
  have hmα : ¬ (3 / 4 ≤ α m ∧ m ≤ n) := Nat.find_min hex (by omega)
  have hmα' : α m < 3 / 4 := by
    by_contra hcon
    exact hmα ⟨le_of_not_gt hcon, hmlt.le⟩
  have hov := hW.overlap m hmlt
  have hb := hW.bounds m hmlt.le
  refine ⟨Nat.find hex, hk₀n, hk₀α, ?_⟩
  rw [hm]
  linarith [hb.2.2.2]

/-! ### Cell locations in normalized coordinates -/

theorem mem_Icc_of_mem (hW : IsTemplateWalk H z r ϑ n v α β) {j : ℕ} (hj : j ≤ n) {s : ℝ}
    (hs : s ∈ Icc (α j) (β j)) : 0 ≤ s ∧ s ≤ 1 := by
  obtain ⟨h0, -, h1, -⟩ := hW.bounds j hj
  exact ⟨h0.trans hs.1, hs.2.trans h1⟩

/-- Every cell of the walk is within `1/60` of the template at each time of its interval (normalized). -/
theorem coord_near (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {j : ℕ} (hj : j ≤ n) {s : ℝ}
    (hs : s ∈ Icc (α j) (β j)) {w : ℂ} (hw : w ∈ H.cell (v j)) :
    ‖tmplCoord z r ϑ w - tmplPt s‖ < 1 / 60 := by
  rw [norm_tmplCoord_sub_tmplPt hr, div_lt_iff₀ hr]
  have := hW.near j hj s hs w hw
  linarith

/-- Every cell of the walk lies in the annulus `22/25 < |·| < 28/25` (normalized). -/
theorem coord_annulus (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {j : ℕ} (hj : j ≤ n) {w : ℂ}
    (hw : w ∈ H.cell (v j)) :
    22 / 25 < ‖tmplCoord z r ϑ w‖ ∧ ‖tmplCoord z r ϑ w‖ < 28 / 25 := by
  have hs : α j ∈ Icc (α j) (β j) := ⟨le_rfl, (hW.bounds j hj).2.1⟩
  have hnear := hW.coord_near hr hj hs hw
  obtain ⟨h0, h1⟩ := hW.mem_Icc_of_mem hj hs
  have hT := norm_tmplPt_of_mem h0 h1
  have hR := polarRadius_four_mul_bounds h0 h1
  have e1 := norm_sub_norm_le (tmplCoord z r ϑ w) (tmplPt (α j))
  have e2 := norm_sub_norm_le (tmplPt (α j)) (tmplCoord z r ϑ w)
  rw [norm_sub_rev] at e2
  constructor <;> linarith

/-- Cells of the radial block lie in `{re > 22/25, |im| < 1/60}` (normalized; TF3 §8 "Geometry" 1). -/
theorem coord_radial (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {j : ℕ} (hj : j ≤ n)
    (h1 : 1 / 4 ≤ α j) (h2 : β j ≤ 1 / 2) {w : ℂ} (hw : w ∈ H.cell (v j)) :
    22 / 25 < (tmplCoord z r ϑ w).re ∧ |(tmplCoord z r ϑ w).im| < 1 / 60 := by
  have hαβ := (hW.bounds j hj).2.1
  have hnear := hW.coord_near hr hj ⟨le_rfl, hαβ⟩ hw
  rw [tmplPt_radial h1 (hαβ.trans h2)] at hnear
  have hre := Complex.abs_re_le_norm (tmplCoord z r ϑ w - ((7 / 10 + 4 / 5 * α j : ℝ) : ℂ))
  have him := Complex.abs_im_le_norm (tmplCoord z r ϑ w - ((7 / 10 + 4 / 5 * α j : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  constructor
  · have := (abs_lt.1 (hre.trans_lt hnear)).1
    linarith
  · exact him.trans_lt hnear

/-- The first cell of the radial block lies inside `|·| < 19/20` (normalized; TF3: `< 0.933`). -/
theorem norm_coord_radial_start (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {j : ℕ} (hj : j ≤ n)
    (h1 : 1 / 4 ≤ α j) (h2 : α j < 1 / 4 + 1 / 50) {w : ℂ} (hw : w ∈ H.cell (v j)) :
    ‖tmplCoord z r ϑ w‖ < 19 / 20 := by
  have hnear := hW.coord_near hr hj ⟨le_rfl, (hW.bounds j hj).2.1⟩ hw
  rw [tmplPt_radial h1 (by linarith)] at hnear
  have hT : ‖(((7 / 10 + 4 / 5 * α j : ℝ)) : ℂ)‖ = 7 / 10 + 4 / 5 * α j := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have e1 := norm_sub_norm_le (tmplCoord z r ϑ w) (((7 / 10 + 4 / 5 * α j : ℝ)) : ℂ)
  linarith

/-- The last cell of the radial block lies outside `|·| > 21/20` (normalized; TF3: `> 1.067`). -/
theorem norm_coord_radial_end (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {j : ℕ} (hj : j ≤ n)
    (h1 : 1 / 2 - 1 / 50 < β j) (h2 : β j ≤ 1 / 2) {w : ℂ} (hw : w ∈ H.cell (v j)) :
    21 / 20 < ‖tmplCoord z r ϑ w‖ := by
  have hnear := hW.coord_near hr hj ⟨(hW.bounds j hj).2.1, le_rfl⟩ hw
  rw [tmplPt_radial (by linarith) h2] at hnear
  have hT : ‖(((7 / 10 + 4 / 5 * β j : ℝ)) : ℂ)‖ = 7 / 10 + 4 / 5 * β j := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have e2 := norm_sub_norm_le (((7 / 10 + 4 / 5 * β j : ℝ)) : ℂ) (tmplCoord z r ϑ w)
  rw [norm_sub_rev] at e2
  linarith

/-- A point within `1/60` of `exp (iθ)`, `|θ| ≤ 1/10`, has modulus in `(0.983, 1.017)` and positive real part. -/
theorem final_arc_props {θ : ℝ} (hθ1 : -(1 / 10) ≤ θ) (hθ2 : θ ≤ 1 / 10) {P : ℂ}
    (hP : ‖P - Complex.exp ((θ : ℂ) * Complex.I)‖ < 1 / 60) :
    983 / 1000 < ‖P‖ ∧ ‖P‖ < 1017 / 1000 ∧ 0 < P.re := by
  have hn : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have e1 := norm_sub_norm_le P (Complex.exp ((θ : ℂ) * Complex.I))
  have e2 := norm_sub_norm_le (Complex.exp ((θ : ℂ) * Complex.I)) P
  rw [norm_sub_rev] at e2
  have hcos : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  have hre := Complex.abs_re_le_norm (P - Complex.exp ((θ : ℂ) * Complex.I))
  rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re] at hre
  have hθsq : θ ^ 2 ≤ 1 / 100 := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩
  have := (abs_lt.1 (hre.trans_lt hP)).1
  linarith

/-- Cells of the final block are within `1/60` of the final arc (normalized; TF3 §8 "Geometry" 2). -/
theorem coord_final (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {j : ℕ} (hj : j ≤ n)
    (h1 : 3 / 4 ≤ α j) {s : ℝ} (hs : s ∈ Icc (α j) (β j)) {w : ℂ} (hw : w ∈ H.cell (v j)) :
    ‖tmplCoord z r ϑ w - Complex.exp (((4 / 5 * s - 7 / 10 : ℝ) : ℂ) * Complex.I)‖ < 1 / 60 := by
  have hnear := hW.coord_near hr hj hs hw
  rwa [tmplPt_final (h1.trans hs.1) (hW.mem_Icc_of_mem hj hs).2] at hnear

/-- Cells of the final block: modulus in `(0.983, 1.017)`, positive real part. -/
theorem coord_final_props (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {j : ℕ} (hj : j ≤ n)
    (h1 : 3 / 4 ≤ α j) {w : ℂ} (hw : w ∈ H.cell (v j)) :
    983 / 1000 < ‖tmplCoord z r ϑ w‖ ∧ ‖tmplCoord z r ϑ w‖ < 1017 / 1000 ∧ 0 < (tmplCoord z r ϑ w).re := by
  have hs : α j ∈ Icc (α j) (β j) := ⟨le_rfl, (hW.bounds j hj).2.1⟩
  have h2 := (hW.mem_Icc_of_mem hj hs).2
  exact final_arc_props (by linarith) (by linarith) (hW.coord_final hr hj h1 hs hw)

/-- The first cell of the final block lies strictly below the real axis, with argument `≤ -1/50` (normalized;
TF3: `arg ∈ (-0.117, -0.067)`). -/
theorem coord_final_start (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {j : ℕ} (hj : j ≤ n)
    (h1 : 3 / 4 ≤ α j) (h2 : α j < 3 / 4 + 1 / 50) {w : ℂ} (hw : w ∈ H.cell (v j)) :
    (tmplCoord z r ϑ w).im < 0 ∧ Complex.arg (tmplCoord z r ϑ w) ≤ -(1 / 50) := by
  have hs : α j ∈ Icc (α j) (β j) := ⟨le_rfl, (hW.bounds j hj).2.1⟩
  have hnear := hW.coord_final hr hj h1 hs hw
  obtain ⟨hn1, hn2, hre⟩ := hW.coord_final_props hr hj h1 hw
  set P := tmplCoord z r ϑ w with hPdef
  set θ := 4 / 5 * α j - 7 / 10 with hθ
  have hpi := Real.pi_gt_three
  have hsinθ : Real.sin θ ≤ Real.sin (-(21 / 250)) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hsin0 : (21 / 250 : ℝ) - (21 / 250) ^ 3 / 6 < Real.sin (21 / 250) := Real.sin_gt_sub_cube (by norm_num)
  rw [Real.sin_neg] at hsinθ
  have him := Complex.abs_im_le_norm (P - Complex.exp ((θ : ℂ) * Complex.I))
  rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im] at him
  have hPim : P.im < -(67 / 1000) := by
    have := (abs_lt.1 (him.trans_lt hnear)).2
    linarith
  have hP0 : P ≠ 0 := fun h => by rw [h, norm_zero] at hn1; linarith
  exact ⟨by linarith, arg_le_of_im_le hP0 hre.le (by linarith)⟩

/-- The last cell of the walk lies strictly above the real axis, with argument `≥ 1/50` (normalized; TF3:
`arg ∈ (0.067, 0.117)`). -/
theorem coord_final_end (hW : IsTemplateWalk H z r ϑ n v α β) (hr : 0 < r) {w : ℂ} (hw : w ∈ H.cell (v n)) :
    0 < (tmplCoord z r ϑ w).im ∧ 1 / 50 ≤ Complex.arg (tmplCoord z r ϑ w) := by
  have h1 : 3 / 4 ≤ α n := by linarith [hW.α_last_ge]
  have hs : (1 : ℝ) ∈ Icc (α n) (β n) := ⟨by rw [← hW.β_last]; exact (hW.bounds n le_rfl).2.1,
    by rw [hW.β_last]⟩
  have hnear := hW.coord_final hr le_rfl h1 hs hw
  obtain ⟨hn1, hn2, hre⟩ := hW.coord_final_props hr le_rfl h1 hw
  set P := tmplCoord z r ϑ w with hPdef
  rw [show (4 / 5 * 1 - 7 / 10 : ℝ) = 1 / 10 by norm_num] at hnear
  have hsin0 : (1 / 10 : ℝ) - (1 / 10) ^ 3 / 6 < Real.sin (1 / 10) := Real.sin_gt_sub_cube (by norm_num)
  have him := Complex.abs_im_le_norm (P - Complex.exp ((((1 / 10 : ℝ)) : ℂ) * Complex.I))
  rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im] at him
  have hPim : 83 / 1000 < P.im := by
    have := (abs_lt.1 (him.trans_lt hnear)).1
    linarith
  have hP0 : P ≠ 0 := fun h => by rw [h, norm_zero] at hn1; linarith
  exact ⟨by linarith, le_arg_of_im_ge hP0 hre.le (by linarith)⟩

end IsTemplateWalk

end MatedCRTHarmonic.RouteM
