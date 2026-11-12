/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53M1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53I5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L316P2

/-!
# DZZ Lemma 5.3, part 1, node 4: geometry and the one-point Markov step (P2-DZZ53M)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2393 and l. 2516–2522.

* `l53_iface_sub_frontier`: the interface `𝖢̄ ∩ 𝖢̄'` of two distinct cells lies on `∂𝖢̄`
  (copy of the case analysis of `l53_iface_ne_top`, S5L53F3).
* **`l53_iface_ge_min`**: for neighbouring cells, `μH¹(𝖢̄ ∩ 𝖢̄') ≥ min(s_𝖢, s_𝖢')`; with the side
  ratio of a good sequence this is (eq-Lambda-i-not-small), DZZ l. 2393 (`𝓛₁(Λ_i) ≥ ε* s_i`).
  Own elementary proof (dyadic nesting, `dy_nested_real`).
* `l53_frontier_ne_top`: `μH¹(∂𝖢̄) < ∞`.
* `l53_tildeBox_sub_uv`: for `w ∈ {u, v}` in the cell `𝖢̄` and `x ∈ 𝖢̄`, `x ≠ w`,
  `𝕍̃_{w,x} ⊆ 𝕍_{c_𝖢, 5 s_𝖢} ⊆ 𝕍̃_{u,v}` once `12 s_𝖢 ≤ |u − v|` (DZZ l. 2361: the pieces are
  `D^{𝕍̃_{u,v}}`-pieces). Own elementary proof.
* **`l53_point_markov`**: Tonelli and Markov for one base point (the "similar but simpler"
  counting of l. 2516–2522; cf. `l53_far_count`, S5L53E3, which has two).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- `μH¹` of a horizontal segment. -/
lemma l53M_hline_eq (a b c : ℝ) :
    μH[1] {z : ℂ | z.im = a ∧ b ≤ z.re ∧ z.re ≤ c} = ENNReal.ofReal (c - b) := by
  have : {z : ℂ | z.im = a ∧ b ≤ z.re ∧ z.re ≤ c} = (fun t : ℝ => (⟨t, a⟩ : ℂ)) '' Icc b c := by
    ext z
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨z.re, ⟨h2, h3⟩, Complex.ext (by simp) (by simp [h1])⟩, ?_⟩
    rintro ⟨t, ⟨h2, h3⟩, rfl⟩
    exact ⟨rfl, h2, h3⟩
  rw [this, (l53_isometry_hline a).hausdorffMeasure_image (Or.inl zero_le_one),
    MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]

/-- `μH¹` of a vertical segment. -/
lemma l53M_vline_eq (a b c : ℝ) :
    μH[1] {z : ℂ | z.re = a ∧ b ≤ z.im ∧ z.im ≤ c} = ENNReal.ofReal (c - b) := by
  have : {z : ℂ | z.re = a ∧ b ≤ z.im ∧ z.im ≤ c} = (fun t : ℝ => (⟨a, t⟩ : ℂ)) '' Icc b c := by
    ext z
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨z.im, ⟨h2, h3⟩, Complex.ext (by simp [h1]) (by simp)⟩, ?_⟩
    rintro ⟨t, ⟨h2, h3⟩, rfl⟩
    exact ⟨rfl, h2, h3⟩
  rw [this, (l53_isometry_vline a).hausdorffMeasure_image (Or.inl zero_le_one),
    MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]

/-- **The interface of two distinct cells lies on the frontier of the first** (copy of the case
analysis of `l53_iface_ne_top`). -/
lemma l53_iface_sub_frontier_of_nest {C C' : DyBox} (hne : C ≠ C')
    (hn1 : C.closedBox ⊆ C'.closedBox → C = C') (hn2 : C'.closedBox ⊆ C.closedBox → C' = C) :
    C.closedBox ∩ C'.closedBox ⊆ frontier C.closedBox := by
  rintro z ⟨hz, hz'⟩
  refine mem_frontier_closedBox hz ?_
  obtain ⟨a1, a2, a3, a4⟩ := hz
  obtain ⟨b1, b2, b3, b4⟩ := hz'
  by_contra hedge
  simp only [not_or] at hedge
  obtain ⟨e1, e2, e3, e4⟩ := hedge
  have hj1 : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side := by
    rcases lt_or_ge ((C.j : ℝ) * C.side) ((C'.j + 1) * C'.side) with h | h
    · exact h
    · exact absurd (le_antisymm (b2.trans h) a1) e1
  have hj2 : (C'.j : ℝ) * C'.side < (C.j + 1) * C.side := by
    rcases lt_or_ge ((C'.j : ℝ) * C'.side) ((C.j + 1) * C.side) with h | h
    · exact h
    · exact absurd (le_antisymm a2 (h.trans b1)) e2
  have hk1 : (C.k : ℝ) * C.side < (C'.k + 1) * C'.side := by
    rcases lt_or_ge ((C.k : ℝ) * C.side) ((C'.k + 1) * C'.side) with h | h
    · exact h
    · exact absurd (le_antisymm (b4.trans h) a3) e3
  have hk2 : (C'.k : ℝ) * C'.side < (C.k + 1) * C.side := by
    rcases lt_or_ge ((C'.k : ℝ) * C'.side) ((C.k + 1) * C.side) with h | h
    · exact h
    · exact absurd (le_antisymm a4 (h.trans b3)) e4
  rcases le_total C'.n C.n with hle | hle
  · have u := dy_nested_real (n := C.n) (n' := C'.n) hle hj1 hj2
    have v := dy_nested_real (n := C.n) (n' := C'.n) hle hk1 hk2
    have hsub : C.closedBox ⊆ C'.closedBox := by
      rintro q ⟨q1, q2, q3, q4⟩
      exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
    exact hne (hn1 hsub)
  · have u := dy_nested_real (n := C'.n) (n' := C.n) hle hj2 hj1
    have v := dy_nested_real (n := C'.n) (n' := C.n) hle hk2 hk1
    have hsub : C'.closedBox ⊆ C.closedBox := by
      rintro q ⟨q1, q2, q3, q4⟩
      exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
    exact hne (hn2 hsub).symm

/-- The core of `l53_iface_ge_min`: `C'` the smaller box. -/
lemma l53_iface_ge_aux {C C' : DyBox} (hn2 : C'.closedBox ⊆ C.closedBox → C' = C)
    (hN : Neighbour C C') (hle : C.n ≤ C'.n) :
    ENNReal.ofReal C'.side ≤ μH[1] (C.closedBox ∩ C'.closedBox) := by
  obtain ⟨hne, hns⟩ := hN
  simp only [Set.Subsingleton, not_forall] at hns
  obtain ⟨z, ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩, z', ⟨⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3, d4⟩⟩,
    hzz⟩ := hns
  have hs' : 0 < C'.side := by unfold DyBox.side; positivity
  -- both coordinates strict: `C̄' ⊆ C̄`
  have hnot : ¬ (((C.j : ℝ) * C.side < (C'.j + 1) * C'.side ∧
      (C'.j : ℝ) * C'.side < (C.j + 1) * C.side) ∧
      ((C.k : ℝ) * C.side < (C'.k + 1) * C'.side ∧
      (C'.k : ℝ) * C'.side < (C.k + 1) * C.side)) := by
    rintro ⟨⟨hj1, hj2⟩, ⟨hk1, hk2⟩⟩
    have u := dy_nested_real (n := C'.n) (n' := C.n) hle hj2 hj1
    have v := dy_nested_real (n := C'.n) (n' := C.n) hle hk2 hk1
    have hsub : C'.closedBox ⊆ C.closedBox := by
      rintro q ⟨q1, q2, q3, q4⟩
      exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
    exact hne (hn2 hsub).symm
  by_cases hx : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side ∧
      (C'.j : ℝ) * C'.side < (C.j + 1) * C.side
  · -- horizontal interface at height `t`
    have u := dy_nested_real (n := C'.n) (n' := C.n) hle hx.2 hx.1
    have hy : ∃ t : ℝ, (t = C.k * C.side ∨ t = (C.k + 1) * C.side) ∧
        C'.k * C'.side ≤ t ∧ t ≤ (C'.k + 1) * C'.side := by
      by_cases hk1 : (C.k : ℝ) * C.side < (C'.k + 1) * C'.side
      · have hk2 : ¬ (C'.k : ℝ) * C'.side < (C.k + 1) * C.side := fun h => hnot ⟨hx, hk1, h⟩
        push Not at hk2
        exact ⟨(C.k + 1) * C.side, Or.inr rfl, by linarith, by linarith⟩
      · push Not at hk1
        exact ⟨C.k * C.side, Or.inl rfl, by linarith, by linarith⟩
    obtain ⟨t, ht, ht1, ht2⟩ := hy
    have hsub : {w : ℂ | w.im = t ∧ C'.j * C'.side ≤ w.re ∧ w.re ≤ (C'.j + 1) * C'.side} ⊆
        C.closedBox ∩ C'.closedBox := by
      rintro w ⟨w1, w2, w3⟩
      have hs : 0 < C.side := by unfold DyBox.side; positivity
      refine ⟨⟨u.1.trans w2, w3.trans u.2, ?_, ?_⟩, ⟨w2, w3, w1 ▸ ht1, w1 ▸ ht2⟩⟩ <;>
        rcases ht with ht | ht <;> rw [w1, ht] <;> nlinarith
    have := measure_mono (μ := μH[1]) hsub
    rw [l53M_hline_eq] at this
    refine le_trans (le_of_eq ?_) this
    congr 1; ring
  · -- vertical interface at abscissa `t`
    have hy : ((C.k : ℝ) * C.side < (C'.k + 1) * C'.side ∧
        (C'.k : ℝ) * C'.side < (C.k + 1) * C.side) := by
      by_contra hy
      apply hzz
      have hre : z.re = z'.re := by
        by_cases hj1 : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side
        · have hj2 : ¬ (C'.j : ℝ) * C'.side < (C.j + 1) * C.side := fun h => hx ⟨hj1, h⟩
          push Not at hj2
          linarith
        · push Not at hj1
          linarith
      have him : z.im = z'.im := by
        by_cases hk1 : (C.k : ℝ) * C.side < (C'.k + 1) * C'.side
        · have hk2 : ¬ (C'.k : ℝ) * C'.side < (C.k + 1) * C.side := fun h => hy ⟨hk1, h⟩
          push Not at hk2
          linarith
        · push Not at hk1
          linarith
      exact Complex.ext hre him
    have v := dy_nested_real (n := C'.n) (n' := C.n) hle hy.2 hy.1
    have hxt : ∃ t : ℝ, (t = C.j * C.side ∨ t = (C.j + 1) * C.side) ∧
        C'.j * C'.side ≤ t ∧ t ≤ (C'.j + 1) * C'.side := by
      by_cases hj1 : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side
      · have hj2 : ¬ (C'.j : ℝ) * C'.side < (C.j + 1) * C.side := fun h => hx ⟨hj1, h⟩
        push Not at hj2
        exact ⟨(C.j + 1) * C.side, Or.inr rfl, by linarith, by linarith⟩
      · push Not at hj1
        exact ⟨C.j * C.side, Or.inl rfl, by linarith, by linarith⟩
    obtain ⟨t, ht, ht1, ht2⟩ := hxt
    have hsub : {w : ℂ | w.re = t ∧ C'.k * C'.side ≤ w.im ∧ w.im ≤ (C'.k + 1) * C'.side} ⊆
        C.closedBox ∩ C'.closedBox := by
      rintro w ⟨w1, w2, w3⟩
      have hs : 0 < C.side := by unfold DyBox.side; positivity
      refine ⟨⟨?_, ?_, v.1.trans w2, w3.trans v.2⟩, ⟨w1 ▸ ht1, w1 ▸ ht2, w2, w3⟩⟩ <;>
        rcases ht with ht | ht <;> rw [w1, ht] <;> nlinarith
    have := measure_mono (μ := μH[1]) hsub
    rw [l53M_vline_eq] at this
    refine le_trans (le_of_eq ?_) this
    congr 1; ring

/-- **(eq-Lambda-i-not-small)**: for neighbouring cells, `μH¹(𝖢̄ ∩ 𝖢̄') ≥ min(s_𝖢, s_𝖢')`. -/
lemma l53_iface_ge_min_of_nest {C C' : DyBox} (hn1 : C.closedBox ⊆ C'.closedBox → C = C')
    (hn2 : C'.closedBox ⊆ C.closedBox → C' = C) (hN : Neighbour C C')
    (hfin : μH[1] (C.closedBox ∩ C'.closedBox) ≠ ⊤) :
    min C.side C'.side ≤ (μH[1] : Measure ℂ).real (C.closedBox ∩ C'.closedBox) := by
  rcases le_total C.n C'.n with hle | hle
  · have h := l53_iface_ge_aux hn2 hN hle
    have hs' : 0 < C'.side := by unfold DyBox.side; positivity
    refine (min_le_right _ _).trans ?_
    rw [measureReal_def, ← ENNReal.ofReal_le_iff_le_toReal hfin]; exact h
  · have hN' : Neighbour C' C := ⟨hN.1.symm, by rw [inter_comm]; exact hN.2⟩
    have h := l53_iface_ge_aux hn1 hN' hle
    refine (min_le_left _ _).trans ?_
    rw [inter_comm, measureReal_def, ← ENNReal.ofReal_le_iff_le_toReal (by rwa [inter_comm])]
    exact h

/-- `μH¹(∂𝖢̄) < ∞`. -/
lemma l53_frontier_ne_top (b : DyBox) : μH[1] (frontier b.closedBox) ≠ ⊤ := by
  have hsub : frontier b.closedBox ⊆
      ({z : ℂ | z.re = b.j * b.side ∧ b.k * b.side ≤ z.im ∧ z.im ≤ (b.k + 1) * b.side} ∪
        {z : ℂ | z.re = (b.j + 1) * b.side ∧ b.k * b.side ≤ z.im ∧ z.im ≤ (b.k + 1) * b.side}) ∪
      ({z : ℂ | z.im = b.k * b.side ∧ b.j * b.side ≤ z.re ∧ z.re ≤ (b.j + 1) * b.side} ∪
        {z : ℂ | z.im = (b.k + 1) * b.side ∧ b.j * b.side ≤ z.re ∧ z.re ≤ (b.j + 1) * b.side}) := by
    intro z hz
    obtain ⟨⟨a1, a2, a3, a4⟩, h⟩ := frontier_closedBox_sub hz
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl ⟨h, a3, a4⟩)
    · exact Or.inl (Or.inr ⟨h, a3, a4⟩)
    · exact Or.inr (Or.inl ⟨h, a1, a2⟩)
    · exact Or.inr (Or.inr ⟨h, a1, a2⟩)
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
  refine ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ?_ (measure_union_le _ _),
    ne_top_of_le_ne_top ?_ (measure_union_le _ _)⟩
  · exact ENNReal.add_ne_top.2 ⟨l53_vline_ne_top _ _ _, l53_vline_ne_top _ _ _⟩
  · exact ENNReal.add_ne_top.2 ⟨l53_hline_ne_top _ _ _, l53_hline_ne_top _ _ _⟩

/-- A closed ball around `u` or `v` of radius `≤ |u − v|/2` lies in `𝕍̃_{u,v}`. -/
lemma l53_closedBall_sub_tildeBox {u v w z : ℂ} (hw : w = u ∨ w = v) {r : ℝ}
    (hr : r ≤ ‖v - u‖ / 2) (hz : ‖z - w‖ ≤ r) : z ∈ tildeBox u v := by
  set d : ℂ := v - u with hd
  have hdn : 0 ≤ ‖d‖ := norm_nonneg _
  have key : ∀ y : ℂ, ‖y‖ ≤ r → |(y * starRingEnd ℂ d).re| ≤ ‖d‖ ^ 2 / 2 ∧
      |(y * starRingEnd ℂ d).im| ≤ ‖d‖ ^ 2 / 2 := by
    intro y hy
    have h1 : ‖y * starRingEnd ℂ d‖ ≤ ‖d‖ ^ 2 / 2 := by
      rw [norm_mul, Complex.norm_conj]
      have : ‖y‖ * ‖d‖ ≤ (‖d‖ / 2) * ‖d‖ := mul_le_mul_of_nonneg_right (hy.trans hr) hdn
      nlinarith
    exact ⟨(Complex.abs_re_le_norm _).trans h1, (Complex.abs_im_le_norm _).trans h1⟩
  have hdd : d * starRingEnd ℂ d = ((‖d‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hre : (d * starRingEnd ℂ d).re = ‖d‖ ^ 2 := by rw [hdd]; exact Complex.ofReal_re _
  have him : (d * starRingEnd ℂ d).im = 0 := by rw [hdd]; exact Complex.ofReal_im _
  have hq : ‖d‖ ^ 2 / 2 ≤ ‖d‖ ^ 2 := by nlinarith [sq_nonneg ‖d‖]
  rcases hw with rfl | rfl
  · obtain ⟨k1, k2⟩ := key (z - w) hz
    have he : (z - (w + v) / 2) * starRingEnd ℂ d =
        (z - w) * starRingEnd ℂ d - (d * starRingEnd ℂ d) / 2 := by rw [hd]; ring
    refine ⟨?_, ?_⟩ <;> rw [he, ← hd]
    · rw [Complex.sub_re, Complex.div_ofNat_re, hre, abs_le]
      rw [abs_le] at k1; constructor <;> nlinarith
    · rw [Complex.sub_im, Complex.div_ofNat_im, him, zero_div, sub_zero]; linarith
  · obtain ⟨k1, k2⟩ := key (z - w) hz
    have he : (z - (u + w) / 2) * starRingEnd ℂ d =
        (z - w) * starRingEnd ℂ d + (d * starRingEnd ℂ d) / 2 := by rw [hd]; ring
    refine ⟨?_, ?_⟩ <;> rw [he, ← hd]
    · rw [Complex.add_re, Complex.div_ofNat_re, hre, abs_le]
      rw [abs_le] at k1; constructor <;> nlinarith
    · rw [Complex.add_im, Complex.div_ofNat_im, him, zero_div, add_zero]; linarith

/-- **The tilde boxes of node 4 lie in `𝕍̃_{u,v}`**: `w ∈ {u, v}` and `x ≠ w` in the closed cell
`𝖢̄` with `12 s_𝖢 ≤ |u − v|` give `𝕍̃_{w,x} ⊆ 𝕍_{c_𝖢, 5 s_𝖢} ⊆ 𝕍̃_{u,v}`. -/
lemma l53_tildeBox_sub_uv {u v w x : ℂ} (hw : w = u ∨ w = v) {b : DyBox}
    (hwb : w ∈ b.closedBox) (hxb : x ∈ b.closedBox) (hne : w ≠ x)
    (hs : 12 * b.side ≤ ‖v - u‖) :
    tildeBox w x ⊆ sqBox b.center (5 * b.side) ∧ sqBox b.center (5 * b.side) ⊆ tildeBox u v := by
  rw [closedBox_eq_sqBox] at hwb hxb
  refine ⟨tildeBox_subset_sqBox_five hwb hxb hne, fun z hz => ?_⟩
  have hb : 0 < b.side := by unfold DyBox.side; positivity
  have h1 : ‖z - b.center‖ ≤ 5 * b.side := by
    obtain ⟨z1, z2⟩ := hz
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]; linarith
  have h2 : ‖w - b.center‖ ≤ b.side := by
    obtain ⟨z1, z2⟩ := hwb
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]; linarith
  refine l53_closedBall_sub_tildeBox hw (r := 6 * b.side) (by linarith) ?_
  calc ‖z - w‖ = ‖(z - b.center) - (w - b.center)‖ := by ring_nf
    _ ≤ ‖z - b.center‖ + ‖w - b.center‖ := norm_sub_le _ _
    _ ≤ 6 * b.side := by linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **One-point Markov** (DZZ l. 2516–2522, "similar but simpler" than l. 2495–2502): if every
`x` is far with probability `≤ p`, then `a P(ν{x : far} ≥ a) ≤ p ν(X)`. -/
theorem l53_point_markov {X : Type*} [MeasurableSpace X] (P : Measure Ω) [SFinite P]
    (ν : Measure X) [SFinite ν] {S : Set (Ω × X)} (hS : MeasurableSet S) {p : ℝ≥0∞}
    (hp : ∀ x, P {ω | (ω, x) ∈ S} ≤ p) (a : ℝ≥0∞) :
    a * P {ω | a ≤ ν {x | (ω, x) ∈ S}} ≤ p * ν univ := by
  set f : Ω × X → ℝ≥0∞ := S.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hS
  set G : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, f (ω, x) ∂ν with hG
  have hGm : Measurable G := hfm.lintegral_prod_right'
  have hG_eq : ∀ ω, G ω = ν {x | (ω, x) ∈ S} := by
    intro ω
    show ∫⁻ x, f (ω, x) ∂ν = ν (Prod.mk ω ⁻¹' S)
    rw [← lintegral_indicator_one (measurable_prodMk_left hS)]
    rfl
  have hEG : ∫⁻ ω, G ω ∂P ≤ p * ν univ := by
    rw [hG, lintegral_lintegral_swap (f := fun ω x => f (ω, x)) hfm.aemeasurable]
    have h3 : ∀ x, ∫⁻ ω, f (ω, x) ∂P ≤ p := by
      intro x
      have hsl : MeasurableSet {ω | (ω, x) ∈ S} :=
        (Measurable.prodMk measurable_id measurable_const) hS
      have : ∫⁻ ω, f (ω, x) ∂P = P {ω | (ω, x) ∈ S} := by
        rw [← lintegral_indicator_one hsl]; rfl
      rw [this]; exact hp x
    calc ∫⁻ x, ∫⁻ ω, f (ω, x) ∂P ∂ν ≤ ∫⁻ _x, p ∂ν := lintegral_mono h3
      _ = p * ν univ := lintegral_const p
  calc a * P {ω | a ≤ ν {x | (ω, x) ∈ S}} = a * P {ω | a ≤ G ω} := by simp only [hG_eq]
    _ ≤ ∫⁻ ω, G ω ∂P := mul_meas_ge_le_lintegral hGm _
    _ ≤ p * ν univ := hEG

end DZZ
end LQGMetric
