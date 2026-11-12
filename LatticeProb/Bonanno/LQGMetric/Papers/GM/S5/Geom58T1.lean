/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58T1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Junc

/-!
# GM Lemma 5.8: local attachment (T5) of a square tube along a straight end (task P2-M2M4, D83 P5)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3086–3091: `U_r^{x,y}` is the interior of the union of the squares meeting
the paths, which near `x` is the path `L̂_x`). Decision D83 (c) adds the clause (T5)
`U ∩ B_{4s}(x) ⊆ connectedComponentIn (U ∩ B_{5s}(x)) x` (`s = ε₀r` the side of the squares) to
the tube properties; it holds when the path is a straight segment ending at `x` near `x`.
Own elementary argument (GM leave this implicit):

* `exists_line_pt_sq`: if a closed grid square `S` (side `s`) meets the line `ℓ = {x − te}`
  (`|e| = 1`) and `w ∈ S`, then `S` meets `ℓ` at a parameter `t ≤ ⟨x − w, e⟩ + s` (move from `w`
  towards a point of `S ∩ ℓ` along one or both coordinate directions; the two contributions to the
  parameter have opposite signs when both are needed);
* `t5_of_segment`: if `x − te ∈ U` for `t ∈ [0, M]` and every point `w ∈ U ∩ B_{4s}(x)` lies in a
  closed square of `U` (open square `⊆ U`) meeting that segment, then (T5) holds: `w` is joined to
  `x` by `ball(w, η) ∪ [v, c] ∪ [c, x]` with `v` in the open square and `c` on the segment with
  `|c − x| < 5s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

/-- parameters between two parameters of a line meeting a closed square also meet it -/
lemma line_mem_sq_of_between {s : ℝ} {g : ℤ × ℤ} {x e : ℂ} {a b t : ℝ}
    (ha : x - (a : ℂ) * e ∈ gridSquare s g) (hb : x - (b : ℂ) * e ∈ gridSquare s g)
    (hat : a ≤ t) (htb : t ≤ b) : x - (t : ℂ) * e ∈ gridSquare s g := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.sub_im, Complex.mul_im, add_zero] at a1 a2 a3 a4 b1 b2 b3 b4
  rcases eq_or_lt_of_le (hat.trans htb) with hab | hab
  · have e1 : t = a := le_antisymm (hab ▸ htb) hat
    subst e1
    exact ⟨by simpa using a1, by simpa using a2, by simpa using a3, by simpa using a4⟩
  have hba : 0 < b - a := by linarith
  have key : ∀ (u p : ℝ), p ≤ u - a * e.re → p ≤ u - b * e.re → p ≤ u - t * e.re :=
    fun u p h1 h2 => by
      have : 0 ≤ (b - a) * (u - t * e.re - p) := by
        nlinarith [mul_nonneg (sub_nonneg.2 htb) (sub_nonneg.2 h1),
          mul_nonneg (sub_nonneg.2 hat) (sub_nonneg.2 h2)]
      nlinarith
  have key' : ∀ (u p : ℝ), u - a * e.re ≤ p → u - b * e.re ≤ p → u - t * e.re ≤ p :=
    fun u p h1 h2 => by
      have : 0 ≤ (b - a) * (p - (u - t * e.re)) := by
        nlinarith [mul_nonneg (sub_nonneg.2 htb) (sub_nonneg.2 h1),
          mul_nonneg (sub_nonneg.2 hat) (sub_nonneg.2 h2)]
      nlinarith
  have keyi : ∀ (u p : ℝ), p ≤ u - a * e.im → p ≤ u - b * e.im → p ≤ u - t * e.im :=
    fun u p h1 h2 => by
      have : 0 ≤ (b - a) * (u - t * e.im - p) := by
        nlinarith [mul_nonneg (sub_nonneg.2 htb) (sub_nonneg.2 h1),
          mul_nonneg (sub_nonneg.2 hat) (sub_nonneg.2 h2)]
      nlinarith
  have keyi' : ∀ (u p : ℝ), u - a * e.im ≤ p → u - b * e.im ≤ p → u - t * e.im ≤ p :=
    fun u p h1 h2 => by
      have : 0 ≤ (b - a) * (p - (u - t * e.im)) := by
        nlinarith [mul_nonneg (sub_nonneg.2 htb) (sub_nonneg.2 h1),
          mul_nonneg (sub_nonneg.2 hat) (sub_nonneg.2 h2)]
      nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.sub_im, Complex.mul_im, add_zero]
  · exact key _ _ a1 b1
  · exact key' _ _ a2 b2
  · exact keyi _ _ a3 b3
  · exact keyi' _ _ a4 b4

/-- **the key fact**: a closed square meeting the line `x − ℝe` at `c₀` and containing `w` meets it
at a parameter `≤ ⟨x − w, e⟩ + s` -/
lemma exists_line_pt_sq {s : ℝ} {g : ℤ × ℤ} {x e w : ℂ} (he : ‖e‖ = 1) {t₀ : ℝ}
    (h0 : x - (t₀ : ℂ) * e ∈ gridSquare s g) (hw : w ∈ gridSquare s g) :
    ∃ t : ℝ, x - (t : ℂ) * e ∈ gridSquare s g ∧
      t ≤ (x.re - w.re) * e.re + (x.im - w.im) * e.im + s := by
  have hn : e.re * e.re + e.im * e.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, he, one_pow]
  have he1 : |e.re| ≤ 1 := he ▸ Complex.abs_re_le_norm e
  have he2 : |e.im| ≤ 1 := he ▸ Complex.abs_im_le_norm e
  set c₀ : ℂ := x - (t₀ : ℂ) * e with hc₀
  set d1 : ℝ := c₀.re - w.re
  set d2 : ℝ := c₀.im - w.im
  obtain ⟨a1, a2, a3, a4⟩ := h0
  obtain ⟨b1, b2, b3, b4⟩ := hw
  have hd1 : |d1| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  have hd2 : |d2| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  -- the point `w + (λ₁ d1, λ₂ d2)` of `S`
  have hmem : ∀ l1 l2 : ℝ, l1 ∈ Icc (0 : ℝ) 1 → l2 ∈ Icc (0 : ℝ) 1 →
      (⟨w.re + l1 * d1, w.im + l2 * d2⟩ : ℂ) ∈ gridSquare s g := by
    rintro l1 l2 ⟨l10, l11⟩ ⟨l20, l21⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [d1, d2] <;>
      nlinarith [mul_nonneg l10 (sub_nonneg.2 a1), mul_nonneg (sub_nonneg.2 l11) (sub_nonneg.2 b1),
        mul_nonneg l10 (sub_nonneg.2 a2), mul_nonneg (sub_nonneg.2 l11) (sub_nonneg.2 b2),
        mul_nonneg l20 (sub_nonneg.2 a3), mul_nonneg (sub_nonneg.2 l21) (sub_nonneg.2 b3),
        mul_nonneg l20 (sub_nonneg.2 a4), mul_nonneg (sub_nonneg.2 l21) (sub_nonneg.2 b4)]
  -- a point of `S` on the line, from the vanishing of the normal coordinate
  have hline : ∀ p : ℂ, (p.im - x.im) * e.re - (p.re - x.re) * e.im = 0 →
      p = x - (((x.re - p.re) * e.re + (x.im - p.im) * e.im : ℝ) : ℂ) * e := fun p hp => by
    apply Complex.ext <;>
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.sub_im, Complex.mul_im, add_zero]
    · linear_combination (x.re - p.re) * hn - e.im * hp
    · linear_combination (x.im - p.im) * hn + e.re * hp
  have hc0n : (c₀.im - x.im) * e.re - (c₀.re - x.re) * e.im = 0 := by
    simp only [hc₀, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.sub_im, Complex.mul_im, add_zero]
    ring
  set A : ℝ := -(d1 * e.im)
  set B : ℝ := d2 * e.re
  have hgw : (w.im - x.im) * e.re - (w.re - x.re) * e.im = -(A + B) := by
    simp only [A, B, d1, d2]; linear_combination hc0n
  have habs : ∀ a b : ℝ, |a| ≤ s → |b| ≤ 1 → |a * b| ≤ s := fun a b ha hb => by
    rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]
  have hA1 := habs d1 e.re hd1 he1
  have hB2 := habs d2 e.im hd2 he2
  -- the point with parameters `l1, l2` and its line parameter
  have main : ∀ l1 l2 : ℝ, l1 ∈ Icc (0 : ℝ) 1 → l2 ∈ Icc (0 : ℝ) 1 →
      -(A + B) + l1 * A + l2 * B = 0 → -(l1 * d1 * e.re) - l2 * d2 * e.im ≤ s →
      ∃ t : ℝ, x - (t : ℂ) * e ∈ gridSquare s g ∧
        t ≤ (x.re - w.re) * e.re + (x.im - w.im) * e.im + s := by
    intro l1 l2 hl1 hl2 hg hf
    set p : ℂ := ⟨w.re + l1 * d1, w.im + l2 * d2⟩
    have hp : (p.im - x.im) * e.re - (p.re - x.re) * e.im = 0 := by
      simp only [p]; simp only [A, B] at hg; linear_combination hgw + hg
    refine ⟨(x.re - p.re) * e.re + (x.im - p.im) * e.im, ?_, ?_⟩
    · rw [← hline p hp]; exact hmem l1 l2 hl1 hl2
    · have e : (x.re - p.re) * e.re + (x.im - p.im) * e.im = (x.re - w.re) * e.re +
          (x.im - w.im) * e.im + (-(l1 * d1 * e.re) - l2 * d2 * e.im) := by simp only [p]; ring
      linarith
  rcases le_or_gt 0 (A * B) with hAB | hAB
  · refine main 1 1 ⟨zero_le_one, le_rfl⟩ ⟨zero_le_one, le_rfl⟩ (by ring) ?_
    have : (d1 * e.re) * (d2 * e.im) ≤ 0 := by
      have : A * B = -((d1 * e.re) * (d2 * e.im)) := by simp only [A, B]; ring
      linarith
    rw [abs_le] at hA1 hB2
    rcases le_total 0 (d1 * e.re) with h | h
    · nlinarith [mul_nonneg h (le_refl (0:ℝ))]
    · nlinarith
  · rcases le_total |B| |A| with hBA | hBA
    · have hA0 : A ≠ 0 := by rintro h; rw [h, zero_mul] at hAB; exact lt_irrefl _ hAB
      have hl : (A + B) / A ∈ Icc (0 : ℝ) 1 := by
        rw [add_div, div_self hA0]
        have : |B / A| ≤ 1 := by rw [abs_div]; exact div_le_one_of_le₀ hBA (abs_nonneg _)
        have hneg : B / A < 0 := by
          rw [show B / A = (A * B) / (A * A) by field_simp]
          exact div_neg_of_neg_of_pos hAB (mul_self_pos.2 hA0)
        rw [abs_le] at this; constructor <;> linarith
      refine main _ 0 hl ⟨le_rfl, zero_le_one⟩ (by field_simp; ring) ?_
      rw [abs_le] at hA1
      have := hl.1; have := hl.2
      nlinarith [mul_le_mul_of_nonneg_left hA1.1 hl.1, mul_le_mul_of_nonneg_left hA1.2 hl.1]
    · have hB0 : B ≠ 0 := by rintro h; rw [h, mul_zero] at hAB; exact lt_irrefl _ hAB
      have hl : (A + B) / B ∈ Icc (0 : ℝ) 1 := by
        rw [add_div, div_self hB0]
        have : |A / B| ≤ 1 := by rw [abs_div]; exact div_le_one_of_le₀ hBA (abs_nonneg _)
        have hneg : A / B < 0 := by
          rw [show A / B = (A * B) / (B * B) by field_simp]
          exact div_neg_of_neg_of_pos hAB (mul_self_pos.2 hB0)
        rw [abs_le] at this; constructor <;> linarith
      refine main 0 _ ⟨le_rfl, zero_le_one⟩ hl (by field_simp; ring) ?_
      have hs0 : 0 ≤ s := (abs_nonneg d1).trans hd1
      rw [abs_le] at hB2
      nlinarith [mul_le_mul_of_nonneg_left hB2.1 hl.1, mul_nonneg (sub_nonneg.2 hl.2) hs0]

/-- `⟨x − w, e⟩ ≤ |x − w|` for `|e| = 1` -/
lemma inner_le_dist {x e w : ℂ} (he : ‖e‖ = 1) :
    (x.re - w.re) * e.re + (x.im - w.im) * e.im ≤ dist w x := by
  have hn : e.re * e.re + e.im * e.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, he, one_pow]
  have hd : dist w x ^ 2 = (x.re - w.re) ^ 2 + (x.im - w.im) ^ 2 := by
    rw [dist_comm, dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]; ring
  have h0 := dist_nonneg (x := w) (y := x)
  nlinarith [sq_nonneg ((x.re - w.re) * e.im - (x.im - w.im) * e.re)]

/-- **(T5) along a straight end** -/
theorem t5_of_segment {U : Set ℂ} (hU : IsOpen U) {s M : ℝ} (hs : 0 < s) {x e : ℂ}
    (he : ‖e‖ = 1) (hL : ∀ t ∈ Icc (0 : ℝ) M, x - (t : ℂ) * e ∈ U)
    (hsq : ∀ w ∈ U, dist w x < 4 * s → ∃ g : ℤ × ℤ, openSq s g ⊆ U ∧ w ∈ gridSquare s g ∧
      ∃ t ∈ Icc (0 : ℝ) M, x - (t : ℂ) * e ∈ gridSquare s g) :
    U ∩ ball x (4 * s) ⊆ connectedComponentIn (U ∩ ball x (5 * s)) x := by
  rintro w ⟨hwU, hwx⟩
  rw [mem_ball] at hwx
  obtain ⟨g, hgU, hwS, t₀, ht₀, hc₀⟩ := hsq w hwU hwx
  obtain ⟨t', ht'S, ht'⟩ := exists_line_pt_sq he hc₀ hwS
  have hf := inner_le_dist (w := w) (x := x) he
  set t : ℝ := max 0 (min t' t₀) with ht
  have htS : x - (t : ℂ) * e ∈ gridSquare s g := by
    rcases le_total t' t₀ with h | h
    · rcases le_total 0 t' with h' | h'
      · rw [ht, min_eq_left h, max_eq_right h']; exact ht'S
      · rw [ht, min_eq_left h, max_eq_left h']
        exact line_mem_sq_of_between ht'S hc₀ h' ht₀.1
    · rw [ht, min_eq_right h, max_eq_right ht₀.1]; exact hc₀
  have ht0 : 0 ≤ t := le_max_left _ _
  have htM : t ≤ M := max_le (ht₀.1.trans ht₀.2) ((min_le_right _ _).trans ht₀.2)
  have ht5 : t < 5 * s := max_lt (by linarith) ((min_le_left _ _).trans_lt (by linarith))
  set c : ℂ := x - (t : ℂ) * e
  have hcU : c ∈ U := hL t ⟨ht0, htM⟩
  have hcx : dist c x < 5 * s := by
    rw [dist_eq_norm, show c - x = -((t : ℂ) * e) by simp [c], norm_neg, norm_mul, he, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact ht5
  -- the pieces
  obtain ⟨η, hη, hηU⟩ := Metric.isOpen_iff.1 (hU.inter isOpen_ball) w ⟨hwU, mem_ball.2 hwx⟩
  obtain ⟨v, hvo, hvw⟩ := exists_openSq_near hs hwS hη
  have hvB : v ∈ ball w η := mem_ball.2 hvw
  have hvx : dist v x < 5 * s := by
    have := (hηU hvB).2; rw [mem_ball] at this; linarith
  have hball : ball w η ⊆ U ∩ ball x (5 * s) := fun u hu =>
    ⟨(hηU hu).1, ball_subset_ball (by linarith) (hηU hu).2⟩
  have hcl : c ∈ closure (openSq s g) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨u, hu, hud⟩ := exists_openSq_near hs htS hε
    exact ⟨u, hu, by rw [dist_comm]; exact hud⟩
  have hseg1 : segment ℝ v c ⊆ U ∩ ball x (5 * s) := by
    intro u hu
    refine ⟨?_, (convex_ball x (5 * s)).segment_subset (mem_ball.2 hvx) (mem_ball.2 hcx) hu⟩
    rw [← insert_endpoints_openSegment] at hu
    rcases hu with rfl | rfl | hu
    · exact (hηU hvB).1
    · exact hcU
    · have := (convex_openSq s g).openSegment_interior_closure_subset_interior
        (by rwa [(isOpen_openSq s g).interior_eq]) hcl hu
      rw [(isOpen_openSq s g).interior_eq] at this
      exact hgU this
  have hseg2 : segment ℝ c x ⊆ U ∩ ball x (5 * s) := by
    intro u hu
    refine ⟨?_, (convex_ball x (5 * s)).segment_subset (mem_ball.2 hcx)
      (mem_ball_self (by linarith)) hu⟩
    rw [segment_eq_image] at hu
    obtain ⟨θ, hθ, rfl⟩ := hu
    show (1 - θ) • c + θ • x ∈ U
    have e1 : (1 - θ) • c + θ • x = x - (((1 - θ) * t : ℝ) : ℂ) * e := by
      simp only [c, Complex.real_smul]; push_cast; ring
    rw [e1]
    exact hL _ ⟨mul_nonneg (by linarith [hθ.2]) ht0,
      (mul_le_of_le_one_left ht0 (by linarith [hθ.1])).trans htM⟩
  have hC : IsPreconnected (ball w η ∪ segment ℝ v c ∪ segment ℝ c x) :=
    (((convex_ball w η).isPreconnected.union v hvB (left_mem_segment ℝ v c)
      (convex_segment v c).isPreconnected)).union c
      (Or.inr (right_mem_segment ℝ v c)) (left_mem_segment ℝ c x)
      (convex_segment c x).isPreconnected
  have hCsub : ball w η ∪ segment ℝ v c ∪ segment ℝ c x ⊆ U ∩ ball x (5 * s) :=
    union_subset (union_subset hball hseg1) hseg2
  exact hC.subset_connectedComponentIn (Or.inr (right_mem_segment ℝ c x)) hCsub
    (Or.inl (Or.inl (mem_ball_self hη)))

end LQGMetric.GM
