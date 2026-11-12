/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.WeylCont at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLength

/-!
# `e^{ξ f}·D` is a continuous length metric

For a continuous length metric `D` on `ℂ` and a continuous `f`, GM's `e^{ξ f}·D` (GM (1.6),
`uniqueness-final.tex` l. 300–302) is again a continuous metric (`weylMetric`), with
`ofReal ((weylMetric ξ f D hD).1 (z, w)) = (e^{ξ f}·D)(z, w)` (`weylMetric_spec`). Hence, by
`LQGMetric.Metric.WeylLength`, it is a length metric (`weylMetric_isLength`) whose internal
metrics are the Weyl infima over paths in `U` (`weylMetric_internal`).

Steps (own elementary proof; GM takes this for granted when it defines `e^{ξ f}·D_h`):
* symmetry: reverse a length-parametrized path (`weylScaleOn_comm`);
* finiteness and the local bound `e^{ξ f}·D(z, z') ≤ e^b · 2D(z, z')` near `z` (Axiom I gives
  paths of length `≤ 2D(z, z')`, which stay in a Euclidean-small `D`-ball);
* Euclidean topology: a path from `z` leaving `B(z, ε)` costs `≥ e^a D(z, B(z, ε)ᶜ) > 0`
  (`le_weylCost_of_exit`);
* continuity on `ℂ × ℂ` from the triangle inequality and the local bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric

open MetricGeometry

variable {ξ : ℝ} {f : C(ℂ, ℝ)} {D : ContMetric} {U : Set ℂ}

/-- Time reversal in a set integral. -/
theorem setLIntegral_Icc_comp_sub (G : ℝ → ℝ≥0∞) (L : ℝ) :
    ∫⁻ τ in Icc 0 L, G (L - τ) = ∫⁻ τ in Icc 0 L, G τ := by
  have himg : (fun x => L - x) '' Icc 0 L = Icc 0 L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
    · intro hx; exact ⟨L - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by ring⟩
  conv_rhs => rw [← himg]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f := fun x => L - x)
    (f' := fun _ => -1)
    (fun x _ => HasDerivAt.hasDerivWithinAt (by simpa using (hasDerivAt_id x).const_sub L))
    (fun x _ y _ hxy => sub_right_injective hxy)]
  simp

theorem weylScaleOn_symm_le (z w : ℂ) : weylScaleOn ξ f D U z w ≤ weylScaleOn ξ f D U w z := by
  refine le_weylScaleOn fun L P hL _ hu h0 h1 hU => ?_
  have hu' : HasUnitSpeedOn (D.pt ∘ (P ∘ fun t => L - t)) (Icc 0 L) := by
    rw [hasUnitSpeedOn_Icc_iff] at hu ⊢
    intro s t hs hst ht
    show curveLength ((D.pt ∘ P) ∘ fun t => L - t) s t = _
    rw [curveLength_comp_of_continuousOn_antitoneOn (D.pt ∘ P) hst (by fun_prop)
      (fun x _ y _ hxy => sub_le_sub_left hxy L), hu _ _ (by linarith) (by linarith) (by linarith)]
    congr 1; ring
  refine (weylScaleOn_le hL (continuousOn_of_hasUnitSpeedOn hu') hu' (by simp [h1])
    (by simp [h0]) (fun t ht => hU _ ⟨by linarith [ht.2], by linarith [ht.1]⟩)).trans_eq ?_
  simp only [Function.comp_apply]
  exact setLIntegral_Icc_comp_sub (fun τ => ENNReal.ofReal (Real.exp (ξ * f (P τ)))) L

theorem weylScaleOn_comm (z w : ℂ) : weylScaleOn ξ f D U z w = weylScaleOn ξ f D U w z :=
  le_antisymm (weylScaleOn_symm_le z w) (weylScaleOn_symm_le w z)

theorem weylScale_comm (z w : ℂ) : weylScale ξ f D z w = weylScale ξ f D w z := by
  rw [← weylScaleOn_univ, weylScaleOn_comm, weylScaleOn_univ]

theorem weylScale_self (z : ℂ) : weylScale ξ f D z z = 0 := by
  rw [← weylScaleOn_univ]; exact weylScaleOn_self (mem_univ z)

theorem weylScale_triangle (x y z : ℂ) :
    weylScale ξ f D x z ≤ weylScale ξ f D x y + weylScale ξ f D y z := by
  simp only [← weylScaleOn_univ]; exact weylScaleOn_triangle x y z

/-- Weyl cost along a path on which `ξ f ≤ b`. -/
theorem weylScale_le_of_path {z w : ℂ} (γ : Path (D.pt z) (D.pt w)) {b : ℝ}
    (hb : ∀ t, ξ * f (weylToC D (γ t)) ≤ b) :
    weylScale ξ f D z w ≤ ENNReal.ofReal (Real.exp b) * pathLength γ := by
  calc weylScale ξ f D z w ≤ weylScaleOn ξ f D {x | ξ * f x ≤ b} z w := weylScale_le_weylScaleOn
    _ ≤ ENNReal.ofReal (Real.exp b) * D.internal {x | ξ * f x ≤ b} z w :=
        weylScaleOn_le_of_le fun x hx => hx
    _ ≤ ENNReal.ofReal (Real.exp b) * pathLength γ := by
        gcongr
        exact internalEDist_le_pathLength γ fun t => ⟨weylToC D (γ t), hb t, rfl⟩

theorem edist_le_pathLength_apply' {X : Type*} [PseudoEMetricSpace X] {x y : X} (γ : Path x y)
    (t : unitInterval) : edist x (γ t) ≤ pathLength γ := by
  have h1 := edist_le_curveLength γ.extend t.2.1
  rw [Path.extend_zero, Path.extend_extends'] at h1
  exact h1.trans (curveLength_mono _ le_rfl t.2.2)

theorem weylScale_ne_top (hD : D.IsLength) (z w : ℂ) : weylScale ξ f D z w ≠ ∞ := by
  obtain ⟨γ, hγ⟩ := hD (D.pt z) (D.pt w) 1 one_pos
  have hK : IsCompact (range fun t => weylToC D (γ t)) :=
    isCompact_range ((continuous_weylToC D).comp γ.continuous)
  obtain ⟨b, hb⟩ := (hK.image (by fun_prop : Continuous fun x => ξ * f x)).bddAbove
  refine ne_top_of_le_ne_top ?_ (weylScale_le_of_path γ (b := b) fun t => hb ⟨_, ⟨t, rfl⟩, rfl⟩)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨edist_ne_top _ _, ENNReal.ofReal_ne_top⟩) hγ)

/-- Local Lipschitz-type bound near `z`. -/
theorem exists_weylScale_le_near (hD : D.IsLength) (z : ℂ) :
    ∃ r > 0, ∃ b : ℝ, ∀ z', D.1 (z, z') < r →
      weylScale ξ f D z z' ≤ ENNReal.ofReal (Real.exp b) * ENNReal.ofReal (2 * D.1 (z, z')) := by
  obtain ⟨δ, hδ, hsmall⟩ := D.2.euclidean_of_small z 1 one_pos
  obtain ⟨b, hb⟩ := ((isCompact_closedBall z 1).image
    (by fun_prop : Continuous fun x => ξ * f x)).bddAbove
  refine ⟨δ / 2, half_pos hδ, b, fun z' hz' => ?_⟩
  have hnn : 0 ≤ D.1 (z, z') := dist_nonneg (x := D.pt z) (y := D.pt z')
  rcases hnn.eq_or_lt with h0 | hpos
  · have : z = z' := D.2.eq_of_eq_zero z z' h0.symm
    subst this
    rw [weylScale_self]; exact bot_le
  obtain ⟨γ, hγ⟩ := hD (D.pt z) (D.pt z') (D.1 (z, z')) hpos
  have hlen : pathLength γ ≤ ENNReal.ofReal (2 * D.1 (z, z')) := by
    refine hγ.trans (le_of_eq ?_)
    rw [edist_dist, show dist (D.pt z) (D.pt z') = D.1 (z, z') from rfl,
      ← ENNReal.ofReal_add hnn hnn, two_mul]
  have hrange : ∀ t, ξ * f (weylToC D (γ t)) ≤ b := by
    intro t
    refine hb ⟨_, ?_, rfl⟩
    have h1 := (edist_le_pathLength_apply' γ t).trans hlen
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
    have h2 : D.1 (z, weylToC D (γ t)) < δ := lt_of_le_of_lt h1 (by linarith)
    have h3 := hsmall _ h2
    rw [mem_closedBall, Complex.dist_eq, norm_sub_rev]
    exact h3.le
  exact (weylScale_le_of_path γ hrange).trans (by gcongr)

theorem isClosed_pt_image_compl (D : ContMetric) {V : Set ℂ} (hV : IsOpen V) :
    IsClosed (D.pt '' Vᶜ) := by
  have : D.pt '' Vᶜ = weylToC D ⁻¹' Vᶜ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [this]; exact hV.isClosed_compl.preimage (continuous_weylToC D)

/-- Small Weyl distance ⇒ small Euclidean distance. -/
theorem weylScale_euclidean_of_small (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ y, weylScale ξ f D z y < δ → ‖z - y‖ < ε := by
  obtain ⟨a, ha⟩ := ((isCompact_closedBall z ε).image
    (by fun_prop : Continuous fun x => ξ * f x)).bddBelow
  have ha' : ∀ x ∈ ball z ε, a ≤ ξ * f x := fun x hx => ha ⟨x, ball_subset_closedBall hx, rfl⟩
  have hpos : 0 < infEDist (D.pt z) (D.pt '' (ball z ε)ᶜ) := by
    refine infEDist_pos_iff_notMem_closure.2 ?_
    rw [(isClosed_pt_image_compl D isOpen_ball).closure_eq]
    rintro ⟨y, hy, hyz⟩
    have : y = z := hyz
    exact hy (this ▸ mem_ball_self hε)
  refine ⟨ENNReal.ofReal (Real.exp a) * infEDist (D.pt z) (D.pt '' (ball z ε)ᶜ),
    ENNReal.mul_pos (by simpa using Real.exp_pos a) hpos.ne', fun y hy => ?_⟩
  by_contra hyε
  have hyV : y ∉ ball z ε := by
    rw [mem_ball, Complex.dist_eq, norm_sub_rev]; exact hyε
  refine absurd hy (not_lt.2 ?_)
  rw [← weylScaleOn_univ]
  refine le_weylScaleOn fun L P hL hc hu h0 h1 _ => ?_
  have := le_weylCost_of_exit hL hc hu isOpen_ball ha' ⟨L, ⟨hL, le_rfl⟩, h1 ▸ hyV⟩
  rwa [h0] at this

end LQGMetric
