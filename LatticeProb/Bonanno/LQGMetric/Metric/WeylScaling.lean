/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.WeylScaling at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylBasic
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Weyl scaling commutes with scaling the metric and with affine changes of coordinates

Blueprint GM.S1.6 (GM, arXiv:1905.00383v3, `uniqueness-final.tex`, used at l. 458–465 (1.15),
l. 491–505 and 537–580 (Lemma 1.10, `D^{(b)}_h = D_{h(·/b)}(b·,b·)`, Axiom III for `D^{(b)}`),
l. 588 (`C D`)):

* `weylScaleOn_smul`: `e^{ξ f}·(C D) = C (e^{ξ f}·D)` for `C > 0` (also with paths in `U`);
* `weylScaleOn_affine`: with `φ(x) = r x + a` (`r ≠ 0` real), `D^φ := D(φ·, φ·)`,
  `(e^{ξ f∘φ}·D^φ)(u, v) = (e^{ξ f}·D)(φ u, φ v)`, i.e. GM's
  `(e^{ξ f}·D)(b·, b·) = e^{ξ f(b·)}·D(b·, b·)` (with paths in `φ⁻¹ V` resp. `V`).

The metric constructions `ContMetric.smul` and `ContMetric.affine` are the paper's `C D` and
`D(r· + a, r· + a)`. Proofs: a path parametrized by `D`-length on `[0, L]` becomes, after the time
change `t ↦ t / C`, a path parametrized by `C D`-length on `[0, C L]` (lengths scale by `C`,
BBI §2.3 / direct from the partition definition), and the integral transforms by the
one-dimensional change of variables (mathlib `lintegral_image_eq_lintegral_abs_deriv_mul`).
Own elementary proof (GM uses these identities without proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric

namespace MetricGeometry

variable {E E' : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace E']

/-- Variation scales with the metric: `edist (F s) (F t) = c · edist (G s) (G t)` ⇒
`Var(F; S) = c · Var(G; S)`. -/
theorem eVariationOn_eq_mul_of_edist {F : ℝ → E} {G : ℝ → E'} {c : ℝ≥0∞}
    (h : ∀ s t, edist (F s) (F t) = c * edist (G s) (G t)) (S : Set ℝ) :
    eVariationOn F S = c * eVariationOn G S := by
  unfold eVariationOn
  rw [ENNReal.mul_iSup]
  congr 1
  ext p
  rw [Finset.mul_sum]
  simp only [h]

theorem hasUnitSpeedOn_Icc_iff {F : ℝ → E} {L : ℝ} :
    HasUnitSpeedOn F (Icc 0 L) ↔
      ∀ s t, 0 ≤ s → s ≤ t → t ≤ L → curveLength F s t = ENNReal.ofReal (t - s) := by
  rw [HasUnitSpeedOn, hasConstantSpeedOnWith_iff_ordered]
  constructor
  · intro h s t hs hst ht
    have := h ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩ hst
    rwa [inter_eq_right.2 (Icc_subset_Icc hs ht), NNReal.coe_one, one_mul] at this
  · intro h x hx y hy hxy
    rw [inter_eq_right.2 (Icc_subset_Icc hx.1 hy.2), NNReal.coe_one, one_mul]
    exact h x y hx.1 hxy hy.2

/-- A unit-speed curve is `1`-Lipschitz. -/
theorem lipschitzOnWith_of_hasUnitSpeedOn {F : ℝ → E} {L : ℝ}
    (hu : HasUnitSpeedOn F (Icc 0 L)) : LipschitzOnWith 1 F (Icc 0 L) := by
  have key : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t → edist (F s) (F t) ≤ 1 * edist s t := by
    intro s hs t ht hst
    rw [one_mul, edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst)]
    exact (edist_le_curveLength F hst).trans_eq (curveLength_of_hasUnitSpeedOn hu hs ht)
  intro s hs t ht
  rcases le_total s t with hst | hst
  · exact_mod_cast key s hs t ht hst
  · rw [edist_comm, edist_comm s]; exact_mod_cast key t ht s hs hst

theorem continuousOn_of_hasUnitSpeedOn {F : ℝ → E} {L : ℝ}
    (hu : HasUnitSpeedOn F (Icc 0 L)) : ContinuousOn F (Icc 0 L) :=
  (lipschitzOnWith_of_hasUnitSpeedOn hu).continuousOn

/-- Time change: if `edist ∘ F = k · edist ∘ G` and `G` has unit speed on `[0, L]`, then
`t ↦ F (t / k)` has unit speed on `[0, k L]`. -/
theorem hasUnitSpeedOn_rescale {F : ℝ → E} {G : ℝ → E'} {k L : ℝ} (hk : 0 < k)
    (hFG : ∀ s t, edist (F s) (F t) = ENNReal.ofReal k * edist (G s) (G t))
    (hG : HasUnitSpeedOn G (Icc 0 L)) :
    HasUnitSpeedOn (F ∘ fun t => t / k) (Icc 0 (k * L)) := by
  rw [hasUnitSpeedOn_Icc_iff] at hG ⊢
  intro s t hs hst ht
  have hmono : MonotoneOn (fun t : ℝ => t / k) (Icc s t) :=
    fun x _ y _ hxy => div_le_div_of_nonneg_right hxy hk.le
  rw [curveLength_comp_of_continuousOn_monotoneOn F hst (by fun_prop) hmono]
  unfold curveLength
  rw [eVariationOn_eq_mul_of_edist hFG]
  have h1 := hG (s / k) (t / k) (div_nonneg hs hk.le) (div_le_div_of_nonneg_right hst hk.le)
    ((div_le_iff₀ hk).2 (by linarith))
  unfold curveLength at h1
  rw [h1, ← ENNReal.ofReal_mul hk.le]
  congr 1
  field_simp

end MetricGeometry

open MetricGeometry

/-! ### `C D` and `D(r· + a, r· + a)` as continuous metrics -/

/-- `C D` for `C > 0` -/
def ContMetric.smul (C : ℝ) (hC : 0 < C) (D : ContMetric) : ContMetric :=
  ⟨C • D.1,
    { self_eq_zero := fun x => by simp [D.2.self_eq_zero x]
      eq_of_eq_zero := fun x y h => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_eq_zero, hC.ne', false_or] at h
        exact D.2.eq_of_eq_zero x y h
      symm := fun x y => by simp [D.2.symm x y]
      triangle := fun x y z => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_add]
        exact mul_le_mul_of_nonneg_left (D.2.triangle x y z) hC.le
      euclidean_of_small := fun x ε hε => by
        obtain ⟨δ, hδ, h⟩ := D.2.euclidean_of_small x ε hε
        refine ⟨C * δ, mul_pos hC hδ, fun y hy => h y ?_⟩
        simp only [ContinuousMap.smul_apply, smul_eq_mul] at hy
        exact lt_of_mul_lt_mul_left hy hC.le }⟩

theorem ContMetric.smul_apply (C : ℝ) (hC : 0 < C) (D : ContMetric) (p : ℂ × ℂ) :
    (D.smul C hC).1 p = C * D.1 p := rfl

/-- the affine map `x ↦ r x + a` -/
def affinePt (r : ℝ) (a : ℂ) : C(ℂ, ℂ) := ⟨fun x => (r : ℂ) * x + a, by fun_prop⟩

theorem affinePt_apply (r : ℝ) (a x : ℂ) : affinePt r a x = (r : ℂ) * x + a := rfl

/-- `D(r· + a, r· + a)` for real `r ≠ 0` -/
def ContMetric.affine (r : ℝ) (hr : r ≠ 0) (a : ℂ) (D : ContMetric) : ContMetric :=
  ⟨D.1.comp ⟨fun p => (affinePt r a p.1, affinePt r a p.2), by fun_prop⟩,
    { self_eq_zero := fun x => D.2.self_eq_zero _
      eq_of_eq_zero := fun x y h => by
        have h' := D.2.eq_of_eq_zero _ _ h
        simp only [affinePt_apply, add_left_inj] at h'
        exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr) h'
      symm := fun x y => D.2.symm _ _
      triangle := fun x y z => D.2.triangle _ _ _
      euclidean_of_small := fun x ε hε => by
        obtain ⟨δ, hδ, h⟩ := D.2.euclidean_of_small (affinePt r a x) (ε * |r|)
          (mul_pos hε (abs_pos.2 hr))
        refine ⟨δ, hδ, fun y hy => ?_⟩
        have h' := h (affinePt r a y) hy
        rw [affinePt_apply, affinePt_apply, add_sub_add_right_eq_sub, ← mul_sub, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, mul_comm] at h'
        exact lt_of_mul_lt_mul_right h' (abs_nonneg r) }⟩

theorem ContMetric.affine_apply (r : ℝ) (hr : r ≠ 0) (a : ℂ) (D : ContMetric) (p : ℂ × ℂ) :
    (D.affine r hr a).1 p = D.1 (affinePt r a p.1, affinePt r a p.2) := rfl

/-! ### Scaling the metric by a constant -/

variable {ξ : ℝ} {f : C(ℂ, ℝ)} {U : Set ℂ} {z w : ℂ}

/-- If `D₂ = k D₁` (as distances) then `(e^{ξ f}·D₂)_U ≤ k (e^{ξ f}·D₁)_U`. -/
theorem weylScaleOn_le_mul_of_edist {D₁ D₂ : ContMetric} {k : ℝ} (hk : 0 < k)
    (h : ∀ x y, edist (D₂.pt x) (D₂.pt y) = ENNReal.ofReal k * edist (D₁.pt x) (D₁.pt y)) :
    weylScaleOn ξ f D₂ U z w ≤ ENNReal.ofReal k * weylScaleOn ξ f D₁ U z w := by
  have hk0 : ENNReal.ofReal k ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hk
  rw [mul_comm, ← ENNReal.div_le_iff hk0 ENNReal.ofReal_ne_top]
  refine le_weylScaleOn fun L P hL _ hu h0 h1 hU => ?_
  rw [ENNReal.div_le_iff hk0 ENNReal.ofReal_ne_top, mul_comm]
  have huQ : HasUnitSpeedOn (D₂.pt ∘ (P ∘ fun t => t / k)) (Icc 0 (k * L)) :=
    hasUnitSpeedOn_rescale (F := D₂.pt ∘ P) (G := D₁.pt ∘ P) hk (fun s t => h _ _) hu
  refine (weylScaleOn_le (mul_nonneg hk.le hL) (continuousOn_of_hasUnitSpeedOn huQ) huQ
    (by simp [h0]) (by simp [hk.ne', h1]) (fun t ht => hU _
      ⟨div_nonneg ht.1 hk.le, (div_le_iff₀ hk).2 (by linarith [ht.2])⟩)).trans_eq ?_
  have himg : (fun x => k * x) '' Icc 0 L = Icc 0 (k * L) := by
    rw [image_mul_left_Icc hk.le hL, mul_zero]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f' := fun _ => k)
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul k).hasDerivWithinAt)
    (fun x _ y _ hxy => mul_left_cancel₀ hk.ne' hxy)]
  rw [setLIntegral_congr_fun measurableSet_Icc
    (g := fun x => ENNReal.ofReal |k| * ENNReal.ofReal (Real.exp (ξ * f (P x))))
    (fun x _ => by simp [hk.ne'])]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_of_pos hk]

theorem ContMetric.edist_smul (C : ℝ) (hC : 0 < C) (D : ContMetric) (x y : ℂ) :
    edist ((D.smul C hC).pt x) ((D.smul C hC).pt y) =
      ENNReal.ofReal C * edist (D.pt x) (D.pt y) := by
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul hC.le]
  rfl

/-- **GM.S1.6**: `e^{ξ f}·(C D) = C (e^{ξ f}·D)` for `C > 0` (paths in `U`). -/
theorem weylScaleOn_smul (C : ℝ) (hC : 0 < C) (D : ContMetric) :
    weylScaleOn ξ f (D.smul C hC) U z w = ENNReal.ofReal C * weylScaleOn ξ f D U z w := by
  refine le_antisymm (weylScaleOn_le_mul_of_edist hC (D.edist_smul C hC)) ?_
  have h2 : weylScaleOn ξ f D U z w ≤
      ENNReal.ofReal C⁻¹ * weylScaleOn ξ f (D.smul C hC) U z w := by
    refine weylScaleOn_le_mul_of_edist (inv_pos.2 hC) fun x y => ?_
    rw [D.edist_smul C hC, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hC).le,
      inv_mul_cancel₀ hC.ne', ENNReal.ofReal_one, one_mul]
  calc ENNReal.ofReal C * weylScaleOn ξ f D U z w
      ≤ ENNReal.ofReal C * (ENNReal.ofReal C⁻¹ * weylScaleOn ξ f (D.smul C hC) U z w) := by
        gcongr
    _ = weylScaleOn ξ f (D.smul C hC) U z w := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC.le, mul_inv_cancel₀ hC.ne', ENNReal.ofReal_one,
          one_mul]

theorem weylScale_smul (C : ℝ) (hC : 0 < C) (D : ContMetric) :
    weylScale ξ f (D.smul C hC) z w = ENNReal.ofReal C * weylScale ξ f D z w := by
  rw [← weylScaleOn_univ, ← weylScaleOn_univ, weylScaleOn_smul]

/-! ### Affine change of coordinates -/

/-- the inverse affine map `y ↦ (y − a) / r` -/
theorem affinePt_inv {r : ℝ} (hr : r ≠ 0) (a y : ℂ) : affinePt r a ((y - a) / r) = y := by
  rw [affinePt_apply, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hr), sub_add_cancel]

theorem affinePt_inv' {r : ℝ} (hr : r ≠ 0) (a x : ℂ) : (affinePt r a x - a) / r = x := by
  rw [affinePt_apply, add_sub_cancel_right, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.2 hr)]

theorem ContMetric.edist_affine {r : ℝ} (hr : r ≠ 0) (a : ℂ) (D : ContMetric) (x y : ℂ) :
    edist ((D.affine r hr a).pt x) ((D.affine r hr a).pt y) =
      edist (D.pt (affinePt r a x)) (D.pt (affinePt r a y)) := by
  rw [edist_dist, edist_dist]
  rfl

theorem hasUnitSpeedOn_congr_edist {F : ℝ → ℂ} {D₁ D₂ : ContMetric} {G : ℝ → ℂ} {L : ℝ}
    (h : ∀ s t, edist (D₂.pt (F s)) (D₂.pt (F t)) = edist (D₁.pt (G s)) (D₁.pt (G t)))
    (hu : HasUnitSpeedOn (D₁.pt ∘ G) (Icc 0 L)) : HasUnitSpeedOn (D₂.pt ∘ F) (Icc 0 L) :=
  fun x hx y hy => (eVariationOn_eq_mul_of_edist (F := D₂.pt ∘ F) (G := D₁.pt ∘ G) (c := 1)
    (fun s t => by rw [one_mul]; exact h s t) _).trans (by rw [one_mul]; exact hu hx hy)

/-- **GM.S1.6** (coordinate change): with `φ x = r x + a`,
`(e^{ξ f∘φ}·D(φ·,φ·))_{φ⁻¹V}(u, v) = (e^{ξ f}·D)_V(φ u, φ v)`; GM's
`(e^{ξf}·D)(b·,b·) = e^{ξ f(b·)}·D(b·,b·)`. -/
theorem weylScaleOn_affine {r : ℝ} (hr : r ≠ 0) (a : ℂ) (D : ContMetric) (V : Set ℂ)
    (u v : ℂ) :
    weylScaleOn ξ (f.comp (affinePt r a)) (D.affine r hr a) (affinePt r a ⁻¹' V) u v =
      weylScaleOn ξ f D V (affinePt r a u) (affinePt r a v) := by
  apply le_antisymm
  · refine le_weylScaleOn fun L Q hL _ hu h0 h1 hU => ?_
    have huP : HasUnitSpeedOn ((D.affine r hr a).pt ∘ fun t => (Q t - a) / r) (Icc 0 L) :=
      hasUnitSpeedOn_congr_edist (fun s t => by
        rw [ContMetric.edist_affine, affinePt_inv hr, affinePt_inv hr]) hu
    refine (weylScaleOn_le hL (continuousOn_of_hasUnitSpeedOn huP) huP
      (by rw [h0, affinePt_inv' hr]) (by rw [h1, affinePt_inv' hr])
      (fun t ht => by simpa [mem_preimage, affinePt_inv hr] using hU t ht)).trans_eq ?_
    simp only [ContinuousMap.comp_apply, affinePt_inv hr]
  · refine le_weylScaleOn fun L P hL _ hu h0 h1 hU => ?_
    have huQ : HasUnitSpeedOn (D.pt ∘ fun t => affinePt r a (P t)) (Icc 0 L) :=
      hasUnitSpeedOn_congr_edist (fun s t => (ContMetric.edist_affine hr a D _ _).symm) hu
    exact weylScaleOn_le hL (continuousOn_of_hasUnitSpeedOn huQ) huQ (by rw [h0]) (by rw [h1])
      (fun t ht => hU t ht)

theorem weylScale_affine {r : ℝ} (hr : r ≠ 0) (a : ℂ) (D : ContMetric) (u v : ℂ) :
    weylScale ξ (f.comp (affinePt r a)) (D.affine r hr a) u v =
      weylScale ξ f D (affinePt r a u) (affinePt r a v) := by
  rw [← weylScaleOn_univ, ← weylScaleOn_univ, ← weylScaleOn_affine hr a D univ u v,
    preimage_univ]

end LQGMetric
