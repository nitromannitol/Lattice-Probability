/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.WeylMetric at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.WeylCont

/-!
# The continuous metric `e^{ξ f}·D`

For a continuous length metric `D` and a continuous `f`, `weylMetric ξ f D hD : ContMetric` is GM's
`e^{ξ f}·D` (GM (1.6), `uniqueness-final.tex` l. 300–302) as a continuous metric:
`weylMetric_spec` identifies it with `weylScale ξ f D`, `weylMetric_isLength` shows it is a length
metric, and `weylMetric_internal` computes its internal metrics on open sets. Own elementary
proof (see `LQGMetric.Metric.WeylCont`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric

variable {ξ : ℝ} {f : C(ℂ, ℝ)} {D : ContMetric}

/-- `e^{ξ f}·D` as a real function on `ℂ × ℂ` -/
def weylDist (ξ : ℝ) (f : C(ℂ, ℝ)) (D : ContMetric) (p : ℂ × ℂ) : ℝ :=
  (weylScale ξ f D p.1 p.2).toReal

theorem ofReal_weylDist (hD : D.IsLength) (z w : ℂ) :
    ENNReal.ofReal (weylDist ξ f D (z, w)) = weylScale ξ f D z w :=
  ENNReal.ofReal_toReal (weylScale_ne_top hD z w)

theorem weylDist_comm (z w : ℂ) : weylDist ξ f D (z, w) = weylDist ξ f D (w, z) := by
  simp only [weylDist, weylScale_comm z w]

theorem weylDist_triangle (hD : D.IsLength) (x y z : ℂ) :
    weylDist ξ f D (x, z) ≤ weylDist ξ f D (x, y) + weylDist ξ f D (y, z) :=
  ENNReal.toReal_le_add (weylScale_triangle x y z) (weylScale_ne_top hD x y)
    (weylScale_ne_top hD y z)

theorem weylDist_le_near (hD : D.IsLength) (z : ℂ) :
    ∃ r > 0, ∃ b : ℝ, ∀ z', D.1 (z, z') < r →
      weylDist ξ f D (z, z') ≤ Real.exp b * (2 * D.1 (z, z')) := by
  obtain ⟨r, hr, b, h⟩ := exists_weylScale_le_near (ξ := ξ) (f := f) hD z
  refine ⟨r, hr, b, fun z' hz' => ?_⟩
  have hnn : 0 ≤ D.1 (z, z') := dist_nonneg (x := D.pt z) (y := D.pt z')
  have h' := h z' hz'
  rw [← ENNReal.ofReal_mul (Real.exp_pos b).le] at h'
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (Real.exp_pos b).le (mul_nonneg zero_le_two hnn)) h'

theorem continuous_weylDist (hD : D.IsLength) : Continuous (weylDist ξ f D) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨z, w⟩
  obtain ⟨r₁, hr₁, b₁, h₁⟩ := weylDist_le_near (ξ := ξ) (f := f) hD z
  obtain ⟨r₂, hr₂, b₂, h₂⟩ := weylDist_le_near (ξ := ξ) (f := f) hD w
  have c1 : Continuous fun q : ℂ × ℂ => D.1 (z, q.1) :=
    D.1.continuous.comp (continuous_const.prodMk continuous_fst)
  have c2 : Continuous fun q : ℂ × ℂ => D.1 (w, q.2) :=
    D.1.continuous.comp (continuous_const.prodMk continuous_snd)
  set g : ℂ × ℂ → ℝ := fun q => Real.exp b₁ * (2 * D.1 (z, q.1)) +
    Real.exp b₂ * (2 * D.1 (w, q.2))
  have hg : Continuous g := by
    simp only [g]
    exact ((continuous_const.mul (continuous_const.mul c1))).add
      (continuous_const.mul (continuous_const.mul c2))
  have hg0 : g (z, w) = 0 := by simp [g, D.2.self_eq_zero]
  have hev1 : ∀ᶠ q in 𝓝 (z, w), D.1 (z, q.1) < r₁ :=
    c1.continuousAt.eventually_lt continuousAt_const (by simpa [D.2.self_eq_zero] using hr₁)
  have hev2 : ∀ᶠ q in 𝓝 (z, w), D.1 (w, q.2) < r₂ :=
    c2.continuousAt.eventually_lt continuousAt_const (by simpa [D.2.self_eq_zero] using hr₂)
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    ((hev1.and hev2).mono fun q hq => ?_) (hg0 ▸ hg.tendsto (z, w)))
  obtain ⟨q₁, q₂⟩ := q
  have e1 := h₁ q₁ hq.1
  have e2 := h₂ q₂ hq.2
  have t1 := weylDist_triangle (ξ := ξ) (f := f) hD q₁ z q₂
  have t2 := weylDist_triangle (ξ := ξ) (f := f) hD z w q₂
  have t3 := weylDist_triangle (ξ := ξ) (f := f) hD z q₁ w
  have t4 := weylDist_triangle (ξ := ξ) (f := f) hD q₁ q₂ w
  rw [weylDist_comm q₁ z] at t1
  rw [weylDist_comm q₂ w] at t4
  rw [Real.dist_eq, abs_sub_le_iff]
  simp only [g]
  constructor <;> linarith

/-- **`e^{ξ f}·D` as a continuous metric** (GM (1.6)), for a continuous length metric `D`. -/
def weylMetric (ξ : ℝ) (f : C(ℂ, ℝ)) (D : ContMetric) (hD : D.IsLength) : ContMetric :=
  ⟨⟨weylDist ξ f D, continuous_weylDist hD⟩,
    { self_eq_zero := fun x => by
        show (weylScale ξ f D x x).toReal = 0
        rw [weylScale_self]; rfl
      eq_of_eq_zero := fun x y h => by
        have h' : weylScale ξ f D x y = 0 := by
          rw [← ofReal_weylDist hD]
          exact ENNReal.ofReal_eq_zero.2 (le_of_eq h)
        by_contra hxy
        obtain ⟨δ, hδ, hsm⟩ := weylScale_euclidean_of_small (ξ := ξ) (f := f) (D := D) x
          ‖x - y‖ (norm_pos_iff.2 (sub_ne_zero.2 hxy))
        exact lt_irrefl _ (hsm y (h' ▸ hδ))
      symm := fun x y => weylDist_comm x y
      triangle := fun x y z => weylDist_triangle hD x y z
      euclidean_of_small := fun x ε hε => by
        obtain ⟨δ, hδ, hsm⟩ := weylScale_euclidean_of_small (ξ := ξ) (f := f) (D := D) x ε hε
        by_cases htop : δ = ⊤
        · exact ⟨1, one_pos, fun y _ =>
            hsm y (htop ▸ lt_top_iff_ne_top.2 (weylScale_ne_top hD x y))⟩
        · refine ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' htop, fun y hy => hsm y ?_⟩
          exact (ENNReal.toReal_lt_toReal (weylScale_ne_top hD x y) htop).1 hy }⟩

theorem weylMetric_spec (hD : D.IsLength) (z w : ℂ) :
    ENNReal.ofReal ((weylMetric ξ f D hD).1 (z, w)) = weylScale ξ f D z w :=
  ofReal_weylDist hD z w

/-- `e^{ξ f}·D` is a length metric. -/
theorem weylMetric_isLength (hD : D.IsLength) : (weylMetric ξ f D hD).IsLength :=
  isLength_of_eq_weylScale _ (weylMetric_spec hD)

/-- Internal metrics of `e^{ξ f}·D` on open sets. -/
theorem weylMetric_internal (hD : D.IsLength) {U : Set ℂ} (hU : IsOpen U) (z w : ℂ) :
    (weylMetric ξ f D hD).internal U z w = weylScaleOn ξ f D U z w :=
  (weylScaleOn_eq_internal _ (weylMetric_spec hD) hU z w).symm

end LQGMetric
