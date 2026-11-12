/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirCK at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDir
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29WN2

/-!
# DGo (3.1): Chapman–Kolmogorov for circle averages of `p^D` (task P2-HEAT1, packet R1)

Ding–Goswami, arXiv:1610.09998, (3.1)–(3.2) (DGo:491–515). For `D = (a, a+L)²`:

* `circFn a L δ v r y = (2π)⁻¹ ∫_{(0,2π]} p^D_r(v + δe^{iθ}, y) dθ` — the Dirichlet heat flow at time
  `r` of the uniform measure on `∂B_δ(v)`.
* `circPair a L δ v v' s = (2π)⁻² ∫∫ p^D_s(v' + δe^{iθ'}, v + δe^{iθ}) dθ' dθ`.
* `integral_sqDirKernel_mul_circFn` — `∫_D p^D_s(x,y) circFn_r(y) dy = circFn_{r+s}(x)`.
* `integral_circFn_mul_circFn` — `∫_D circFn_{v,r} circFn_{v',t} = circPair_{v,v'}(r+t)`.

Both from the square Chapman–Kolmogorov `HeatSq.integral_sqDirKernel_mul` (image series) and Fubini
(all kernels are bounded for fixed positive time, `DDDF.P29WN.abs_sqDirKernel_le_const`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Real Set Function
open scoped ENNReal

namespace LQGMetric
namespace DGo
namespace HeatDir

open HeatSq

variable {a L δ : ℝ} {v v' : ℂ}

/-- `(2π)⁻¹ ∫_{(0,2π]} p^D_r(v + δe^{iθ}, y) dθ` -/
def circFn (a L δ : ℝ) (v : ℂ) (r : ℝ) (y : ℂ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), sqDirKernel a L r (circleMap v δ θ) y

/-- `(2π)⁻¹ ∫_{(0,2π]} circFn_{v',s}(v + δe^{iθ}) dθ = (2π)⁻² ∫∫ p^D_s(x_θ, x'_θ')` (up to symmetry) -/
def circPair (a L δ : ℝ) (v v' : ℂ) (s : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), circFn a L δ v' s (circleMap v δ θ)

lemma measurable_sqDirKernel_comp (hL : 0 < L) {r : ℝ} (hr : 0 < r) {α : Type*}
    [MeasurableSpace α] {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => sqDirKernel a L r (f p) (g p) := by
  have := DDDF.P29WN.measurable_sqDirKernel_joint (a := a) hL (s := fun _ : α => r)
    measurable_const hf hg
  simpa [hr] using this

lemma measurable_circFn (hL : 0 < L) {r : ℝ} (hr : 0 < r) : Measurable (circFn a L δ v r) := by
  have h := (measurable_sqDirKernel_comp (a := a) hL hr
    ((continuous_circleMap v δ).measurable.comp measurable_snd)
    (measurable_fst (α := ℂ) (β := ℝ))).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioc 0 (2 * π)))
  exact h.measurable.const_mul _

lemma abs_circFn_le (hL : 0 < L) {r : ℝ} (hr : 0 < r) (y : ℂ) :
    |circFn a L δ v r y| ≤ decayConst L r ^ 2 := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  unfold circFn
  rw [abs_mul, abs_of_pos (inv_pos.2 h2π), ← Real.norm_eq_abs]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) (2 * π))
    (f := fun θ => sqDirKernel a L r (circleMap v δ θ) y) (C := decayConst L r ^ 2)
    measure_Ioc_lt_top fun θ _ => by
      rw [Real.norm_eq_abs]; exact DDDF.P29WN.abs_sqDirKernel_le_const hL hr _ _
  rw [Real.volume_real_Ioc_of_le h2π.le, sub_zero] at hb
  calc (2 * π)⁻¹ * ‖∫ θ in Ioc 0 (2 * π), sqDirKernel a L r (circleMap v δ θ) y‖
      ≤ (2 * π)⁻¹ * (decayConst L r ^ 2 * (2 * π)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

instance isFiniteMeasure_restrict_sqOpen (a L : ℝ) :
    IsFiniteMeasure ((volume : Measure ℂ).restrict (sqOpen a L)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (volume_sqOpen_ne_top a L).lt_top⟩

/-- Fubini for a bounded `θ`-family against a bounded function on `D`. -/
lemma integral_avg_mul {f : ℝ → ℂ → ℝ} (hf : Measurable (uncurry f)) {C : ℝ}
    (hfC : ∀ θ y, |f θ y| ≤ C) {g : ℂ → ℝ} (hg : Measurable g) {C' : ℝ} (hgC : ∀ y, |g y| ≤ C') :
    ∫ y in sqOpen a L, (∫ θ in Ioc 0 (2 * π), f θ y) * g y =
      ∫ θ in Ioc 0 (2 * π), ∫ y in sqOpen a L, f θ y * g y := by
  simp_rw [← integral_mul_const]
  refine integral_integral_swap ?_
  refine Integrable.of_bound ?_ (C * C') (Filter.Eventually.of_forall fun p => ?_)
  · exact ((hf.comp measurable_swap).mul (hg.comp measurable_fst)).aestronglyMeasurable
  · simp only [uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hfC _ _) (hgC _) (abs_nonneg _) ((abs_nonneg _).trans (hfC 0 0))

/-- `∫_D p^D_s(x,y) circFn_r(y) dy = circFn_{r+s}(x)` -/
theorem integral_sqDirKernel_mul_circFn (hL : 0 < L) {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (x : ℂ) :
    ∫ y in sqOpen a L, sqDirKernel a L s x y * circFn a L δ v r y =
      circFn a L δ v (r + s) x := by
  have e : ∀ y, sqDirKernel a L s x y * circFn a L δ v r y = (2 * π)⁻¹ *
      ((∫ θ in Ioc 0 (2 * π), sqDirKernel a L r (circleMap v δ θ) y) * sqDirKernel a L s y x) := by
    intro y; unfold circFn; rw [sqDirKernel_symm hs hL x y]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_avg_mul (f := fun θ y => sqDirKernel a L r (circleMap v δ θ) y)
    (C := decayConst L r ^ 2) (C' := decayConst L s ^ 2)
    (measurable_sqDirKernel_comp hL hr (f := fun p : ℝ × ℂ => circleMap v δ p.1)
      (g := fun p : ℝ × ℂ => p.2) ((continuous_circleMap v δ).measurable.comp measurable_fst)
      measurable_snd)
    (fun θ y => DDDF.P29WN.abs_sqDirKernel_le_const hL hr _ _)
    (g := fun y => sqDirKernel a L s y x)
    (measurable_sqDirKernel_comp hL hs (f := fun y : ℂ => y) (g := fun _ => x) measurable_id
      measurable_const)
    (fun y => DDDF.P29WN.abs_sqDirKernel_le_const hL hs _ _)]
  unfold circFn
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc fun θ _ => integral_sqDirKernel_mul hr hs hL _ _

/-- `∫_D circFn_{v,r} circFn_{v',t} = circPair_{v,v'}(r+t)` -/
theorem integral_circFn_mul_circFn (hL : 0 < L) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    ∫ z in sqOpen a L, circFn a L δ v r z * circFn a L δ v' t z = circPair a L δ v v' (r + t) := by
  have e : ∀ z, circFn a L δ v r z * circFn a L δ v' t z = (2 * π)⁻¹ *
      ((∫ θ in Ioc 0 (2 * π), sqDirKernel a L r (circleMap v δ θ) z) * circFn a L δ v' t z) := by
    intro z; unfold circFn; ring
  simp_rw [e]
  rw [integral_const_mul, integral_avg_mul (f := fun θ y => sqDirKernel a L r (circleMap v δ θ) y)
    (C := decayConst L r ^ 2) (C' := decayConst L t ^ 2)
    (measurable_sqDirKernel_comp hL hr (f := fun p : ℝ × ℂ => circleMap v δ p.1)
      (g := fun p : ℝ × ℂ => p.2) ((continuous_circleMap v δ).measurable.comp measurable_fst)
      measurable_snd)
    (fun θ y => DDDF.P29WN.abs_sqDirKernel_le_const hL hr _ _)
    (measurable_circFn hL ht) (fun y => abs_circFn_le hL ht y)]
  unfold circPair
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  rw [integral_sqDirKernel_mul_circFn hL hr ht, add_comm]

end HeatDir
end DGo
end LQGMetric
