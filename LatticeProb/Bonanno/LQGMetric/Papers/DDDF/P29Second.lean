/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P29Second at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29Kernel
import LatticeProb.Bonanno.LQGMetric.Field.ExistKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Prop 29, second term: the noise outside `D` (task P2-DDDFP29, WP-110)

DDDF (arXiv:1904.08021), `tightness.tex:1576–1588`: for `x, x' ∈ U`, `d = d(U, D^c)`,
`φ²_t(x) = √π ∫_0^{1−t} ∫_{D^c} p_{(t+s)/2}(x − y) W(dy, ds)` satisfies
`E(φ²_t(x) − φ²_t(x'))² ≤ C|x − x'|` and `E φ²_t(x)² ≤ C`, uniformly in `t`.

With `r = (t + s)/2` the variances are `2π ∫_{t/2}^{1/2} F(r) dr` with
`F(r) = ∫_{D^c} (p_r(x,y) − p_r(x',y))² dy` (resp. `p_r(x,y)²`), so it suffices to bound
`∫_0^∞ F(r) dr`, which we do here in `ℝ≥0∞`. DDDF's proof: split the time integral; for large
`r` use `∫_{ℝ²} (p_r(x−·) − p_r(x'−·))² = 2(p_{2r}(0) − p_{2r}(x−x')) ≤ |x−x'|²/(8πr²)`
(`GFFExist.integral_sq_heatKernel_sub_le`, via `1 − e^{−z} ≤ z`), for small `r` use
`|y − x|, |y − x'| ≥ d` on `D^c`. DDDF split at `r = √|x−x'|`; we split at `r = |x − x'|`,
which gives the stated `O(|x − x'|)` directly (the `√` split only gives `O(√|x−x'|)` for the
small-time part).
-/

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal

namespace LQGMetric
namespace HeatSq

lemma heatKernel_d_le_const {r d : ℝ} (hr : 0 < r) (hd : 0 < d) :
    heatKernel r (d : ℂ) 0 ≤ 2 * (π * d ^ 2)⁻¹ := by
  refine (heatKernel_d_le_exp hr hd).trans ?_
  have : Real.exp (-(d ^ 2 / 4) / r) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg d]) hr.le)
  have h0 : 0 ≤ 2 * (π * d ^ 2)⁻¹ := by positivity
  nlinarith

lemma integrable_sq_heatKernel_sub {r : ℝ} (hr : 0 < r) (x x' : ℂ) :
    Integrable (fun y => (heatKernel r x y - heatKernel r x' y) ^ 2) := by
  have e : (fun y => (heatKernel r x y - heatKernel r x' y) ^ 2) = fun y =>
      heatKernel r x y * heatKernel r x y - 2 * (heatKernel r x y * heatKernel r x' y) +
        heatKernel r x' y * heatKernel r x' y := by funext y; ring
  rw [e]
  exact ((WhiteNoise.integrable_heatKernel_mul_heatKernel r hr x x).sub
    ((WhiteNoise.integrable_heatKernel_mul_heatKernel r hr x x').const_mul 2)).add
    (WhiteNoise.integrable_heatKernel_mul_heatKernel r hr x' x')

/-- `∫ (p_r(x,y) − p_r(x',y))² dy ≤ |x − x'|²/(8πr²)`. -/
lemma integral_sq_heatKernel_sub_le' {r : ℝ} (hr : 0 < r) (x x' : ℂ) :
    ∫ y, (heatKernel r x y - heatKernel r x' y) ^ 2 ≤ ‖x - x'‖ ^ 2 / (8 * π * r ^ 2) := by
  rw [← integral_add_right_eq_self (fun y => (heatKernel r x y - heatKernel r x' y) ^ 2) x']
  refine le_of_eq_of_le ?_ (GFFExist.integral_sq_heatKernel_sub_le r hr (x - x'))
  congr 1; funext y
  unfold heatKernel
  congr 4
  · congr 2; ring_nf
  · congr 2; ring_nf

/-- Large times: `∫_{D^c} (p_r(x,·) − p_r(x',·))² ≤ |x−x'|²/(8πr²)`. -/
lemma lintegral_compl_sq_le_dist {r : ℝ} (hr : 0 < r) (S : Set ℂ) (x x' : ℂ) :
    ∫⁻ y in S, ENNReal.ofReal ((heatKernel r x y - heatKernel r x' y) ^ 2) ≤
      ENNReal.ofReal (‖x - x'‖ ^ 2 / (8 * π * r ^ 2)) := by
  refine (setLIntegral_le_lintegral _ _).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_heatKernel_sub hr x x')
    (Filter.Eventually.of_forall fun y => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (integral_sq_heatKernel_sub_le' hr x x')

/-- Small times: on `D^c` both kernels are at most `p_r(d, 0)`. -/
lemma lintegral_compl_sq_le_near {a L r d : ℝ} (hr : 0 < r) (hd : 0 < d) {x x' : ℂ}
    (hxre : x.re ∈ Icc (a + d) (a + L - d)) (hxim : x.im ∈ Icc (a + d) (a + L - d))
    (hx're : x'.re ∈ Icc (a + d) (a + L - d)) (hx'im : x'.im ∈ Icc (a + d) (a + L - d)) :
    ∫⁻ y in (sqOpen a L)ᶜ, ENNReal.ofReal ((heatKernel r x y - heatKernel r x' y) ^ 2) ≤
      ENNReal.ofReal (4 * heatKernel r (d : ℂ) 0) := by
  set e := heatKernel r (d : ℂ) 0
  have hcont : ∀ z : ℂ, Continuous (heatKernel r z) := fun z => by unfold heatKernel; fun_prop
  have hle : ∀ z : ℂ, z.re ∈ Icc (a + d) (a + L - d) → z.im ∈ Icc (a + d) (a + L - d) →
      ∀ y ∈ (sqOpen a L)ᶜ, heatKernel r z y ≤ e := fun z h1 h2 y hy => by
    rw [heatKernel_symm]
    exact heatKernel_le_of_le_norm hr hd.le (le_norm_of_not_mem_sqOpen hy h1 h2)
  have hm : Measurable (fun y => ENNReal.ofReal (2 * e * (heatKernel r x y + heatKernel r x' y))) :=
    ENNReal.measurable_ofReal.comp (((hcont x).add (hcont x')).const_mul _).measurable
  refine (setLIntegral_mono hm fun y hy => ENNReal.ofReal_le_ofReal ?_).trans
    ((setLIntegral_le_lintegral _ _).trans ?_)
  · have h1 := hle x hxre hxim y hy
    have h2 := hle x' hx're hx'im y hy
    have h3 := heatKernel_nonneg r hr.le x y
    have h4 := heatKernel_nonneg r hr.le x' y
    nlinarith
  · have hi : Integrable (fun y => 2 * e * (heatKernel r x y + heatKernel r x' y)) :=
      ((integrable_heatKernel r hr x).add (integrable_heatKernel r hr x')).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun y => mul_nonneg (by
        have := heatKernel_nonneg r hr.le (d : ℂ) 0; positivity)
        (add_nonneg (heatKernel_nonneg r hr.le x y) (heatKernel_nonneg r hr.le x' y)))]
    rw [integral_const_mul, integral_add (integrable_heatKernel r hr x)
      (integrable_heatKernel r hr x'), integral_heatKernel r hr, integral_heatKernel r hr]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Second term, increments** (DDDF `tightness.tex:1580–1586`): for `x, x'` in
`[a+d, a+L−d]²`, `∫_0^∞ ∫_{D^c} (p_r(x,y) − p_r(x',y))² dy dr ≤ (8/(πd²) + 1/(8π)) |x − x'|`. -/
theorem lintegral_secondTerm_incr_le {a L d : ℝ} (hd : 0 < d) {x x' : ℂ}
    (hxre : x.re ∈ Icc (a + d) (a + L - d)) (hxim : x.im ∈ Icc (a + d) (a + L - d))
    (hx're : x'.re ∈ Icc (a + d) (a + L - d)) (hx'im : x'.im ∈ Icc (a + d) (a + L - d)) :
    ∫⁻ r in Ioi 0, ∫⁻ y in (sqOpen a L)ᶜ,
        ENNReal.ofReal ((heatKernel r x y - heatKernel r x' y) ^ 2) ≤
      ENNReal.ofReal ((8 * (π * d ^ 2)⁻¹ + (8 * π)⁻¹) * ‖x - x'‖) := by
  set δ := ‖x - x'‖
  rcases eq_or_lt_of_le (norm_nonneg (x - x')) with h0 | hδ
  · have hxx : x = x' := sub_eq_zero.mp (norm_eq_zero.mp h0.symm)
    subst hxx
    simp
  have hM : ∀ r ∈ Ioc (0 : ℝ) δ, ∫⁻ y in (sqOpen a L)ᶜ,
      ENNReal.ofReal ((heatKernel r x y - heatKernel r x' y) ^ 2) ≤
        ENNReal.ofReal (8 * (π * d ^ 2)⁻¹) := fun r hr =>
    (lintegral_compl_sq_le_near hr.1 hd hxre hxim hx're hx'im).trans
      (ENNReal.ofReal_le_ofReal (by linarith [heatKernel_d_le_const hr.1 hd]))
  have hD : ∀ r ∈ Ioi δ, ∫⁻ y in (sqOpen a L)ᶜ,
      ENNReal.ofReal ((heatKernel r x y - heatKernel r x' y) ^ 2) ≤
        ENNReal.ofReal (δ ^ 2 / (8 * π)) * ENNReal.ofReal (r ^ (-2 : ℝ)) := fun r hr => by
    have hr0 : 0 < r := hδ.trans hr
    refine (lintegral_compl_sq_le_dist hr0 _ x x').trans_eq ?_
    rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_neg hr0.le, Real.rpow_two]
    congr 1; field_simp
    all_goals rfl
  rw [← Ioc_union_Ioi_eq_Ioi hδ.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have hI : ∫⁻ r in Ioi δ, ENNReal.ofReal (r ^ (-2 : ℝ)) = ENNReal.ofReal δ⁻¹ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) hδ)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun r hr =>
        Real.rpow_nonneg (hδ.trans hr).le _)), integral_Ioi_rpow_of_lt (by norm_num) hδ]
    congr 1; norm_num; rw [Real.rpow_neg_one]
  calc (∫⁻ r in Ioc 0 δ, ∫⁻ y in (sqOpen a L)ᶜ,
          ENNReal.ofReal ((heatKernel r x y - heatKernel r x' y) ^ 2)) +
        ∫⁻ r in Ioi δ, ∫⁻ y in (sqOpen a L)ᶜ,
          ENNReal.ofReal ((heatKernel r x y - heatKernel r x' y) ^ 2)
      ≤ (∫⁻ _ in Ioc 0 δ, ENNReal.ofReal (8 * (π * d ^ 2)⁻¹)) +
        ∫⁻ r in Ioi δ, ENNReal.ofReal (δ ^ 2 / (8 * π)) * ENNReal.ofReal (r ^ (-2 : ℝ)) :=
        add_le_add (setLIntegral_mono' measurableSet_Ioc hM) (setLIntegral_mono' measurableSet_Ioi hD)
    _ = ENNReal.ofReal (8 * (π * d ^ 2)⁻¹) * ENNReal.ofReal δ +
        ENNReal.ofReal (δ ^ 2 / (8 * π)) * ENNReal.ofReal δ⁻¹ := by
      rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
        lintegral_const_mul _ (Measurable.ennreal_ofReal (by fun_prop)), hI]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; field_simp

/-- **Second term, variance** (DDDF `tightness.tex:1587`): for `x` in `[a+d, a+L−d]²` and
`R > 0`, `∫_0^R ∫_{D^c} p_r(x,y)² dy dr ≤ 2R/(πd²)`. -/
theorem lintegral_secondTerm_var_le {a L d R : ℝ} (hd : 0 < d) {x : ℂ}
    (hxre : x.re ∈ Icc (a + d) (a + L - d)) (hxim : x.im ∈ Icc (a + d) (a + L - d)) :
    ∫⁻ r in Ioc 0 R, ∫⁻ y in (sqOpen a L)ᶜ, ENNReal.ofReal (heatKernel r x y ^ 2) ≤
      ENNReal.ofReal (2 * (π * d ^ 2)⁻¹ * R) := by
  have hpt : ∀ r ∈ Ioc (0 : ℝ) R, ∫⁻ y in (sqOpen a L)ᶜ, ENNReal.ofReal (heatKernel r x y ^ 2) ≤
      ENNReal.ofReal (2 * (π * d ^ 2)⁻¹) := by
    intro r hr
    have hr0 := hr.1
    have hcont : Continuous (heatKernel r x) := by unfold heatKernel; fun_prop
    set e := heatKernel r (d : ℂ) 0
    have hm : Measurable (fun y => ENNReal.ofReal (e * heatKernel r x y)) :=
      ENNReal.measurable_ofReal.comp (hcont.const_mul _).measurable
    refine (setLIntegral_mono hm fun y hy => ENNReal.ofReal_le_ofReal ?_).trans
      ((setLIntegral_le_lintegral _ _).trans ?_)
    · have h1 : heatKernel r x y ≤ e := by
        rw [heatKernel_symm]
        exact heatKernel_le_of_le_norm hr0 hd.le (le_norm_of_not_mem_sqOpen hy hxre hxim)
      have h3 := heatKernel_nonneg r hr0.le x y
      nlinarith
    · rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_heatKernel r hr0 x).const_mul _)
        (Filter.Eventually.of_forall fun y => mul_nonneg (heatKernel_nonneg r hr0.le _ _)
          (heatKernel_nonneg r hr0.le x y)), integral_const_mul, integral_heatKernel r hr0,
        mul_one]
      exact ENNReal.ofReal_le_ofReal (heatKernel_d_le_const hr0 hd)
  refine (setLIntegral_mono' measurableSet_Ioc hpt).trans_eq ?_
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]

end HeatSq
end LQGMetric
