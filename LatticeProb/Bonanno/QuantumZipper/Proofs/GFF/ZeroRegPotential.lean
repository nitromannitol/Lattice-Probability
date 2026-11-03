/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.ZeroRegPotential at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue

/-!
# Folded-circle potentials of the zero-boundary kernel (task RG-0, part 0)

For `x ∈ Hbar`, the potential `z ↦ ∫ greenH x y d(foldedCircle z r)(y)` is `4/r`-Lipschitz in
the centre `z`, uniformly in `x` (`abs_integral_greenH_foldedCircle_sub_le`).

Folding is not harmless for the odd kernel `greenH`, so there is no closed form. Instead:

* `greenH x (foldH u) = 2 hLog x u − log‖u − x‖ − log‖u − x̄‖` with
  `hLog x u = log max(‖u − x‖, ‖u − x̄‖)` (`greenH_foldH_eq`);
* Möbius/Poisson representation: `hLog x u = ∫ log‖(u − x) − (u − x̄) ζ‖ dζ` over the unit circle
  (`integral_log_norm_sub_mul_unit`);
* swapping the two circle integrals (Fubini), for fixed `ζ ≠ 1` the `u`-integrand is
  `log‖1 − ζ‖ + log‖u − c_ζ‖`, whose circle average `log‖1 − ζ‖ + log max(r, ‖z − c_ζ‖)` is
  `1/r`-Lipschitz in `z`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real ComplexConjugate

namespace QuantumZipper
namespace ZeroReg

/-! ## Circle measures have no atoms; affine log averages -/

theorem circleUnif_singleton_zr (z : ℂ) {r : ℝ} (hr : r ≠ 0) (c : ℂ) :
    circleUnif z r {c} = 0 := by
  rw [CircleMV.circleUnif_eq_circMeas]; exact LQGDimension.Coupling.circMeas_singleton hr c

theorem ae_ne_circleUnif_zr (z : ℂ) {r : ℝ} (hr : r ≠ 0) (c : ℂ) :
    ∀ᵐ u ∂circleUnif z r, u ≠ c := by
  rw [ae_iff]
  have : {a : ℂ | ¬a ≠ c} = {c} := by ext; simp
  rw [this]; exact circleUnif_singleton_zr z hr c

/-- Circle average of `log‖α u − β‖`. -/
theorem integral_log_norm_affine_zr (z : ℂ) {r : ℝ} (hr : 0 < r) {α : ℂ} (hα : α ≠ 0) (β : ℂ) :
    Integrable (fun u => Real.log ‖α * u - β‖) (circleUnif z r) ∧
      ∫ u, Real.log ‖α * u - β‖ ∂circleUnif z r =
        Real.log ‖α‖ + Real.log (max r ‖z - β / α‖) := by
  have hae : (fun u => Real.log ‖α * u - β‖) =ᵐ[circleUnif z r]
      fun u => Real.log ‖α‖ + Real.log ‖u - β / α‖ := by
    filter_upwards [ae_ne_circleUnif_zr z hr.ne' (β / α)] with u hu
    have e : α * u - β = α * (u - β / α) := by field_simp
    rw [e, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hα) (norm_ne_zero_iff.2 (sub_ne_zero.2 hu))]
  have hi : Integrable (fun u => Real.log ‖α‖ + Real.log ‖u - β / α‖) (circleUnif z r) :=
    (integrable_const _).add (CircleMV.integrable_log_norm_sub_circleUnif z _ r)
  refine ⟨hi.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add (integrable_const _)
    (CircleMV.integrable_log_norm_sub_circleUnif z _ r), integral_const,
    integral_log_norm_sub_circleUnif z _ hr]
  simp

/-- Jensen's formula on the unit circle: `∫ log‖a − b ζ‖ dζ = log max(‖a‖, ‖b‖)`. -/
theorem integral_log_norm_sub_mul_unit (a b : ℂ) :
    Integrable (fun ζ => Real.log ‖a - b * ζ‖) (circleUnif 0 1) ∧
      ∫ ζ, Real.log ‖a - b * ζ‖ ∂circleUnif 0 1 = Real.log (max ‖a‖ ‖b‖) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [zero_mul, sub_zero, norm_zero]
    refine ⟨integrable_const _, ?_⟩
    simp
  · have e : ∀ ζ, a - b * ζ = (-b) * ζ - (-a) := fun ζ => by ring
    simp_rw [e]
    obtain ⟨h1, h2⟩ := integral_log_norm_affine_zr 0 one_pos (neg_ne_zero.2 hb) (-a)
    refine ⟨h1, ?_⟩
    have hb' : 0 < ‖b‖ := norm_pos_iff.2 hb
    rw [h2, norm_neg, zero_sub, neg_div_neg_eq, norm_neg, norm_div,
      ← Real.log_mul hb'.ne' (lt_of_lt_of_le one_pos (le_max_left _ _)).ne',
      mul_max_of_nonneg _ _ hb'.le, mul_one, mul_div_cancel₀ _ hb'.ne', max_comm]

/-! ## The folded kernel -/

/-- `hLog x u = log max(‖u − x‖, ‖u − x̄‖)`. -/
def hLog (x u : ℂ) : ℝ := Real.log (max ‖u - x‖ ‖u - conj x‖)

theorem measurable_hLog (x : ℂ) : Measurable (hLog x) :=
  Real.measurable_log.comp (by fun_prop : Continuous fun u : ℂ =>
    max ‖u - x‖ ‖u - conj x‖).measurable

theorem greenH_foldH_eq {x : ℂ} (hx : x ∈ Hbar) (u : ℂ) :
    greenH x (foldH u) = 2 * hLog x u - Real.log ‖u - x‖ - Real.log ‖u - conj x‖ := by
  unfold foldH hLog greenH
  split_ifs with h
  · have h1 : ‖x - conj u‖ = ‖u - conj x‖ := norm_sub_conj_comm x u
    have h2 : ‖u - x‖ ≤ ‖u - conj x‖ := norm_sub_le_norm_sub_conj h hx
    rw [h1, max_eq_right h2, norm_sub_rev x u]; ring
  · have hu : conj u ∈ Hbar := by
      show 0 ≤ (conj u).im
      rw [Complex.conj_im]; linarith [not_le.1 h]
    have h1 : ‖x - conj (conj u)‖ = ‖u - x‖ := by rw [Complex.conj_conj, norm_sub_rev]
    have h2 : ‖x - conj u‖ = ‖u - conj x‖ := norm_sub_conj_comm x u
    have h3 : ‖u - conj x‖ ≤ ‖u - x‖ := by
      have := norm_sub_le_norm_sub_conj hu hx
      rwa [CircleMV.norm_foldH_sub_conj, ← map_sub, Complex.norm_conj] at this
    rw [h1, h2, max_eq_left h3]; ring

theorem abs_log_max_le_zr (a b : ℝ) : |Real.log (max a b)| ≤ |Real.log a| + |Real.log b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; linarith [abs_nonneg (Real.log a)]
  · rw [max_eq_left h]; linarith [abs_nonneg (Real.log b)]

theorem integrable_hLog (x z : ℂ) (r : ℝ) : Integrable (hLog x) (circleUnif z r) := by
  refine Integrable.mono' ((CircleMV.integrable_log_norm_sub_circleUnif z x r).abs.add
    (CircleMV.integrable_log_norm_sub_circleUnif z (conj x) r).abs)
    (measurable_hLog x).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs]
  exact abs_log_max_le_zr _ _

/-! ## Fubini on the product of two circles -/

/-- The Möbius integrand `log‖(u − x) − (u − x̄) ζ‖`. -/
def FM (x : ℂ) (p : ℂ × ℂ) : ℝ := Real.log ‖(p.1 - x) - (p.1 - conj x) * p.2‖

theorem measurable_FM (x : ℂ) : Measurable (FM x) :=
  Real.measurable_log.comp (by fun_prop : Continuous fun p : ℂ × ℂ =>
    ‖(p.1 - x) - (p.1 - conj x) * p.2‖).measurable

theorem log_le_log_max_one_zr {t S : ℝ} (ht : 0 ≤ t) (h : t ≤ S) :
    Real.log t ≤ Real.log (max 1 S) := by
  rcases ht.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; exact Real.log_nonneg (le_max_left _ _)
  · exact Real.log_le_log h0 (h.trans (le_max_right _ _))

theorem integrable_FM (x z : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (FM x) ((circleUnif z r).prod (circleUnif 0 1)) := by
  set B : ℝ := Real.log (max 1 (‖z - x‖ + ‖z - conj x‖ + 2 * r)) with hB
  have hB0 : 0 ≤ B := Real.log_nonneg (le_max_left _ _)
  have hm := (measurable_FM x).aestronglyMeasurable (μ := (circleUnif z r).prod (circleUnif 0 1))
  rw [integrable_prod_iff hm]
  refine ⟨ae_of_all _ fun u => (integral_log_norm_sub_mul_unit (u - x) (u - conj x)).1, ?_⟩
  refine Integrable.mono' ((integrable_const (2 * B)).sub (integrable_hLog x z r))
    hm.norm.integral_prod_right' ?_
  filter_upwards [CircleMV.ae_circleUnif z r] with u hu
  rw [abs_of_pos hr] at hu
  obtain ⟨i1, i2⟩ := integral_log_norm_sub_mul_unit (u - x) (u - conj x)
  have hle : ∀ᵐ ζ ∂circleUnif 0 1, ‖FM x (u, ζ)‖ ≤ 2 * B - FM x (u, ζ) := by
    filter_upwards [CircleMV.ae_circleUnif 0 1] with ζ hζ
    rw [sub_zero, abs_one] at hζ
    have hFB : FM x (u, ζ) ≤ B := by
      unfold FM
      refine log_le_log_max_one_zr (norm_nonneg _) ?_
      calc ‖(u - x) - (u - conj x) * ζ‖ ≤ ‖u - x‖ + ‖(u - conj x) * ζ‖ := norm_sub_le _ _
        _ = ‖(u - z) + (z - x)‖ + ‖(u - z) + (z - conj x)‖ := by
            rw [norm_mul, hζ, mul_one]; ring_nf
        _ ≤ (‖u - z‖ + ‖z - x‖) + (‖u - z‖ + ‖z - conj x‖) :=
            add_le_add (norm_add_le _ _) (norm_add_le _ _)
        _ = ‖z - x‖ + ‖z - conj x‖ + 2 * r := by rw [hu]; ring
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  calc ∫ ζ, ‖FM x (u, ζ)‖ ∂circleUnif 0 1 ≤ ∫ ζ, (2 * B - FM x (u, ζ)) ∂circleUnif 0 1 :=
        integral_mono_ae i1.norm ((integrable_const _).sub i1) hle
    _ = 2 * B - hLog x u := by
        simp only [FM, hLog]
        rw [integral_sub (integrable_const _) i1, integral_const, i2]
        simp

/-- The circle average of `hLog x`. -/
def avgHLog (r : ℝ) (x z : ℂ) : ℝ := ∫ u, hLog x u ∂circleUnif z r

/-- The `u`-integral of the Möbius integrand. -/
def innerFM (r : ℝ) (x z ζ : ℂ) : ℝ := ∫ u, FM x (u, ζ) ∂circleUnif z r

theorem avgHLog_eq_integral_innerFM (x z : ℂ) {r : ℝ} (hr : 0 < r) :
    avgHLog r x z = ∫ ζ, innerFM r x z ζ ∂circleUnif 0 1 := by
  have e : ∀ u, hLog x u = ∫ ζ, FM x (u, ζ) ∂circleUnif 0 1 := fun u =>
    (integral_log_norm_sub_mul_unit (u - x) (u - conj x)).2.symm
  unfold avgHLog innerFM
  simp_rw [e]
  exact integral_integral_swap (f := fun u ζ => FM x (u, ζ)) (integrable_FM x z hr)

theorem integrable_innerFM (x z : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (innerFM r x z) (circleUnif 0 1) :=
  (integrable_FM x z hr).integral_prod_right

theorem innerFM_eq (x z : ℂ) {r : ℝ} (hr : 0 < r) {ζ : ℂ} (hζ : ζ ≠ 1) :
    innerFM r x z ζ = Real.log ‖1 - ζ‖ +
      Real.log (max r ‖z - (x - conj x * ζ) / (1 - ζ)‖) := by
  have e : ∀ u, FM x (u, ζ) = Real.log ‖(1 - ζ) * u - (x - conj x * ζ)‖ := fun u => by
    unfold FM; ring_nf
  unfold innerFM
  simp_rw [e]
  exact (integral_log_norm_affine_zr z hr (sub_ne_zero.2 hζ.symm) _).2

theorem abs_avgHLog_sub_le (x z w : ℂ) {r : ℝ} (hr : 0 < r) :
    |avgHLog r x z - avgHLog r x w| ≤ ‖z - w‖ / r := by
  rw [avgHLog_eq_integral_innerFM x z hr, avgHLog_eq_integral_innerFM x w hr,
    ← integral_sub (integrable_innerFM x z hr) (integrable_innerFM x w hr)]
  have hb : ∀ᵐ ζ ∂circleUnif 0 1, ‖innerFM r x z ζ - innerFM r x w ζ‖ ≤ ‖z - w‖ / r := by
    filter_upwards [ae_ne_circleUnif_zr 0 one_ne_zero 1] with ζ hζ
    rw [innerFM_eq x z hr hζ, innerFM_eq x w hr hζ, Real.norm_eq_abs]
    have := abs_log_max_sub_le z w ((x - conj x * ζ) / (1 - ζ)) hr
    have e : Real.log ‖1 - ζ‖ + Real.log (max r ‖z - (x - conj x * ζ) / (1 - ζ)‖) -
        (Real.log ‖1 - ζ‖ + Real.log (max r ‖w - (x - conj x * ζ) / (1 - ζ)‖)) =
        Real.log (max r ‖z - (x - conj x * ζ) / (1 - ζ)‖) -
          Real.log (max r ‖w - (x - conj x * ζ) / (1 - ζ)‖) := by ring
    rw [e]; exact this
  have := norm_integral_le_of_norm_le_const hb
  simpa [Real.norm_eq_abs] using this

/-! ## The folded-circle potential of `greenH` -/

theorem integral_greenH_foldedCircle_eq {x : ℂ} (hx : x ∈ Hbar) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ y, greenH x y ∂foldedCircle z r =
      2 * avgHLog r x z - Real.log (max r ‖z - x‖) - Real.log (max r ‖z - conj x‖) := by
  have hm : Measurable fun y => greenH x y :=
    measurable_greenH.comp (measurable_const.prodMk measurable_id)
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable hm.aestronglyMeasurable]
  simp_rw [greenH_foldH_eq hx]
  rw [integral_sub (f := fun u => 2 * hLog x u - Real.log ‖u - x‖)
      (g := fun u => Real.log ‖u - conj x‖) ((integrable_hLog x z r).const_mul 2 |>.sub
      (CircleMV.integrable_log_norm_sub_circleUnif z x r))
      (CircleMV.integrable_log_norm_sub_circleUnif z (conj x) r),
    integral_sub (f := fun u => 2 * hLog x u) (g := fun u => Real.log ‖u - x‖)
      ((integrable_hLog x z r).const_mul 2)
      (CircleMV.integrable_log_norm_sub_circleUnif z x r),
    integral_const_mul, integral_log_norm_sub_circleUnif z x hr,
    integral_log_norm_sub_circleUnif z _ hr, avgHLog]

/-- **Lipschitz dependence on the centre** of folded-circle potentials of `greenH`,
uniformly in the pole `x ∈ Hbar`. -/
theorem abs_integral_greenH_foldedCircle_sub_le {x : ℂ} (hx : x ∈ Hbar) (z w : ℂ) {r : ℝ}
    (hr : 0 < r) :
    |∫ y, greenH x y ∂foldedCircle z r - ∫ y, greenH x y ∂foldedCircle w r| ≤
      4 * ‖z - w‖ / r := by
  rw [integral_greenH_foldedCircle_eq hx z hr, integral_greenH_foldedCircle_eq hx w hr]
  have h1 := abs_avgHLog_sub_le x z w hr
  have h2 := abs_log_max_sub_le z w x hr
  have h3 := abs_log_max_sub_le z w (conj x) hr
  have e : 2 * avgHLog r x z - Real.log (max r ‖z - x‖) - Real.log (max r ‖z - conj x‖) -
      (2 * avgHLog r x w - Real.log (max r ‖w - x‖) - Real.log (max r ‖w - conj x‖)) =
      2 * (avgHLog r x z - avgHLog r x w) -
        (Real.log (max r ‖z - x‖) - Real.log (max r ‖w - x‖)) -
        (Real.log (max r ‖z - conj x‖) - Real.log (max r ‖w - conj x‖)) := by ring
  rw [e]
  have e4 : 4 * ‖z - w‖ / r = 2 * (‖z - w‖ / r) + ‖z - w‖ / r + ‖z - w‖ / r := by ring
  rw [e4]
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ h2)) h3)
  rw [abs_mul, abs_two]; linarith

end ZeroReg
end QuantumZipper
