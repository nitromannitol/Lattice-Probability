import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Stieltjes measures as images of Lebesgue measure under an inverse

Let `f` be a Stieltjes function on `ℝ` and let `g : ℝ → ℝ` be a measurable lower adjoint of `f` on the
values `r ∈ (f x, f y]`, in the sense that `g r ≤ t ↔ r ≤ f t` for every `t`. Then the Stieltjes measure
of `f` restricted to `(x, y]` is the image of Lebesgue measure on `(f x, f y]` under `g` (the quantile
transform). In particular `∫_{(x, y]} F df = ∫_{(f x, f y]} F (g r) dr` for every measurable `F ≥ 0`.

For a continuous, strictly increasing, unbounded clock `φ : ℝ≥0 → ℝ≥0`, its right inverse
`r ↦ inf {s | r < φ s}` is such a lower adjoint of the Stieltjes function `x ↦ φ x⁺`, which gives the
change of variables `∫_{(x, y]} F dφ = ∫_{(φ x, φ y]} F (φ⁻¹ r) dr` for the Lebesgue–Stieltjes integral of
a time change.

## Main results

* `LatticeProb.stieltjes_measure_restrict_Ioc_eq_map`: `f.measure|_(x,y] = (Leb|_(f x, f y]).map g`.
* `LatticeProb.lintegral_stieltjes_Ioc_eq_lintegral_comp`: the corresponding change of variables.
* `LatticeProb.sInf_lt_le_iff`: the Galois property of the right inverse of a continuous strictly
  increasing clock.
* `LatticeProb.lintegral_stieltjes_Ioc_eq_lintegral_clockInverse`: the change of variables for a clock.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace LatticeProb

/-- **Quantile transform of a Stieltjes measure on an interval.** If `g` is measurable and is a lower
adjoint of the Stieltjes function `f` on the values `r ∈ (f x, f y]` (`g r ≤ t ↔ r ≤ f t` for all `t`),
then the Stieltjes measure of `f` on `(x, y]` is the image of Lebesgue measure on `(f x, f y]` under
`g`. -/
theorem stieltjes_measure_restrict_Ioc_eq_map (f : StieltjesFunction ℝ) {x y : ℝ} {g : ℝ → ℝ}
    (hg : Measurable g) (hgal : ∀ r ∈ Ioc (f x) (f y), ∀ t, g r ≤ t ↔ r ≤ f t) :
    f.measure.restrict (Ioc x y) = (volume.restrict (Ioc (f x) (f y))).map g := by
  refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b _ => ?_)
  · rw [Measure.restrict_apply measurableSet_Ioc]
    exact ((measure_mono inter_subset_left).trans_lt
      (by rw [f.measure_Ioc]; exact ENNReal.ofReal_lt_top)).ne
  · rw [Measure.restrict_apply measurableSet_Ioc, Measure.map_apply hg measurableSet_Ioc,
      Measure.restrict_apply (hg measurableSet_Ioc), Ioc_inter_Ioc, f.measure_Ioc]
    have hset : g ⁻¹' Ioc a b ∩ Ioc (f x) (f y) = Ioc (f (a ⊔ x)) (f (b ⊓ y)) := by
      ext r
      simp only [mem_inter_iff, mem_preimage, mem_Ioc]
      constructor
      · rintro ⟨⟨hra, hrb⟩, hr1, hr2⟩
        have hr : r ∈ Ioc (f x) (f y) := ⟨hr1, hr2⟩
        have hx : x < g r := lt_of_not_ge fun h => (not_le.2 hr1) ((hgal r hr x).1 h)
        refine ⟨lt_of_not_ge fun h => ?_, (hgal r hr _).1 (le_inf hrb ((hgal r hr y).2 hr2))⟩
        exact (not_le.2 (max_lt hra hx)) ((hgal r hr _).2 h)
      · rintro ⟨hr1, hr2⟩
        have hr : r ∈ Ioc (f x) (f y) :=
          ⟨(f.mono le_sup_right).trans_lt hr1, hr2.trans (f.mono inf_le_right)⟩
        refine ⟨⟨lt_of_not_ge fun h => ?_, ((hgal r hr _).2 hr2).trans inf_le_left⟩, hr⟩
        exact (not_le.2 hr1) ((hgal r hr _).1 (h.trans le_sup_left))
    rw [hset, Real.volume_Ioc]

/-- **Change of variables for a Stieltjes integral on an interval.** Under the hypotheses of
`stieltjes_measure_restrict_Ioc_eq_map`, `∫_{(x, y]} F df = ∫_{(f x, f y]} F (g r) dr`. -/
theorem lintegral_stieltjes_Ioc_eq_lintegral_comp (f : StieltjesFunction ℝ) {x y : ℝ} {g : ℝ → ℝ}
    (hg : Measurable g) (hgal : ∀ r ∈ Ioc (f x) (f y), ∀ t, g r ≤ t ↔ r ≤ f t) {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ s in Ioc x y, F s ∂f.measure = ∫⁻ r in Ioc (f x) (f y), F (g r) := by
  rw [stieltjes_measure_restrict_Ioc_eq_map f hg hgal, lintegral_map hF hg]

/-- **The right inverse of a continuous strictly increasing clock is a lower adjoint.** If
`φ : ℝ≥0 → ℝ≥0` is continuous and strictly increasing and `r < φ s` for some `s`, then
`inf {s | r < φ s} ≤ t ↔ r ≤ φ t`. -/
theorem sInf_lt_le_iff {φ : ℝ≥0 → ℝ≥0} (hc : Continuous φ) (hs : StrictMono φ) {r : ℝ≥0}
    (hr : ∃ s, r < φ s) (t : ℝ≥0) : sInf {s | r < φ s} ≤ t ↔ r ≤ φ t := by
  constructor
  · intro h
    have hne : {s | r < φ s}.Nonempty := hr
    have hmap : φ (sInf {s | r < φ s}) = sInf (φ '' {s | r < φ s}) :=
      Monotone.map_csInf_of_continuousAt hc.continuousAt hs.monotone hne (OrderBot.bddBelow _)
    have hle : r ≤ φ (sInf {s | r < φ s}) := by
      rw [hmap]
      exact le_csInf (hne.image φ) (by rintro _ ⟨s, hs', rfl⟩; exact le_of_lt hs')
    exact hle.trans (hs.monotone h)
  · intro h
    calc sInf {s | r < φ s} ≤ sInf (Ioi t) :=
          csInf_le_csInf (OrderBot.bddBelow _) nonempty_Ioi fun s hs' => h.trans_lt (hs hs')
      _ = t := csInf_Ioi

/-- The right inverse `r ↦ inf {s | r⁺ < φ s}` of an unbounded continuous strictly increasing clock, as a
real function of a real level, is monotone. -/
theorem monotone_clockInverse_real {φ : ℝ≥0 → ℝ≥0} (hu : Tendsto φ atTop atTop) :
    Monotone fun r : ℝ => ((sInf {s | r.toNNReal < φ s} : ℝ≥0) : ℝ) := by
  intro r r' hrr'
  have hne : {s | r'.toNNReal < φ s}.Nonempty := (hu.eventually_gt_atTop r'.toNNReal).exists
  exact NNReal.coe_le_coe.2 (csInf_le_csInf (OrderBot.bddBelow _) hne
    fun s hs' => (Real.toNNReal_mono hrr').trans_lt hs')

/-- **The real right inverse of a clock is a lower adjoint of its Stieltjes function.** If
`φ : ℝ≥0 → ℝ≥0` is continuous, strictly increasing and unbounded, and `f x = φ x⁺` for all real `x`,
then for every level `r > φ 0`, `inf {s | r⁺ < φ s} ≤ t ↔ r ≤ f t` for all real `t`. -/
theorem clockInverse_real_le_iff {φ : ℝ≥0 → ℝ≥0} (hc : Continuous φ) (hs : StrictMono φ)
    (hu : Tendsto φ atTop atTop) (f : StieltjesFunction ℝ) (hf : ∀ x, f x = φ x.toNNReal) {r : ℝ}
    (hr0 : (φ 0 : ℝ) < r) (t : ℝ) :
    ((sInf {s | r.toNNReal < φ s} : ℝ≥0) : ℝ) ≤ t ↔ r ≤ f t := by
  have hr : 0 ≤ r := (φ 0).coe_nonneg.trans hr0.le
  have hex : ∃ s, r.toNNReal < φ s := (hu.eventually_gt_atTop r.toNNReal).exists
  rw [hf]
  rcases le_or_gt 0 t with ht | ht
  · have ht' : t = (t.toNNReal : ℝ) := (Real.coe_toNNReal t ht).symm
    rw [ht', NNReal.coe_le_coe, Real.toNNReal_coe, sInf_lt_le_iff hc hs hex,
      Real.toNNReal_le_iff_le_coe]
  · refine iff_of_false (fun h => not_le.2 ht ((NNReal.coe_nonneg _).trans h)) fun h => ?_
    rw [Real.toNNReal_of_nonpos ht.le] at h
    exact not_le.2 hr0 h

/-- **Change of variables for the Lebesgue–Stieltjes integral of a clock.** If `φ : ℝ≥0 → ℝ≥0` is
continuous, strictly increasing and unbounded, `f x = φ x⁺` for all real `x`, and `F ≥ 0` is measurable,
then `∫_{(x, y]} F df = ∫_{(f x, f y]} F (inf {s | r⁺ < φ s}) dr`. -/
theorem lintegral_stieltjes_Ioc_eq_lintegral_clockInverse {φ : ℝ≥0 → ℝ≥0} (hc : Continuous φ)
    (hs : StrictMono φ) (hu : Tendsto φ atTop atTop) (f : StieltjesFunction ℝ)
    (hf : ∀ x, f x = φ x.toNNReal) {x y : ℝ} {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ s in Ioc x y, F s ∂f.measure =
      ∫⁻ r in Ioc (f x) (f y), F ((sInf {s | r.toNNReal < φ s} : ℝ≥0) : ℝ) := by
  refine lintegral_stieltjes_Ioc_eq_lintegral_comp f (monotone_clockInverse_real hu).measurable
    (fun r hr t => clockInverse_real_le_iff hc hs hu f hf ?_ t) hF
  calc (φ 0 : ℝ) ≤ φ x.toNNReal := NNReal.coe_le_coe.2 (hs.monotone bot_le)
    _ = f x := (hf x).symm
    _ < r := hr.1

end LatticeProb
