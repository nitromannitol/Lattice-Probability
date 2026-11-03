/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.PolygonDixonFubini at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.PolygonDixonReduce
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini for polygon integrals (EXT-CA node H3, part 3)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "H. Homology Cauchy", node H3 (Dixon's theorem).

This module supplies the "swap the two integrals" step of Dixon's proof: for a kernel
`K : ℂ → ℂ → ℂ` continuous on a rectangle times the carrier of a polygon, the integral of
`z ↦ ∮_p K z w dw` over a side of a rectangle equals the polygon integral of the `z`-integrals
of `K`.  This is what lets Morera's theorem be applied to the parametric polygon integral
`z ↦ ∮_p K z w dw`: the inner rectangle integral vanishes for every `w` on the carrier.

The proof reduces the polygon integral to the integrals over its edges
(`curveIntegral_segment_dzForm_eq`) and each side of a rectangle to a real interval integral, and
applies Fubini's theorem for interval integrals (`intervalIntegral_intervalIntegral_swap`).  The
integrability needed for Fubini, and the continuity used to compare the iterated integrals, come
from joint continuity of the kernel on the compact product of the side and the polyline, via the
dominated convergence theorem for interval integrals (`continuousWithinAt_of_dominated_interval`).

## Sources

S. A. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. Amer. Math. Soc. **29** (1971)
625-626 (the two-variable kernel is swapped onto the polygon; the inner rectangle integral is
evaluated by the rectangle form of Cauchy's theorem).  R. B. Burckel, *Classical Analysis in the
Complex Plane* (Birkhäuser 2021), Theorem 10.11 and Ch. 4.
-/

noncomputable section

open Set Metric Filter Complex Real AffineMap MeasureTheory
open scoped Topology Convex Interval

namespace QuantumZipper.CA.Homology

/-! ## The `Ι`-membership used for the segment parametrization -/

theorem lineMap_mem_segment_uIoc (c d : ℂ) {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) :
    lineMap c d t ∈ segment ℝ c d :=
  lineMap_mem_segment c d (by simpa [uIcc_of_le zero_le_one] using uIoc_subset_uIcc ht)

theorem lineMap_mem_segment_uIcc (c d : ℂ) {t : ℝ} (ht : t ∈ [[(0 : ℝ), 1]]) :
    lineMap c d t ∈ segment ℝ c d :=
  lineMap_mem_segment c d (by simpa [uIcc_of_le zero_le_one] using ht)

/-! ## Continuity of a parametric interval integral -/

/-- **Continuity of an interval integral in a complex parameter.** If the kernel `K` is jointly
continuous on `s × [[a,b]]` and bounded by `C` on `s × Ι a b`, then `z ↦ ∫_a^b K z t dt` is
continuous on `s` (dominated convergence). -/
theorem continuousOn_intervalIntegral_param {K : ℂ → ℝ → ℂ} {a b : ℝ} {s : Set ℂ} {C : ℝ}
    (hK : ContinuousOn (fun p : ℂ × ℝ => K p.1 p.2) (s ×ˢ [[a, b]]))
    (hC : ∀ z ∈ s, ∀ t ∈ Ι a b, ‖K z t‖ ≤ C) :
    ContinuousOn (fun z => ∫ t in a..b, K z t) s := by
  intro z₀ hz₀
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (μ := volume)
    (F := fun z t => K z t) (bound := fun _ => C) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hcont : ContinuousOn (fun t : ℝ => K z t) (Ι a b) :=
      hK.comp ((continuous_const.prodMk continuous_id :
        Continuous fun t : ℝ => (z, t))).continuousOn
        (fun t ht => ⟨hz, uIoc_subset_uIcc ht⟩)
    exact hcont.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with z hz
    filter_upwards with t ht
    exact hC z hz t ht
  · refine Eventually.of_forall fun t ht => ?_
    have hmap : ContinuousWithinAt (fun z : ℂ => (z, t)) s z₀ :=
      continuousWithinAt_id.prodMk continuousWithinAt_const
    exact (hK.continuousWithinAt ⟨hz₀, uIoc_subset_uIcc ht⟩).comp hmap
      (fun z hz => ⟨hz, uIoc_subset_uIcc ht⟩)

/-- **Continuity of a parametric interval integral in its second variable.** If `K` is jointly
continuous on `S × T`, `φ` maps `[[a,b]]` into `S` and `T` is compact, then
`η ↦ ∫_a^b K (φ t) η dt` is continuous on `T`. -/
theorem continuousOn_intervalIntegral_param_snd {K : ℂ → ℂ → ℂ} {S T : Set ℂ} {φ : ℝ → ℂ}
    {a b : ℝ} (hφ : ContinuousOn φ [[a, b]]) (hφS : ∀ t ∈ [[a, b]], φ t ∈ S)
    (hT : IsCompact T) (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (S ×ˢ T)) :
    ContinuousOn (fun η => ∫ t in a..b, K (φ t) η) T := by
  obtain ⟨C, hC⟩ := ((isCompact_uIcc.image_of_continuousOn hφ).prod hT).exists_bound_of_continuousOn
    (hK.mono (prod_mono (image_subset_iff.mpr hφS) Subset.rfl))
  refine continuousOn_intervalIntegral_param (a := a) (b := b) (s := T)
    (K := fun η t => K (φ t) η) (C := C) ?_ ?_
  · have hfst : Continuous fun p : ℂ × ℝ => p.1 := continuous_fst
    have hsnd : Continuous fun p : ℂ × ℝ => p.2 := continuous_snd
    have hA : ContinuousOn (fun p : ℂ × ℝ => φ p.2) (T ×ˢ [[a, b]]) :=
      hφ.comp hsnd.continuousOn (fun p hp => hp.2)
    have hB : ContinuousOn (fun p : ℂ × ℝ => p.1) (T ×ˢ [[a, b]]) := hfst.continuousOn
    have hmap : ContinuousOn (fun p : ℂ × ℝ => (φ p.2, p.1)) (T ×ˢ [[a, b]]) := hA.prodMk hB
    exact hK.comp hmap (fun p hp => mk_mem_prod (hφS p.2 hp.2) hp.1)
  · intro η hη t ht
    exact hC _ (mk_mem_prod (mem_image_of_mem φ (uIoc_subset_uIcc ht)) hη)

/-! ## The segment/interval swap -/

/-- **Continuity of a parametric segment integral.** For a kernel jointly continuous on
`φ '' [[a,b]] × [c,d]`, the function `t ↦ ∫ᶜ_{[c,d]} K (φ t) dw` is continuous. -/
theorem continuousOn_curveIntegral_segment_param {K : ℂ → ℂ → ℂ} {φ : ℝ → ℂ} {c d : ℂ} {a b : ℝ}
    (hφ : ContinuousOn φ [[a, b]])
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) ((φ '' [[a, b]]) ×ˢ segment ℝ c d)) :
    ContinuousOn (fun t => ∫ᶜ η in Path.segment c d, dzForm (K (φ t)) η) [[a, b]] := by
  obtain ⟨C, hC⟩ := ((isCompact_uIcc.image_of_continuousOn hφ).prod (isCompact_segmentC c d))
    |>.exists_bound_of_continuousOn hK
  have hmain : ContinuousOn (fun z => ∫ s in (0 : ℝ)..1, K z (lineMap c d s) * (d - c))
      (φ '' [[a, b]]) := by
    refine continuousOn_intervalIntegral_param (a := (0 : ℝ)) (b := 1) (s := φ '' [[a, b]])
      (K := fun z s => K z (lineMap c d s) * (d - c)) (C := C * ‖d - c‖) ?_ ?_
    · have hfst : Continuous fun p : ℂ × ℝ => p.1 := continuous_fst
      have hsnd : Continuous fun p : ℂ × ℝ => p.2 := continuous_snd
      have hlm : Continuous fun p : ℂ × ℝ => lineMap c d p.2 := (continuous_lineMap c d).comp hsnd
      have hpair : ContinuousOn (fun p : ℂ × ℝ => (p.1, lineMap c d p.2))
          ((φ '' [[a, b]]) ×ˢ [[(0 : ℝ), 1]]) := (hfst.prodMk hlm).continuousOn
      have hflip := hK.comp hpair
        (fun p hp => mk_mem_prod hp.1 (lineMap_mem_segment_uIcc c d hp.2))
      exact hflip.mul continuousOn_const
    · intro z hz s hs
      have h1 : (z, lineMap c d s) ∈ (φ '' [[a, b]]) ×ˢ segment ℝ c d :=
        ⟨hz, lineMap_mem_segment_uIoc c d hs⟩
      calc ‖K z (lineMap c d s) * (d - c)‖ = ‖K z (lineMap c d s)‖ * ‖d - c‖ := norm_mul _ _
        _ ≤ C * ‖d - c‖ := mul_le_mul_of_nonneg_right (hC _ h1) (norm_nonneg _)
  have hcomp : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..1, K (φ t) (lineMap c d s) * (d - c))
      [[a, b]] :=
    hmain.comp hφ (fun t ht => mem_image_of_mem φ ht)
  refine hcomp.congr fun t _ => ?_
  rw [curveIntegral_segment_dzForm_eq]

/-- **Fubini for a segment integral and a parameter interval.** -/
theorem intervalIntegral_curveIntegral_segment_swap {K : ℂ → ℂ → ℂ} {φ : ℝ → ℂ} {c d : ℂ}
    {a b : ℝ} (hφ : ContinuousOn φ [[a, b]])
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) ((φ '' [[a, b]]) ×ˢ segment ℝ c d)) :
    IntervalIntegrable (fun t => ∫ᶜ η in Path.segment c d, dzForm (K (φ t)) η) volume a b ∧
      (∫ t in a..b, ∫ᶜ η in Path.segment c d, dzForm (K (φ t)) η)
        = ∫ᶜ η in Path.segment c d, dzForm (fun η => ∫ t in a..b, K (φ t) η) η := by
  refine ⟨(continuousOn_curveIntegral_segment_param hφ hK).intervalIntegrable, ?_⟩
  rw [curveIntegral_segment_dzForm_eq (fun η => ∫ t in a..b, K (φ t) η) c d]
  simp_rw [curveIntegral_segment_dzForm_eq]
  have hfst : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
  have hsnd : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
  have hA : ContinuousOn (fun p : ℝ × ℝ => φ p.1) ([[a, b]] ×ˢ [[(0 : ℝ), 1]]) :=
    hφ.comp hfst.continuousOn (fun p hp => hp.1)
  have hB : ContinuousOn (fun p : ℝ × ℝ => lineMap c d p.2) ([[a, b]] ×ˢ [[(0 : ℝ), 1]]) :=
    ((continuous_lineMap c d).comp hsnd).continuousOn
  have hpair : ContinuousOn (fun p : ℝ × ℝ => (φ p.1, lineMap c d p.2))
      ([[a, b]] ×ˢ [[(0 : ℝ), 1]]) := hA.prodMk hB
  have hcont : ContinuousOn (fun p : ℝ × ℝ => K (φ p.1) (lineMap c d p.2))
      ([[a, b]] ×ˢ [[(0 : ℝ), 1]]) :=
    hK.comp hpair (fun p hp => mk_mem_prod (mem_image_of_mem φ hp.1)
      (lineMap_mem_segment_uIcc c d hp.2))
  have hint : IntegrableOn (fun p : ℝ × ℝ => K (φ p.1) (lineMap c d p.2))
      (Ι a b ×ˢ Ι (0 : ℝ) 1) :=
    (hcont.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hFub := intervalIntegral_intervalIntegral_swap
    (F := fun t s => K (φ t) (lineMap c d s)) hint
  have key : (fun t : ℝ => ∫ s in (0 : ℝ)..1, K (φ t) (lineMap c d s) * (d - c))
      = fun t : ℝ => (∫ s in (0 : ℝ)..1, K (φ t) (lineMap c d s)) * (d - c) :=
    funext fun t => intervalIntegral.integral_mul_const (d - c) _
  rw [key, intervalIntegral.integral_mul_const, hFub, intervalIntegral.integral_mul_const]

/-! ## The polygon/interval swap -/

/-- **Fubini for a polygon integral and a parameter interval.** -/
theorem intervalIntegral_walkIntegral_swap {K : ℂ → ℂ → ℂ} {φ : ℝ → ℂ} {a b : ℝ} {u : ℂ}
    {l : List ℂ} (hφ : ContinuousOn φ [[a, b]])
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) ((φ '' [[a, b]]) ×ˢ walkCarrier u l)) :
    IntervalIntegrable (fun t => walkIntegral (fun η => K (φ t) η) u l) volume a b ∧
      (∫ t in a..b, walkIntegral (fun η => K (φ t) η) u l)
        = walkIntegral (fun η => ∫ t in a..b, K (φ t) η) u l := by
  induction l generalizing u with
  | nil =>
    have hzero : (fun t : ℝ => walkIntegral (fun η => K (φ t) η) u []) = fun _ => (0 : ℂ) := by
      funext t
      simp [walkIntegral, walkIntegralCLM]
    refine ⟨?_, ?_⟩
    · rw [hzero]
      exact intervalIntegrable_const (μ := volume) (a := a) (b := b)
    · simp [walkIntegral, walkIntegralCLM]
  | cons v t ih =>
    have hseg : segment ℝ u v ⊆ walkCarrier u (v :: t) := fun z hz => Or.inl hz
    have htail : walkCarrier v t ⊆ walkCarrier u (v :: t) := fun z hz => Or.inr hz
    have hih := ih (u := v) (hK.mono (prod_mono_right htail))
    have hatom := intervalIntegral_curveIntegral_segment_swap hφ (hK.mono (prod_mono_right hseg))
    have hI₁ : IntervalIntegrable
        (fun x => ∫ᶜ η in Path.segment u v, dzForm (K (φ x)) η) volume a b := hatom.1
    have hI₂ : IntervalIntegrable
        (fun x => walkIntegral (fun η => K (φ x) η) v t) volume a b := hih.1
    refine ⟨?_, ?_⟩
    · simpa only [walkIntegral, walkIntegralCLM] using hI₁.add hI₂
    · rw [show (∫ x in a..b, walkIntegral (fun η => K (φ x) η) u (v :: t))
          = ∫ x in a..b, ((∫ᶜ η in Path.segment u v, dzForm (K (φ x)) η)
              + walkIntegral (fun η => K (φ x) η) v t) from rfl,
        intervalIntegral.integral_add hI₁ hI₂, hatom.2, hih.2]
      rfl

/-! ## The two sides of a rectangle -/

theorem add_mul_I_mem_Rectangle {z w : ℂ} {x b : ℝ} (hx : x ∈ [[z.re, w.re]])
    (hb : b ∈ [[z.im, w.im]]) : x + b * I ∈ Rectangle z w := by
  rw [Rectangle, mem_reProdIm]
  exact ⟨by simp_all, by simp_all⟩

/-- The `x`-side of the Fubini swap: the kernel is integrated over `[z.re, w.re]` at height
`z.im`. -/
theorem intervalIntegral_walkIntegral_swap_horizontal {K : ℂ → ℂ → ℂ} {z w u : ℂ} {l : List ℂ}
    {b : ℝ} (hb : b ∈ [[z.im, w.im]])
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (Rectangle z w ×ˢ walkCarrier u l)) :
    (∫ x in z.re..w.re, walkIntegral (fun η => K (x + b * I) η) u l)
      = walkIntegral (fun η => ∫ x in z.re..w.re, K (x + b * I) η) u l :=
  (intervalIntegral_walkIntegral_swap (φ := fun x : ℝ => x + b * I)
    (a := z.re) (b := w.re) (by fun_prop)
    (hK.mono (prod_mono (by rintro ζ ⟨x, hx, rfl⟩; exact add_mul_I_mem_Rectangle hx hb)
      Subset.rfl))).2

/-- The `y`-side of the Fubini swap: the kernel is integrated over `[z.im, w.im]` at real part
`w.re`. -/
theorem intervalIntegral_walkIntegral_swap_vertical {K : ℂ → ℂ → ℂ} {z w u : ℂ} {l : List ℂ}
    {a : ℝ} (ha : a ∈ [[z.re, w.re]])
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (Rectangle z w ×ˢ walkCarrier u l)) :
    (∫ y in z.im..w.im, walkIntegral (fun η => K (a + y * I) η) u l)
      = walkIntegral (fun η => ∫ y in z.im..w.im, K (a + y * I) η) u l :=
  (intervalIntegral_walkIntegral_swap (φ := fun y : ℝ => a + y * I)
    (a := z.im) (b := w.im) (by fun_prop)
    (hK.mono (prod_mono (by rintro ζ ⟨y, hy, rfl⟩; exact add_mul_I_mem_Rectangle ha hy)
      Subset.rfl))).2

/-! ## The wedge form: Fubini for the polygon integral and the rectangle boundary -/

/-- **Fubini for the polygon integral and the wedge integral.** For a kernel jointly continuous
on the rectangle `Rectangle z w` times the carrier of the polygon, the wedge integral of the
parametric polygon integral is the polygon integral of the wedge integrals.  In particular the
boundary integral `∮_{∂R} ∮_p K(z,w) dw dz` equals `∮_p ∮_{∂R} K(z,w) dz dw`. -/
theorem wedgeIntegral_walkIntegral_swap {K : ℂ → ℂ → ℂ} {z w u : ℂ} {l : List ℂ}
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (Rectangle z w ×ˢ walkCarrier u l)) :
    wedgeIntegral z w (fun ζ => walkIntegral (fun η => K ζ η) u l)
      = walkIntegral (fun η => wedgeIntegral z w (fun ζ => K ζ η)) u l := by
  have hT : IsCompact (walkCarrier u l) := isCompact_walkCarrier u l
  have hpm : (z.im : ℝ) ∈ [[z.im, w.im]] := left_mem_uIcc
  have hqm : (w.re : ℝ) ∈ [[z.re, w.re]] := right_mem_uIcc
  have hcontH : ContinuousOn (fun η => ∫ x in z.re..w.re, K (x + z.im * I) η)
      (walkCarrier u l) :=
    continuousOn_intervalIntegral_param_snd (φ := fun x : ℝ => x + z.im * I)
      (S := Rectangle z w) (T := walkCarrier u l) (by fun_prop)
      (fun x hx => add_mul_I_mem_Rectangle hx hpm) hT hK
  have hcontV : ContinuousOn (fun η => ∫ y in z.im..w.im, K (w.re + y * I) η)
      (walkCarrier u l) :=
    continuousOn_intervalIntegral_param_snd (φ := fun y : ℝ => w.re + y * I)
      (S := Rectangle z w) (T := walkCarrier u l) (by fun_prop)
      (fun y hy => add_mul_I_mem_Rectangle hqm hy) hT hK
  rw [wedgeIntegral, intervalIntegral_walkIntegral_swap_horizontal hpm hK,
    intervalIntegral_walkIntegral_swap_vertical hqm hK]
  rw [show (fun η => wedgeIntegral z w (fun ζ => K ζ η))
      = fun η => (∫ x in z.re..w.re, K (x + z.im * I) η)
        + I • (∫ y in z.im..w.im, K (w.re + y * I) η) from rfl]
  simp only [smul_eq_mul]
  rw [walkIntegral_add u l hcontH (hcontV.const_mul I), walkIntegral_const_mul I u l hcontV]

end QuantumZipper.CA.Homology
