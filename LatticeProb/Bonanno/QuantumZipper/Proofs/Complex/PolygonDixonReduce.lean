/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.PolygonDixonReduce at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.PolygonDixonBasic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.PolygonWinding

/-!
# Dixon's theorem: reduction to the two-variable Cauchy kernel (EXT-CA node H3, part 2)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "H. Homology Cauchy", node H3 (Dixon's theorem).

This file contains the *algebraic* end of Dixon's proof: the linearity of the polygon integral in
its integrand, and the derivation of

`∮_p f dz = 0`   (for `f` holomorphic on an open `U`, `p` a closed polygon in `U` with
`wind p a = 0` for all `a ∉ U`)

from the **two-variable Cauchy kernel lemma**: for every `F` holomorphic on `U` and every `z` off
the carrier with `wind p z = 0`, the Cauchy-type integral `∮_p F(w)/(w - z) dw` vanishes.  The
kernel lemma is the analytic core of Dixon's proof (the function `h(z) = ∮_p sec f z w dw` is
holomorphic on `U` by Morera + Fubini, `h₂(z) = ∮_p f(w)/(w-z) dw` is holomorphic where the
winding number vanishes, the two glue to an entire function which is bounded and tends to `0` at
`∞`); it is proved in `PolygonDixonIntegral.lean`.

## The reduction

Fix `z` far from the carrier, so that `z ∉ |p|` and `wind p z = 0` (`wind_eq_zero_of_large`).
Dixon's key identity, applied to `f` and to `w ↦ w * f(w)` at the point `z`, gives
`∮_p f(w)/(w-z) dw = 0` and `∮_p w f(w)/(w-z) dw = 0`; since `w f(w)/(w-z) = f(w) + z f(w)/(w-z)`
pointwise on the carrier (where `w ≠ z`), linearity of the integral yields `∮_p f = 0`.

## Sources

S. A. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. Amer. Math. Soc. **29** (1971)
625-626.  R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser 2021), Ch. 4
(homology form of Cauchy's theorem).
-/

noncomputable section

open Set Metric Filter Complex Real
open scoped Topology Convex

namespace QuantumZipper.CA.Homology

/-! ## Congruence and linearity of the polygon integral -/

/-- The polygon integral only depends on the integrand on the carrier. -/
theorem walkIntegral_congr {f g : ℂ → ℂ} {u : ℂ} {l : List ℂ}
    (h : ∀ z ∈ walkCarrier u l, f z = g z) : walkIntegral f u l = walkIntegral g u l := by
  induction l generalizing u with
  | nil => simp [walkIntegral, walkIntegralCLM]
  | cons v t ih =>
    have hedge : (∫ᶜ z in Path.segment u v, dzForm f z)
        = ∫ᶜ z in Path.segment u v, dzForm g z := by
      rw [curveIntegral_segment_dzForm_eq, curveIntegral_segment_dzForm_eq]
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        rwa [← uIcc_of_le zero_le_one]
      rw [h _ (Or.inl (lineMap_mem_segment u v hs'))]
    rw [walkIntegral_cons, walkIntegral_cons, hedge, ih (fun z hz => h z (Or.inr hz))]

/-- Additivity of the polygon integral in the integrand. -/
theorem walkIntegral_add {f g : ℂ → ℂ} (u : ℂ) (l : List ℂ)
    (hf : ContinuousOn f (walkCarrier u l)) (hg : ContinuousOn g (walkCarrier u l)) :
    walkIntegral (fun z => f z + g z) u l = walkIntegral f u l + walkIntegral g u l := by
  induction l generalizing u with
  | nil => simp [walkIntegral, walkIntegralCLM]
  | cons v t ih =>
    have hseg : segment ℝ u v ⊆ walkCarrier u (v :: t) := fun z hz => Or.inl hz
    have htail : walkCarrier v t ⊆ walkCarrier u (v :: t) := fun z hz => Or.inr hz
    have hfseg : ContinuousOn f (segment ℝ u v) := hf.mono hseg
    have hgseg : ContinuousOn g (segment ℝ u v) := hg.mono hseg
    have hedge : (∫ᶜ z in Path.segment u v, dzForm (fun z => f z + g z) z)
        = (∫ᶜ z in Path.segment u v, dzForm f z)
          + ∫ᶜ z in Path.segment u v, dzForm g z := by
      rw [curveIntegral_segment_dzForm_eq (fun z => f z + g z),
        curveIntegral_segment_dzForm_eq f, curveIntegral_segment_dzForm_eq g]
      have hint := intervalIntegral.integral_add (intervalIntegrable_segment_mul hfseg)
        (intervalIntegrable_segment_mul hgseg)
      rw [← hint]
      refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    rw [walkIntegral_cons, walkIntegral_cons, walkIntegral_cons, hedge,
      ih v (hf.mono htail) (hg.mono htail)]
    abel

/-- Negation of the polygon integral. -/
theorem walkIntegral_neg {f : ℂ → ℂ} (u : ℂ) (l : List ℂ)
    (hf : ContinuousOn f (walkCarrier u l)) :
    walkIntegral (fun z => -f z) u l = -walkIntegral f u l := by
  induction l generalizing u with
  | nil => simp [walkIntegral, walkIntegralCLM]
  | cons v t ih =>
    have hseg : segment ℝ u v ⊆ walkCarrier u (v :: t) := fun z hz => Or.inl hz
    have htail : walkCarrier v t ⊆ walkCarrier u (v :: t) := fun z hz => Or.inr hz
    have hfseg : ContinuousOn f (segment ℝ u v) := hf.mono hseg
    have hedge : (∫ᶜ z in Path.segment u v, dzForm (fun z => -f z) z)
        = -∫ᶜ z in Path.segment u v, dzForm f z := by
      rw [curveIntegral_segment_dzForm_eq (fun z => -f z),
        curveIntegral_segment_dzForm_eq f]
      have hint : (∫ t in (0:ℝ)..1, -((fun s : ℝ => f (AffineMap.lineMap u v s) * (v - u)) t))
          = -∫ t in (0:ℝ)..1, f (AffineMap.lineMap u v t) * (v - u) :=
        intervalIntegral.integral_neg
      rw [← hint]
      refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    rw [walkIntegral_cons, walkIntegral_cons, hedge, ih v (hf.mono htail)]
    ring

/-- Scalar multiples of a polygon integral. -/
theorem walkIntegral_const_mul {f : ℂ → ℂ} (c : ℂ) (u : ℂ) (l : List ℂ)
    (hf : ContinuousOn f (walkCarrier u l)) :
    walkIntegral (fun z => c * f z) u l = c * walkIntegral f u l := by
  induction l generalizing u with
  | nil => simp [walkIntegral, walkIntegralCLM]
  | cons v t ih =>
    have hseg : segment ℝ u v ⊆ walkCarrier u (v :: t) := fun z hz => Or.inl hz
    have htail : walkCarrier v t ⊆ walkCarrier u (v :: t) := fun z hz => Or.inr hz
    have hfseg : ContinuousOn f (segment ℝ u v) := hf.mono hseg
    have hedge : (∫ᶜ z in Path.segment u v, dzForm (fun z => c * f z) z)
        = c * ∫ᶜ z in Path.segment u v, dzForm f z := by
      rw [curveIntegral_segment_dzForm_eq (fun z => c * f z), curveIntegral_segment_dzForm_eq f]
      have hfun : (fun t : ℝ => c * f (AffineMap.lineMap u v t) * (v - u))
          = fun t : ℝ => c * (f (AffineMap.lineMap u v t) * (v - u)) := by
        funext t
        ring
      rw [hfun, intervalIntegral.integral_const_mul]
    rw [walkIntegral_cons, walkIntegral_cons, hedge, ih v (hf.mono htail)]
    ring

/-! ## A point far from the carrier -/

/-- There are points off the carrier with vanishing winding number, far enough to be used as the
base point of Dixon's identity (`wind_eq_zero_of_large`). -/
theorem exists_notMem_carrier_wind_eq_zero (p : Polygon) (hcl : p.last = p.head) :
    ∃ z : ℂ, z ∉ p.carrier ∧ wind p z = 0 := by
  have hL : (0 : ℝ) ≤ p.length * ‖(2 * π * I)⁻¹‖ :=
    mul_nonneg (by rw [Polygon.length_def]; exact walkLength_nonneg _ _) (norm_nonneg _)
  have hW : (0 : ℝ) ≤ walkLength p.head p.rest := walkLength_nonneg _ _
  have hH : (0 : ℝ) ≤ ‖p.head‖ := norm_nonneg _
  have hpos : (0 : ℝ) < 1 + (‖p.head‖ + walkLength p.head p.rest)
      + p.length * ‖(2 * π * I)⁻¹‖ + 2 := by linarith
  refine ⟨(((1 + (‖p.head‖ + walkLength p.head p.rest)) + p.length * ‖(2 * π * I)⁻¹‖ + 2 : ℝ)
    : ℂ), ?_, ?_⟩
  · intro hmem
    have h1 := carrier_subset_ball p hmem
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos] at h1
    linarith
  · refine wind_eq_zero_of_large p hcl (carrier_subset_ball p) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    linarith

/-! ## The reduction -/

/-- **Dixon's theorem, reduced form.**  If the two-variable Cauchy kernel lemma holds, then the
polygon integral of a holomorphic function over a closed polygon with vanishing winding number off
`U` is zero. -/
theorem walkIntegral_eq_zero_of_cauchyKernel {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {p : Polygon} (hcl : p.last = p.head) (hpU : p.carrier ⊆ U)
    (hw : ∀ a ∉ U, wind p a = 0)
    (hkey : ∀ (F : ℂ → ℂ), DifferentiableOn ℂ F U → ∀ z : ℂ, z ∉ p.carrier → wind p z = 0 →
      walkIntegral (fun w => F w / (w - z)) p.head p.rest = 0) :
    walkIntegral f p.head p.rest = 0 := by
  obtain ⟨z, hzC, hzw⟩ := exists_notMem_carrier_wind_eq_zero p hcl
  have hzU : z ∉ p.carrier := hzC
  -- the two instances of the kernel lemma
  have h1 : walkIntegral (fun w => f w / (w - z)) p.head p.rest = 0 := hkey f hf z hzU hzw
  have h2 : walkIntegral (fun w => (w * f w) / (w - z)) p.head p.rest = 0 :=
    hkey (fun w => w * f w) (differentiableOn_id.mul hf) z hzU hzw
  -- continuity of the integrands on the carrier
  have hcontf : ContinuousOn f p.carrier := hf.continuousOn.mono hpU
  have hcontq : ContinuousOn (fun w => f w / (w - z)) p.carrier :=
    hcontf.div ((continuous_id.sub continuous_const).continuousOn)
      (fun w hw' => sub_ne_zero.mpr (fun h => hzC (h ▸ hw')))
  have hcontz : ContinuousOn (fun w => z * (f w / (w - z))) p.carrier :=
    continuousOn_const.mul hcontq
  -- the pointwise identity on the carrier turns `w f w / (w - z)` into `f + z f/(w - z)`
  have hpoint : ∀ w ∈ p.carrier, (w * f w) / (w - z) = f w + z * (f w / (w - z)) := by
    intro w hw'
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr fun h => hzC (h ▸ hw')
    field_simp
    ring
  have hchain : walkIntegral (fun w => (w * f w) / (w - z)) p.head p.rest
      = walkIntegral f p.head p.rest := by
    rw [walkIntegral_congr (fun w hw' => hpoint w hw'),
      walkIntegral_add p.head p.rest hcontf hcontz,
      walkIntegral_const_mul z p.head p.rest hcontq, h1, mul_zero, add_zero]
  rw [hchain] at h2
  exact h2

end QuantumZipper.CA.Homology
