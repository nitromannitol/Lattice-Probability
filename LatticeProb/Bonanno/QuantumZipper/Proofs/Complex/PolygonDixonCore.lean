/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.PolygonDixonCore at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.PolygonDixonFubini
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Dixon's theorem: the parametric polygon integral is holomorphic (EXT-CA node H3, part 4)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "H. Homology Cauchy", node H3 (Dixon's theorem).

For a kernel `K : ℂ → ℂ → ℂ` continuous on a rectangle times the carrier of a polygon and
holomorphic in its first variable, Morera's theorem gives that the parametric polygon integral
`z ↦ ∮_p K z w dw` is holomorphic where the "inner" rectangle integrals vanish.  Applied to the
Dixon kernel `sec F z w = (F z - F w)/(z - w)` this yields the function
`h(z) = ∮_p sec F z w dw` holomorphic on the domain `U` of `F`, and applied to the Cauchy kernel
`K z w = F w / (w - z)` it yields `h₂(z) = ∮_p F w/(w - z) dw` holomorphic off the carrier.

## Sources

S. A. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. Amer. Math. Soc. **29** (1971)
625-626.  R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser 2021),
Theorem 10.11 (Morera for parametric integrals), Exercise 2.9 (the norm bound).
-/

noncomputable section

open Set Metric Filter Complex Real AffineMap MeasureTheory
open scoped Topology Convex Interval

namespace QuantumZipper.CA.Homology

/-- A kernel continuous on `s × t` is continuous in its first variable at a fixed point of
`t`. -/
theorem continuousOn_slice_right {f : ℂ × ℂ → ℂ} {s t : Set ℂ} {η : ℂ}
    (hf : ContinuousOn f (s ×ˢ t)) (hη : η ∈ t) : ContinuousOn (fun ζ => f (ζ, η)) s :=
  hf.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℂ => η)).continuousOn
    (fun _ hζ => mk_mem_prod hζ hη)

/-! ## Two elementary vanishing lemmas for the polygon integral -/

/-- Membership in `[[a,b]]` from membership in the interior interval. -/
theorem mem_uIcc_of_mem_Ioo_minmax {a b t : ℝ} (h : t ∈ Ioo (min a b) (max a b)) : t ∈ [[a, b]] :=
  ⟨le_of_lt h.1, le_of_lt h.2⟩

/-- The integral of a 1-form along a segment over which the form vanishes is zero. -/
theorem curveIntegral_segment_dzForm_eq_zero {f : ℂ → ℂ} {a b : ℂ}
    (h : ∀ z ∈ segment ℝ a b, f z = 0) : (∫ᶜ z in Path.segment a b, dzForm f z) = 0 := by
  rw [curveIntegral_segment_dzForm_eq]
  trans ∫ t in (0 : ℝ)..1, (0 : ℂ)
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [h _ (lineMap_mem_segment_uIcc a b ht), zero_mul]
  · simp

/-- **A polygon integral vanishes if the integrand does.**  No continuity hypothesis is needed. -/
theorem walkIntegral_eq_zero_of_eq_zero_on_carrier {f : ℂ → ℂ} (u : ℂ) (l : List ℂ)
    (h : ∀ z ∈ walkCarrier u l, f z = 0) : walkIntegral f u l = 0 := by
  induction l generalizing u with
  | nil => simp [walkIntegral, walkIntegralCLM]
  | cons v t ih =>
    have hseg : segment ℝ u v ⊆ walkCarrier u (v :: t) := fun z hz => Or.inl hz
    have htail : walkCarrier v t ⊆ walkCarrier u (v :: t) := fun z hz => Or.inr hz
    rw [show walkIntegral f u (v :: t)
        = (∫ᶜ z in Path.segment u v, dzForm f z) + walkIntegral f v t from rfl,
      curveIntegral_segment_dzForm_eq_zero (fun z hz => h z (hseg hz)),
      ih (u := v) (fun z hz => h z (htail hz))]
    simp

/-! ## Continuity of the parametric polygon integral -/

/-- **Continuity of a parametric polygon integral.**  If the kernel is continuous on
`s × |p|` and bounded there by `C`, then `z ↦ ∮_p K z w dw` is continuous on `s`. -/
theorem continuousOn_walkIntegral_param {K : ℂ → ℂ → ℂ} {s : Set ℂ} {u : ℂ} {l : List ℂ} {C : ℝ}
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (s ×ˢ walkCarrier u l))
    (hC : ∀ z ∈ s, ∀ w ∈ walkCarrier u l, ‖K z w‖ ≤ C) :
    ContinuousOn (fun z => walkIntegral (fun w => K z w) u l) s := by
  induction l generalizing u with
  | nil => simpa only [walkIntegral, walkIntegralCLM] using continuousOn_const (c := (0 : ℂ))
  | cons v t ih =>
    have hseg : segment ℝ u v ⊆ walkCarrier u (v :: t) := fun z hz => Or.inl hz
    have htail : walkCarrier v t ⊆ walkCarrier u (v :: t) := fun z hz => Or.inr hz
    have hfst : Continuous fun p : ℂ × ℝ => p.1 := continuous_fst
    have hsnd : Continuous fun p : ℂ × ℝ => p.2 := continuous_snd
    have hlm : Continuous fun p : ℂ × ℝ => lineMap u v p.2 := (continuous_lineMap u v).comp hsnd
    have hpair : ContinuousOn (fun p : ℂ × ℝ => (p.1, lineMap u v p.2)) (s ×ˢ [[(0 : ℝ), 1]]) :=
      (hfst.prodMk hlm).continuousOn
    have hker : ContinuousOn (fun p : ℂ × ℝ => K p.1 (lineMap u v p.2) * (v - u))
        (s ×ˢ [[(0 : ℝ), 1]]) :=
      (hK.comp hpair (fun p hp => mk_mem_prod hp.1
        (Or.inl (lineMap_mem_segment_uIcc u v hp.2)))).mul continuousOn_const
    have hbound : ∀ z ∈ s, ∀ τ ∈ Ι (0 : ℝ) 1,
        ‖K z (lineMap u v τ) * (v - u)‖ ≤ C * ‖v - u‖ := by
      intro z hz τ hτ
      calc ‖K z (lineMap u v τ) * (v - u)‖ = ‖K z (lineMap u v τ)‖ * ‖v - u‖ := norm_mul _ _
        _ ≤ C * ‖v - u‖ :=
          mul_le_mul_of_nonneg_right (hC z hz _ (hseg (lineMap_mem_segment_uIoc u v hτ)))
            (norm_nonneg _)
    have hedge : ContinuousOn (fun z => ∫ᶜ w in Path.segment u v, dzForm (K z) w) s :=
      (continuousOn_intervalIntegral_param (K := fun z τ => K z (lineMap u v τ) * (v - u))
        (C := C * ‖v - u‖) hker hbound).congr fun z _ => curveIntegral_segment_dzForm_eq (K z) u v
    have hrest : ContinuousOn (fun z => walkIntegral (fun w => K z w) v t) s :=
      ih (u := v) (hK.mono (Set.prod_mono_right htail)) (fun z hz w hw => hC z hz w (htail hw))
    exact (hedge.add hrest).congr fun z _ => rfl

/-- **Continuity at a point of the parametric polygon integral.** -/
theorem continuousAt_walkIntegral_of_continuousOn {K : ℂ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ} {l : List ℂ} (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (U ×ˢ walkCarrier u l))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ContinuousAt (fun z => walkIntegral (fun w => K z w) u l) z₀ := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz₀)
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  have hsU : closedBall z₀ (r / 2) ⊆ U := fun z hz =>
    hrU (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith)))
  have hK' : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (closedBall z₀ (r / 2) ×ˢ walkCarrier u l) :=
    hK.mono (Set.prod_mono hsU Subset.rfl)
  have hcp : IsCompact (closedBall z₀ (r / 2) ×ˢ walkCarrier u l) :=
    (isCompact_closedBall z₀ (r / 2)).prod (isCompact_walkCarrier u l)
  obtain ⟨C, hC⟩ := hcp.exists_bound_of_continuousOn hK'
  have hcont := continuousOn_walkIntegral_param hK' (fun z hz w hw => hC _ (mk_mem_prod hz hw))
  exact hcont.continuousAt (closedBall_mem_nhds z₀ hr2)

/-! ## Morera's step for parametric polygon integrals -/

/-- **Morera's step.**  If the kernel is continuous on the rectangle times the carrier and, for
every point `η` of the carrier, the boundary integral of `ζ ↦ K ζ η` over the rectangle vanishes,
then `∮_{∂R} ∮_p K(z,w) dw dz = 0`. -/
theorem wedgeIntegral_add_walkIntegral_eq_zero {K : ℂ → ℂ → ℂ} {z w u : ℂ} {l : List ℂ}
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (Rectangle z w ×ˢ walkCarrier u l))
    (hcon : ∀ η ∈ walkCarrier u l,
      wedgeIntegral z w (fun ζ => K ζ η) + wedgeIntegral w z (fun ζ => K ζ η) = 0) :
    wedgeIntegral z w (fun ζ => walkIntegral (fun η => K ζ η) u l)
      + wedgeIntegral w z (fun ζ => walkIntegral (fun η => K ζ η) u l) = 0 := by
  have hT : IsCompact (walkCarrier u l) := isCompact_walkCarrier u l
  have hpm : (z.im : ℝ) ∈ [[z.im, w.im]] := left_mem_uIcc
  have hqm : (w.im : ℝ) ∈ [[z.im, w.im]] := right_mem_uIcc
  have hpr : (z.re : ℝ) ∈ [[z.re, w.re]] := left_mem_uIcc
  have hqr : (w.re : ℝ) ∈ [[z.re, w.re]] := right_mem_uIcc
  have hK' : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (Rectangle w z ×ˢ walkCarrier u l) :=
    hK.mono (Set.prod_mono (by
      intro ζ hζ
      rw [Rectangle, mem_reProdIm] at hζ ⊢
      exact ⟨by simpa only [uIcc_comm] using hζ.1, by simpa only [uIcc_comm] using hζ.2⟩)
      Subset.rfl)
  have hA₁ : ContinuousOn (fun η => ∫ x in z.re..w.re, K (x + z.im * I) η)
      (walkCarrier u l) :=
    continuousOn_intervalIntegral_param_snd (φ := fun x : ℝ => x + z.im * I)
      (S := Rectangle z w) (T := walkCarrier u l) (by fun_prop)
      (fun x hx => add_mul_I_mem_Rectangle hx hpm) hT hK
  have hA₂ : ContinuousOn (fun η => ∫ y in z.im..w.im, K (w.re + y * I) η)
      (walkCarrier u l) :=
    continuousOn_intervalIntegral_param_snd (φ := fun y : ℝ => w.re + y * I)
      (S := Rectangle z w) (T := walkCarrier u l) (by fun_prop)
      (fun y hy => add_mul_I_mem_Rectangle hqr hy) hT hK
  have hcontA : ContinuousOn (fun η => wedgeIntegral z w (fun ζ => K ζ η)) (walkCarrier u l) :=
    (hA₁.add (hA₂.const_smul I)).congr fun η _ => rfl
  have hB₁ : ContinuousOn (fun η => ∫ x in w.re..z.re, K (x + w.im * I) η)
      (walkCarrier u l) :=
    continuousOn_intervalIntegral_param_snd (φ := fun x : ℝ => x + w.im * I)
      (S := Rectangle z w) (T := walkCarrier u l) (by fun_prop)
      (fun x hx => add_mul_I_mem_Rectangle (by simpa only [uIcc_comm] using hx) hqm) hT hK
  have hB₂ : ContinuousOn (fun η => ∫ y in w.im..z.im, K (z.re + y * I) η)
      (walkCarrier u l) :=
    continuousOn_intervalIntegral_param_snd (φ := fun y : ℝ => z.re + y * I)
      (S := Rectangle z w) (T := walkCarrier u l) (by fun_prop)
      (fun y hy => add_mul_I_mem_Rectangle hpr (by simpa only [uIcc_comm] using hy)) hT hK
  have hcontB : ContinuousOn (fun η => wedgeIntegral w z (fun ζ => K ζ η)) (walkCarrier u l) :=
    (hB₁.add (hB₂.const_smul I)).congr fun η _ => rfl
  rw [wedgeIntegral_walkIntegral_swap hK, wedgeIntegral_walkIntegral_swap hK',
    ← walkIntegral_add u l hcontA hcontB]
  exact walkIntegral_eq_zero_of_eq_zero_on_carrier u l fun η hη => hcon η hη

/-! ## The Dixion kernel `sec` and the Cauchy kernel -/

/-- **The function `h z = ∮_p sec F z w dw` is holomorphic on the domain of `F`.** -/
theorem differentiableOn_walkIntegral_sec {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {p : Polygon} (hpU : p.carrier ⊆ U) :
    DifferentiableOn ℂ (fun z => walkIntegral (fun w => sec F z w) p.head p.rest) U := by
  rw [← isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU]
  refine ⟨fun z w hzw => add_eq_zero_iff_eq_neg.mp (wedgeIntegral_add_walkIntegral_eq_zero
    ((continuousOn_sec hU hF).mono (Set.prod_mono hzw hpU)) ?_), ?_⟩
  · intro η hη
    rw [wedgeIntegral_add_wedgeIntegral_eq]
    refine integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
      (fun ζ => sec F ζ η) z w {η} (Set.countable_singleton η) ?_ ?_
    · exact continuousOn_slice_right
        ((continuousOn_sec hU hF).mono (Set.prod_mono hzw hpU)) hη
    · intro x hx
      have hxne : x ≠ η := fun h => hx.2 (by simpa [h])
      have hxU : x ∈ U := hzw (by
        rw [Rectangle, mem_reProdIm]
        exact ⟨mem_uIcc_of_mem_Ioo_minmax hx.1.1, mem_uIcc_of_mem_Ioo_minmax hx.1.2⟩)
      have hd1 : DifferentiableAt ℂ (fun ζ => (F ζ - F η) / (ζ - η)) x :=
        ((hF.differentiableAt (hU.mem_nhds hxU)).sub (differentiableAt_const (c := F η))).div
          (differentiableAt_id.sub (differentiableAt_const (c := η))) (sub_ne_zero.mpr hxne)
      have hev : (fun ζ : ℂ => sec F ζ η) =ᶠ[𝓝 x] (fun ζ => (F ζ - F η) / (ζ - η)) := by
        filter_upwards [eventually_ne_nhds hxne] with ζ hζ
        exact sec_of_ne hζ
      exact hd1.congr_of_eventuallyEq hev
  · intro z₀ hz₀
    exact (continuousAt_walkIntegral_of_continuousOn hU
      ((continuousOn_sec hU hF).mono (Set.prod_mono Subset.rfl hpU)) hz₀).continuousWithinAt

/-- The Cauchy kernel `(z,w) ↦ F w/(w - z)` is continuous off the carrier times the carrier. -/
theorem continuousOn_cauchyKernel_prod {U : Set ℂ} (_hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {p : Polygon} (hpU : p.carrier ⊆ U) :
    ContinuousOn (fun q : ℂ × ℂ => F q.2 / (q.2 - q.1)) (p.carrierᶜ ×ˢ p.carrier) := by
  have hFc : ContinuousOn (fun q : ℂ × ℂ => F q.2) (p.carrierᶜ ×ˢ p.carrier) :=
    (hF.continuousOn.mono hpU).comp
      (continuous_snd : Continuous fun q : ℂ × ℂ => q.2).continuousOn (fun q hq => hq.2)
  refine hFc.div (((continuous_snd : Continuous fun q : ℂ × ℂ => q.2).sub
    (continuous_fst : Continuous fun q : ℂ × ℂ => q.1)).continuousOn) fun q hq => ?_
  exact sub_ne_zero.mpr fun h => hq.1 (h ▸ hq.2)

/-- **The function `h₂ z = ∮_p F w/(w - z) dw` is holomorphic off the carrier.** -/
theorem differentiableOn_walkIntegral_cauchy {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {p : Polygon} (hpU : p.carrier ⊆ U) :
    DifferentiableOn ℂ (fun z => walkIntegral (fun w => F w / (w - z)) p.head p.rest)
      p.carrierᶜ := by
  have hopen : IsOpen p.carrierᶜ := (Polygon.isCompact_carrier p).isClosed.isOpen_compl
  have hK := continuousOn_cauchyKernel_prod hU hF hpU
  rw [← isConservativeOn_and_continuousOn_iff_isDifferentiableOn hopen]
  refine ⟨fun z w hzw => add_eq_zero_iff_eq_neg.mp (wedgeIntegral_add_walkIntegral_eq_zero
    (hK.mono (Set.prod_mono hzw Subset.rfl)) ?_), ?_⟩
  · intro η hη
    rw [wedgeIntegral_add_wedgeIntegral_eq]
    refine integral_boundary_rect_eq_zero_of_differentiableOn (fun ζ => F η / (η - ζ)) z w ?_
    have hnum : DifferentiableOn ℂ (fun _ : ℂ => F η) (Rectangle z w) :=
      differentiableOn_const (c := F η)
    have hden : DifferentiableOn ℂ (fun ζ : ℂ => η - ζ) (Rectangle z w) :=
      (differentiableOn_const (c := η)).sub differentiableOn_id
    exact hnum.div hden fun ζ hζ => sub_ne_zero.mpr fun h => hzw hζ (h ▸ hη)
  · intro z₀ hz₀
    exact (continuousAt_walkIntegral_of_continuousOn hopen hK hz₀).continuousWithinAt

end QuantumZipper.CA.Homology
