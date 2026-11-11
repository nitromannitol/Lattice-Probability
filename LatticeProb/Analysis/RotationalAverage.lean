import Mathlib

/-!
# Rotational averages of functions on `ℂ`

For `Φ : ℂ → ℝ` the rotational average `avgRot Φ x = (2π)⁻¹ ∫_0^{2π} Φ (e^{iθ} x) dθ` is invariant under
rotations about `0`, smooth with compact support when `Φ` is, and pairs with rotation-invariant functions as `Φ`
does: `∫ avgRot Φ · g = ∫ Φ · g` for every rotation-invariant `g`. This is the averaging over the rotation
group `SO(2)` (Armitage-Gardiner, *Classical Potential Theory*, Section 1.4, spherical and circular means).
-/

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

noncomputable section

namespace LatticeProb.RotationalAverage

/-- The rotation `x ↦ e^{iθ} x` of the plane about `0`. -/
def rot (θ : ℝ) (x : ℂ) : ℂ := Complex.exp (θ * Complex.I) * x

/-- The rotational average `(2π)⁻¹ ∫_0^{2π} Φ (e^{iθ} x) dθ` of `Φ` over the rotations about `0`. -/
def avgRot (Φ : ℂ → ℝ) (x : ℂ) : ℝ := (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), Φ (rot θ x)

lemma rot_add (α β : ℝ) (x : ℂ) : rot α (rot β x) = rot (α + β) x := by
  simp only [rot, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma norm_rot (θ : ℝ) (x : ℂ) : ‖rot θ x‖ = ‖x‖ := by
  simp [rot, Complex.norm_exp_ofReal_mul_I]

lemma rot_periodic (θ : ℝ) (x : ℂ) : rot (θ + 2 * π) x = rot θ x := by
  simp only [rot]
  congr 1
  have h : ((θ + 2 * π : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + 2 * π * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma measurePreserving_rot (θ : ℝ) : MeasurePreserving (rot θ) volume volume := by
  have hfun : ⇑(rotation (Circle.exp θ)) = rot θ := by
    funext x
    simp [rot, rotation_apply, Circle.coe_exp]
  rw [← hfun]
  exact (rotation (Circle.exp θ)).measurePreserving

lemma measurableEmbedding_rot (θ : ℝ) : MeasurableEmbedding (rot θ) := by
  have hfun : ⇑(rotation (Circle.exp θ)) = rot θ := by
    funext x
    simp [rot, rotation_apply, Circle.coe_exp]
  rw [← hfun]
  exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding

/-- A parametric integral over a compact interval of a jointly smooth family is smooth in the parameter
(differentiation under the integral sign, by induction on the order of smoothness). -/
theorem contDiff_intervalIntegral_param (a b : ℝ) (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (Φ : ℝ × ℂ → E),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ →
        ContDiff ℝ n (fun y : ℂ => ∫ θ in a..b, Φ (θ, y)) := by
  induction n with
  | zero =>
    intro E _ _ _ Φ hΦ
    refine contDiff_zero.mpr ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := a)
      (f := fun y θ => Φ (θ, y))
      (hΦ.continuous.comp (continuous_snd.prodMk continuous_fst)) continuous_const
  | succ n ih =>
    intro E _ _ _ Φ hΦ
    set Ψ : ℝ × ℂ → (ℂ →L[ℝ] E) := fun p => (fderiv ℝ Φ p).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)
      with hΨdef
    have hfderiv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ Φ) :=
      hΦ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
    have hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ :=
      hfderiv.clm_comp contDiff_const
    have hdiff : ∀ (t : ℝ) (y : ℂ), HasFDerivAt (fun y' : ℂ => Φ (t, y')) (Ψ (t, y)) y := by
      intro t y
      have h1 : HasFDerivAt Φ (fderiv ℝ Φ (t, y)) (t, y) :=
        ((hΦ.differentiable (by simp)) (t, y)).hasFDerivAt
      have h2 : HasFDerivAt (fun y' : ℂ => ((t, y') : ℝ × ℂ)) (ContinuousLinearMap.inr ℝ ℝ ℂ) y :=
        hasFDerivAt_prodMk_right t y
      exact h1.comp y h2
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨fun y => ∫ θ in a..b, Ψ (θ, y),
      ih (ℂ →L[ℝ] E) Ψ hΨ, fun y => ?_⟩
    obtain ⟨C, hC⟩ := ((isCompact_uIcc (a := a) (b := b)).prod (isCompact_closedBall y 1)
      ).exists_bound_of_continuousOn hΨ.continuous.continuousOn
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
      (F := fun x θ => Φ (θ, x)) (F' := fun x θ => Ψ (θ, x)) (bound := fun _ => C)
      (Metric.closedBall_mem_nhds y one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Filter.Eventually.of_forall fun x =>
        (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
    · exact (hΨ.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact ae_of_all _ fun t ht x hx => hC (t, x) ⟨uIoc_subset_uIcc ht, hx⟩
    · exact ae_of_all _ fun t _ x _ => hdiff t x

/-- The rotational average of a smooth function is smooth. -/
theorem contDiff_avgRot {Φ : ℂ → ℝ} (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (avgRot Φ) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => ((p.1 : ℂ) * Complex.I)) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const
  have hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => Φ (rot p.1 p.2)) :=
    hΦ.comp ((Complex.contDiff_exp.comp h1).mul contDiff_snd)
  have hint := contDiff_infty.2 fun n => contDiff_intervalIntegral_param 0 (2 * π) n ℝ _ hP
  exact contDiff_const.mul hint

/-- A `2π`-periodic function integrated over a period is invariant under shifts of the variable. -/
lemma intervalIntegral_shift_periodic {F : ℝ → ℝ} (hF : Function.Periodic F (2 * π)) (a : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), F (θ + a) = ∫ θ in (0 : ℝ)..(2 * π), F θ := by
  rw [intervalIntegral.integral_comp_add_right F a, zero_add, add_comm (2 * π) a]
  exact hF.intervalIntegral_add_eq a 0 |>.trans (by simp)

/-- The rotational average is invariant under rotations about `0`: it is a radial function. -/
lemma avgRot_rot (Φ : ℂ → ℝ) (α : ℝ) (x : ℂ) : avgRot Φ (rot α x) = avgRot Φ x := by
  unfold avgRot
  congr 1
  have hper : Function.Periodic (fun θ : ℝ => Φ (rot θ x)) (2 * π) := fun θ => by
    simp only [rot_periodic]
  have h1 : ∫ θ in (0 : ℝ)..(2 * π), Φ (rot θ (rot α x))
      = ∫ θ in (0 : ℝ)..(2 * π), (fun θ : ℝ => Φ (rot θ x)) (θ + α) := by
    congr 1
    funext θ
    simp only [rot_add]
  rw [h1, intervalIntegral_shift_periodic hper α]

/-- A test function supported in the unit disc has a rotational average with the same properties. -/
lemma exists_radius_of_tsupport {Φ : ℂ → ℝ} (hΦc : HasCompactSupport Φ)
    (hsub : tsupport Φ ⊆ Metric.ball 0 1) : ∃ R < 1, ∀ y, Φ y ≠ 0 → ‖y‖ ≤ R := by
  obtain ⟨R, hR1, hK⟩ := exists_lt_subset_ball hΦc.isCompact.isClosed hsub
  refine ⟨R, hR1, fun y hy => ?_⟩
  have := hK (subset_tsupport _ hy)
  exact le_of_lt (by simpa using this)

lemma avgRot_eq_zero_of_norm_gt {Φ : ℂ → ℝ} {R : ℝ} (hR : ∀ y, Φ y ≠ 0 → ‖y‖ ≤ R) {x : ℂ}
    (hx : R < ‖x‖) : avgRot Φ x = 0 := by
  have h0 : ∀ θ : ℝ, Φ (rot θ x) = 0 := fun θ => by
    by_contra h
    have := hR _ h
    rw [norm_rot] at this
    linarith
  simp [avgRot, h0]

theorem avgRot_test {Φ : ℂ → ℝ} (hΦs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦc : HasCompactSupport Φ) (hsub : tsupport Φ ⊆ Metric.ball 0 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (avgRot Φ) ∧ HasCompactSupport (avgRot Φ) ∧
      tsupport (avgRot Φ) ⊆ Metric.ball 0 1 := by
  obtain ⟨R, hR1, hR⟩ := exists_radius_of_tsupport hΦc hsub
  have hcs : HasCompactSupport (avgRot Φ) :=
    HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx =>
      avgRot_eq_zero_of_norm_gt hR (not_le.mp fun h => hx (by simpa using h))
  have hsupp : tsupport (avgRot Φ) ⊆ Metric.ball 0 1 :=
    (closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hR1)
  · exact ⟨contDiff_avgRot hΦs, hcs, hsupp⟩
  · by_contra h
    exact hx (avgRot_eq_zero_of_norm_gt hR (not_le.mp (fun h' => h (by simpa using h'))))

/-- Averaging over rotations does not change the integral against a rotation-invariant function:
`∫ avgRot Φ · g = ∫ Φ · g`, by Fubini in the rotation angle and invariance of Lebesgue measure. -/
theorem integral_avgRot_mul {Φ g : ℂ → ℝ} (hΦ : Measurable Φ) (hg : Measurable g)
    (hgr : ∀ θ x, g (rot θ x) = g x) (hint : Integrable (fun x => Φ x * g x)) :
    ∫ x, avgRot Φ x * g x = ∫ x, Φ x * g x := by
  have hrotc : Continuous (fun p : ℝ × ℂ => rot p.1 p.2) := by
    unfold rot
    fun_prop
  have hmeas : Measurable (fun p : ℝ × ℂ => Φ (rot p.1 p.2) * g p.2) :=
    (hΦ.comp hrotc.measurable).mul (hg.comp measurable_snd)
  have hslice : ∀ θ : ℝ, Integrable (fun x => Φ (rot θ x) * g x) := fun θ => by
    have h := ((measurePreserving_rot θ).integrable_comp_emb (measurableEmbedding_rot θ)).2 hint
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Function.comp_apply, hgr]
  have hconst : ∀ θ : ℝ, ∫ x, ‖Φ (rot θ x) * g x‖ = ∫ x, ‖Φ x * g x‖ := fun θ => by
    calc ∫ x, ‖Φ (rot θ x) * g x‖ = ∫ x, ‖Φ (rot θ x) * g (rot θ x)‖ := by simp only [hgr]
      _ = ∫ x, ‖Φ x * g x‖ :=
        (measurePreserving_rot θ).integral_comp (measurableEmbedding_rot θ) (fun y => ‖Φ y * g y‖)
  have hH : Integrable (fun p : ℝ × ℂ => Φ (rot p.1 p.2) * g p.2)
      (((volume : Measure ℝ).restrict (Ioc 0 (2 * π))).prod volume) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun θ => hslice θ, ?_⟩
    simp only [hconst]
    exact integrable_const _
  have hswap : ∫ x, ∫ θ in (0 : ℝ)..(2 * π), Φ (rot θ x) * g x
      = ∫ θ in (0 : ℝ)..(2 * π), ∫ x, Φ (rot θ x) * g x := by
    simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
    exact integral_integral_swap (f := fun x θ => Φ (rot θ x) * g x) hH.swap
  have hinner : ∀ θ : ℝ, ∫ x, Φ (rot θ x) * g x = ∫ x, Φ x * g x := fun θ => by
    calc ∫ x, Φ (rot θ x) * g x = ∫ x, Φ (rot θ x) * g (rot θ x) := by simp only [hgr]
      _ = ∫ x, Φ x * g x :=
        (measurePreserving_rot θ).integral_comp (measurableEmbedding_rot θ) (fun y => Φ y * g y)
  have step1 : ∫ x, avgRot Φ x * g x = ∫ x, (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), Φ (rot θ x) * g x := by
    congr 1
    funext x
    rw [avgRot, mul_assoc, ← intervalIntegral.integral_mul_const]
  rw [step1, integral_const_mul, hswap]
  simp only [hinner, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp

/-- A rotation of the point `R e^{ia}` is the point of the circle `∂B_R(0)` at angle `θ + a`. -/
lemma rot_eq_circleMap (θ R a : ℝ) :
    rot θ ((R : ℂ) * Complex.exp (a * Complex.I)) = circleMap 0 R (θ + a) := by
  simp only [rot, circleMap, zero_add]
  rw [show ((θ + a : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + (a : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add]
  ring

/-- For `y ≠ 0` the rotational average of `Φ` at `y` is the average of `Φ` over the circle `∂B_{|y|}(0)`. -/
lemma avgRot_eq_circleAverage (Φ : ℂ → ℝ) {y : ℂ} :
    avgRot Φ y = Real.circleAverage Φ 0 ‖y‖ := by
  have hy' : y = ((‖y‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg y : ℝ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I y).symm
  have hper : Function.Periodic (fun θ : ℝ => Φ (circleMap 0 ‖y‖ θ)) (2 * π) := fun θ => by
    show Φ (circleMap 0 ‖y‖ (θ + 2 * π)) = Φ (circleMap 0 ‖y‖ θ)
    have h : circleMap 0 ‖y‖ (θ + 2 * π) = circleMap 0 ‖y‖ θ := by
      unfold circleMap
      rw [show ((θ + 2 * π : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [h]
  have key : ∀ θ : ℝ, Φ (rot θ y) = Φ (circleMap 0 ‖y‖ (θ + Complex.arg y)) := fun θ => by
    rw [congrArg (rot θ) hy', rot_eq_circleMap]
  have h1 : ∫ θ in (0 : ℝ)..(2 * π), Φ (rot θ y)
      = ∫ θ in (0 : ℝ)..(2 * π), (fun θ : ℝ => Φ (circleMap 0 ‖y‖ θ)) (θ + Complex.arg y) := by
    simp_rw [key]
  rw [Real.circleAverage_def, smul_eq_mul, avgRot, h1, intervalIntegral_shift_periodic hper]

end LatticeProb.RotationalAverage
