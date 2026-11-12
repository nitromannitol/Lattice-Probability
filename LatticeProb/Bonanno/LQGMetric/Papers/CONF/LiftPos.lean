/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.LiftPos at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.Lift
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBdy
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic

/-!
# S-PosLift: positive Jordan lifts of `∂𝓑^•_s` (DEC-D (a))

Node **S-PosLift** of decision D-D1 (`decisions/DEC-D.md` (a): "a package node S-PosLift:
∀ t > 0, ∃ φ θ, IsPosJordanLift (∂𝓑^•_t) z φ θ", from J1/J2 plus orientation).
Route (DEC-D: "orientation from J2"): `f` is the Carathéodory map of DEC-B J2 onto the inverted
exterior `jordanOmega` (`jo_disc_map`, task P2-M2I), with `f 0 = 0`; `φ(t) := z + 1/f(e^{-it})`.
Writing `f(w) = w g(w)` with `g` continuous and zero-free on the closed disc (`g(0) = f′(0) ≠ 0`
by QuantumZipper `Koebe.deriv_ne_zero_of_injOn`), a continuous logarithm `Λ` of
`(σ, t) ↦ g(σ e^{-it})` (mathlib homotopy lifting `IsCoveringMap.liftHomotopy` for
`Complex.isCoveringMap_exp`) gives the angle `θ(t) = t − Im Λ(1, t)`, and `Λ(1, t + 2π) = Λ(1, t)`
because both lift the same homotopy from the same constant. Own elementary argument (standard).
The hypotheses are those of J1/J2 (`gm_filledBall_conformal`); `FilledBallBdyLC` is the open node
J1b of task P2-M2I.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter

namespace LQGMetric.CONF.DD

open LQGMetric.Blueprint

/-- positive Jordan lift of `Γ` around `z` from a disc map `f` onto the inverted exterior -/
theorem posLift_of_disc_map {Γ : Set ℂ} {z : ℂ} {f : ℂ → ℂ} (hfc : ContinuousOn f (closedBall 0 1))
    (hfi : InjOn f (closedBall 0 1)) (hfd : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0 = 0)
    (hfs : f '' sphere 0 1 = (fun x => (x - z)⁻¹) '' Γ) :
    ∃ φ θ, IsPosJordanLift Γ z φ θ := by
  classical
  -- `g = f(w)/w`, `g(0) = f′(0)`
  set g : ℂ → ℂ := fun w => if w = 0 then deriv f 0 else f w / w with hg
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hd0 : deriv f 0 ≠ 0 :=
    QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd
      (hfi.mono ball_subset_closedBall) h0b
  have hfne : ∀ w ∈ closedBall (0 : ℂ) 1, w ≠ 0 → f w ≠ 0 := fun w hw hw0 h =>
    hw0 (hfi hw (mem_closedBall_self zero_le_one) (h.trans hf0.symm))
  have hgne : ∀ w ∈ closedBall (0 : ℂ) 1, g w ≠ 0 := by
    intro w hw
    by_cases hw0 : w = 0
    · simp only [hg, hw0, if_true]; exact hd0
    · simp only [hg, hw0, if_false]; exact div_ne_zero (hfne w hw hw0) hw0
  have hgc : ContinuousOn g (closedBall 0 1) := by
    intro w hw
    by_cases hw0 : w = 0
    · subst hw0
      have hda : HasDerivAt f (deriv f 0) 0 :=
        ((hfd 0 h0b).differentiableAt (isOpen_ball.mem_nhds h0b)).hasDerivAt
      have ht := hda.tendsto_slope_zero
      simp only [zero_add, hf0, sub_zero] at ht
      have hca : ContinuousAt g 0 := by
        rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
        have he : g =ᶠ[𝓝[≠] (0 : ℂ)] fun t => t⁻¹ • f t := by
          filter_upwards [self_mem_nhdsWithin] with t ht0
          have ht0' : t ≠ 0 := ht0
          simp only [hg, if_neg ht0', smul_eq_mul, div_eq_mul_inv]; ring
        simp only [hg, if_true]
        exact ht.congr' he.symm
      exact hca.continuousWithinAt
    · have hcw : ContinuousWithinAt (fun w => f w / w) (closedBall 0 1) w :=
        (hfc w hw).div continuousWithinAt_id hw0
      refine hcw.congr_of_eventuallyEq ?_ (by simp only [hg, if_neg hw0])
      filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hw0)] with t ht0
      simp only [hg, if_neg (show t ≠ 0 from ht0)]
  -- the homotopy `(σ, t) ↦ g(σ e^{-it})` and its logarithm
  have hmem : ∀ (σ : unitInterval) (t : ℝ),
      (σ : ℂ) * Complex.exp (-(t : ℂ) * Complex.I) ∈ closedBall (0 : ℂ) 1 := by
    intro σ t
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_exp]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg σ.2.1]
    have : (-(t : ℂ) * Complex.I).re = 0 := by simp
    rw [this, Real.exp_zero, mul_one]; exact σ.2.2
  have hHc : Continuous fun p : unitInterval × ℝ =>
      g ((p.1 : ℂ) * Complex.exp (-(p.2 : ℂ) * Complex.I)) :=
    hgc.comp_continuous (by fun_prop) (fun p => hmem p.1 p.2)
  let H : C(unitInterval × ℝ, {w : ℂ // w ≠ 0}) :=
    ⟨fun p => ⟨g ((p.1 : ℂ) * Complex.exp (-(p.2 : ℂ) * Complex.I)), hgne _ (hmem p.1 p.2)⟩,
      hHc.subtype_mk _⟩
  have hg0 : g 0 ≠ 0 := hgne 0 (mem_closedBall_self zero_le_one)
  let c0 : C(ℝ, ℂ) := ContinuousMap.const ℝ (Complex.log (g 0))
  have H0 : ∀ t, H (0, t) = (fun w : ℂ => (⟨Complex.exp w, Complex.exp_ne_zero w⟩ :
      {w : ℂ // w ≠ 0})) (c0 t) := by
    intro t
    apply Subtype.ext
    simp [H, c0, Complex.exp_log hg0]
  set Λ := Complex.isCoveringMap_exp.liftHomotopy H c0 H0 with hΛ
  have hΛe : ∀ p, Complex.exp (Λ p) = g ((p.1 : ℂ) * Complex.exp (-(p.2 : ℂ) * Complex.I)) := by
    intro p
    have := congrArg Subtype.val
      (congr_fun (Complex.isCoveringMap_exp.liftHomotopy_lifts H c0 H0) p)
    exact this
  have hΛ0 : ∀ t, Λ (0, t) = Complex.log (g 0) := fun t =>
    Complex.isCoveringMap_exp.liftHomotopy_zero H c0 H0 t
  -- periodicity of `Λ(1, ·)`
  have hper : ∀ t, Λ (1, t + 2 * Real.pi) = Λ (1, t) := by
    intro t
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hexp : ∀ σ : unitInterval, Complex.exp (-((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-(t : ℂ) * Complex.I) := fun σ => by
      rw [show -((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
        -(t : ℂ) * Complex.I + ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hmaps : MapsTo (fun σ : unitInterval => (Λ (σ, t + 2 * Real.pi) - Λ (σ, t)) /
        (2 * Real.pi * Complex.I)) univ (range ((↑) : ℤ → ℂ)) := by
      intro σ _
      have he : Complex.exp (Λ (σ, t + 2 * Real.pi) - Λ (σ, t)) = 1 := by
        rw [Complex.exp_sub, hΛe, hΛe]
        simp only
        rw [hexp σ, div_self (hgne _ (hmem σ t))]
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he
      exact ⟨n, by simp only [hn, mul_div_cancel_right₀ _ h2]⟩
    have hcont : Continuous fun σ : unitInterval =>
        (Λ (σ, t + 2 * Real.pi) - Λ (σ, t)) / (2 * Real.pi * Complex.I) := by
      have := Λ.continuous; fun_prop
    have hcon := isPreconnected_univ.constant_of_mapsTo
      Complex.isClosedEmbedding_intCast.isInducing.isDiscrete_range hcont.continuousOn hmaps
      (mem_univ (1 : unitInterval)) (mem_univ (0 : unitInterval))
    simp only [hΛ0, sub_self, zero_div, div_eq_zero_iff, h2, or_false, sub_eq_zero] at hcon
    exact hcon
  -- the parametrization
  set w : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ) * Complex.I) with hw
  have hwS : ∀ t, w t ∈ sphere (0 : ℂ) 1 := fun t => by
    simp only [hw, mem_sphere_zero_iff_norm, Complex.norm_exp]
    simp
  have hwB : ∀ t, w t ∈ closedBall (0 : ℂ) 1 := fun t => sphere_subset_closedBall (hwS t)
  have hw0 : ∀ t, w t ≠ 0 := fun t => Complex.exp_ne_zero _
  have hfw : ∀ t, f (w t) ≠ 0 := fun t => hfne _ (hwB t) (hw0 t)
  have hΛ1 : ∀ t, Complex.exp (Λ (1, t)) = g (w t) := fun t => by
    rw [hΛe]; congr 1; simp [hw]
  have hfg : ∀ t, f (w t) = w t * Complex.exp (Λ (1, t)) := by
    intro t
    rw [hΛ1]
    simp only [hg, if_neg (hw0 t)]
    exact (mul_div_cancel₀ _ (hw0 t)).symm
  refine ⟨fun t => z + (f (w t))⁻¹, fun t => t - (Λ (1, t)).im, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.add ((hfc.comp_continuous (by fun_prop) hwB).inv₀ hfw)
  · intro t
    simp only [hw]
    rw [show -((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
      -(t : ℂ) * Complex.I + ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · intro t ht t' ht' h
    have h1 : f (w t) = f (w t') := inv_injective (add_left_cancel h)
    have h2 := hfi (hwB t) (hwB t') h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h2
    have h3 : t' - t = n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simp at this
      linarith
    have hn0 : n = 0 := by
      have hlt : |(n : ℝ) * (2 * Real.pi)| < 1 * (2 * Real.pi) := by
        rw [← h3, one_mul, abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hlt
      have := lt_of_mul_lt_mul_right hlt (by positivity)
      have : |n| < 1 := by exact_mod_cast this
      exact Int.abs_lt_one_iff.1 this
    subst hn0
    simp at h3; linarith
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      show z + (f (w t))⁻¹ ∈ Γ
      obtain ⟨y, hy, hyx⟩ : f (w t) ∈ (fun x => (x - z)⁻¹) '' Γ := hfs ▸ mem_image_of_mem f (hwS t)
      simp only at hyx
      rw [← hyx, inv_inv]; simpa using hy
    · intro hx
      obtain ⟨v, hv, hvx⟩ : (x - z)⁻¹ ∈ f '' sphere 0 1 := hfs ▸ mem_image_of_mem _ hx
      have hv1 : ‖v‖ = 1 := mem_sphere_zero_iff_norm.1 hv
      refine ⟨-Complex.arg v, ?_⟩
      have h := Complex.norm_mul_exp_arg_mul_I v
      rw [hv1, Complex.ofReal_one, one_mul] at h
      have hvw : w (-Complex.arg v) = v := by
        calc w (-Complex.arg v) = Complex.exp ((Complex.arg v : ℂ) * Complex.I) := by
              simp only [hw]; congr 1; push_cast; ring
          _ = v := h
      simp only [hvw, hvx, inv_inv, add_sub_cancel]
  · exact continuous_id.sub (Complex.continuous_im.comp
      (Λ.continuous.comp (continuous_const.prodMk continuous_id)))
  · intro t
    simp only [hper]; ring
  · intro t
    simp only [add_sub_cancel_left]
    rw [hfg, mul_inv, norm_mul, norm_inv, norm_inv]
    have hwn : ‖w t‖ = 1 := mem_sphere_zero_iff_norm.1 (hwS t)
    rw [hwn, inv_one, one_mul, Complex.norm_exp, ← Complex.exp_neg, ← Real.exp_neg]
    rw [← Complex.exp_neg (Λ (1, t)), Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [sub_eq_add_neg]

/-- **S-PosLift** (DEC-D (a)), under the J1/J2 hypotheses of `gm_filledBall_conformal` -/
theorem posLift_filledBall {D : ContMetric} {z : ℂ} {s : ℝ} (hs : 0 < s) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D z s)) (hlc : GM.FilledBallBdyLC D z s) :
    ∃ φ θ, IsPosJordanLift (frontier (filledBall D z s)) z φ θ := by
  obtain ⟨f, hfc, hfi, hfd, hf0, -, hfs⟩ := GM.jo_disc_map hs hL hbd hlc
  exact posLift_of_disc_map hfc hfi hfd hf0 hfs

end LQGMetric.CONF.DD
