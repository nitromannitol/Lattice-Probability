/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.CarLengthArea at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# EXT-CA nodes C1 and C2: Carathéodory standing hypotheses, properness, length–area

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "C. Carathéodory boundary theory".

* `CarHyp`: the standing hypotheses `(Hψ)` of the blueprint, without the ULC condition on `E`
  (added in C3).
* C1 `frontier_mem_of_tendsto`, `frontier_mem_of_tendsto_cobounded`: if `z_n ∈ H` tends to a
  real point (or to `∞`), every cluster value of `ψ z_n` lies in `frontier D`. This is the
  properness of a conformal map, cf. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992),
  §1.1 / Prop. 1.1 (printed p. 5). Proof here: open mapping theorem
  (`AnalyticOnNhd.is_constant_or_isOpen`) plus injectivity, instead of continuity of `ψ⁻¹`
  (own elementary argument, ~40 lines).
* C2 `exists_short_semicircle`: Wolff's length–area lemma, Pommerenke, *Boundary Behaviour*,
  Proposition 2.2 (printed p. 20, PDF p. 28), in the half-plane form with semicircles
  `x₀ + r e^{iθ}`, `θ ∈ (0, π)`, radii `r ∈ (ρ², ρ)` (instead of Pommerenke's
  `ρ < r < √ρ` and full circles; the constant `2π²R₀²/log(1/ρ)` is twice what the proof gives).
  Proof as in Pommerenke: Cauchy–Schwarz in `θ`, integrate `ℓ(r)²/r` over `r`, polar
  coordinates (`Complex.lintegral_comp_polarCoord_symm`), area formula
  (`lintegral_abs_det_fderiv_eq_addHaar_image` with Jacobian `‖h'‖²`,
  `QuantumZipper.abs_det_fderiv_eq_normSq`), `area(h(half-disk)) ≤ π R₀²`, and choose `r`
  below the mean. Everything is done in `ℝ≥0∞`, so no integrability side conditions arise.
  The conclusion is therefore stated with the lower Lebesgue integral `∫⁻` and not with an
  `intervalIntegral`: the latter is the junk value `0` when `θ ↦ ‖h'(x₀ + r e^{iθ})‖` is not
  integrable on `(0, π)` (possible, `U` need not contain the feet `x₀ ± r` of the semicircle),
  which would let the statement be satisfied by a radius of infinite semicircle length; the
  source bounds a genuine finite length (AUDIT6 finding P1). The corollary
  `exists_short_semicircle_finite` records the finiteness explicitly.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal Real

namespace QuantumZipper.CA.Car

/-- Standing hypotheses `(Hψ)` of EXT-CA §3 C, without the ULC condition on `E`. -/
structure CarHyp (ψ : ℂ → ℂ) (D E : Set ℂ) (R₀ : ℝ) : Prop where
  holo : DifferentiableOn ℂ ψ H
  bij : Set.BijOn ψ H D
  isOpen : IsOpen D
  bdd : D ⊆ Metric.ball 0 R₀
  isClosed : IsClosed E
  frontier_sub : frontier D ⊆ E
  sub_compl : E ⊆ Dᶜ
  E_bdd : E ⊆ Metric.closedBall 0 R₀

/-! ### C1: properness -/

/-- Abstract properness: if `z` eventually leaves the ball `B(ζ, Im ζ / 2)` for every `ζ ∈ H`,
then every cluster value of `ψ ∘ z` lies in `frontier D`. -/
theorem frontier_mem_of_eventually_not_mem_ball {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ}
    (h : CarHyp ψ D E R₀) {ι : Type*} {l : Filter ι} {z : ι → ℂ} (hz : ∀ n, z n ∈ H)
    (hfar : ∀ ζ ∈ H, ∀ᶠ n in l, z n ∉ ball ζ (ζ.im / 2)) {w : ℂ}
    (hw : MapClusterPt w l (ψ ∘ z)) : w ∈ frontier D := by
  rw [h.isOpen.frontier_eq]
  constructor
  · rw [mem_closure_iff_nhds]
    intro s hs
    obtain ⟨n, hn⟩ := (mapClusterPt_iff_frequently.1 hw s hs).exists
    exact ⟨_, hn, h.bij.mapsTo (hz n)⟩
  · intro hwD
    obtain ⟨ζ, hζ, rfl⟩ := h.bij.surjOn hwD
    have hζ0 : 0 < ζ.im := hζ
    set B := ball ζ (ζ.im / 2) with hB
    have hBH : B ⊆ H := by
      intro y hy
      have h1 : |y.im - ζ.im| ≤ ‖y - ζ‖ := by
        simpa using Complex.abs_im_le_norm (y - ζ)
      have h2 : ‖y - ζ‖ < ζ.im / 2 := by simpa [hB, dist_eq_norm] using hy
      show 0 < y.im
      have := (abs_lt.1 (h1.trans_lt h2)).1
      linarith
    have hBo : IsOpen (ψ '' B) := by
      have han : AnalyticOnNhd ℂ ψ B := (h.holo.mono hBH).analyticOnNhd isOpen_ball
      rcases han.is_constant_or_isOpen (convex_ball _ _).isPreconnected with ⟨c, hc⟩ | hop
      · exfalso
        have hm1 : ζ ∈ B := mem_ball_self (by positivity)
        have hm2 : ζ + ((ζ.im / 4 : ℝ) : ℂ) ∈ B := by
          rw [hB, mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by positivity)]
          linarith
        have := h.bij.injOn (hBH hm1) (hBH hm2) ((hc _ hm1).trans (hc _ hm2).symm)
        have h4 : ((ζ.im / 4 : ℝ) : ℂ) = 0 := by linear_combination -this
        have : ζ.im / 4 = 0 := by exact_mod_cast h4
        linarith
      · exact hop B subset_rfl isOpen_ball
    have hfr := mapClusterPt_iff_frequently.1 hw _
      (hBo.mem_nhds ⟨ζ, mem_ball_self (by positivity), rfl⟩)
    obtain ⟨n, ⟨b, hb, hbe⟩, hn2⟩ := (hfr.and_eventually (hfar ζ hζ)).exists
    have := h.bij.injOn (hBH hb) (hz n) hbe
    exact hn2 (this ▸ hb)

/-- **C1 (properness at a real point).** -/
theorem frontier_mem_of_tendsto {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : CarHyp ψ D E R₀)
    {z : ℕ → ℂ} (hz : ∀ n, z n ∈ H) {x : ℝ}
    (hzx : Tendsto z atTop (𝓝 (x : ℂ))) {w : ℂ} (hw : MapClusterPt w atTop (ψ ∘ z)) :
    w ∈ frontier D := by
  refine frontier_mem_of_eventually_not_mem_ball h hz (fun ζ hζ => ?_) hw
  have hζ0 : 0 < ζ.im := hζ
  have hd : Tendsto (fun n => dist (z n) ζ) atTop (𝓝 (dist (x : ℂ) ζ)) :=
    hzx.dist tendsto_const_nhds
  have hge : ζ.im ≤ dist (x : ℂ) ζ := by
    rw [dist_comm, dist_eq_norm]
    have := Complex.abs_im_le_norm (ζ - x)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  filter_upwards [hd.eventually (lt_mem_nhds (show ζ.im / 2 < dist (x : ℂ) ζ by linarith))]
    with n hn hmem
  rw [mem_ball] at hmem
  linarith

/-- **C1 (properness at `∞`).** -/
theorem frontier_mem_of_tendsto_cobounded {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ}
    (h : CarHyp ψ D E R₀) {z : ℕ → ℂ} (hz : ∀ n, z n ∈ H)
    (hzx : Tendsto z atTop (Bornology.cobounded ℂ)) {w : ℂ}
    (hw : MapClusterPt w atTop (ψ ∘ z)) : w ∈ frontier D := by
  refine frontier_mem_of_eventually_not_mem_ball h hz (fun ζ hζ => ?_) hw
  exact hzx.eventually (Bornology.isBounded_def.1 (isBounded_ball (x := ζ) (r := ζ.im / 2)))

/-! ### C2: Wolff's length–area lemma -/

/-- Area formula (as EXT-JS A2, `QuantumZipper.JS.volume_image_eq_lintegral_normSq_deriv`;
reproduced here to avoid a build dependency). -/
private theorem volume_image_eq_lintegral_normSq_deriv' {U : Set ℂ} {h : ℂ → ℂ}
    (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) (hinj : InjOn h U) :
    volume (h '' U) = ∫⁻ z in U, ‖deriv h z‖ₑ ^ 2 := by
  have hd : ∀ z ∈ U, HasFDerivWithinAt h (fderiv ℝ h z) U z := fun z hz =>
    ((hh.differentiableAt (hU.mem_nhds hz)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hU.measurableSet hd hinj]
  refine setLIntegral_congr_fun hU.measurableSet (fun z hz => ?_)
  rw [abs_det_fderiv_eq_normSq (hh.differentiableAt (hU.mem_nhds hz)),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Cauchy–Schwarz on `(0, π)` in `ℝ≥0∞`. -/
private theorem sq_lintegral_Ioo_le {f : ℝ → ℝ≥0∞} (hf : AEMeasurable f) :
    (∫⁻ θ in Ioo 0 π, f θ) ^ 2 ≤ ENNReal.ofReal π * ∫⁻ θ in Ioo 0 π, f θ ^ 2 := by
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioo 0 π))
    Real.HolderConjugate.two_two hf.restrict (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply,
    MeasurableSet.univ, univ_inter, Real.volume_Ioo, sub_zero, one_mul] at hcs
  have hsq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc (∫⁻ θ in Ioo 0 π, f θ) ^ 2
      ≤ ((∫⁻ θ in Ioo 0 π, f θ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * ENNReal.ofReal π ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ bot_le hcs 2
    _ = ENNReal.ofReal π * ∫⁻ θ in Ioo 0 π, f θ ^ 2 := by
        rw [mul_pow, hsq, hsq, mul_comm]
        simp_rw [ENNReal.rpow_two]

/-- **C2 (Wolff's length–area lemma, half-plane form).** Pommerenke, *Boundary Behaviour*,
Prop. 2.2 (Wolff's lemma, printed p. 20): there is a radius `r` for which the image of the
semicircle `{x₀ + r e^{iθ} | θ ∈ (0, π)}` has small *length*. The length is stated as the lower
Lebesgue integral `∫⁻` (finite for the witness, see `exists_short_semicircle_finite`); a Bochner
`intervalIntegral` would be the junk value `0` for a non-integrable integrand and the statement
could be satisfied by a radius of infinite length (AUDIT6 P1). -/
theorem exists_short_semicircle {U : Set ℂ} (hU : IsOpen U) {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h U)
    (hi : Set.InjOn h U) {R₀ : ℝ} (hR : h '' U ⊆ Metric.ball 0 R₀) {x₀ : ℝ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hsub : {z : ℂ | 0 < z.im ∧ ‖z - x₀‖ < ρ} ⊆ U) :
    ∃ r ∈ Set.Ioo (ρ ^ 2) ρ, (∫⁻ θ in Set.Ioo 0 Real.pi,
        ‖deriv h (x₀ + r * Complex.exp (θ * Complex.I))‖ₑ * ENNReal.ofReal r) ^ 2 ≤
      ENNReal.ofReal (2 * Real.pi ^ 2 * R₀ ^ 2 / Real.log (1 / ρ)) := by
  set c : ℝ := 2 * π ^ 2 * R₀ ^ 2 / Real.log (1 / ρ) with hc
  have hlog : 0 < Real.log (1 / ρ) := Real.log_pos ((one_lt_div hρ0).2 hρ1)
  have hρ2 : ρ ^ 2 < ρ := by nlinarith
  have hρ20 : 0 < ρ ^ 2 := by positivity
  -- the translated map on the half-disk `A`
  set k : ℂ → ℂ := fun z => h ((x₀ : ℂ) + z) with hk
  set A : Set ℂ := {z | 0 < z.im ∧ ‖z‖ < ρ} with hA
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt continuous_norm continuous_const)
  have hAU : ∀ z ∈ A, (x₀ : ℂ) + z ∈ U := fun z hz =>
    hsub ⟨by simpa using hz.1, by simpa using hz.2⟩
  have hkd : DifferentiableOn ℂ k A := fun z hz =>
    (((hd _ (hAU z hz)).differentiableAt (hU.mem_nhds (hAU z hz))).comp z
      (differentiableAt_id.const_add (x₀ : ℂ))).differentiableWithinAt
  have hki : InjOn k A := fun a ha b hb hab => add_left_cancel (hi (hAU a ha) (hAU b hb) hab)
  have hkimg : k '' A ⊆ ball 0 R₀ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hR ⟨_, hAU z hz, rfl⟩
  have hR0 : 0 < R₀ := by
    have hz : (((ρ / 2 : ℝ) : ℂ) * Complex.I) ∈ A := by
      refine ⟨by simp; positivity, ?_⟩
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    exact nonempty_ball.1 ⟨_, hkimg ⟨_, hz, rfl⟩⟩
  set G : ℂ → ℝ≥0∞ := fun z => ‖deriv k z‖ₑ with hG
  have hGm : Measurable G := (measurable_deriv k).enorm
  -- area bound
  have harea : ∫⁻ z in A, G z ^ 2 ≤ ENNReal.ofReal (π * R₀ ^ 2) := by
    rw [← volume_image_eq_lintegral_normSq_deriv' hAo hkd hki]
    calc volume (k '' A) ≤ volume (ball (0 : ℂ) R₀) := measure_mono hkimg
      _ = ENNReal.ofReal (π * R₀ ^ 2) := by
        rw [Complex.volume_ball, mul_comm, ENNReal.ofReal_mul Real.pi_pos.le,
          ENNReal.ofReal_pow hR0.le, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal, mul_comm]
  -- polar coordinates
  have hPc : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp_rw [Complex.polarCoord_symm_apply]; fun_prop
  set S : Set (ℝ × ℝ) := Ioo (ρ ^ 2) ρ ×ˢ Ioo 0 π with hS
  have hpolar : ∫⁻ p in S, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) ^ 2 ≤
      ∫⁻ z in A, G z ^ 2 := by
    rw [← lintegral_indicator hAo.measurableSet, ← Complex.lintegral_comp_polarCoord_symm]
    have hST : S ⊆ Complex.polarCoord.target := by
      rintro ⟨r, θ⟩ ⟨hr, hθ⟩
      rw [Complex.polarCoord_target]
      exact ⟨lt_trans hρ20 hr.1, by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    calc ∫⁻ p in S, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) ^ 2
        = ∫⁻ p in S, ENNReal.ofReal p.1 •
            A.indicator (fun z => G z ^ 2) (Complex.polarCoord.symm p) := by
          refine setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) ?_
          rintro ⟨r, θ⟩ ⟨hr, hθ⟩
          have hr0 : 0 < r := lt_trans hρ20 hr.1
          have hmem : Complex.polarCoord.symm (r, θ) ∈ A := by
            refine ⟨?_, ?_⟩
            · simp only [Complex.polarCoord_symm_apply]
              simp only [Complex.mul_im, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
                Complex.add_re, Complex.mul_I_re, zero_mul, add_zero]
              have := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
              simp only [Complex.I_im]
              nlinarith
            · rw [Complex.norm_polarCoord_symm, abs_of_pos hr0]; exact hr.2
          dsimp only
          rw [indicator_of_mem hmem, smul_eq_mul]
      _ ≤ _ := lintegral_mono_set hST
  -- Tonelli
  have htonelli : ∫⁻ r in Ioo (ρ ^ 2) ρ, ∫⁻ θ in Ioo 0 π,
      ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)) ^ 2 =
      ∫⁻ p in S, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) ^ 2 := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
    exact ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((hGm.comp hPc.measurable).pow_const 2)).aemeasurable
  -- the lengths
  set L : ℝ → ℝ≥0∞ := fun r => ∫⁻ θ in Ioo 0 π,
    G (Complex.polarCoord.symm (r, θ)) * ENNReal.ofReal r with hL
  have hCS : ∀ r ∈ Ioo (ρ ^ 2) ρ, L r ^ 2 * (ENNReal.ofReal r)⁻¹ ≤
      ENNReal.ofReal π * ∫⁻ θ in Ioo 0 π,
        ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)) ^ 2 := by
    intro r hr
    have hr0 : 0 < r := lt_trans hρ20 hr.1
    have hm : Measurable fun θ : ℝ => G (Complex.polarCoord.symm (r, θ)) * ENNReal.ofReal r :=
      (hGm.comp (hPc.comp (Continuous.prodMk_right r)).measurable).mul_const _
    have hne0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hr0
    have hnet : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
    calc L r ^ 2 * (ENNReal.ofReal r)⁻¹
        ≤ (ENNReal.ofReal π * ∫⁻ θ in Ioo 0 π,
            (G (Complex.polarCoord.symm (r, θ)) * ENNReal.ofReal r) ^ 2) *
            (ENNReal.ofReal r)⁻¹ := by gcongr; exact sq_lintegral_Ioo_le hm.aemeasurable
      _ = ENNReal.ofReal π * ((∫⁻ θ in Ioo 0 π,
            ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)) ^ 2) *
            (ENNReal.ofReal r * (ENNReal.ofReal r)⁻¹)) := by
          have hsq : ∫⁻ θ in Ioo 0 π,
              (G (Complex.polarCoord.symm (r, θ)) * ENNReal.ofReal r) ^ 2 =
              (∫⁻ θ in Ioo 0 π, ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)) ^ 2) *
                ENNReal.ofReal r := by
            rw [← lintegral_mul_const' _ _ hnet]; congr 1; funext θ; ring
          rw [hsq, mul_assoc, mul_assoc]
      _ = _ := by rw [ENNReal.mul_inv_cancel hne0 hnet, mul_one]
  -- the polar-coordinate integrand `G (polarCoord.symm (r, θ))` is the semicircle integrand
  have hLeq : ∀ r : ℝ, L r = ∫⁻ θ in Ioo 0 π,
      ‖deriv h (x₀ + r * Complex.exp (θ * Complex.I))‖ₑ * ENNReal.ofReal r := by
    intro r
    show (∫⁻ θ in Ioo 0 π, G (Complex.polarCoord.symm (r, θ)) * ENNReal.ofReal r) = _
    refine setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    have hstep : G (Complex.polarCoord.symm (r, θ)) =
        ‖deriv h (x₀ + r * Complex.exp (θ * Complex.I))‖ₑ := by
      show ‖deriv (fun z : ℂ => h ((x₀ : ℂ) + z)) (Complex.polarCoord.symm (r, θ))‖ₑ = _
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin, deriv_comp_const_add]
    rw [hstep]
  suffices hmain : ∃ r ∈ Ioo (ρ ^ 2) ρ, L r ^ 2 ≤ ENNReal.ofReal c by
    obtain ⟨r, hr, hle⟩ := hmain
    exact ⟨r, hr, by simpa [hLeq r, hc] using hle⟩
  have hc0 : 0 ≤ c := by positivity
  by_contra hne
  push Not at hne
  have hlow : ∀ r ∈ Ioo (ρ ^ 2) ρ, ENNReal.ofReal c ≤ L r ^ 2 := fun r hr => (hne r hr).le
  -- `∫_{ρ²}^{ρ} dr / r = log (1/ρ)`
  have hinv : ∫⁻ r in Ioo (ρ ^ 2) ρ, (ENNReal.ofReal r)⁻¹ = ENNReal.ofReal (Real.log (1 / ρ)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioo
      (fun r hr => (ENNReal.ofReal_inv_of_pos (lt_trans hρ20 hr.1)).symm),
      ← ofReal_integral_eq_lintegral_ofReal]
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ2.le,
        integral_inv_of_pos hρ20 hρ0]
      congr 2
      field_simp
    · exact (ContinuousOn.integrableOn_Icc (a := ρ ^ 2) (b := ρ) (continuousOn_inv₀.mono
        (fun r hr => (hρ20.trans_le hr.1).ne'))).mono_set Ioo_subset_Icc_self
    · exact ae_restrict_of_forall_mem measurableSet_Ioo (fun r hr => (inv_pos.2
        (lt_trans hρ20 hr.1)).le)
  have hchain : ENNReal.ofReal c * ENNReal.ofReal (Real.log (1 / ρ)) ≤
      ENNReal.ofReal π * ENNReal.ofReal (π * R₀ ^ 2) := by
    calc ENNReal.ofReal c * ENNReal.ofReal (Real.log (1 / ρ))
        = ∫⁻ r in Ioo (ρ ^ 2) ρ, ENNReal.ofReal c * (ENNReal.ofReal r)⁻¹ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hinv]
      _ ≤ ∫⁻ r in Ioo (ρ ^ 2) ρ, L r ^ 2 * (ENNReal.ofReal r)⁻¹ :=
          setLIntegral_mono' measurableSet_Ioo (fun r hr => by gcongr; exact hlow r hr)
      _ ≤ ∫⁻ r in Ioo (ρ ^ 2) ρ, ENNReal.ofReal π * ∫⁻ θ in Ioo 0 π,
            ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)) ^ 2 :=
          setLIntegral_mono' measurableSet_Ioo hCS
      _ = ENNReal.ofReal π * ∫⁻ p in S, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) ^ 2 := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htonelli]
      _ ≤ _ := by gcongr; exact hpolar.trans harea
  rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul Real.pi_pos.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have : c * Real.log (1 / ρ) = 2 * π ^ 2 * R₀ ^ 2 := by
    rw [hc]; field_simp
  rw [this] at hchain
  have : 0 < π ^ 2 * R₀ ^ 2 := by positivity
  nlinarith

/-- A square in `ℝ≥0∞` is `⊤` only if its base is (own elementary proof). -/
private theorem lt_top_of_sq_le_ofReal {a : ℝ≥0∞} {c : ℝ}
    (h : a ^ 2 ≤ ENNReal.ofReal c) : a < ⊤ := by
  by_contra ha
  rw [not_lt, top_le_iff] at ha
  rw [ha] at h
  simp at h

/-- **C2, finite-length form.** The witness radius of `exists_short_semicircle` has *finite*
semicircle length: this is the form the consumers (EXT-CA C3, EXT-RS GEN) need, since a finite
lower Lebesgue integral is what bounds `diam h(semicircle)`. -/
theorem exists_short_semicircle_finite {U : Set ℂ} (hU : IsOpen U) {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h U) (hi : Set.InjOn h U) {R₀ : ℝ} (hR : h '' U ⊆ Metric.ball 0 R₀)
    {x₀ : ℝ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : {z : ℂ | 0 < z.im ∧ ‖z - x₀‖ < ρ} ⊆ U) :
    ∃ r ∈ Set.Ioo (ρ ^ 2) ρ,
      (∫⁻ θ in Set.Ioo 0 Real.pi,
          ‖deriv h (x₀ + r * Complex.exp (θ * Complex.I))‖ₑ * ENNReal.ofReal r) < ⊤ ∧
        (∫⁻ θ in Set.Ioo 0 Real.pi,
          ‖deriv h (x₀ + r * Complex.exp (θ * Complex.I))‖ₑ * ENNReal.ofReal r) ^ 2 ≤
        ENNReal.ofReal (2 * Real.pi ^ 2 * R₀ ^ 2 / Real.log (1 / ρ)) := by
  obtain ⟨r, hr, hb⟩ := exists_short_semicircle hU hd hi hR hρ0 hρ1 hsub
  exact ⟨r, hr, lt_top_of_sq_le_ofReal hb, hb⟩

end QuantumZipper.CA.Car
