/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.KoebeHalfPlane at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeDistortion

/-!
# Koebe estimates for univalent maps of the upper half-plane (EXT-CA node K5)

Interface for EXT-RS, EXT-JS and the kernel theorem. For `f` injective and holomorphic on
`ℍ = {z | 0 < z.im}` and `z ∈ ℍ`:

* `infDist_compl_image_ge` (K5a lower): `c₁ · Im z · ‖f'(z)‖ ≤ dist (f z, ∂ f(ℍ))`, `c₁ = 1/48`;
* `infDist_compl_image_le` (K5a upper): `dist (f z, ∂ f(ℍ)) ≤ 2 · Im z · ‖f'(z)‖`;
* `deriv_ratio_le` (K5b): `‖w − z‖ ≤ Im z / 2 → ‖f'(w)‖ ≤ 2^C₂ ‖f'(z)‖ ∧ ‖f'(z)‖ ≤ 2^C₂ ‖f'(w)‖`;
* `norm_sub_le_im_mul_deriv` (K5b growth): `‖w − z‖ ≤ Im z / 2 → ‖f w − f z‖ ≤ M · Im z · ‖f'(z)‖`.

Sources: Garnett–Marshall, *Harmonic Measure*, Ch. I, Thm 4.3 (4.13) and Cor. 4.4 (4.14), p. 20
(Koebe's estimate in invariant form; our upper bound is their proof of the right inequality of
(4.13), the Schwarz lemma for the inverse map composed with the Möbius map
`w ↦ (w − z)/(w − z̄)` of `ℍ` onto the disk); Thm 4.5 for distortion. The constants are the
non-sharp ones of `KoebeCovering.lean` / `KoebeDistortion.lean` (DEVIATIONS.md, D-KOEBE).
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology Real ComplexConjugate

namespace QuantumZipper.CA.Koebe

theorem isOpen_upperHalfPlaneSet : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

theorem ball_im_subset_upperHalfPlane {z : ℂ} :
    ball z z.im ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  rw [mem_ball, Complex.dist_eq] at hw
  have := Complex.abs_im_le_norm (w - z)
  rw [Complex.sub_im] at this
  show 0 < w.im
  linarith [(abs_lt.1 (this.trans_lt hw)).1]

/-- The Möbius map `w ↦ (w − z)/(w − z̄)` of `ℍ` into the unit disk: its properties at `z`. -/
theorem halfPlaneMobius_props {z : ℂ} (hz : 0 < z.im) :
    DifferentiableOn ℂ (fun w => (w - z) / (w - conj z)) {w : ℂ | 0 < w.im} ∧
    MapsTo (fun w => (w - z) / (w - conj z)) {w : ℂ | 0 < w.im}
      (closedBall ((fun w => (w - z) / (w - conj z)) z) 1) ∧
    ‖deriv (fun w => (w - z) / (w - conj z)) z‖ = 1 / (2 * z.im) := by
  have hne : ∀ w : ℂ, 0 < w.im → w - conj z ≠ 0 := by
    intro w hw h
    have := congrArg Complex.im h
    simp at this
    linarith
  refine ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩
  · exact ((differentiableAt_id.sub_const z).div (differentiableAt_id.sub_const _)
      (hne w hw)).differentiableWithinAt
  · simp only [sub_self, zero_div, mem_closedBall, dist_zero_right, norm_div]
    have hp : 0 < ‖w - conj z‖ := norm_pos_iff.2 (hne w hw)
    rw [div_le_one hp]
    have hw' : 0 < w.im := hw
    have hsq : ‖w - z‖ ^ 2 ≤ ‖w - conj z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
      nlinarith
    nlinarith [norm_nonneg (w - z), norm_nonneg (w - conj z)]
  · have h := ((hasDerivAt_id' z).sub_const z).div ((hasDerivAt_id' z).sub_const (conj z))
      (hne z hz)
    have h' : HasDerivAt (fun w => (w - z) / (w - conj z))
        ((1 * (z - conj z) - (z - z) * 1) / (z - conj z) ^ 2) z := h
    rw [h'.deriv]
    simp only [sub_self, one_mul, mul_one, sub_zero]
    rw [Complex.sub_conj, norm_div, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    field_simp

/-- Schwarz lemma for the inverse of a univalent map of `ℍ`: a disk `ball (f z) R` inside
`f(ℍ)` has `R ≤ 2 Im z ‖f'(z)‖`. -/
theorem radius_le_of_ball_subset_image_halfPlane {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (hinj : InjOn f {z : ℂ | 0 < z.im})
    {z : ℂ} (hz : 0 < z.im) {R : ℝ} (hR : 0 < R)
    (hsub : ball (f z) R ⊆ f '' {z : ℂ | 0 < z.im}) :
    R ≤ 2 * z.im * ‖deriv f z‖ := by
  obtain ⟨hMd, hMmaps, hMder⟩ := halfPlaneMobius_props hz
  have := radius_mul_norm_deriv_le_of_ball_subset_image isOpen_upperHalfPlaneSet hd hinj
    (show z ∈ {z : ℂ | 0 < z.im} from hz) hMd hMmaps hR hsub
  rw [hMder, one_mul, mul_one_div, div_le_iff₀ (by linarith)] at this
  linarith

/-- An injective holomorphic map of `ℍ` is not onto `ℂ`. -/
theorem image_upperHalfPlane_ne_univ {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (hinj : InjOn f {z : ℂ | 0 < z.im}) :
    f '' {z : ℂ | 0 < z.im} ≠ univ := by
  intro h
  have hI : (0 : ℝ) < (I : ℂ).im := by simp
  have := radius_le_of_ball_subset_image_halfPlane hd hinj hI
    (R := 2 * (I : ℂ).im * ‖deriv f I‖ + 1) (by rw [Complex.I_im]; positivity) (by rw [h]; exact subset_univ _)
  linarith

/-- **K5a, lower bound** (Koebe; Garnett–Marshall Cor. I.4.4, left inequality, constant
`1/48`): `c₁ · Im z · ‖f'(z)‖ ≤ dist (f z, ∂ f(ℍ))`. -/
theorem infDist_compl_image_ge {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (hinj : InjOn f {z : ℂ | 0 < z.im})
    {z : ℂ} (hz : 0 < z.im) :
    koebeCovConst * z.im * ‖deriv f z‖ ≤ infDist (f z) (f '' {z : ℂ | 0 < z.im})ᶜ := by
  have hsub := ball_im_subset_upperHalfPlane (z := z)
  have h1 := koebeCovConst_mul_le_infDist hz (hd.mono hsub) (hinj.mono hsub)
  have hne : ((f '' {z : ℂ | 0 < z.im})ᶜ).Nonempty := by
    rw [nonempty_compl]; exact image_upperHalfPlane_ne_univ hd hinj
  exact h1.trans (infDist_le_infDist_of_subset (compl_subset_compl.2 (image_mono hsub)) hne)

/-- **K5b, derivative ratio** (Koebe distortion on a Whitney disk, exponent `C₂`):
if `‖w − z‖ ≤ Im z / 2` then `‖f'(w)‖ ≤ 2^C₂ ‖f'(z)‖` and `‖f'(z)‖ ≤ 2^C₂ ‖f'(w)‖`. -/
theorem deriv_ratio_le {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (hinj : InjOn f {z : ℂ | 0 < z.im})
    {z w : ℂ} (hz : 0 < z.im) (hw : dist w z ≤ z.im / 2) :
    ‖deriv f w‖ ≤ 2 ^ koebeDistExp * ‖deriv f z‖ ∧
    ‖deriv f z‖ ≤ 2 ^ koebeDistExp * ‖deriv f w‖ := by
  have hsub := ball_im_subset_upperHalfPlane (z := z)
  have hwB : w ∈ ball z z.im := mem_ball.2 (by linarith)
  have hs : 1 / 2 ≤ 1 - dist w z / z.im := by
    have : dist w z / z.im ≤ 1 / 2 := by
      rw [div_le_iff₀ hz]; linarith
    linarith
  have hC := koebeDistExp_pos
  constructor
  · have h := norm_deriv_le_distortion (hd.mono hsub) (hinj.mono hsub) hwB
    refine h.trans ?_
    rw [mul_comm]
    gcongr
    calc (1 - dist w z / z.im) ^ (-koebeDistExp) ≤ (1 / 2 : ℝ) ^ (-koebeDistExp) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hs (by linarith)
      _ = 2 ^ koebeDistExp := by
          rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]
  · have h := distortion_le_norm_deriv (hd.mono hsub) (hinj.mono hsub) hwB
    have hq : (1 / 2 : ℝ) ^ koebeDistExp ≤ (1 - dist w z / z.im) ^ koebeDistExp :=
      Real.rpow_le_rpow (by norm_num) hs hC.le
    have h2 : (1 / 2 : ℝ) ^ koebeDistExp * 2 ^ koebeDistExp = 1 := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
    have hpos : 0 < (2 : ℝ) ^ koebeDistExp := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : ‖deriv f z‖ * (1 / 2 : ℝ) ^ koebeDistExp ≤ ‖deriv f w‖ :=
      (mul_le_mul_of_nonneg_left hq (norm_nonneg _)).trans h
    calc ‖deriv f z‖ = ‖deriv f z‖ * ((1 / 2 : ℝ) ^ koebeDistExp * 2 ^ koebeDistExp) := by
          rw [h2, mul_one]
      _ = (‖deriv f z‖ * (1 / 2 : ℝ) ^ koebeDistExp) * 2 ^ koebeDistExp := by ring
      _ ≤ ‖deriv f w‖ * 2 ^ koebeDistExp := by gcongr
      _ = 2 ^ koebeDistExp * ‖deriv f w‖ := by ring

end QuantumZipper.CA.Koebe
