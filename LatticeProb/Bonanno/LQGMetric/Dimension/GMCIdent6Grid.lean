/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent6Grid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent5Mom
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent6Cov
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent6Kah
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Fin

/-!
# Moments of the band approximation of `M̃_{γ,δ}` on a square, via Riemann sums (P2-GMCID6)

For `δ = 2^{-m}`, `ε = 2^{-n}` (`m ≤ n`), the band density
`f_n(z) = e^{γ h̃^δ_ε(z) − γ²/2 Var h̃^δ_ε(z)}` (`GMCIdent5.fineDens`) and a square
`a + L·[0,1)²` with `δ ≤ 4L`:

* `fineDens_ae_eq_exp` : `f_n(z) = e^{X(z) − Var X(z)/2}` a.s., `X = γ h̃^δ_ε`;
* `cov_band_le` : `Cov(X(z), X(w)) ≤ γ²(log(2L / max(ε, ‖z − w‖)) + 1)` for `‖z − w‖ ≤ 2L`
  (`pi_integral_killedHeat_le`);
* `lintegral_gridSum_rpow_le` : for the level-`j` Riemann sum at offset `t`, with
  `2^{-j} ≤ ε/L`, the one-sided Kahane comparison `kahane_logRef` with a `γ²`-log-correlated
  reference family;
* `lintegral_cell0_eq` : `∫_{[0,1)²} G = ∫_{t ∈ [0,1)²} ∑_{i} 4^{-j} G(cellMap j i t) dt`;
* **`lintegral_square_rpow_le`** : `E (∫_{[0,1)²} f_n(a + L y) dy)^q ≤ C`, uniformly in
  `m ≤ n`, `a`, `L` with `2^{-m} ≤ 4L`, for every `q < 0` or `1 < q` for which the reference
  family has uniformly bounded `q`-th moments (Jensen in `t`, as in
  `uniform_moment_areaApprox_sqIn`).

This is the discretized form of the argument of DZZ l. 684–688 (Kahane's inequality, with the
covariance of the band field bounded above by a log-correlated one; Rhodes–Vargas
arXiv:1305.6221 Thm 2.11, 2.12; Berestycki–Powell arXiv:2404.16642 Thm 3.23, `T:negmom`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Finset
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent6

open KilledHeat WhiteNoise DZZ DGMC GMCIdent GMCIdent4 GMCIdent5

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}
variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}

/-- the band density is the normalized exponential of `γ h̃^δ_ε` -/
lemma fineDens_ae_eq_exp (hW : IsWhiteNoise P' W) (γ : ℝ) {m n : ℕ} (hmn : m ≤ n) (z : ℂ) :
    fineDens W γ m n z =ᵐ[P'] fun ω =>
      Real.exp (γ * tildeH W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) z ω -
        Var[fun ω => γ * tildeH W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) z ω; P'] / 2) := by
  set κ := wndKernelL2 openSquare (Ioo (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ m) ^ 2)) z
  have hV : Var[tildeH W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) z; P'] = Real.pi * ‖κ‖ ^ 2 :=
    variance_sqrtPi_wn hW κ
  filter_upwards [bandDens_eq_fineDens_ae hW γ hmn z, bandDens_ae_eq hW γ hmn z] with ω h1 h2
  rw [← h1, h2, variance_const_mul, hV]
  congr 1; ring

variable (W) in
/-- the band field `γ h̃^δ_ε` at the points `zs i` -/
def bandVec (γ ε δ : ℝ) {ι : Type*} (zs : ι → ℂ) (ω : Ω') (i : ι) : ℝ :=
  γ * tildeH W ε δ (zs i) ω

lemma hasGaussianLaw_bandVec (hW : IsWhiteNoise P' W) (γ ε δ : ℝ) {ι : Type} [Fintype ι]
    (zs : ι → ℂ) : HasGaussianLaw (bandVec W γ ε δ zs) P' := by
  have h := (hW.isGaussianProcess_comp (fun i : ι =>
    wndKernelL2 openSquare (Ioo (ε ^ 2) (δ ^ 2)) (zs i))).smul (fun _ => γ * Real.sqrt Real.pi)
  have e : (fun i ω => bandVec W γ ε δ zs ω i) = fun i ω => (γ * Real.sqrt Real.pi) *
      W (wndKernelL2 openSquare (Ioo (ε ^ 2) (δ ^ 2)) (zs i)) ω := by
    funext i ω
    simp only [bandVec, tildeH, DZZ.wnField]; ring
  have h' : IsGaussianProcess (fun i ω => bandVec W γ ε δ zs ω i) P' := by
    rw [e]; simpa [smul_eq_mul] using h
  exact hasGaussianLaw_fintype h' (fun i => i)

lemma integral_bandVec (hW : IsWhiteNoise P' W) (γ ε δ : ℝ) {ι : Type*} (zs : ι → ℂ) (i : ι) :
    ∫ ω, bandVec W γ ε δ zs ω i ∂P' = 0 := by
  simp only [bandVec, tildeH, DZZ.wnField]
  rw [integral_const_mul, integral_const_mul, (hW.hasLaw_single _).integral_eq,
    integral_id_gaussianReal, mul_zero, mul_zero]

lemma measurable_bandVec (hW : IsWhiteNoise P' W) (γ ε δ : ℝ) {ι : Type*} (zs : ι → ℂ)
    (i : ι) : Measurable fun ω => bandVec W γ ε δ zs ω i :=
  ((hW.measurable _).const_mul _).const_mul _

lemma integrable_exp_bandVec (hW : IsWhiteNoise P' W) (γ ε δ : ℝ) {ι : Type*} (zs : ι → ℂ)
    (i : ι) (t : ℝ) : Integrable (fun ω => Real.exp (t * bandVec W γ ε δ zs ω i)) P' := by
  have h := integrable_exp_wn hW (t * γ * Real.sqrt Real.pi)
    (wndKernelL2 openSquare (Ioo (ε ^ 2) (δ ^ 2)) (zs i))
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp only [bandVec, tildeH, DZZ.wnField]; ring_nf

/-- **covariance upper bound for the band field** -/
lemma cov_bandVec_le (hW : IsWhiteNoise P' W) (γ : ℝ) {ε δ L : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hδL : δ ≤ L) {ι : Type*} (zs : ι → ℂ) (i k : ι) (hik : ‖zs i - zs k‖ ≤ L) :
    cov[fun ω => bandVec W γ ε δ zs ω i, fun ω => bandVec W γ ε δ zs ω k; P'] ≤
      γ ^ 2 * (Real.log (L / max ε ‖zs i - zs k‖) + 1) := by
  have hε2 : (0 : ℝ) < ε ^ 2 / 2 := by positivity
  simp only [bandVec]
  rw [covariance_const_mul_left, covariance_const_mul_right]
  have hc := cov_wnField (P := P') (I := Ioo (ε ^ 2) (δ ^ 2)) hW LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball measurableSet_Ioo hε2 (fun s hs => (half_lt_self (by positivity)).trans
      hs.1) (zs i) (zs k)
  show γ * (γ * cov[DZZ.wnField W openSquare (Ioo (ε ^ 2) (δ ^ 2)) (zs i),
    DZZ.wnField W openSquare (Ioo (ε ^ 2) (δ ^ 2)) (zs k); P']) ≤ _
  rw [hc, ← mul_assoc, ← sq]
  exact mul_le_mul_of_nonneg_left (pi_integral_killedHeat_le hε hεδ hδL _ _ hik) (sq_nonneg γ)

lemma norm_sub_le_two_of_unitSq {x y : ℂ} (hx : x ∈ unitSq) (hy : y ∈ unitSq) : ‖x - y‖ ≤ 2 := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have := abs_le.2 (⟨by linarith, by linarith⟩ : -1 ≤ x.re - y.re ∧ x.re - y.re ≤ 1)
  have := abs_le.2 (⟨by linarith, by linarith⟩ : -1 ≤ x.im - y.im ∧ x.im - y.im ≤ 1)
  linarith

/-- the Riemann points `a + L · cellMap j i t` -/
def rPt (a : ℂ) (L : ℝ) (j : ℕ) (t : ℂ) (i : ↥(grid j)) : ℂ := a + (L : ℂ) * cellMap j i t

lemma norm_rPt_sub (a : ℂ) {L : ℝ} (hL : 0 < L) (j : ℕ) (t : ℂ) (i k : ↥(grid j)) :
    ‖rPt a L j t i - rPt a L j t k‖ = L * ‖cpt j i - cpt j k‖ := by
  rw [rPt, rPt, add_sub_add_left_eq_sub, ← mul_sub, cellMap_eq, cellMap_eq,
    add_sub_add_right_eq_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hL.le]

/-- **the Kahane step at a fixed offset** -/
theorem lintegral_gridSum_rpow_le (hW : IsWhiteNoise P' W) (γ : ℝ) {m n j : ℕ} (hmn : m ≤ n)
    {a : ℂ} {L : ℝ} (hL : 0 < L) (hδL : (2 : ℝ)⁻¹ ^ m ≤ 4 * L)
    (hj : (2 : ℝ)⁻¹ ^ j ≤ (2 : ℝ)⁻¹ ^ n / L) (t : ℂ) {Z : ℕ → ℂ → Ω₀ → ℝ} {c : ℝ}
    (hZ : LogCorr Z P₀ (γ ^ 2) c) {q : ℝ} (hq : q ≤ 0 ∨ 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i : ↥(grid j), (4 : ℝ)⁻¹ ^ j *
        fineDens W γ m n (rPt a L j t i) ω) ^ q) ∂P' ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) *
        ∫ ω, gM (Z j) P₀ j (grid j) ω ^ q ∂P₀) := by
  set ε : ℝ := (2 : ℝ)⁻¹ ^ n
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m
  have hε : 0 < ε := by positivity
  have hεδ : ε ≤ δ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  set X := bandVec W γ ε δ (rPt a L j t)
  have hae : ∀ᵐ ω ∂P', ∀ i : ↥(grid j), fineDens W γ m n (rPt a L j t i) ω =
      Real.exp (X ω i - Var[fun ω => X ω i; P'] / 2) :=
    ae_all_iff.2 fun i => fineDens_ae_eq_exp hW γ hmn _
  have hcov : ∀ i k, cov[fun ω => X ω i, fun ω => X ω k; P'] ≤
      -(γ ^ 2 * Real.log (max ((2 : ℝ)⁻¹ ^ j) ‖cpt j i - cpt j k‖)) +
        γ ^ 2 * (Real.log 4 + 1) := by
    intro i k
    have hd := norm_sub_le_two_of_unitSq (cpt_mem_unitSq i.2) (cpt_mem_unitSq k.2)
    have hik : ‖rPt a L j t i - rPt a L j t k‖ ≤ 4 * L := by
      rw [norm_rPt_sub a hL]; nlinarith
    refine (cov_bandVec_le hW γ hε hεδ hδL _ i k hik).trans ?_
    rw [norm_rPt_sub a hL]
    have hm0 : 0 < max ((2 : ℝ)⁻¹ ^ j) ‖cpt j i - cpt j k‖ :=
      lt_max_of_lt_left (by positivity)
    have hmax : L * max ((2 : ℝ)⁻¹ ^ j) ‖cpt j i - cpt j k‖ ≤ max ε (L * ‖cpt j i - cpt j k‖) := by
      rw [mul_max_of_nonneg _ _ hL.le]
      refine max_le_max ?_ le_rfl
      rw [le_div_iff₀ hL] at hj; linarith
    have hlog : Real.log (4 * L / max ε (L * ‖cpt j i - cpt j k‖)) ≤
        Real.log 4 - Real.log (max ((2 : ℝ)⁻¹ ^ j) ‖cpt j i - cpt j k‖) := by
      rw [← Real.log_div (by norm_num) hm0.ne']
      refine Real.log_le_log (div_pos (by positivity) (lt_max_of_lt_left hε)) ?_
      rw [div_le_div_iff₀ (lt_max_of_lt_left hε) hm0]
      nlinarith
    nlinarith [sq_nonneg γ]
  have hK := kahane_logRef (hasGaussianLaw_bandVec hW γ ε δ (rPt a L j t))
    (integral_bandVec hW γ ε δ _) (measurable_bandVec hW γ ε δ _)
    (integrable_exp_bandVec hW γ ε δ _) (by positivity) hcov hZ hq
  refine le_trans (le_of_eq (lintegral_congr_ae (hae.mono fun ω h => ?_))) hK
  simp_rw [h]; rfl

end GMCIdent6
end LQGMetric
