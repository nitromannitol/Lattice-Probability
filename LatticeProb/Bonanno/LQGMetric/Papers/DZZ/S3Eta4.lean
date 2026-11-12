/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta3
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent6Mom

/-!
# Moments of the η-band approximations on a square, via Riemann sums (P2-DZZETA)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 684–688): (eq-LQG-negative-moment) "by a
straightforward adaption of the proof of Lemma 2.8" (Kahane's comparison with a log-correlated
field; Rhodes–Vargas arXiv:1305.6221 Thm 2.11/2.12). We run the discretized Kahane argument of
`GMCIdent6Grid`/`GMCIdent6Sq` (written for the `h̃`-band density `fineDens`) for the η-band density:

* `etaVec`: the vector `γ η^δ_ε(z_i)` (Gaussian, centred);
* `inner_etaKernelL2_le_wnd`: `⟪K^η_u, K^η_v⟫ ≤ ⟪K^{h̃}_u, K^{h̃}_v⟫` (`0 ≤ K^η ≤ K^{h̃}`, DZZ l. 446:
  the η kernel is the killed kernel of the smaller domain `𝕍 ∩ B(v, r(s))`), hence
  **`cov_etaVec_le`**: the η-band covariance has the same log upper bound as the `h̃`-band one;
* `lintegral_gridSum_etaDens_le`: the one-sided Kahane step `kahane_logRef` at level `j`;
* **`lintegral_square_etaDens_rpow_le`**: `E (∫_{[0,1)²} f_n(a + L y) dy)^q ≤ C`, uniformly in
  `δ`, `n` with `2^{-n} ≤ δ ≤ 4L`, `a`, `L` (Jensen in the offset, Tonelli).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat GMCIdent GMCIdent5 GMCIdent6 DGMC QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}

variable (W) in
/-- the real η-band density `e^{γ η^δ_{2^{-n}}(z) − γ²/2 Var}` -/
def etaDensR (γ δ : ℝ) (n : ℕ) (z : ℂ) (ω : Ω) : ℝ :=
  Real.exp (γ * etaVer W δ n z ω - γ ^ 2 / 2 * etaBVar δ n z)

lemma etaDens_eq_ofReal (γ δ : ℝ) (n : ℕ) (z : ℂ) (ω : Ω) :
    etaDens W γ δ n z ω = ENNReal.ofReal (etaDensR W γ δ n z ω) := rfl

lemma measurable_etaDensR (hW : IsWhiteNoise P W) (γ δ : ℝ) (n : ℕ) :
    Measurable fun p : ℂ × Ω => etaDensR W γ δ n p.1 p.2 :=
  Real.measurable_exp.comp (((measurable_etaVer hW δ n).const_mul γ).sub
    (((continuous_etaBVar hW δ n).measurable.comp measurable_fst).const_mul _))

variable (W) in
/-- the vector `γ η_I(z_i)` -/
def etaVec (γ : ℝ) (I : Set ℝ) {ι : Type*} (zs : ι → ℂ) (ω : Ω) (i : ι) : ℝ :=
  γ * etaField W I (zs i) ω

lemma hasGaussianLaw_etaVec (hW : IsWhiteNoise P W) (γ : ℝ) (I : Set ℝ) {ι : Type} [Fintype ι]
    (zs : ι → ℂ) : HasGaussianLaw (etaVec W γ I zs) P := by
  have h := (hW.isGaussianProcess_comp (fun i : ι => etaKernelL2 I (zs i))).smul
    (fun _ => γ * Real.sqrt Real.pi)
  have e : (fun i ω => etaVec W γ I zs ω i) = fun i ω => (γ * Real.sqrt Real.pi) *
      W (etaKernelL2 I (zs i)) ω := by
    funext i ω
    simp only [etaVec, etaField]; ring
  have h' : IsGaussianProcess (fun i ω => etaVec W γ I zs ω i) P := by
    rw [e]; simpa [smul_eq_mul] using h
  exact hasGaussianLaw_fintype h' (fun i => i)

lemma integral_etaVec (hW : IsWhiteNoise P W) (γ : ℝ) (I : Set ℝ) {ι : Type*} (zs : ι → ℂ)
    (i : ι) : ∫ ω, etaVec W γ I zs ω i ∂P = 0 := by
  simp only [etaVec, etaField]
  rw [integral_const_mul, integral_const_mul, (hW.hasLaw_single _).integral_eq,
    integral_id_gaussianReal, mul_zero, mul_zero]

lemma measurable_etaVec (hW : IsWhiteNoise P W) (γ : ℝ) (I : Set ℝ) {ι : Type*} (zs : ι → ℂ)
    (i : ι) : Measurable fun ω => etaVec W γ I zs ω i :=
  ((hW.measurable _).const_mul _).const_mul _

lemma integrable_exp_etaVec (hW : IsWhiteNoise P W) (γ : ℝ) (I : Set ℝ) {ι : Type*}
    (zs : ι → ℂ) (i : ι) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * etaVec W γ I zs ω i)) P := by
  have h := integrable_exp_wn hW (t * γ * Real.sqrt Real.pi) (etaKernelL2 I (zs i))
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp only [etaVec, etaField]; ring_nf

/-- `0 ≤ K^η ≤ K^{h̃}` gives `⟪K^η_u, K^η_v⟫ ≤ ⟪K^{h̃}_u, K^{h̃}_v⟫` -/
lemma inner_etaKernelL2_le_wnd {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (u v : ℂ) :
    ⟪etaKernelL2 I u, etaKernelL2 I v⟫ ≤
      ⟪wndKernelL2 openSquare I u, wndKernelL2 openSquare I v⟫ := by
  have hu := memLp_wndKernel LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball hI hc₀ hI0 u
  have hv := memLp_wndKernel LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball hI hc₀ hI0 v
  have heu := memLp_etaKernel hI hc₀ hI0 u
  have hev := memLp_etaKernel hI hc₀ hI0 v
  rw [inner_etaKernelL2 hI hc₀ hI0, wndKernelL2, wndKernelL2,
    dite_eq_left_of_eq_true (eq_true hu), dite_eq_left_of_eq_true (eq_true hv), L2.inner_def]
  have h1 : (fun p => ⟪(hu.toLp _ : ℝ × ℂ → ℝ) p, (hv.toLp _ : ℝ × ℂ → ℝ) p⟫) =ᵐ[volume]
      fun p => wndKernel openSquare I u p * wndKernel openSquare I v p := by
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with p h1 h2
    rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
    simp [mul_comm]
  rw [integral_congr_ae h1]
  refine integral_mono (heu.integrable_mul hev) (hu.integrable_mul hv) fun p => ?_
  exact mul_le_mul (etaKernel_le I u p) (etaKernel_le I v p) (etaKernel_nonneg _ _ _)
    (wndKernel_nonneg _ _ _ _)

/-- **covariance upper bound for the η band** (as `cov_bandVec_le`) -/
lemma cov_etaVec_le (hW : IsWhiteNoise P W) (γ : ℝ) {ε δ L : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hδL : δ ≤ L) {ι : Type*} (zs : ι → ℂ) (i k : ι) (hik : ‖zs i - zs k‖ ≤ L) :
    cov[fun ω => etaVec W γ (Ioo (ε ^ 2) (δ ^ 2)) zs ω i,
        fun ω => etaVec W γ (Ioo (ε ^ 2) (δ ^ 2)) zs ω k; P] ≤
      γ ^ 2 * (Real.log (L / max ε ‖zs i - zs k‖) + 1) := by
  have hε2 : (0 : ℝ) < ε ^ 2 / 2 := by positivity
  have hI0 : Ioo (ε ^ 2) (δ ^ 2) ⊆ Ioi (ε ^ 2 / 2) := fun s hs =>
    (half_lt_self (by positivity)).trans hs.1
  simp only [etaVec]
  rw [covariance_const_mul_left, covariance_const_mul_right]
  have hc : cov[etaField W (Ioo (ε ^ 2) (δ ^ 2)) (zs i), etaField W (Ioo (ε ^ 2) (δ ^ 2)) (zs k); P]
      = Real.pi * ⟪etaKernelL2 (Ioo (ε ^ 2) (δ ^ 2)) (zs i),
          etaKernelL2 (Ioo (ε ^ 2) (δ ^ 2)) (zs k)⟫ := by
    unfold etaField
    rw [covariance_const_mul_left, covariance_const_mul_right, hW.cov_eq, ← mul_assoc,
      Real.mul_self_sqrt Real.pi_pos.le]
  have hin := inner_etaKernelL2_le_wnd measurableSet_Ioo hε2 hI0 (zs i) (zs k)
  rw [inner_wndKernelL2 LQGMetric.isOpen_openSquare (by norm_num : (0 : ℝ) ≤ 2)
    openSquare_subset_ball measurableSet_Ioo hε2 hI0] at hin
  have hk := pi_integral_killedHeat_le hε hεδ hδL (zs i) (zs k) hik
  show γ * (γ * cov[etaField W (Ioo (ε ^ 2) (δ ^ 2)) (zs i),
    etaField W (Ioo (ε ^ 2) (δ ^ 2)) (zs k); P]) ≤ _
  rw [hc, ← mul_assoc, ← sq]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg γ)
  exact (mul_le_mul_of_nonneg_left hin Real.pi_pos.le).trans hk

lemma etaDensR_ae_eq_exp (hW : IsWhiteNoise P W) (γ δ : ℝ) (n : ℕ) {ι : Type*} (zs : ι → ℂ)
    (i : ι) : (fun ω => etaDensR W γ δ n (zs i) ω) =ᵐ[P] fun ω =>
      Real.exp (etaVec W γ (etaBand δ n) zs ω i -
        Var[fun ω => etaVec W γ (etaBand δ n) zs ω i; P] / 2) := by
  have hV : Var[fun ω => etaVec W γ (etaBand δ n) zs ω i; P] = γ ^ 2 * etaBVar δ n (zs i) := by
    have e : (fun ω => etaVec W γ (etaBand δ n) zs ω i) =
        γ • fun ω => Real.sqrt Real.pi * W (etaKernelL2 (etaBand δ n) (zs i)) ω := by
      funext ω; simp [etaVec, etaField]
    rw [e, variance_smul, variance_sqrtPi hW, etaBVar]
  filter_upwards [etaVer_ae_eq hW δ n (zs i)] with ω h
  rw [etaDensR, h, hV, etaVec]
  congr 1; ring

/-- **the Kahane step at a fixed offset**, η band -/
theorem lintegral_gridSum_etaDens_le (hW : IsWhiteNoise P W) (γ δ : ℝ) {n j : ℕ}
    (hn : (2 : ℝ)⁻¹ ^ n ≤ δ) {a : ℂ} {L : ℝ} (hL : 0 < L) (hδL : δ ≤ 4 * L)
    (hj : (2 : ℝ)⁻¹ ^ j ≤ (2 : ℝ)⁻¹ ^ n / L) (t : ℂ) {Z : ℕ → ℂ → Ω₀ → ℝ} {c : ℝ}
    (hZ : LogCorr Z P₀ (γ ^ 2) c) {q : ℝ} (hq : q ≤ 0 ∨ 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i : ↥(grid j), (4 : ℝ)⁻¹ ^ j *
        etaDensR W γ δ n (rPt a L j t i) ω) ^ q) ∂P ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) *
        ∫ ω, gM (Z j) P₀ j (grid j) ω ^ q ∂P₀) := by
  set ε : ℝ := (2 : ℝ)⁻¹ ^ n
  have hε : 0 < ε := by positivity
  set X := etaVec W γ (etaBand δ n) (rPt a L j t)
  have hae : ∀ᵐ ω ∂P, ∀ i : ↥(grid j), etaDensR W γ δ n (rPt a L j t i) ω =
      Real.exp (X ω i - Var[fun ω => X ω i; P] / 2) :=
    ae_all_iff.2 fun i => etaDensR_ae_eq_exp hW γ δ n _ i
  have hcov : ∀ i k, cov[fun ω => X ω i, fun ω => X ω k; P] ≤
      -(γ ^ 2 * Real.log (max ((2 : ℝ)⁻¹ ^ j) ‖cpt j i - cpt j k‖)) +
        γ ^ 2 * (Real.log 4 + 1) := by
    intro i k
    have hd := norm_sub_le_two_of_unitSq (cpt_mem_unitSq i.2) (cpt_mem_unitSq k.2)
    have hik : ‖rPt a L j t i - rPt a L j t k‖ ≤ 4 * L := by
      rw [norm_rPt_sub a hL]; nlinarith
    refine (cov_etaVec_le hW γ hε hn hδL _ i k hik).trans ?_
    rw [norm_rPt_sub a hL]
    have hm0 : 0 < max ((2 : ℝ)⁻¹ ^ j) ‖cpt j i - cpt j k‖ :=
      lt_max_of_lt_left (by positivity)
    have hlog : Real.log (4 * L / max ε (L * ‖cpt j i - cpt j k‖)) ≤
        Real.log 4 - Real.log (max ((2 : ℝ)⁻¹ ^ j) ‖cpt j i - cpt j k‖) := by
      rw [← Real.log_div (by norm_num) hm0.ne']
      refine Real.log_le_log (div_pos (by positivity) (lt_max_of_lt_left hε)) ?_
      rw [div_le_div_iff₀ (lt_max_of_lt_left hε) hm0]
      have hmax : L * max ((2 : ℝ)⁻¹ ^ j) ‖cpt j i - cpt j k‖ ≤
          max ε (L * ‖cpt j i - cpt j k‖) := by
        rw [mul_max_of_nonneg _ _ hL.le]
        refine max_le_max ?_ le_rfl
        rw [le_div_iff₀ hL] at hj; linarith
      nlinarith
    nlinarith [sq_nonneg γ]
  have hK := kahane_logRef (hasGaussianLaw_etaVec hW γ (etaBand δ n) (rPt a L j t))
    (integral_etaVec hW γ _ _) (measurable_etaVec hW γ _ _)
    (integrable_exp_etaVec hW γ _ _) (by positivity) hcov hZ hq
  refine le_trans (le_of_eq (lintegral_congr_ae (hae.mono fun ω h => ?_))) hK
  simp_rw [h]; rfl

omit [MeasurableSpace Ω] in
lemma etaDensR_pos (γ δ : ℝ) (n : ℕ) (z : ℂ) (ω : Ω) : 0 < etaDensR W γ δ n z ω :=
  Real.exp_pos _

attribute [local irreducible] etaDensR in
/-- **uniform moments of the η-band integral over a square** -/
theorem lintegral_square_etaDens_rpow_le (hW : IsWhiteNoise P W) (γ : ℝ)
    {Z : ℕ → ℂ → Ω₀ → ℝ} {c : ℝ} (hZ : LogCorr Z P₀ (γ ^ 2) c) {q : ℝ} (hq : q < 0 ∨ 1 < q)
    {C₀ : ℝ} (hC₀ : ∀ j, ∫ ω, gM (Z j) P₀ j (grid j) ω ^ q ∂P₀ ≤ C₀) (δ : ℝ) {n : ℕ}
    (hn : (2 : ℝ)⁻¹ ^ n ≤ δ) (a : ℂ) {L : ℝ} (hL : 0 < L) (hδL : δ ≤ 4 * L) :
    ∫⁻ ω, (∫⁻ y in cell0, ENNReal.ofReal (etaDensR W γ δ n (a + (L : ℂ) * y) ω)) ^ q ∂P ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) * C₀) := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < (2 : ℝ)⁻¹ ^ n / L by positivity)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have hq' : q ≤ 0 ∨ 1 ≤ q := hq.imp le_of_lt le_of_lt
  have hP := hW.isProbabilityMeasure
  have hmeas := measurable_etaDensR hW γ δ n
  set G : Ω → ℂ → ℝ≥0∞ := fun ω y => ENNReal.ofReal (etaDensR W γ δ n (a + (L : ℂ) * y) ω)
  have hGm : Measurable fun p : ℂ × Ω => G p.2 p.1 :=
    ENNReal.measurable_ofReal.comp (hmeas.comp
      ((measurable_const.add (measurable_const.mul measurable_fst)).prodMk measurable_snd))
  set V : ℂ → Ω → ℝ≥0∞ := fun t ω =>
    ∑ i ∈ grid j, ENNReal.ofReal ((4 : ℝ)⁻¹ ^ j) * G ω (cellMap j i t)
  have hV : ∀ ω, ∫⁻ y in cell0, G ω y = ∫⁻ t in cell0, V t ω := fun ω =>
    lintegral_cell0_eq (G ω) (hGm.comp (measurable_id.prodMk measurable_const)) j
  have hVm : Measurable fun p : ℂ × Ω => V p.1 p.2 :=
    Finset.measurable_sum _ fun i _ => Measurable.const_mul (hGm.comp
      (((measurable_cellMap j i).comp measurable_fst).prodMk measurable_snd)) _
  have hpoint : ∀ t, ∫⁻ ω, V t ω ^ q ∂P ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) * C₀) := by
    intro t
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_))
      ((lintegral_gridSum_etaDens_le (a := a) hW γ δ hn hL hδL hj.le t hZ hq').trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hC₀ j) (Real.exp_pos _).le)))
    have hpos : 0 < ∑ i : ↥(grid j), (4 : ℝ)⁻¹ ^ j * etaDensR W γ δ n (rPt a L j t i) ω := by
      haveI := DGMC.grid_nonempty j
      exact Finset.sum_pos (fun i _ => mul_pos (by positivity) (etaDensR_pos γ δ n _ ω))
        Finset.univ_nonempty
    rw [← ENNReal.ofReal_rpow_of_pos hpos]
    congr 1
    simp only [V, G, rPt]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (mul_pos (by positivity)
      (etaDensR_pos γ δ n _ ω)).le), ← Finset.sum_coe_sort (grid j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have hjen : ∀ ω, (∫⁻ t in cell0, V t ω) ^ q ≤ ∫⁻ t in cell0, V t ω ^ q := fun ω => by
    have hm : AEMeasurable (fun t => V t ω) (volume.restrict cell0) :=
      (hVm.comp (measurable_id.prodMk (measurable_const (a := ω)))).aemeasurable
    rcases hq with hq | hq
    · exact Neg3.rpow_lintegral_le_of_neg hm hq
    · exact rpow_lintegral_le hm hq
  calc ∫⁻ ω, (∫⁻ y in cell0, G ω y) ^ q ∂P
      = ∫⁻ ω, (∫⁻ t in cell0, V t ω) ^ q ∂P := lintegral_congr fun ω => by rw [hV ω]
    _ ≤ ∫⁻ ω, (∫⁻ t in cell0, V t ω ^ q) ∂P := lintegral_mono hjen
    _ = ∫⁻ t in cell0, ∫⁻ ω, V t ω ^ q ∂P :=
        lintegral_lintegral_swap ((hVm.comp (measurable_snd.prodMk measurable_fst)).pow_const
          q).aemeasurable
    _ ≤ ∫⁻ (_t : ℂ) in cell0, ENNReal.ofReal
          (Real.exp (q * (q - 1) * (γ ^ 2 * (Real.log 4 + 1) + c) / 2) * C₀) :=
        lintegral_mono fun t => hpoint t
    _ = _ := by rw [setLIntegral_const, volume_cell0, mul_one]

end DZZ
end LQGMetric
