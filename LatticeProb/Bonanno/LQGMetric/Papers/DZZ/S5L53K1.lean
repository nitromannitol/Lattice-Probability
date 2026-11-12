/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53K1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeas

/-!
# DZZ Lemma 5.3 part 1, R1: the local proxy `ν_B = c_B · M̃_{γ,s',η}` (P2-DZZ53K, packet P-131C)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2433–2459: the proof of
(eq-z-open) uses, for a sub-box `𝖡` (side `t = s/K`), a proxy measure
`δ² s^{-2} e^{(log δ⁻¹)^{0.91}} M_γ^{η̌^𝖡}` that is measurable for the white noise near `𝖡` at
times `< s²` (l. 2452) and dominates `M_γ` on `𝖡` (eq-M-A-upper-bound-bis, l. 2455).

Following decision D131 (DV-D131-1: the killed-kernel field `η̌^𝖡` is replaced by the
time-truncated field `η^{s'}`, `s' = 2^{-m} ≤ s`), the proxy here is DZZ's own η-chaos
`M̃_{γ,s',η}` of (eq-def-tilde-M), l. 677–683, which the library already has set by set:
`etaChaos W γ s' B` (S3Eta1; a.s. limit of its approximations, `ae_tendsto_etaApprox`, S3Eta3;
the domination `M_γ ≤ c δ² s^{-2} M̃_{γ,ε²s,η}` in the analogous situation of (eq-M-tilde-B-bound)
is `l32TildeMUpper_wickQArea`, S3EtaB2). The proxy is a *mass map* on rational balls, the form of
node 2 of decision D131 §3 (P-131D).

* `etaRegT`, `measurable_locFieldT`, **`measurable_etaApprox_locT`**,
  **`measurable_etaChaos_locT`**: the finite-range locality of S3Eta1 (`measurable_etaChaos_loc`,
  proof copied) with the time window `(0, s'^2)` in place of `(0, ∞)` (the band kernels live in
  `(4^{-n}, s'^2)`, `supportedIn_etaKernelL2_Ioo`).
* `fineMass W γ m ω c q = M̃_{γ,2^{-m},η}(B(c, q))`, and `proxyMass W γ m c_B S`: `c_B · fineMass`
  on the rational balls inside `S`, `∞` on the others (balls leaving `S` are never used: the walls
  `𝕍̃_{z,z'}` of node 2 lie in `S = sqBox c_B (5t)`, `tildeBox_subset_sqBox_five`).
* **`measurable_proxyMass_local`**, **`l53_proxyMass_local`**: R1's locality
  `Measurable[wnSigma W (Ioo 0 (s^2) ×ˢ sqBox c (7t))]` for every rational ball, when
  `2^{-m} ≤ s` and `(s' log s'^{-1} + s')/2 < t` (the range bound `etaRad_le_bandHalf`).
* **`ae_tendsto_fineMass`**: a.s., simultaneously for all rational balls, the approximations
  `∫_B e^{γη^{s'}_{2^{-n}} − γ²/2 Var}` converge to `fineMass` (DZZ l. 683).

Why not `fineChaos := dzzMuIn · fineDens⁻¹` (DEC-131 §3 as first written): `dzzMuIn` is the chaos of
`h̃` (`DZZWickChaosAlong`, `ae_isChaosLimit_wickQArea`), so `dzzMuIn · e^{−γη_{s'} + γ²/2 Var η_{s'}}`
is the chaos of `h̃_ε − η_{s'} = (h̃_ε − η_ε) + η^{s'}_ε`, whose first summand reads the white noise in
all of `𝕍` at all times; it is not local and is not the η-band chaos (see the report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat GMCIdent QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-! ## Locality with the time window `(0, δ²)` -/

/-- the white-noise region `(0, δ²) × B^{R+ρ}` -/
def etaRegT (δ R ρ : ℝ) (B : Set ℂ) : Set (ℝ × ℂ) := Ioo 0 (δ ^ 2) ×ˢ thickening (R + ρ) B

lemma etaRegT_subset {δ R ρ : ℝ} {B S' : Set ℂ} {s : ℝ} (hδs : δ ^ 2 ≤ s ^ 2)
    (hB : thickening (R + ρ) B ⊆ S') : etaRegT δ R ρ B ⊆ Ioo 0 (s ^ 2) ×ˢ S' :=
  prod_mono (Ioo_subset_Ioo_right hδs) hB

omit [MeasurableSpace Ω] in
/-- `measurable_locField` (S3Eta1) with the time window (same proof). -/
lemma measurable_locFieldT {δ R ρ : ℝ} (hR : ∀ u ∈ Ioo 0 (δ ^ 2), etaRad u ≤ R) (n : ℕ)
    (B : Set ℂ) (w : ℂ) :
    Measurable[wnSigma W (etaRegT δ R ρ B)] (locField W δ n ρ B w) := by
  unfold locField
  by_cases hw : w ∈ thickening ρ B
  · simp only [hw, ite_true]
    have hs := supportedIn_etaKernelL2_Ioo (a := ((2 : ℝ)⁻¹ ^ n) ^ 2) (b := δ ^ 2) (R := R)
      (by positivity) (fun u hu => hR u ⟨(by positivity : (0 : ℝ) < _).trans hu.1, hu.2⟩) w
    refine (measurable_wnSigma (supportedIn_mono hs ?_)).const_mul _
    rintro ⟨s, x⟩ ⟨hs1, hs2⟩
    refine ⟨⟨(by positivity : (0 : ℝ) < ((2 : ℝ)⁻¹ ^ n) ^ 2).trans hs1.1, hs1.2⟩, ?_⟩
    refine thickening_thickening_subset R ρ B ?_
    rw [mem_thickening_iff]
    exact ⟨w, hw, hs2⟩
  · simp only [hw, ite_false]; exact measurable_const

/-- **finite range with time window**: `etaApprox W γ δ n B` is measurable for the white noise in
`(0, δ²) × B^{R+ρ}` (`measurable_etaApprox_loc`, S3Eta1, same proof). -/
theorem measurable_etaApprox_locT (hW : IsWhiteNoise P W) {δ R ρ : ℝ}
    (hR : ∀ u ∈ Ioo 0 (δ ^ 2), etaRad u ≤ R) (hρ : 0 < ρ) (γ : ℝ) (n : ℕ) {B : Set ℂ}
    (hB : MeasurableSet B) :
    Measurable[wnSigma W (etaRegT δ R ρ B)] (etaApprox W γ δ n B) := by
  have e : etaApprox W γ δ n B = fun ω => ∫⁻ z in B, ENNReal.ofReal (Real.exp
      (γ * dyVer (locField W δ n ρ B) z ω - γ ^ 2 / 2 * etaBVar δ n z)) := by
    funext ω
    refine setLIntegral_congr_fun hB fun z hz => ?_
    rw [etaDens, etaVer_eq_locVer hρ δ n hz ω]
  rw [e]
  have hc := (continuous_etaBVar hW δ n).measurable
  let _ : MeasurableSpace Ω := wnSigma W (etaRegT δ R ρ B)
  have hm := measurable_dyVer (m := wnSigma W (etaRegT δ R ρ B))
    (fun w => measurable_locFieldT (W := W) hR n B w)
  exact ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hm.const_mul γ).sub
    ((hc.comp measurable_fst).const_mul _)))).comp
    measurable_swap).lintegral_prod_right'

/-- **`M̃_{γ,δ,η}(B)` is measurable for the white noise in `(0, δ²) × B^{R+ρ}`**. -/
theorem measurable_etaChaos_locT (hW : IsWhiteNoise P W) {δ R ρ : ℝ}
    (hR : ∀ u ∈ Ioo 0 (δ ^ 2), etaRad u ≤ R) (hρ : 0 < ρ) (γ : ℝ) {B : Set ℂ}
    (hB : MeasurableSet B) :
    Measurable[wnSigma W (etaRegT δ R ρ B)] (etaChaos W γ δ B) := by
  have h := fun n => measurable_etaApprox_locT hW hR hρ γ n hB
  let _ : MeasurableSpace Ω := wnSigma W (etaRegT δ R ρ B)
  exact Measurable.liminf h

/-! ## The proxy mass map -/

variable (W) in
/-- DZZ's `M̃_{γ,s',η}` (eq-def-tilde-M) on the rational balls, `s' = 2^{-m}` -/
def fineMass (γ : ℝ) (m : ℕ) (ω : Ω) (c : ℚ × ℚ) (q : ℚ) : ℝ≥0∞ :=
  etaChaos W γ ((2 : ℝ)⁻¹ ^ m) (Metric.ball (ratPt c) q) ω

open Classical in
variable (W) in
/-- **the proxy `ν_B`** (DZZ l. 2455, DV-D131-1): `c_B · M̃_{γ,s',η}` on the rational balls inside
`S`, `∞` on the others -/
def proxyMass (γ : ℝ) (m : ℕ) (cB : ℝ≥0∞) (S : Set ℂ) (ω : Ω) (c : ℚ × ℚ) (q : ℚ) : ℝ≥0∞ :=
  if Metric.ball (ratPt c) q ⊆ S then cB * fineMass W γ m ω c q else ⊤

omit [MeasurableSpace Ω] in
lemma proxyMass_of_subset (γ : ℝ) (m : ℕ) (cB : ℝ≥0∞) {S : Set ℂ} (ω : Ω) {c : ℚ × ℚ} {q : ℚ}
    (h : Metric.ball (ratPt c) q ⊆ S) :
    proxyMass W γ m cB S ω c q = cB * fineMass W γ m ω c q := by
  simp [proxyMass, h]

omit [MeasurableSpace Ω] in
lemma proxyMass_of_not_subset (γ : ℝ) (m : ℕ) (cB : ℝ≥0∞) {S : Set ℂ} (ω : Ω) {c : ℚ × ℚ}
    {q : ℚ} (h : ¬ Metric.ball (ratPt c) q ⊆ S) : proxyMass W γ m cB S ω c q = ⊤ := by
  simp [proxyMass, h]

lemma measurable_fineMass (hW : IsWhiteNoise P W) (γ : ℝ) (m : ℕ) (c : ℚ × ℚ) (q : ℚ) :
    Measurable fun ω => fineMass W γ m ω c q :=
  measurable_etaChaos hW γ _ _

lemma measurable_proxyMass (hW : IsWhiteNoise P W) (γ : ℝ) (m : ℕ) (cB : ℝ≥0∞) (S : Set ℂ)
    (c : ℚ × ℚ) (q : ℚ) : Measurable fun ω => proxyMass W γ m cB S ω c q := by
  by_cases h : Metric.ball (ratPt c) q ⊆ S
  · simp only [proxyMass, h, ite_true]
    exact (measurable_fineMass hW γ m c q).const_mul _
  · simp only [proxyMass, h, ite_false]; exact measurable_const

/-- **locality of the proxy** (DZZ l. 2452, "measurable with respect to the field `η̌^𝖡`"): every
rational ball mass of `proxyMass` is measurable for the white noise in `(0, s^2) × S'`, if
`S^{R+ρ} ⊆ S'`, `r ≤ R` on `(0, s'^2)` and `s' ≤ s`. -/
theorem measurable_proxyMass_local (hW : IsWhiteNoise P W) {m : ℕ} {R ρ s : ℝ}
    (hR : ∀ u ∈ Ioo 0 (((2 : ℝ)⁻¹ ^ m) ^ 2), etaRad u ≤ R) (hρ : 0 < ρ)
    (hs : ((2 : ℝ)⁻¹ ^ m) ^ 2 ≤ s ^ 2) (γ : ℝ) (cB : ℝ≥0∞) {S S' : Set ℂ}
    (hSS' : thickening (R + ρ) S ⊆ S') (c : ℚ × ℚ) (q : ℚ) :
    Measurable[wnSigma W (Ioo 0 (s ^ 2) ×ˢ S')] fun ω => proxyMass W γ m cB S ω c q := by
  by_cases h : Metric.ball (ratPt c) q ⊆ S
  · simp only [proxyMass, h, ite_true]
    have h1 := measurable_etaChaos_locT hW hR hρ γ (B := Metric.ball (ratPt c) q)
      Metric.isOpen_ball.measurableSet
    have h2 : wnSigma W (etaRegT ((2 : ℝ)⁻¹ ^ m) R ρ (Metric.ball (ratPt c) q)) ≤
        wnSigma W (Ioo 0 (s ^ 2) ×ˢ S') :=
      GMCIdent.wnSigma_mono (etaRegT_subset hs ((thickening_subset_of_subset _ h).trans hSS'))
    exact (h1.mono h2 le_rfl).const_mul _
  · simp only [proxyMass, h, ite_false]; exact measurable_const

/-- `sqBox c (5t)^{r} ⊆ sqBox c (7t)` for `r ≤ t` -/
lemma thickening_sqBox_five_subset {c : ℂ} {t r : ℝ} (hr : r ≤ t) :
    thickening r (sqBox c (5 * t)) ⊆ sqBox c (7 * t) := by
  intro z hz
  rw [mem_thickening_iff] at hz
  obtain ⟨w, ⟨hw1, hw2⟩, hzw⟩ := hz
  rw [dist_eq_norm] at hzw
  have h1 : |z.re - w.re| ≤ ‖z - w‖ := by
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have h2 : |z.im - w.im| ≤ ‖z - w‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  constructor
  · calc |z.re - c.re| ≤ |z.re - w.re| + |w.re - c.re| := abs_sub_le _ _ _
      _ ≤ 7 * t / 2 := by linarith
  · calc |z.im - c.im| ≤ |z.im - w.im| + |w.im - c.im| := abs_sub_le _ _ _
      _ ≤ 7 * t / 2 := by linarith

/-- **R1, locality, at a sub-box** (DZZ l. 2433–2438 and 2452 with DV-D131-1): for the sub-box
centred at `c` of side `t`, the proxy on `sqBox c (5t)` (DZZ's `𝖡*`) is measurable for the white
noise in `(0, s^2) × sqBox c (7t)` (DZZ's `(0, s_i²) × 𝖡**`), if `s' = 2^{-m} ≤ s` and the range
`(s' log s'^{-1} + s')/2` of `η^{s'}` is `< t`. -/
theorem l53_proxyMass_local (hW : IsWhiteNoise P W) (γ : ℝ) {m : ℕ} {s t : ℝ}
    (hs : (2 : ℝ)⁻¹ ^ m ≤ s)
    (ht : ((2 : ℝ)⁻¹ ^ m * Real.log ((2 : ℝ)⁻¹ ^ m)⁻¹ + (2 : ℝ)⁻¹ ^ m) / 2 < t)
    (cB : ℝ≥0∞) (c : ℂ) (c' : ℚ × ℚ) (q : ℚ) :
    Measurable[wnSigma W (Ioo 0 (s ^ 2) ×ˢ sqBox c (7 * t))]
      fun ω => proxyMass W γ m cB (sqBox c (5 * t)) ω c' q := by
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set R : ℝ := (δ * Real.log δ⁻¹ + δ) / 2
  refine measurable_proxyMass_local hW (R := R) (ρ := t - R) (etaRad_le_bandHalf hδ0 hδ1)
    (by linarith) (pow_le_pow_left₀ hδ0.le hs 2) γ cB
    (thickening_sqBox_five_subset (by linarith)) c' q

/-- **the proxy is DZZ's limit** (l. 683): a.s., for all rational balls simultaneously, the
approximations `∫_B e^{γη^{s'}_{2^{-n}} − γ²/2 Var}` converge to `fineMass`. -/
theorem ae_tendsto_fineMass (hW : IsWhiteNoise P W) (γ : ℝ) (m : ℕ) :
    ∀ᵐ ω ∂P, ∀ (c : ℚ × ℚ) (q : ℚ), Tendsto
      (fun n => etaApprox W γ ((2 : ℝ)⁻¹ ^ m) n (Metric.ball (ratPt c) q) ω) atTop
      (𝓝 (fineMass W γ m ω c q)) := by
  rw [ae_all_iff]; intro c
  rw [ae_all_iff]; intro q
  exact ae_tendsto_etaApprox hW γ _ Metric.isOpen_ball.measurableSet measure_ball_lt_top.ne

end DZZ
end LQGMetric
