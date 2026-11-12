/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Z3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Z2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53K2

/-!
# DZZ Lemma 5.3 part 1, R2: the event `𝓔₄` and the domination `dzzMuIn ≤ ν_𝖡`
(P2-DZZ53Z, packet P-131R)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, `𝓔₄` l. 2440–2443 and (eq-M-A-upper-bound-bis)
l. 2453–2456, with decision D131 §3 and its amendment §9 (the proxy is
`proxyMass W γ m c_𝖡 S = c_𝖡 · M̃_{γ,2^{-m},η}` on the rational balls inside `S`, S5L53K1).

* `l53ProxyGood`: the full-measure set of the limit step `ae_dzzMuIn_ball_le_proxyMass` (S5L53K2),
  for all scales `m` at once.
* **`l53E4`**: the field part of DZZ's `𝓔₄`: `wickGoodU` (S3EtaB2) ∩ `l53ProxyGood` ∩
  (eq-tilde-h-eta-assump) (`tildeEtaEvent`, from L2.7) ∩ the band comparison
  `nbrFineGen W δ^{-C_mc} e^{L^{0.55}} L^{0.8}` (S3L4Fine; DZZ's band sup l. 2537–2545 and
  (Eq.error-coarse-fine)). The chain part `𝓔* ∩ 𝒟₁` of DZZ's `𝓔₄` is not needed for the
  domination: the mass clause is used through the cell `𝖢` containing the chain box
  (`M_{γ,s_𝖢}(𝖢) < δ²`), with the coarse scale `s_𝖢` and the band `(s', s_𝖢)` controlled by
  `nbrFineGen` (`2^j = s_𝖢/s' ≤ e^{L^{0.55}}`).
* **`l53_E4_prob`**: `P(𝓔₄ᶜ) ≤ e^{−L^{0.23}}` for small `δ` (hence also
  `P(𝒟₁ᴮ ∩ 𝓔₄ᶜ) ≤ e^{−L^{0.23}}`, the DEC-131 §3 target).
* `l53DomC_le`: the constant of the comparison is `≤ e^{L^{0.91}}`.
* **`l53_domination`**: on `𝓔₄`, for every dyadic box `𝖢` of side `≥ δ^{C_mc}` with
  `M_{γ,s_𝖢}(𝖢) ≤ δ²` (every cell, on `cellSizeEvent`), every `j` with `2^j ≤ e^{L^{0.55}}`, every
  `0 < s ≤ s_𝖢`, and every `S` within `3 s_𝖢` of `c_𝖢`: on every rational ball in `(0,1)²`,
  `dzzMuIn ≤ proxyMass W γ (n_𝖢 + j) (δ² s^{−2} e^{L^{0.91}}) S`. With `s = s_b` the side of the
  chain box `b ⊆ 𝖢`, `S = sqBox c_𝖡 (5 s_b/K)` (`sqBox_five_near_center`) and
  `n_𝖢 + j = m_b` this is (eq-M-A-upper-bound-bis) with DZZ's factor `δ² s_i^{−2} e^{L^{0.91}}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the full-measure set of the R2 limit step, all scales -/
def l53ProxyGood (hW : IsWhiteNoise P W) (γ : ℝ) : Set Ω :=
  {ω | ∀ (m : ℕ) (c : ℝ) (x : ℚ × ℚ) (q : ℚ), ball (ratPt x) q ⊆ openSquare →
    (∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict (ball (ratPt x) q)),
      wickDensC hW γ n z ω ≤ ENNReal.ofReal c * etaDens W γ ((2 : ℝ)⁻¹ ^ m) n z ω) →
    dzzMuIn γ W ω (ball (ratPt x) q) ≤ ENNReal.ofReal c * fineMass W γ m ω x q}

theorem ae_l53ProxyGood (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ω ∈ l53ProxyGood hW γ := by
  simp only [l53ProxyGood, mem_ofPred_eq]
  rw [ae_all_iff]; intro m
  filter_upwards [ae_dzzMuIn_ball_le_proxyMass hW hγ hγ2 m univ] with ω hω c x q hB hd
  have h := hω c x q hB (subset_univ _) hd
  rwa [proxyMass_of_subset γ m _ ω (subset_univ _)] at h

/-- **the field part of DZZ's `𝓔₄`** (l. 2440–2443) -/
def l53E4 (hW : IsWhiteNoise P W) (γ δ : ℝ) : Set Ω :=
  wickGoodU hW γ ∩ l53ProxyGood hW γ ∩ tildeEtaEvent hW δ ∩
    nbrFineGen W (δ ^ (-dzzCmc γ)) (Real.exp (Real.log δ⁻¹ ^ (0.55 : ℝ)))
      (Real.log δ⁻¹ ^ (0.8 : ℝ))

/-- **`P(𝓔₄ᶜ) ≤ e^{−L^{0.23}}`** for all small `δ` -/
theorem l53_E4_prob (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P (l53E4 hW γ δ)ᶜ ≤ ENNReal.ofReal (Real.exp (-Real.log δ⁻¹ ^ (0.23 : ℝ))) := by
  have := hW.isProbabilityMeasure
  obtain ⟨c₁, hc₁, δ₁, hδ₁, htilde⟩ := highProb_tildeEtaEvent hW
  obtain ⟨δ₂, hδ₂, hnbr⟩ := l53_nbrFineGen_prob (P := P) hW (dzzCmc_nonneg hγ hγ2)
  set c' := min c₁ 1 with hc'
  have hc'0 : 0 < c' := lt_min hc₁ one_pos
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 ((l53z_ev_mul_rpow_le (2 / c')
    (by norm_num : (0.23 : ℝ) < 1)).and (eventually_ge_atTop (4 / c')))
  refine ⟨min δ₁ (min δ₂ (Real.exp (-max L₀ 1))), by positivity, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδa : δ < δ₁ := hδlt.trans_le (min_le_left _ _)
  have hδb : δ < δ₂ := hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδc : δ < Real.exp (-max L₀ 1) := hδlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set L := Real.log δ⁻¹ with hLdef
  have hLgt : max L₀ 1 < L := by
    rw [hLdef, Real.log_inv, lt_neg]
    exact (Real.log_lt_iff_lt_exp hδ0).2 hδc
  obtain ⟨h1, h2⟩ := hL₀ L ((le_max_left _ _).trans hLgt.le)
  rw [Real.rpow_one] at h1
  have hL1 : 1 < L := (le_max_right _ _).trans_lt hLgt
  have hδ1 : δ < 1 := hδc.trans_le
    (Real.exp_le_one_iff.2 (by linarith [le_max_right L₀ 1]))
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  -- the four pieces
  have hA : P (wickGoodU hW γ)ᶜ = 0 := ae_iff.1 (ae_wickGoodU hW hγ hγ2)
  have hB : P (l53ProxyGood hW γ)ᶜ = 0 := ae_iff.1 (ae_l53ProxyGood hW hγ hγ2)
  have hC := htilde δ ⟨hδ0, hδa⟩
  have hD : P (nbrFineGen W (δ ^ (-dzzCmc γ)) (Real.exp (L ^ (0.55 : ℝ))) (L ^ (0.8 : ℝ)))ᶜ ≤
      ENNReal.ofReal (2 * δ) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hnbr δ ⟨hδ0, hδb⟩)
  have hsplit : P (l53E4 hW γ δ)ᶜ ≤ P (wickGoodU hW γ)ᶜ + P (l53ProxyGood hW γ)ᶜ +
      P (tildeEtaEvent hW δ)ᶜ +
      P (nbrFineGen W (δ ^ (-dzzCmc γ)) (Real.exp (L ^ (0.55 : ℝ))) (L ^ (0.8 : ℝ)))ᶜ := by
    simp only [l53E4, compl_inter]
    refine (measure_union_le _ _).trans (add_le_add_left ((measure_union_le _ _).trans
      (add_le_add_left (measure_union_le _ _) _)) _)
  refine hsplit.trans ?_
  rw [hA, hB, zero_add, zero_add]
  refine (add_le_add hC hD).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `δ^{c₁} + 2δ ≤ 3 δ^{c'} = 3 e^{−c' L} ≤ e^{−L^{0.23}}`
  have e1 : δ ^ c₁ ≤ δ ^ c' := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left _ _)
  have e2 : δ ≤ δ ^ c' := by
    have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right c₁ 1)
    rwa [Real.rpow_one] at this
  have e3 : δ ^ c' = Real.exp (-(c' * L)) := by
    rw [Real.rpow_def_of_pos hδ0, hlogδ]; ring_nf
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hc'L : 4 ≤ c' * L := by
    have := mul_le_mul_of_nonneg_left h2 hc'0.le
    rwa [mul_div_cancel₀ _ hc'0.ne'] at this
  have hc'L2 : L ^ (0.23 : ℝ) ≤ c' * L / 2 := by
    have := mul_le_mul_of_nonneg_left h1 hc'0.le
    rw [← mul_assoc, mul_div_cancel₀ _ hc'0.ne'] at this
    linarith
  calc δ ^ c₁ + 2 * δ ≤ 3 * Real.exp (-(c' * L)) := by rw [← e3]; linarith
    _ = Real.exp (Real.log 3 - c' * L) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-L ^ (0.23 : ℝ)) := Real.exp_le_exp.2 (by linarith)

/-- **the comparison constant is `≤ e^{L^{0.91}}`** for cells of side `≥ δ^{C}` -/
theorem l53DomC_le {γ b₁ Cm : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hb₁ : 0 ≤ b₁) (hCm : 0 ≤ Cm) :
    ∃ L₀ : ℝ, ∀ δ : ℝ, L₀ ≤ Real.log δ⁻¹ → ∀ s : ℝ, Real.log s⁻¹ ≤ Cm * Real.log δ⁻¹ →
      l53DomC γ δ (Real.log δ⁻¹ ^ (0.8 : ℝ)) b₁ s ≤ Real.exp (Real.log δ⁻¹ ^ (0.91 : ℝ)) := by
  set A : ℝ := 4 + 296 * Real.sqrt (Cm + 4) + 2 * b₁ with hA
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 ((l53z_ev_mul_rpow_le A
    (by norm_num : (0.8 : ℝ) < 0.91)).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨L₀, fun δ hδ s hs => ?_⟩
  set L := Real.log δ⁻¹ with hLdef
  obtain ⟨h1, hL1⟩ := hL₀ L hδ
  set T := L ^ (0.8 : ℝ) with hT
  have hL0 : 0 < L := by linarith
  have hT1 : 1 ≤ T := Real.one_le_rpow hL1 (by norm_num)
  have hsqL : Real.sqrt L ≤ T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h5380 : Real.sqrt (1076 * 5) ≤ 74 := by
    calc Real.sqrt (1076 * 5) ≤ Real.sqrt (74 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 74 := Real.sqrt_sq (by norm_num)
  have hsq : Real.sqrt (Real.log s⁻¹ + 4) ≤ Real.sqrt (Cm + 4) * T := by
    calc Real.sqrt (Real.log s⁻¹ + 4) ≤ Real.sqrt ((Cm + 4) * L) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = Real.sqrt (Cm + 4) * Real.sqrt L := Real.sqrt_mul (by linarith) _
      _ ≤ Real.sqrt (Cm + 4) * T := mul_le_mul_of_nonneg_left hsqL (Real.sqrt_nonneg _)
  have hsC := Real.sqrt_nonneg (Cm + 4)
  have hs5 := Real.sqrt_nonneg (1076 * 5)
  have hsl := Real.sqrt_nonneg (Real.log s⁻¹ + 4)
  have hbr : b₁ + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log s⁻¹ + 4) ≤
      b₁ + 148 * (Real.sqrt (Cm + 4) * T) := by
    have := mul_le_mul h5380 hsq hsl (by norm_num)
    nlinarith
  have hbr0 : 0 ≤ b₁ + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log s⁻¹ + 4) := by positivity
  have hg1 : γ * (Real.sqrt L + T) ≤ 2 * (T + T) :=
    (mul_le_mul_of_nonneg_right hγ2.le (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by norm_num))
  have hg2 : γ ^ 2 / 2 * (b₁ + 2 * Real.sqrt (1076 * 5) * Real.sqrt (Real.log s⁻¹ + 4)) ≤
      2 * (b₁ + 148 * (Real.sqrt (Cm + 4) * T)) := by
    have hγ4 : γ ^ 2 / 2 ≤ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hγ4 hbr0).trans
      (mul_le_mul_of_nonneg_left hbr (by norm_num))
  unfold l53DomC
  refine Real.exp_le_exp.2 ?_
  have : 2 * b₁ ≤ 2 * b₁ * T := by nlinarith
  have hAT : A * T = 4 * T + 296 * (Real.sqrt (Cm + 4) * T) + 2 * b₁ * T := by rw [hA]; ring
  linarith

/-- the `5t`-box around a point of `𝖢` lies within `3 s_𝖢` of `c_𝖢` when `5t ≤ s_𝖢` -/
lemma sqBox_five_near_center {B : DyBox} {x : ℂ} (hx : x ∈ B.closedBox) {t : ℝ}
    (ht : 5 * t ≤ B.side) : ∀ z ∈ sqBox x (5 * t), ‖z - B.center‖ ≤ 3 * B.side := by
  intro z ⟨hz1, hz2⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx
  have hs := DyBox.side_pos' B
  have hre : |z.re - B.center.re| ≤ B.side := by
    have : |x.re - B.center.re| ≤ B.side / 2 := by
      simp only [DyBox.center]; rw [abs_le]; constructor <;> nlinarith
    calc |z.re - B.center.re| ≤ |z.re - x.re| + |x.re - B.center.re| := abs_sub_le _ _ _
      _ ≤ B.side := by linarith
  have him : |z.im - B.center.im| ≤ B.side := by
    have : |x.im - B.center.im| ≤ B.side / 2 := by
      simp only [DyBox.center]; rw [abs_le]; constructor <;> nlinarith
    calc |z.im - B.center.im| ≤ |z.im - x.im| + |x.im - B.center.im| := abs_sub_le _ _ _
      _ ≤ B.side := by linarith
  calc ‖z - B.center‖ ≤ |(z - B.center).re| + |(z - B.center).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 3 * B.side := by rw [Complex.sub_re, Complex.sub_im]; linarith

/-- **DZZ (eq-M-A-upper-bound-bis) on `𝓔₄`** (l. 2453–2456, with DV-D131-1 and DEC-131 §9):
for all small `δ`, on `l53E4`, for every dyadic box `𝖢` of side `≥ δ^{C_mc}` with
`M_{γ,s_𝖢}(𝖢) ≤ δ²`, every `j` with `2^j ≤ e^{L^{0.55}}`, every `0 < s ≤ s_𝖢` and every set `S`
within `3 s_𝖢` of `c_𝖢`, on every rational ball in `(0,1)²`:
`dzzMuIn(B(x,q)) ≤ proxyMass W γ (n_𝖢 + j) (δ² s^{−2} e^{L^{0.91}}) S ω x q`. -/
theorem l53_domination (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ ω ∈ l53E4 hW γ δ, ∀ B : DyBox,
      δ ^ dzzCmc γ ≤ B.side → approxLQG γ W ω B ≤ δ ^ 2 →
      ∀ j : ℕ, (2 : ℝ) ^ j ≤ Real.exp (Real.log δ⁻¹ ^ (0.55 : ℝ)) →
      ∀ s : ℝ, 0 < s → s ≤ B.side → ∀ S : Set ℂ, (∀ z ∈ S, ‖z - B.center‖ ≤ 3 * B.side) →
      ∀ (x : ℚ × ℚ) (q : ℚ), ball (ratPt x) q ⊆ openSquare →
        dzzMuIn γ W ω (ball (ratPt x) q) ≤
          proxyMass W γ (B.n + j)
            (ENNReal.ofReal (δ ^ 2 / s ^ 2 * Real.exp (Real.log δ⁻¹ ^ (0.91 : ℝ)))) S ω x q := by
  obtain ⟨b₁, hb₁0, hb₁⟩ := dzz_var_compare
  obtain ⟨L₀, hL₀⟩ := l53DomC_le (Cm := dzzCmc γ) hγ hγ2 hb₁0 (dzzCmc_nonneg hγ hγ2)
  refine ⟨Real.exp (-L₀), Real.exp_pos _, fun δ ⟨hδ0, hδ1⟩ ω hω B hside happ j hj s hs hsB S hS
    x q hBo => ?_⟩
  obtain ⟨⟨⟨hgood, hprox⟩, hE27⟩, hnbr⟩ := hω
  set L := Real.log δ⁻¹ with hLdef
  have hL : L₀ ≤ L := by
    rw [hLdef, Real.log_inv, le_neg]
    exact ((Real.log_lt_iff_lt_exp hδ0).2 hδ1).le
  have hs0 := DyBox.side_pos' B
  -- `2^{n_𝖢} ≤ δ^{-C}` and `log s_𝖢⁻¹ ≤ C L`
  have hsinv : B.side⁻¹ ≤ δ ^ (-dzzCmc γ) := by
    rw [Real.rpow_neg hδ0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hδ0 _) hside
  have hX : (2 : ℝ) ^ B.n ≤ δ ^ (-dzzCmc γ) := by
    refine le_trans (le_of_eq ?_) hsinv
    unfold DyBox.side; rw [inv_pow, inv_inv]
  have hlogs : Real.log B.side⁻¹ ≤ dzzCmc γ * L := by
    have := Real.log_le_log (inv_pos.2 hs0) hsinv
    rw [Real.log_rpow hδ0] at this
    rw [hLdef, Real.log_inv δ]; linarith
  by_cases hBS : ball (ratPt x) q ⊆ S
  swap
  · rw [proxyMass_of_not_subset γ _ _ ω hBS]; exact le_top
  rw [proxyMass_of_subset γ _ _ ω hBS]
  set c := l53DomC γ δ (L ^ (0.8 : ℝ)) b₁ B.side * δ ^ 2 / B.side ^ 2 with hc
  have hd : ∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict (ball (ratPt x) q)),
      wickDensC hW γ n z ω ≤ ENNReal.ofReal c * etaDens W γ ((2 : ℝ)⁻¹ ^ (B.n + j)) n z ω := by
    refine eventually_atTop.2 ⟨B.n + j, fun n hn => ?_⟩
    filter_upwards [ae_restrict_of_ae (l53_dens_le hW hγ hb₁ hgood hE27 hnbr hX happ hj hn),
      ae_restrict_mem measurableSet_ball] with z hz hzb
    exact hz (openSquare_subset_dzzV (hBo hzb)) (by linarith [hS z (hBS hzb)])
  refine (hprox (B.n + j) c x q hBo hd).trans (mul_le_mul_of_nonneg_right ?_ bot_le)
  refine ENNReal.ofReal_le_ofReal ?_
  have hC := hL₀ δ hL B.side hlogs
  have hδ2 : 0 ≤ δ ^ 2 := by positivity
  rw [hc, mul_div_assoc, mul_comm]
  refine mul_le_mul ?_ hC (l53DomC_pos _ _ _ _ _).le (by positivity)
  exact div_le_div_of_nonneg_left hδ2 (by positivity) (pow_le_pow_left₀ hs.le hsB 2)

end DZZ
end LQGMetric
