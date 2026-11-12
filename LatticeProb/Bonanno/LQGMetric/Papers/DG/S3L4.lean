/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Max
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseL4
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw

/-!
# DG Lemma 3.4: the `δ`-scale oscillation of `ĥ_δ` (task P2-DG3A, WP-118)

Ding–Gwynne, *The fractal dimension of Liouville quantum gravity: universality, monotonicity,
and bounds*, arXiv:1807.01072, `metric-comparison-final.tex` (cited `DG:`), Lemma 3.4
(`lem-use-btis`, DG:1044–1050): "For each `ζ ∈ (0,1)` and each bounded domain `U ⊂ ℂ`, it holds
with superpolynomially high probability as `δ → 0` that
`max_{z,w ∈ U : |z−w| ≤ δ} |ĥ_δ(z) − ĥ_δ(w)| ≤ ζ log δ⁻¹`."

DG's proof (DG:1051–1062): `Var(ĥ_δ(z) − ĥ_δ(w)) ≤ |z−w|²/δ² ≤ |z−w|/δ` for `|z−w| ≤ δ`
([DGo, Lemma 3.1]); Fernique ([DZZ, Lemma 2.3]) on squares of side `δ/2`; Borell–TIS; union bound
over `O(δ^{-2})` squares. Here:

* `ĥ_δ` is the continuous version `DDDF.phiVer W P δ 1` of DDDF's `φ_{δ,1}` (DG (3.1),
  DG:907 = DDDF's `φ_{δ,1}`, decision D35; `Blueprint.DFGPSInputsDG` uses the same field);
* the increment bound is used in the form `Var ≤ √2 |z−w|/δ` for all `z, w`
  (`WhiteNoise.variance_phi_sub_le`, DDDF Lemma 4), which is what the packaged
  Fernique + Borell–TIS + union bound `DZZ.dzz_sup_incr_tail` (DZZ Lemma 2.6, second
  inequality, tail form; boxes of side `3δ` around a grid of mesh `≤ δ`) needs;
* a bounded `U` is put inside a square `ferniqueBox x₀ s`, and `dzz_sup_incr_tail` (stated on
  `[0,1]²`) is transported to it by the affine map `v ↦ x₀ + s v` (`osc_tail_box`; own
  bookkeeping step).

"Superpolynomially high probability as `δ → 0`" is read as in `Blueprint.DFGPSInputsDG`
(`P[failure] ≤ K δ^p` for `δ < δ₀`, every `p > 0`; outer measure).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DG

open WhiteNoise DZZ SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma mem_ferniqueBox_iff (x₀ : ℂ) (s : ℝ) (z : ℂ) :
    z ∈ ferniqueBox x₀ s ↔ x₀.re ≤ z.re ∧ z.re ≤ x₀.re + s ∧ x₀.im ≤ z.im ∧ z.im ≤ x₀.im + s := by
  simp [ferniqueBox, Complex.mem_reProdIm, and_assoc]

/-- the affine chart `v ↦ x₀ + s v` of `ferniqueBox x₀ s` by `[0,1]²` -/
lemma affine_mem_unitBox {x₀ z : ℂ} {s : ℝ} (hs : 0 < s) (hz : z ∈ ferniqueBox x₀ s) :
    (z - x₀) / (s : ℂ) ∈ ferniqueBox 0 1 ∧ x₀ + (s : ℂ) * ((z - x₀) / (s : ℂ)) = z := by
  rw [mem_ferniqueBox_iff] at hz ⊢
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  refine ⟨?_, by field_simp; ring⟩
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.zero_re, Complex.zero_im, zero_add]
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨div_nonneg (by linarith) hs.le, (div_le_one hs).2 (by linarith),
    div_nonneg (by linarith) hs.le, (div_le_one hs).2 (by linarith)⟩

/-- `dzz_sup_incr_tail` transported from `[0,1]²` to the square `ferniqueBox x₀ s` -/
theorem osc_tail_box [IsProbabilityMeasure P] {X : ℂ → Ω → ℝ} (hX : IsGaussianProcess X P)
    (h0 : ∀ v, ∫ ω, X v ω ∂P = 0) (hc : ∀ ω, Continuous fun v => X v ω) {K δ s : ℝ} (hK : 0 < K)
    (hδ : 0 < δ) (hs : 0 < s) (x₀ : ℂ)
    (hinc : ∀ u v, ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ K * ‖u - v‖ / δ) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | ∃ u ∈ ferniqueBox x₀ s, ∃ v ∈ ferniqueBox x₀ s, ‖u - v‖ ≤ δ ∧
      2 * (Real.sqrt (2 * (6 * K) * Real.log (2 * (⌈s / δ⌉₊ : ℝ) ^ 2)) +
        ferniqueCF * Real.sqrt (3 * K) + x) ≤ |X u ω - X v ω|} ≤
      Real.exp (-x ^ 2 / (2 * (6 * K))) := by
  set Y : ℂ → Ω → ℝ := fun v ω => X (x₀ + (s : ℂ) * v) ω
  have hY : IsGaussianProcess Y P := hX.comp_right (fun v => x₀ + (s : ℂ) * v)
  have hYc : ∀ ω, Continuous fun v => Y v ω := fun ω =>
    (hc ω).comp (continuous_const.add (continuous_const.mul continuous_id))
  have hδ' : 0 < δ / s := div_pos hδ hs
  have hinc' : ∀ u v, ∫ ω, (Y v ω - Y u ω) ^ 2 ∂P ≤ K * ‖u - v‖ / (δ / s) := by
    intro u v
    refine (hinc _ _).trans (le_of_eq ?_)
    have : x₀ + (s : ℂ) * u - (x₀ + (s : ℂ) * v) = (s : ℂ) * (u - v) := by ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    field_simp
  have h := dzz_sup_incr_tail hY (fun v => h0 _) hYc hK hδ' hinc' hx
  have e : 1 / (δ / s) = s / δ := by field_simp
  rw [e] at h
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)) h
  obtain ⟨u, hu, v, hv, huv, hlt⟩ := hω
  obtain ⟨hu1, hu2⟩ := affine_mem_unitBox hs hu
  obtain ⟨hv1, hv2⟩ := affine_mem_unitBox hs hv
  refine ⟨_, hu1, _, hv1, ?_, ?_⟩
  · have : u - x₀ - (v - x₀) = u - v := by ring
    rw [← sub_div, this, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact div_le_div_of_nonneg_right huv hs.le
  · simp only [Y, hu2, hv2]
    exact hlt

/-- a bounded set lies in a square of side `≥ 1` -/
lemma exists_box_of_isBounded {U : Set ℂ} (hU : Bornology.IsBounded U) :
    ∃ x₀ : ℂ, ∃ s : ℝ, 1 ≤ s ∧ U ⊆ ferniqueBox x₀ s := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hU
  set r := |R| + 1
  refine ⟨⟨-r, -r⟩, 2 * r, by have := abs_nonneg R; linarith, fun z hz => ?_⟩
  have hz' : ‖z‖ ≤ R := by simpa using hR hz
  have h1 := Complex.abs_re_le_norm z
  have h2 := Complex.abs_im_le_norm z
  have h3 := le_abs_self R
  rw [mem_ferniqueBox_iff]
  simp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    [linarith [neg_abs_le z.re]; linarith [le_abs_self z.re];
      linarith [neg_abs_le z.im]; linarith [le_abs_self z.im]]

variable {W : WNSpace → Ω → ℝ}

/-- the facts on `ĥ_δ = phiVer W P δ 1` used below: Gaussian process, centred,
`E(ĥ_δ(v) − ĥ_δ(u))² ≤ √2 |u − v|/δ` -/
lemma phiVer_props (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    IsGaussianProcess (DDDF.phiVer W P δ 1) P ∧ (∀ v, ∫ ω, DDDF.phiVer W P δ 1 v ω ∂P = 0) ∧
      (∀ ω, Continuous fun v => DDDF.phiVer W P δ 1 v ω) ∧
      ∀ u v, ∫ ω, (DDDF.phiVer W P δ 1 v ω - DDDF.phiVer W P δ 1 u ω) ^ 2 ∂P ≤
        Real.sqrt 2 * ‖u - v‖ / δ := by
  have := hW.isProbabilityMeasure
  have hver := DDDF.isPhiVersion_phiVer hW hδ hδ1
  have hG : IsGaussianProcess (fun v => phi W δ 1 (id v)) P := isGaussianProcess_phi_comp hW δ 1 id
  refine ⟨hG.congr fun x => (hver.ae_eq x).symm, fun v => ?_, hver.cont, fun u v => ?_⟩
  · rw [integral_congr_ae (hver.ae_eq v)]; exact integral_phi hW δ 1 v
  · have hae : (fun ω => (DDDF.phiVer W P δ 1 v ω - DDDF.phiVer W P δ 1 u ω) ^ 2) =ᵐ[P]
        fun ω => (phi W δ 1 v ω - phi W δ 1 u ω) ^ 2 := by
      filter_upwards [hver.ae_eq u, hver.ae_eq v] with ω h1 h2; rw [h1, h2]
    have hiv : Integrable (phi W δ 1 v) P := (hG.hasGaussianLaw_eval v).integrable
    have hiu : Integrable (phi W δ 1 u) P := (hG.hasGaussianLaw_eval u).integrable
    have h0 : ∫ ω, (phi W δ 1 v ω - phi W δ 1 u ω) ∂P = 0 := by
      rw [integral_sub hiv hiu, integral_phi hW, integral_phi hW, sub_zero]
    have hv := variance_of_integral_eq_zero (X := fun ω => phi W δ 1 v ω - phi W δ 1 u ω)
      (μ := P) ((measurable_phi hW δ 1 v).sub (measurable_phi hW δ 1 u)).aemeasurable h0
    rw [integral_congr_ae hae, ← hv, norm_sub_rev]
    exact variance_phi_sub_le hW hδ hδ1 v u

/-- the oscillation tail of `ĥ_δ` on a square (`osc_tail_box` with `K = √2`) -/
theorem phiVer_osc_tail (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {C : ℝ}
    (hC : 0 < C) (x₀ : ℂ) {s : ℝ} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | ∃ u ∈ ferniqueBox x₀ s, ∃ v ∈ ferniqueBox x₀ s, ‖u - v‖ ≤ C * δ ∧
      2 * (Real.sqrt (2 * (6 * (Real.sqrt 2 * C)) * Real.log (2 * (⌈s / (C * δ)⌉₊ : ℝ) ^ 2)) +
        ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * C)) + x) ≤
          |DDDF.phiVer W P δ 1 u ω - DDDF.phiVer W P δ 1 v ω|} ≤
      Real.exp (-x ^ 2 / (2 * (6 * (Real.sqrt 2 * C)))) := by
  have := hW.isProbabilityMeasure
  obtain ⟨hG, h0, hc, hinc⟩ := phiVer_props hW hδ hδ1
  refine osc_tail_box hG h0 hc (K := Real.sqrt 2 * C) (δ := C * δ) (by positivity)
    (by positivity) hs x₀ (fun u v => (hinc u v).trans (le_of_eq ?_)) hx
  field_simp

/-- `log(2⌈s/δ⌉²) ≤ log(2(s+1)²) + 2 log δ⁻¹` for `0 < δ ≤ 1`, `s > 0` -/
lemma log_two_ceil_sq_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (2 * (⌈s / δ⌉₊ : ℝ) ^ 2) ≤ Real.log (2 * (s + 1) ^ 2) + 2 * Real.log δ⁻¹ := by
  have hm1 : (1 : ℝ) ≤ ⌈s / δ⌉₊ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (div_pos hs hδ)).ne'
  have hm2 : (⌈s / δ⌉₊ : ℝ) ≤ (s + 1) * δ⁻¹ := by
    have := Nat.ceil_lt_add_one (div_pos hs hδ).le
    have h1 : 1 ≤ δ⁻¹ := one_le_inv_iff₀.2 ⟨hδ, hδ1⟩
    have e : s / δ = s * δ⁻¹ := div_eq_mul_inv s δ
    rw [e] at this ⊢
    nlinarith
  calc Real.log (2 * (⌈s / δ⌉₊ : ℝ) ^ 2) ≤ Real.log (2 * (s + 1) ^ 2 * (δ⁻¹ ^ 2)) := by
        apply Real.log_le_log (by positivity)
        have : (⌈s / δ⌉₊ : ℝ) ^ 2 ≤ ((s + 1) * δ⁻¹) ^ 2 := pow_le_pow_left₀ (by linarith) hm2 2
        nlinarith
    _ = Real.log (2 * (s + 1) ^ 2) + 2 * Real.log δ⁻¹ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring

/-- **DG Lemma 3.4** (`lem-use-btis`, DG:1044–1050), for pairs at distance `≤ Cδ` (`C ≥ 1`; this
form is used in DG's proofs of Lemmas 3.6 and 3.7, "applied with `ζ/(2C)` in place of `ζ`"):
for `ζ > 0` and bounded `U`, with superpolynomially high probability as `δ → 0`,
`max_{z,w ∈ U, |z−w| ≤ Cδ} |ĥ_δ(z) − ĥ_δ(w)| ≤ ζ log δ⁻¹`. -/
theorem dg_lemma34C (hW : IsWhiteNoise P W) {U : Set ℂ} (hU : Bornology.IsBounded U) {ζ : ℝ}
    (hζ : 0 < ζ) {C : ℝ} (hC : 1 ≤ C) {p : ℝ} (hp : 0 < p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ∃ z ∈ U, ∃ w ∈ U, ‖z - w‖ ≤ C * δ ∧
        ζ * Real.log δ⁻¹ < |DDDF.phiVer W P δ 1 z ω - DDDF.phiVer W P δ 1 w ω|} ≤
        ENNReal.ofReal (δ ^ p) := by
  have := hW.isProbabilityMeasure
  obtain ⟨x₀, s, hs1, hUs⟩ := exists_box_of_isBounded hU
  have hs : 0 < s := by linarith
  have hC0 : 0 < C := by linarith
  set c : ℝ := 2 * (6 * (Real.sqrt 2 * C)) with hc_def
  have hc : 0 < c := by positivity
  set a : ℝ := Real.log (2 * (s + 1) ^ 2)
  have ha : 0 ≤ a := Real.log_nonneg (by nlinarith)
  set B : ℝ := ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * C))
  have hB : 0 ≤ B := mul_nonneg ferniqueCF_pos.le (Real.sqrt_nonneg _)
  set L₀ : ℝ := max 1 (max (64 * c * (a + 2) / ζ ^ 2) (max (8 * B / ζ) (16 * c * p / ζ ^ 2)))
  refine ⟨min 1 (Real.exp (-L₀)), lt_min one_pos (Real.exp_pos _), fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδ1 : δ ≤ 1 := (hδ.trans_le (min_le_left _ _)).le
  set L := Real.log δ⁻¹ with hL_def
  have hLL : L₀ < L := by
    have h := Real.log_lt_log hδ0 (hδ.trans_le (min_le_right _ _))
    rw [Real.log_exp] at h
    rw [hL_def, Real.log_inv]; linarith
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hLL.le
  have hLa : 64 * c * (a + 2) / ζ ^ 2 ≤ L :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hLL.le
  have hLB : 8 * B / ζ ≤ L :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hLL.le
  have hLp : 16 * c * p / ζ ^ 2 ≤ L :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hLL.le
  have hζ2 : 0 < ζ ^ 2 := by positivity
  -- the threshold of `phiVer_osc_tail` with `x = ζL/4` is `≤ ζL`
  have hA : Real.sqrt (c * Real.log (2 * (⌈s / (C * δ)⌉₊ : ℝ) ^ 2)) ≤ ζ * L / 8 := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : Real.log (2 * (⌈s / (C * δ)⌉₊ : ℝ) ^ 2) ≤ a + 2 * L := by
      refine le_trans ?_ (log_two_ceil_sq_le hs hδ0 hδ1)
      have hpos : (0 : ℝ) < ⌈s / (C * δ)⌉₊ :=
        Nat.cast_pos.2 (Nat.ceil_pos.2 (by positivity))
      apply Real.log_le_log (by positivity)
      have : (⌈s / (C * δ)⌉₊ : ℝ) ≤ ⌈s / δ⌉₊ := by
        exact_mod_cast Nat.ceil_mono (div_le_div_of_nonneg_left hs.le hδ0 (by nlinarith))
      have := pow_le_pow_left₀ hpos.le this 2
      linarith
    have h2 : c * (a + 2) ≤ ζ ^ 2 * L / 64 := by
      rw [div_le_iff₀ hζ2] at hLa; nlinarith
    calc c * Real.log (2 * (⌈s / (C * δ)⌉₊ : ℝ) ^ 2) ≤ c * (a + 2 * L) :=
          mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ c * (a + 2) * L := by
          have : a ≤ a * L := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left this hc.le]
      _ ≤ ζ ^ 2 * L / 64 * L := mul_le_mul_of_nonneg_right h2 (by linarith)
      _ = (ζ * L / 8) ^ 2 := by ring
  have hB' : B ≤ ζ * L / 8 := by
    rw [div_le_iff₀ hζ] at hLB; linarith
  have hx : 0 ≤ ζ * L / 4 := by positivity
  have h := phiVer_osc_tail (P := P) hW hδ0 hδ1 hC0 x₀ hs hx
  have hsub : {ω | ∃ z ∈ U, ∃ w ∈ U, ‖z - w‖ ≤ C * δ ∧
        ζ * L < |DDDF.phiVer W P δ 1 z ω - DDDF.phiVer W P δ 1 w ω|} ⊆
      {ω | ∃ u ∈ ferniqueBox x₀ s, ∃ v ∈ ferniqueBox x₀ s, ‖u - v‖ ≤ C * δ ∧
        2 * (Real.sqrt (2 * (6 * (Real.sqrt 2 * C)) * Real.log (2 * (⌈s / (C * δ)⌉₊ : ℝ) ^ 2)) +
          ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * C)) + ζ * L / 4) ≤
            |DDDF.phiVer W P δ 1 u ω - DDDF.phiVer W P δ 1 v ω|} := by
    rintro ω ⟨z, hz, w, hw, hzw, hlt⟩
    refine ⟨z, hUs hz, w, hUs hw, hzw, ?_⟩
    have : 2 * (Real.sqrt (c * Real.log (2 * (⌈s / (C * δ)⌉₊ : ℝ) ^ 2)) + B + ζ * L / 4) ≤ ζ * L := by
      linarith
    exact this.trans hlt.le
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal (h.trans ?_)
  rw [Real.rpow_def_of_pos hδ0]
  apply Real.exp_le_exp.2
  have hlog : Real.log δ = -L := by rw [hL_def, Real.log_inv, neg_neg]
  rw [hlog, ← hc_def]
  have h3 : p ≤ ζ ^ 2 * L / (16 * c) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hζ2] at hLp; nlinarith
  rw [div_le_iff₀ (by positivity)]
  have : (ζ * L / 4) ^ 2 = ζ ^ 2 * L / (16 * c) * (c * L) := by field_simp; ring
  nlinarith

/-- **DG Lemma 3.4** (`lem-use-btis`, DG:1044–1050): for `ζ > 0` and bounded `U`, with
superpolynomially high probability as `δ → 0`,
`max_{z,w ∈ U, |z−w| ≤ δ} |ĥ_δ(z) − ĥ_δ(w)| ≤ ζ log δ⁻¹` (the case `C = 1` of
`dg_lemma34C`). -/
theorem dg_lemma34 (hW : IsWhiteNoise P W) {U : Set ℂ} (hU : Bornology.IsBounded U) {ζ : ℝ}
    (hζ : 0 < ζ) {p : ℝ} (hp : 0 < p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ∃ z ∈ U, ∃ w ∈ U, ‖z - w‖ ≤ δ ∧
        ζ * Real.log δ⁻¹ < |DDDF.phiVer W P δ 1 z ω - DDDF.phiVer W P δ 1 w ω|} ≤
        ENNReal.ofReal (δ ^ p) := by
  simpa only [one_mul] using dg_lemma34C hW hU hζ le_rfl hp

end DG
end LQGMetric
