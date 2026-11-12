/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61P1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117F2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117G3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61G1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CMW2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Reg
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcL2

/-!
# DZZ (eq-point-to-boundary-kappa), lower half: tools (P2-DZZ61P, D117 packet P-61P)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2593–2596: "by Lemma 5.4 and a
similar derivation to (eq-distance-point-to-boundary-bound)". The derivation transports L5.4 at
a fixed box by lem-scaling-coupling (l. 611–624) and removes the wall by (eq-geodesic-range)
(l. 2340–2345). Deterministic and measure-theoretic tools:

* `integral_ge_of_ae_le_off`: `E Y − t P(Bd) − E Y²/t ≤ E X` when `0 ≤ X` and `Y ≤ X` off `Bd`
  (own elementary step: `Y ≤ t + Y²/t`; the second moment replaces DZZ's tacit
  "with high probability ⇒ in expectation", made rigorous with the crude moments l. 849–857);
* `lgdMinSet_le_image`: monotonicity of `min D` under a pointwise comparison through a map
  (with `log_toNat_mono`, S3ConcL2, for `log D`);
* `simMap_ofReal_image_sqBox`, `simMap_image_frontier`: `θ(𝕍_{c,l}) = 𝕍_{θc, r l}` and
  `θ(∂S) = ∂(θS)` for `θ = simMap r b`, `r > 0`;
* `integral_ballMassQ_eq`: expectations of functions of the rational ball masses of `M_{γ,η}` do
  not depend on the white noise (from `map_ballMassQ_dzzMuIn_eq`, P2-DZZDB);
* `ae_lgdMinSet_wallSq_lt_top`: a.s. finiteness of `min_{∂𝕍_{v,κ}} D̄^{v,2κ}(v,·)` (pattern of
  `ae_lgd_tilde_lt_top`, S5L53Side).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- `E Y − t P(Bd) − E Y²/t ≤ E X` if `X ≥ 0` is integrable, `Y ∈ L²` and `Y ≤ X` a.s. off `Bd`
(any set; own elementary step, `Y ≤ t + Y²/t`). -/
theorem integral_ge_of_ae_le_off {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    {Bd : Set Ω} (hX0 : ∀ ω, 0 ≤ X ω) (hXi : Integrable X P) (hY : MemLp Y 2 P)
    (h : ∀ᵐ ω ∂P, ω ∉ Bd → Y ω ≤ X ω) {t : ℝ} (ht : 0 < t) :
    ∫ ω, Y ω ∂P - t * P.real Bd - (∫ ω, Y ω ^ 2 ∂P) / t ≤ ∫ ω, X ω ∂P := by
  set T := toMeasurable P Bd with hTdef
  have hT : MeasurableSet T := measurableSet_toMeasurable P Bd
  have hBT : Bd ⊆ T := subset_toMeasurable P Bd
  have hPT : P.real T = P.real Bd := by
    simp only [measureReal_def, hTdef, measure_toMeasurable]
  have hYi : Integrable Y P := hY.integrable one_le_two
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := hY.integrable_sq
  have hI : Integrable (T.indicator (1 : Ω → ℝ)) P := (integrable_const (1 : ℝ)).indicator hT
  have hpt : ∀ᵐ ω ∂P, Y ω - t * T.indicator (1 : Ω → ℝ) ω - Y ω ^ 2 / t ≤ X ω := by
    filter_upwards [h] with ω hω
    have hsq : Y ω - t ≤ Y ω ^ 2 / t := by
      rw [le_div_iff₀ ht]; nlinarith [sq_nonneg (Y ω - t / 2)]
    have hsq0 : 0 ≤ Y ω ^ 2 / t := by positivity
    by_cases hωT : ω ∈ T
    · rw [indicator_of_mem hωT, Pi.one_apply]
      linarith [hX0 ω]
    · rw [indicator_of_notMem hωT]
      have := hω (fun hb => hωT (hBT hb))
      linarith
  calc ∫ ω, Y ω ∂P - t * P.real Bd - (∫ ω, Y ω ^ 2 ∂P) / t
      = ∫ ω, (Y ω - t * T.indicator (1 : Ω → ℝ) ω - Y ω ^ 2 / t) ∂P := by
        rw [integral_sub (f := fun ω => Y ω - t * T.indicator (1 : Ω → ℝ) ω)
          (g := fun ω => Y ω ^ 2 / t) (hYi.sub (hI.const_mul t)) (hY2.div_const t),
          integral_sub (f := Y) (g := fun ω => t * T.indicator (1 : Ω → ℝ) ω) hYi
            (hI.const_mul t), integral_const_mul, integral_indicator_one hT,
          integral_div, hPT]
    _ ≤ ∫ ω, X ω ∂P := integral_mono_ae ((hYi.sub (hI.const_mul t)).sub (hY2.div_const t)) hXi hpt

/-- a pointwise comparison through a map `f` passes to the set minima -/
lemma lgdMinSet_le_image {μ₁ μ₂ : Measure ℂ} {δ₁ δ₂ : ℝ} {f : ℂ → ℂ} {A B : Set ℂ}
    (h : ∀ x ∈ A, ∀ y ∈ B, lgdDZZ μ₁ δ₁ x y ≤ lgdDZZ μ₂ δ₂ (f x) (f y)) :
    lgdMinSet μ₁ δ₁ A B ≤ lgdMinSet μ₂ δ₂ (f '' A) (f '' B) := by
  unfold lgdMinSet
  refine le_iInf₂ fun x' hx' => le_iInf₂ fun y' hy' => ?_
  obtain ⟨x, hx, rfl⟩ := hx'
  obtain ⟨y, hy, rfl⟩ := hy'
  exact (iInf₂_le x hx).trans ((iInf₂_le y hy).trans (h x hx y hy))

/-- `simMap a b` as a homeomorphism (`a ≠ 0`) -/
def simHomeo (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)

lemma coe_simHomeo (a b : ℂ) (ha : a ≠ 0) : ⇑(simHomeo a b ha) = simMap a b := by
  funext z; simp [simHomeo, simMap]

lemma simMap_image_frontier {a : ℂ} (ha : a ≠ 0) (b : ℂ) (S : Set ℂ) :
    simMap a b '' frontier S = frontier (simMap a b '' S) := by
  rw [← coe_simHomeo a b ha]; exact (simHomeo a b ha).image_frontier S

lemma simMap_ofReal_re (r : ℝ) (b w : ℂ) : (simMap (r : ℂ) b w).re = r * w.re + b.re := by
  simp [simMap]

lemma simMap_ofReal_im (r : ℝ) (b w : ℂ) : (simMap (r : ℂ) b w).im = r * w.im + b.im := by
  simp [simMap]

/-- `θ(𝕍_{c,l}) = 𝕍_{θc, r l}` for `θ = simMap r b`, `r > 0` -/
lemma simMap_ofReal_image_sqBox {r : ℝ} (hr : 0 < r) (b c : ℂ) (l : ℝ) :
    simMap (r : ℂ) b '' sqBox c l = sqBox (simMap (r : ℂ) b c) (r * l) := by
  ext z
  constructor
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    simp only [sqBox, mem_setOf_eq, simMap_ofReal_re, simMap_ofReal_im]
    rw [show r * w.re + b.re - (r * c.re + b.re) = r * (w.re - c.re) by ring,
      show r * w.im + b.im - (r * c.im + b.im) = r * (w.im - c.im) by ring, abs_mul, abs_mul,
      abs_of_pos hr]
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    simp only [simMap_ofReal_re, simMap_ofReal_im] at h1 h2
    refine ⟨⟨(z.re - b.re) / r, (z.im - b.im) / r⟩, ⟨?_, ?_⟩, ?_⟩
    · show |(z.re - b.re) / r - c.re| ≤ l / 2
      rw [show (z.re - b.re) / r - c.re = (z.re - (r * c.re + b.re)) / r by field_simp; ring,
        abs_div, abs_of_pos hr, div_le_iff₀ hr]
      linarith
    · show |(z.im - b.im) / r - c.im| ≤ l / 2
      rw [show (z.im - b.im) / r - c.im = (z.im - (r * c.im + b.im)) / r by field_simp; ring,
        abs_div, abs_of_pos hr, div_le_iff₀ hr]
      linarith
    · apply Complex.ext
      · rw [simMap_ofReal_re]; field_simp; ring
      · rw [simMap_ofReal_im]; field_simp; ring

/-- **expectations of functions of the rational ball masses of `M_{γ,η}` do not depend on the
white noise** -/
theorem integral_ballMassQ_eq {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ}
    {W' : WNSpace → Ω' → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {F : (ℚ × ℚ → ℚ → ℝ≥0∞) → ℝ} (hF : Measurable F) :
    ∫ ω, F (ballMassQ (dzzMuIn γ W ω)) ∂P = ∫ ω, F (ballMassQ (dzzMuIn γ W' ω)) ∂P' := by
  rw [← integral_map (aemeasurable_ballMassQ_dzzMuIn hW hγ hγ2) hF.aestronglyMeasurable,
    ← integral_map (aemeasurable_ballMassQ_dzzMuIn hW' hγ hγ2) hF.aestronglyMeasurable,
    map_ballMassQ_dzzMuIn_eq hW hW' hγ hγ2]

lemma measurable_eval_ballMassQ (c : ℚ × ℚ) (q : ℚ) :
    Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => m c q :=
  (measurable_pi_apply q).comp (measurable_pi_apply c)

/-- the law transfer for the walled `log min D` -/
theorem integral_logMinLGD_wall_eq {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ}
    {W' : WNSpace → Ω' → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (K : Set ℂ) (δ : ℝ) (A B : Set ℂ) :
    ∫ ω, logMinLGD (dzzWall K (dzzMuIn γ W ω)) δ A B ∂P =
      ∫ ω, logMinLGD (dzzWall K (dzzMuIn γ W' ω)) δ A B ∂P' := by
  have hF : Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ =>
      Real.log ((lgdRat (wallMass K m) δ A B).toNat : ℝ) :=
    measurable_log_toNat.comp (measurable_lgdRat (m := fun m => wallMass K m)
      (fun c q => (measurable_eval_ballMassQ c q).add measurable_const) δ A B)
  have e : ∀ μ : Measure ℂ, logMinLGD (dzzWall K μ) δ A B =
      Real.log ((lgdRat (wallMass K (ballMassQ μ)) δ A B).toNat : ℝ) := fun μ => by
    rw [logMinLGD, lgdMinSet_eq_lgdRat, ballMassQ_dzzWall]
  simp_rw [e]
  exact integral_ballMassQ_eq hW hW' hγ hγ2 hF

/-- the point `v + κ/2` lies on `∂𝕍_{v,κ}` -/
lemma right_mem_frontier_sqBox (v : ℂ) {κ : ℝ} (hκ : 0 < κ) :
    (⟨v.re + κ / 2, v.im⟩ : ℂ) ∈ frontier (sqBox v κ) := by
  rw [frontier_sqBox hκ]
  refine Or.inr ?_
  rw [Complex.mem_reProdIm]
  exact ⟨rfl, ⟨by linarith, by linarith⟩⟩

/-- **a.s. finiteness of `min_{∂𝕍_{v,κ}} D̄^{v,2κ}(v,·)`** (pattern of `ae_lgd_tilde_lt_top`) -/
theorem ae_lgdMinSet_wallSq_lt_top {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {v : ℂ} {κ : ℝ} (hκ : 0 < κ)
    (hre : |v.re - 1 / 2| + κ < 1 / 2) (him : |v.im - 1 / 2| + κ < 1 / 2) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, lgdMinSet (dzzWall (sqBox v (2 * κ)) (dzzMuIn γ W ω)) δ {v}
      (frontier (sqBox v κ)) < ⊤ := by
  filter_upwards [ae_wickQArea_reg hW hγ hγ2] with ω hω
  obtain ⟨hK, hat⟩ := hω
  have hBS : Metric.ball v κ ⊆ openSquare := fun z hz => by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - v)
    have h2 := Complex.abs_im_le_norm (z - v)
    rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
    rw [abs_le] at h1 h2
    have a1 := le_abs_self (v.re - 1 / 2)
    have a2 := neg_abs_le (v.re - 1 / 2)
    have a3 := le_abs_self (v.im - 1 / 2)
    have a4 := neg_abs_le (v.im - 1 / 2)
    show 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hBT : Metric.ball v κ ⊆ sqBox v (2 * κ) := fun z hz => by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - v)
    have h2 := Complex.abs_im_le_norm (z - v)
    rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
    exact ⟨by linarith, by linarith⟩
  have hBV : Metric.ball v κ ⊆ dzzV := hBS.trans fun z hz =>
    ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  have hw : ∀ K ⊆ Metric.ball v κ,
      dzzWall (sqBox v (2 * κ)) (dzzMuIn γ W ω) K = wickQArea γ W ω K := fun K hKB => by
    rw [dzzWall_apply_of_subset (isClosed_sqBox _ _).measurableSet (hKB.trans hBT),
      dzzMuIn, dzzWall_apply_of_subset isClosed_dzzV.measurableSet (hKB.trans hBV)]
  set y : ℂ := ⟨v.re + κ / 2, v.im⟩
  have hy := right_mem_frontier_sqBox v hκ
  have hvm : v ∈ Metric.ball v κ := Metric.mem_ball_self hκ
  have hym : y ∈ Metric.ball v κ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : y - v = ((κ / 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [y]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  refine lt_of_le_of_lt ?_ (lgdDZZ_lt_top_of_convex Metric.isOpen_ball (convex_ball _ _)
    (fun K hKc hKB => by rw [hw K hKB]; exact hK K hKc (hKB.trans hBS))
    (fun x hx => by rw [hw {x} (singleton_subset_iff.mpr hx)]; exact hat x (hBS hx))
    hδ hvm hym)
  unfold lgdMinSet
  exact iInf₂_le_of_le v (mem_singleton v) (iInf₂_le y hy)

/-- lintegral version of `integral_ballMassQ_eq` -/
theorem lintegral_ballMassQ_eq {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ}
    {W' : WNSpace → Ω' → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {F : (ℚ × ℚ → ℚ → ℝ≥0∞) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (ballMassQ (dzzMuIn γ W ω)) ∂P = ∫⁻ ω, F (ballMassQ (dzzMuIn γ W' ω)) ∂P' := by
  rw [← lintegral_map' hF.aemeasurable (aemeasurable_ballMassQ_dzzMuIn hW hγ hγ2),
    ← lintegral_map' hF.aemeasurable (aemeasurable_ballMassQ_dzzMuIn hW' hγ hγ2),
    map_ballMassQ_dzzMuIn_eq hW hW' hγ hγ2]

/-- the law transfer for the second moment of the walled `log min D` -/
theorem lintegral_sq_logMinLGD_wall_eq {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ}
    {W' : WNSpace → Ω' → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (K : Set ℂ) (δ : ℝ) (A B : Set ℂ) :
    ∫⁻ ω, ENNReal.ofReal (logMinLGD (dzzWall K (dzzMuIn γ W ω)) δ A B) ^ 2 ∂P =
      ∫⁻ ω, ENNReal.ofReal (logMinLGD (dzzWall K (dzzMuIn γ W' ω)) δ A B) ^ 2 ∂P' := by
  have hF : Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ =>
      ENNReal.ofReal (Real.log ((lgdRat (wallMass K m) δ A B).toNat : ℝ)) ^ 2 :=
    (ENNReal.measurable_ofReal.comp (measurable_log_toNat.comp
      (measurable_lgdRat (m := fun m => wallMass K m)
        (fun c q => (measurable_eval_ballMassQ c q).add measurable_const) δ A B))).pow_const 2
  have e : ∀ μ : Measure ℂ, logMinLGD (dzzWall K μ) δ A B =
      Real.log ((lgdRat (wallMass K (ballMassQ μ)) δ A B).toNat : ℝ) := fun μ => by
    rw [logMinLGD, lgdMinSet_eq_lgdRat, ballMassQ_dzzWall]
  simp_rw [e]
  exact lintegral_ballMassQ_eq hW hW' hγ hγ2 hF

lemma aemeasurable_dzzWall_dzzMuIn_ball {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (K : Set ℂ) (c : ℂ) (r : ℝ) :
    AEMeasurable (fun ω => dzzWall K (dzzMuIn γ W ω) (Metric.ball c r)) P := by
  simp only [dzzWall, dzzMuIn, Measure.add_apply, Measure.smul_apply]
  exact ((aemeasurable_wickQArea_ball hW hγ hγ2 c r).add aemeasurable_const).add
    aemeasurable_const

/-- second-moment bounds of the walled `log min D` transfer between white noises -/
theorem memLp_logMinLGD_wall_of {P : Measure Ω} {P' : Measure Ω'} {W : WNSpace → Ω → ℝ}
    {W' : WNSpace → Ω' → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (K : Set ℂ) (δ : ℝ) (A B : Set ℂ) {Bnd : ℝ} (hB : 0 ≤ Bnd)
    (h : ∫⁻ ω, ENNReal.ofReal (logMinLGD (dzzWall K (dzzMuIn γ W ω)) δ A B) ^ 2 ∂P ≤
      ENNReal.ofReal Bnd) :
    MemLp (fun ω => logMinLGD (dzzWall K (dzzMuIn γ W' ω)) δ A B) 2 P' ∧
      ∫ ω, logMinLGD (dzzWall K (dzzMuIn γ W' ω)) δ A B ^ 2 ∂P' ≤ Bnd :=
  memLp_two_of_lintegral_sq (fun ω => logMinLGD_nonneg _ _ _ _)
    (aemeasurable_logMinLGD (fun c r => aemeasurable_dzzWall_dzzMuIn_ball hW' hγ hγ2 K c r) δ A B)
    hB (by rw [← lintegral_sq_logMinLGD_wall_eq hW hW' hγ hγ2]; exact h)

/-- the segment from `c` to `c + κ/2` keeps a `ρ`-neighbourhood inside `𝕍_{c,2κ}` (`ρ ≤ κ/2`) -/
lemma ball_lineMap_subset_sqBox (c : ℂ) {κ ρ : ℝ} (hρ : ρ ≤ κ / 2) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Metric.ball (AffineMap.lineMap c (⟨c.re + κ / 2, c.im⟩ : ℂ) t) ρ ⊆ sqBox c (2 * κ) := by
  intro z hz
  set p := AffineMap.lineMap c (⟨c.re + κ / 2, c.im⟩ : ℂ) t with hp
  have hpre : p.re = c.re + t * (κ / 2) := by
    rw [hp, AffineMap.lineMap_apply_module]; simp; ring
  have hpim : p.im = c.im := by
    rw [hp, AffineMap.lineMap_apply_module]; simp; ring
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 := Complex.abs_re_le_norm (z - p)
  have h2 := Complex.abs_im_le_norm (z - p)
  rw [Complex.sub_re, hpre] at h1
  rw [Complex.sub_im, hpim] at h2
  rw [abs_le] at h1 h2
  obtain ⟨ht0, ht1⟩ := ht
  exact ⟨abs_le.mpr ⟨by nlinarith, by nlinarith⟩, abs_le.mpr ⟨by nlinarith, by nlinarith⟩⟩

end DZZ
end LQGMetric
