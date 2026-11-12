/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17V1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L37V1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L13V

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17 at `𝕍`-scale, part 1: the white noise rescaled by `1/2` (P2-DG317V)

Ding–Gwynne arXiv:1807.01072 (`metric-comparison-final.tex`), proof of Prop 3.17 (DG:1523–1591),
D121. `DGP317Show` lives on `𝕊 = [0,1]²` with Lemma 3.13's rectangles on `Q ⊇ [−r,1+r]²`, while
`μ_ĥ` (`muHat`) lives on `K₀ = [1/10,9/10]² ⊂ 𝕍`. We carry `𝕊` into `𝕍` by the *dyadic* map
`T(z) = z/2 + (1+i)/4` (`p17vT`, inverse `T⁻¹ y = 2y − (1+i)/2`, `p17vTinv`): it maps the
dyadic grid of `[0,1]²` of level `m` onto the grid of level `m + 1` with corner `(1+i)/4`, so the
rectangles of DG Lemma 3.13 at `𝕍`-scale are exactly the images of those at `𝕊`-scale
(with D121's `T(z) = (z+1+i)/3` the two grids are incommensurable). `T⁻¹[1/6,5/6]² = [−1/6,7/6]²`.

* `p17vW W = W ∘ U_{2,−(1+i)/2}` (`wnScale`, S3D105Sc1) is a white noise, pathwise
  `φ_{a,c}[W'](y) = φ_{2a,2c}[W](T⁻¹ y)`, and a.s. for all `y`
  `ĥ_δ[W'](y) = ĥ_{2δ}[W](T⁻¹ y) + φ_{1,2}[W](T⁻¹ y)` (`ae_phiVer_p17vW`, as `ae_phiVer_l37W`);
* `p17vMu μ = (T⁻¹)_* μ` and the LGD comparisons `p17v_lgd_up`, `p17v_lgd_down`
  (`dgLGD_affine_le`): `D^ε_μ(Tz, Tw; U) ≤ D^ε_{μ'}(z, w; T⁻¹U)`, `D^ε_{μ'}(T⁻¹z, T⁻¹w; U) ≤
  D^ε_μ(z, w; TU)`;
* the preimages of L3.13's rectangles and sides under `T⁻¹`.

Own elementary glue (scale covariance of the white noise, DG:1010; proposed DV-DG317V-1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

/-- `b = −(1+i)/2`, so that `affineC 2 b = T⁻¹` -/
def p17vb : ℂ := ⟨-1 / 2, -1 / 2⟩

/-- `T⁻¹ y = 2y − (1+i)/2` -/
def p17vTinv : ℂ → ℂ := affineC 2 p17vb

/-- `T z = z/2 + (1+i)/4` -/
def p17vT : ℂ → ℂ := affineC 2⁻¹ (-p17vb / 2)

lemma p17vTinv_T (z : ℂ) : p17vTinv (p17vT z) = z :=
  affineC_affineC_inv (by norm_num) p17vb z

lemma p17vT_Tinv (z : ℂ) : p17vT (p17vTinv z) = z :=
  affineC_inv_affineC (by norm_num) p17vb z

lemma continuous_p17vTinv : Continuous p17vTinv := continuous_affineC 2 p17vb

lemma continuous_p17vT : Continuous p17vT := continuous_affineC _ _

lemma p17vTinv_re (y : ℂ) : (p17vTinv y).re = 2 * y.re - 1 / 2 := by
  simp only [p17vTinv, affineC, p17vb, Complex.add_re, Complex.re_ofReal_mul]; ring

lemma p17vTinv_im (y : ℂ) : (p17vTinv y).im = 2 * y.im - 1 / 2 := by
  simp only [p17vTinv, affineC, p17vb, Complex.add_im, Complex.im_ofReal_mul]; ring

lemma p17vT_re (y : ℂ) : (p17vT y).re = y.re / 2 + 1 / 4 := by
  have h := p17vTinv_re (p17vT y)
  rw [p17vTinv_T] at h; linarith

lemma p17vT_im (y : ℂ) : (p17vT y).im = y.im / 2 + 1 / 4 := by
  have h := p17vTinv_im (p17vT y)
  rw [p17vTinv_T] at h; linarith

lemma norm_p17vT_sub (y z : ℂ) : ‖p17vT y - p17vT z‖ = ‖y - z‖ / 2 := by
  have h := dist_affineC (by norm_num : (0 : ℝ) < 2⁻¹) (-p17vb / 2) y z
  rw [dist_eq_norm, dist_eq_norm] at h
  simp only [p17vT]; rw [h]; ring

lemma p17vT_image_eq (S : Set ℂ) : p17vT '' S = p17vTinv ⁻¹' S :=
  congrFun (image_eq_preimage_of_inverse p17vTinv_T p17vT_Tinv) S

/-- the white noise at `𝕍`-scale: `W' = W ∘ U_{2,−(1+i)/2}` -/
def p17vW {Ω : Type*} (W : WNSpace → Ω → ℝ) : WNSpace → Ω → ℝ :=
  fun f ω => W (wnScale (by norm_num : (0 : ℝ) < 2) p17vb f) ω

theorem isWhiteNoise_p17vW {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) : IsWhiteNoise P (p17vW W) :=
  isWhiteNoise_comp hW _

/-- pathwise: `φ_{a,c}[W'](y) = φ_{2a,2c}[W](T⁻¹ y)` -/
lemma phi_p17vW {Ω : Type*} (W : WNSpace → Ω → ℝ) {a : ℝ} (ha : 0 < a) (c : ℝ) (y : ℂ)
    (ω : Ω) : phi (p17vW W) a c y ω = phi W (2 * a) (2 * c) (p17vTinv y) ω := by
  simp only [phi, p17vW, wnScale_phiKernelL2 _ p17vb ha, p17vTinv]

/-- **`φ_δ` of the rescaled white noise** (`0 < δ ≤ 1/2`): a.s., for all `y`,
`φ_δ[W'](y) = φ_{2δ}[W](T⁻¹ y) + φ_{1,2}[W](T⁻¹ y)` (continuous versions). -/
theorem ae_phiVer_p17vW {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ ≤ 1) :
    ∀ᵐ ω ∂P, ∀ y, DDDF.phiVer (p17vW W) P δ 1 y ω =
      DDDF.phiVer W P (2 * δ) 1 (p17vTinv y) ω + DDDF.phiVer W P 1 2 (p17vTinv y) ω := by
  have h2 : (0 : ℝ) < 2 * δ := by positivity
  have hY := DDDF.isPhiVersion_phiVer (b := 1) (isWhiteNoise_p17vW hW) hδ (by linarith)
  have hA := DDDF.isPhiVersion_phiVer hW h2 hδ2
  have hB := DDDF.isPhiVersion_phiVer (P := P) hW one_pos (by norm_num : (1 : ℝ) ≤ 2)
  refine DDDF.ae_eq_of_continuous_modification hY.cont
    (Y₂ := fun y ω => DDDF.phiVer W P (2 * δ) 1 (p17vTinv y) ω +
      DDDF.phiVer W P 1 2 (p17vTinv y) ω)
    (fun ω => ((hA.cont ω).comp continuous_p17vTinv).add
      ((hB.cont ω).comp continuous_p17vTinv)) fun y => ?_
  filter_upwards [hY.ae_eq y, hA.ae_eq (p17vTinv y), hB.ae_eq (p17vTinv y),
    phi_add_ae hW h2 hδ2 (by norm_num : (1 : ℝ) ≤ 2) (p17vTinv y)] with ω h1 h2 h3' h4
  rw [h1, phi_p17vW W hδ 1 y ω, mul_one, h4, h2, h3']

/-- the measure at `𝕊`-scale: `μ' = (T⁻¹)_* μ` -/
def p17vMu {Ω : Type*} (μ : Ω → Measure ℂ) (ω : Ω) : Measure ℂ := (μ ω).map p17vTinv

/-- `D^ε_μ(Tz, Tw; U) ≤ D^ε_{μ'}(z, w; T⁻¹U)` -/
lemma p17v_lgd_up (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (z w : ℂ) :
    dgLGD μ ε U (p17vT z) (p17vT w) ≤ dgLGD (μ.map p17vTinv) ε (p17vT ⁻¹' U) z w := by
  refine dgLGD_affine_le (by norm_num) (fun y r hr _ hν => ?_) z w
  refine le_trans ?_ hν
  have hpre : p17vTinv ⁻¹' Metric.ball y r = Metric.ball (p17vT y) (2⁻¹ * r) := by
    have := preimage_ball_affineC (by norm_num : (0 : ℝ) < 2) p17vb (p17vT y) (2⁻¹ * r)
    rwa [show (2 : ℝ) * (2⁻¹ * r) = r by ring, ← p17vTinv, p17vTinv_T] at this
  show μ (Metric.ball (p17vT y) (2⁻¹ * r)) ≤ _
  rw [← hpre]
  exact Measure.le_map_apply continuous_p17vTinv.measurable.aemeasurable _

/-- `D^ε_{μ'}(T⁻¹z, T⁻¹w; U) ≤ D^ε_μ(z, w; TU)` -/
lemma p17v_lgd_down (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (z w : ℂ) :
    dgLGD (μ.map p17vTinv) ε U (p17vTinv z) (p17vTinv w) ≤
      dgLGD μ ε (p17vTinv ⁻¹' U) z w := by
  refine dgLGD_affine_le (by norm_num) (fun y r hr _ hν => ?_) z w
  rw [Measure.map_apply continuous_p17vTinv.measurable Metric.isOpen_ball.measurableSet]
  have := preimage_ball_affineC (by norm_num : (0 : ℝ) < 2) p17vb y r
  rw [← p17vTinv] at this
  show μ (p17vTinv ⁻¹' Metric.ball (p17vTinv y) (2 * r)) ≤ _
  rwa [this]

/-! ## The rectangles of Lemma 3.13 under `T⁻¹` -/

/-- the corner of the `𝕍`-scale grid: `T(0) = (1+i)/4` -/
def p17vc0 : ℂ := ⟨1 / 4, 1 / 4⟩

lemma p17vTinv_corner (m : ℕ) (x : ℕ × ℕ) :
    p17vTinv (l313Corner p17vc0 (m + 1) x) = l313Corner 0 m x := by
  apply Complex.ext
  · rw [p17vTinv_re]; simp only [l313Corner, p17vc0, Complex.zero_re, pow_succ]; ring
  · rw [p17vTinv_im]; simp only [l313Corner, p17vc0, Complex.zero_im, pow_succ]; ring

lemma p17v_pre_str (s : ℝ) (b : ℂ) (n : ℕ) :
    p17vTinv ⁻¹' l313Str s (p17vTinv b) n = l313Str (s / 2) b n := by
  ext z
  simp only [mem_preimage, l313Str, Complex.mem_reProdIm, mem_Icc, p17vTinv_re, p17vTinv_im]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma p17v_pre_strV (s : ℝ) (b : ℂ) (n : ℕ) :
    p17vTinv ⁻¹' l313StrV s (p17vTinv b) n = l313StrV (s / 2) b n := by
  ext z
  simp only [mem_preimage, l313StrV, Complex.mem_reProdIm, mem_Icc, p17vTinv_re, p17vTinv_im]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma p17v_mem_left {s : ℝ} {b z : ℂ} {n : ℕ} (hz : z ∈ l313Left (s / 2) b n) :
    p17vTinv z ∈ l313Left s (p17vTinv b) n := by
  simp only [l313Left, mem_ofPred_eq, p17vTinv_re, p17vTinv_im] at hz ⊢
  refine ⟨?_, ?_, ?_⟩ <;> linarith [hz.1, hz.2.1, hz.2.2]

lemma p17v_mem_right {s : ℝ} {b z : ℂ} {n : ℕ} (hz : z ∈ l313Right (s / 2) b n) :
    p17vTinv z ∈ l313Right s (p17vTinv b) n := by
  simp only [l313Right, mem_ofPred_eq, p17vTinv_re, p17vTinv_im] at hz ⊢
  refine ⟨?_, ?_, ?_⟩ <;> linarith [hz.1, hz.2.1, hz.2.2]

lemma p17v_mem_bot {s : ℝ} {b z : ℂ} {n : ℕ} (hz : z ∈ l313Bot (s / 2) b n) :
    p17vTinv z ∈ l313Bot s (p17vTinv b) n := by
  simp only [l313Bot, mem_ofPred_eq, p17vTinv_re, p17vTinv_im] at hz ⊢
  refine ⟨?_, ?_, ?_⟩ <;> linarith [hz.1, hz.2.1, hz.2.2]

lemma p17v_mem_top {s : ℝ} {b z : ℂ} {n : ℕ} (hz : z ∈ l313Top (s / 2) b n) :
    p17vTinv z ∈ l313Top s (p17vTinv b) n := by
  simp only [l313Top, mem_ofPred_eq, p17vTinv_re, p17vTinv_im] at hz ⊢
  refine ⟨?_, ?_, ?_⟩ <;> linarith [hz.1, hz.2.1, hz.2.2]

/-- `l313Set` under the change of scale: `D^ε_{μ'}(L, R; S) ≤ D^ε_μ(L', R'; S')` -/
lemma p17v_set_le {μ : Measure ℂ} {ε : ℝ} {S L R S' L' R' : Set ℂ}
    (hS : p17vTinv ⁻¹' S = S') (hL : ∀ z ∈ L', p17vTinv z ∈ L)
    (hR : ∀ z ∈ R', p17vTinv z ∈ R) :
    l313Set (μ.map p17vTinv) ε S L R ≤ l313Set μ ε S' L' R' := by
  unfold l313Set
  refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
  refine (iInf₂_le _ (hL z hz)).trans ((iInf₂_le _ (hR w hw)).trans ?_)
  rw [← hS]
  exact p17v_lgd_down μ ε S z w

/-- `T⁻¹[1/6,5/6]² = [−1/6,7/6]²` -/
lemma p17v_pre_box : p17vTinv ⁻¹' p39Box 0 1 (1 / 6) = p39Box p18c0 (1 / 3) (1 / 6) := by
  ext z
  simp only [mem_preimage, p39Box, Complex.mem_reProdIm, mem_Icc, p17vTinv_re, p17vTinv_im,
    p18c0, Complex.zero_re, Complex.zero_im]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- the `𝕊`-scale grid rectangles are `T⁻¹` of `𝕍`-scale grid rectangles -/
lemma p17v_grid_mem {m : ℕ} {x : ℕ × ℕ} (hx : x ∈ l313Grid (p39Box 0 1 (1 / 6)) 0 m) :
    x ∈ l313Grid (p39Box p18c0 (1 / 3) (1 / 6)) p17vc0 (m + 1) := by
  simp only [l313Grid, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  have hp : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)
  refine ⟨⟨h1.trans_le hp, h2.trans_le hp⟩, ?_⟩
  rw [← p17v_pre_box]
  have := p17v_pre_str ((2 : ℝ)⁻¹ ^ m) (l313Corner p17vc0 (m + 1) x) 1
  rw [show (2 : ℝ)⁻¹ ^ m / 2 = (2 : ℝ)⁻¹ ^ (m + 1) by rw [pow_succ]; ring] at this
  rw [← this, p17vTinv_corner]
  exact preimage_mono h3

lemma p17v_gridV_mem {m : ℕ} {x : ℕ × ℕ} (hx : x ∈ l313GridV (p39Box 0 1 (1 / 6)) 0 m) :
    x ∈ l313GridV (p39Box p18c0 (1 / 3) (1 / 6)) p17vc0 (m + 1) := by
  simp only [l313GridV, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  have hp : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)
  refine ⟨⟨h1.trans_le hp, h2.trans_le hp⟩, ?_⟩
  rw [← p17v_pre_box]
  have := p17v_pre_strV ((2 : ℝ)⁻¹ ^ m) (l313Corner p17vc0 (m + 1) x) 1
  rw [show (2 : ℝ)⁻¹ ^ m / 2 = (2 : ℝ)⁻¹ ^ (m + 1) by rw [pow_succ]; ring] at this
  rw [← this, p17vTinv_corner]
  exact preimage_mono h3

end DG
end LQGMetric
