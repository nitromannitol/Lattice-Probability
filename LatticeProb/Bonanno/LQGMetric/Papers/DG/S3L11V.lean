/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11V at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Meas
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L13V

/-!
# DG Lemma 3.11 for vertical rectangles: `DGLem311ScaledV` (P2-DG105g)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.11 (DG:1189–1278) for the
vertical rectangles `b + [0,sn] × [0,2sn]` (DG:1335, "`2^{-m} × 2^{-m+1}`"). The reflection
`swapC z = z.im + i z.re` (an involutive isometry of `ℂ`) maps the horizontal rectangle
`l313Str s (swapC b) n` with its left/right sides onto the vertical rectangle `l313StrV s b n`
with its bottom/top sides, and the Liouville graph distance of `μ` equals that of `μ ∘ swapC`
on the reflected sets (`dgLGD_map_swapC_le`). The reduction `dgLem311ScaledV_of_input` is the
horizontal one (S3L11Sc) for the reflected measure; the random factor is `l311TV` (the maximum
of `ĥ_s` over the vertical rectangle).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- the reflection `x + iy ↦ y + ix` -/
def swapC (z : ℂ) : ℂ := ⟨z.im, z.re⟩

@[simp] lemma swapC_re (z : ℂ) : (swapC z).re = z.im := rfl
@[simp] lemma swapC_im (z : ℂ) : (swapC z).im = z.re := rfl

@[simp] lemma swapC_swapC (z : ℂ) : swapC (swapC z) = z := Complex.ext rfl rfl

lemma dist_swapC (z w : ℂ) : dist (swapC z) (swapC w) = dist z w := by
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
  simp only [swapC_re, swapC_im]
  rw [add_comm]

lemma isometry_swapC : Isometry swapC := Isometry.of_dist_eq dist_swapC

lemma continuous_swapC : Continuous swapC := isometry_swapC.continuous

/-- `swapC` as a homeomorphism -/
def swapCHomeo : ℂ ≃ₜ ℂ where
  toFun := swapC
  invFun := swapC
  left_inv := swapC_swapC
  right_inv := swapC_swapC
  continuous_toFun := continuous_swapC
  continuous_invFun := continuous_swapC

lemma image_swapC (S : Set ℂ) : swapC '' S = swapC ⁻¹' S :=
  congrFun (image_eq_preimage_of_inverse swapC_swapC swapC_swapC) S

lemma preimage_swapC_ball (x : ℂ) (ρ : ℝ) :
    swapC ⁻¹' Metric.ball (swapC x) ρ = Metric.ball x ρ := by
  ext y; simp only [mem_preimage, Metric.mem_ball, dist_swapC]

lemma image_swapC_ball (x : ℂ) (ρ : ℝ) : swapC '' Metric.ball x ρ = Metric.ball (swapC x) ρ := by
  rw [image_swapC]; ext y
  simp only [mem_preimage, Metric.mem_ball]
  rw [← dist_swapC, swapC_swapC]

lemma image_swapC_closure (U : Set ℂ) : swapC '' closure U = closure (swapC '' U) :=
  swapCHomeo.image_closure U

/-- the reflected measure has the reflected Liouville graph distances (one inequality; the
other one is the same for `μ.map swapC`) -/
lemma dgLGD_map_swapC_le (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (z w : ℂ) :
    dgLGD (μ.map swapC) ε (swapC '' U) (swapC z) (swapC w) ≤ dgLGD μ ε U z w := by
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, hb, hc⟩ := hN
  refine iInf₂_le N ⟨fun i => swapC (x i), ρ, P.map continuous_swapC, fun i => ⟨(hb i).1, ?_, ?_⟩,
    fun t => ?_⟩
  · rw [← image_swapC_ball, ← image_swapC_closure]
    exact image_mono (hb i).2.1
  · rw [Measure.map_apply continuous_swapC.measurable Metric.isOpen_ball.measurableSet,
      preimage_swapC_ball]
    exact (hb i).2.2
  · obtain ⟨i, hi⟩ := hc t
    refine ⟨i, ?_⟩
    simp only [Path.map_coe, Function.comp_apply, Metric.mem_ball, dist_swapC] at hi ⊢
    exact hi

lemma map_map_swapC (μ : Measure ℂ) : (μ.map swapC).map swapC = μ := by
  rw [Measure.map_map continuous_swapC.measurable continuous_swapC.measurable]
  have : swapC ∘ swapC = id := funext swapC_swapC
  rw [this, Measure.map_id]

lemma swapC_l313Str (s : ℝ) (b : ℂ) (n : ℕ) :
    swapC '' l313Str s (swapC b) n = l313StrV s b n := by
  rw [image_swapC]; ext y
  simp only [mem_preimage, l313Str, l313StrV, Complex.mem_reProdIm, swapC_re, swapC_im]
  tauto

lemma swapC_l313Left (s : ℝ) (b : ℂ) (n : ℕ) :
    swapC '' l313Left s (swapC b) n = l313Bot s b n := by
  rw [image_swapC]; ext y
  simp only [mem_preimage, l313Left, l313Bot, mem_ofPred_eq, swapC_re, swapC_im]

lemma swapC_l313Right (s : ℝ) (b : ℂ) (n : ℕ) :
    swapC '' l313Right s (swapC b) n = l313Top s b n := by
  rw [image_swapC]; ext y
  simp only [mem_preimage, l313Right, l313Top, mem_ofPred_eq, swapC_re, swapC_im]

/-- the vertical crossing distance of `ν` is at most the horizontal crossing distance of the
reflected measure -/
lemma l313Set_V_le (ν : Measure ℂ) (ε s : ℝ) (b : ℂ) (n : ℕ) :
    l313Set ν ε (l313StrV s b n) (l313Bot s b n) (l313Top s b n) ≤
      dgLGDSet (ν.map swapC) ε (l313Str s (swapC b) n) (l313Left s (swapC b) n)
        (l313Right s (swapC b) n) := by
  refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
  have hz' : swapC z ∈ l313Bot s b n := by rw [← swapC_l313Left]; exact mem_image_of_mem _ hz
  have hw' : swapC w ∈ l313Top s b n := by rw [← swapC_l313Right]; exact mem_image_of_mem _ hw
  have := dgLGD_map_swapC_le (ν.map swapC) ε (l313Str s (swapC b) n) z w
  rw [map_map_swapC, swapC_l313Str] at this
  exact (iInf₂_le (swapC z) hz').trans ((iInf₂_le (swapC w) hw').trans this)

/-- DG's random factor `T_R ε` of the vertical rectangle (verbatim as in `DGLem311ScaledV`) -/
def l311TV (P : Measure Ω) (W : WNSpace → Ω → ℝ) (γ ε : ℝ) (j n : ℕ) (b : ℂ) (ω : Ω) : ℝ :=
  ε * (((2 : ℝ)⁻¹ ^ j) ^ (2 + γ ^ 2 / 2))⁻¹ *
    Real.exp (-(γ * sSup ((fun z => DDDF.phiVer W P ((2 : ℝ)⁻¹ ^ j) 1 z ω) ''
      l313StrV ((2 : ℝ)⁻¹ ^ j) b n)))

lemma l311TV_pos {P : Measure Ω} {W : WNSpace → Ω → ℝ} {γ ε : ℝ} (hε : 0 < ε) (j n : ℕ)
    (b : ℂ) (ω : Ω) : 0 < l311TV P W γ ε j n b ω := by
  unfold l311TV; positivity

/-- `T_R` of the vertical rectangle is measurable -/
theorem measurable_l311TV {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (γ ε : ℝ) (j n : ℕ) (b : ℂ) : Measurable (l311TV P W γ ε j n b) := by
  have hv := DDDF.isPhiVersion_phiVer hW (a := (2 : ℝ)⁻¹ ^ j) (b := 1) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num))
  have hS : l313StrV ((2 : ℝ)⁻¹ ^ j) b n = swapC '' l313Str ((2 : ℝ)⁻¹ ^ j) (swapC b) n :=
    (swapC_l313Str _ _ _).symm
  have hM := measurable_sSup_image_of_cont (S := l313StrV ((2 : ℝ)⁻¹ ^ j) b n)
    (by rw [hS]; exact (isCompact_l313Str _ _ _).image continuous_swapC)
    (by rw [hS]; exact (l313Str_nonempty (by positivity) _ n).image _) hv.cont hv.meas
  unfold l311TV
  exact measurable_const.mul (Real.measurable_exp.comp (hM.const_mul γ).neg)

/-- **the single-square inputs of DG Lemma 3.11 for vertical rectangles at scale `2^{-j}`**
(the horizontal inputs `L311LevelInput` for the measure reflected by `swapC`, DG:1335) (DG:1240–1267 with
DG:1222–1225 and DG:1300–1305): for every rectangle `sℛ_n + b ⊆ Q` and `ε > 0`, the factor
`T` is measurable, and there are fine events `E k x` (level `k`, grid square `x` of side `s/32`)
generating a σ-algebra independent of `T`, each of probability `≥ 1 − 32^{−100}` and with the
product bound at distance `> 9` for the levels `e^k ≤ ε_*`, and an exceptional event `Z` of
probability `≤ a₂ e^{−a₃ n}` (DG's comparison `max |ĥ − ĥ^tr| > c√n`, DG:1226–1227), such that
a.s. off `Z`, on `{e^k ≤ T e^{−(d−ζ₁)√n/2}}`, `E k x` implies that the square `x` is good with
threshold `C e^{−k/(d−ζ₁)}`. -/
def L311LevelInputV (P : Measure Ω) (W : WNSpace → Ω → ℝ) (μ : Ω → Measure ℂ) (γ d : ℝ)
    (Q : Set ℂ) : Prop :=
  ∀ ζ₁ : ℝ, 0 < ζ₁ → ζ₁ < 1 → ∃ C εs a₂ a₃ : ℝ, 0 < C ∧ 0 < εs ∧ 0 ≤ a₂ ∧ 0 < a₃ ∧
    ∀ (j n : ℕ) (b : ℂ), l313StrV ((2 : ℝ)⁻¹ ^ j) b n ⊆ Q → ∀ ε : ℝ, 0 < ε →
    Measurable (l311TV P W γ ε j n b) ∧
    ∃ (Fg : Set (Set Ω)) (E : ℤ → ℤ × ℤ → Set Ω) (Z : Set Ω),
      P Z ≤ ENNReal.ofReal (a₂ * Real.exp (-(a₃ * n))) ∧ (∀ k x, E k x ∈ Fg) ∧
      (∀ B : Set ℝ, MeasurableSet B → ∀ A : Set Ω,
        MeasurableSet[MeasurableSpace.generateFrom Fg] A →
        P (l311TV P W γ ε j n b ⁻¹' B ∩ A) = P (l311TV P W γ ε j n b ⁻¹' B) * P A) ∧
      (∀ k : ℤ, Real.exp k ≤ εs → ∀ x,
        percInGrid (2 * ((32 * n : ℕ) : ℤ)) (((32 * n : ℕ) : ℤ) - 2) x →
        P (E k x)ᶜ ≤ (32⁻¹ : ℝ≥0∞) ^ 100) ∧
      (∀ k : ℤ, Real.exp k ≤ εs → ∀ F : Finset (ℤ × ℤ),
        (∀ x ∈ F, percInGrid (2 * ((32 * n : ℕ) : ℤ)) (((32 * n : ℕ) : ℤ) - 2) x) →
        (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar 9 x y) →
        P (⋂ x ∈ F, (E k x)ᶜ) ≤ ∏ x ∈ F, P (E k x)ᶜ) ∧
      (∀ᵐ ω ∂P, ω ∉ Z → ∀ (k : ℤ) (x : ℤ × ℤ),
        Real.exp k ≤ l311TV P W γ ε j n b ω * Real.exp (-((d - ζ₁) / 2 * √(n : ℝ))) →
        ω ∈ E k x →
        goodSq ((μ ω).map swapC) ε ((2 : ℝ)⁻¹ ^ j / 32) (swapC b)
          (C * Real.exp (-(k / (d - ζ₁)))) x)

/-- **DG Lemma 3.11 for vertical rectangles at scale `2^{-j}`, transported by (3.7)**
(`DGLem311ScaledV`, the input of `dg_lemma313V`/`dg_lemma314V`, Papers/DG/S3L13V) from the single-square inputs. -/
theorem dgLem311ScaledV_of_input {P : Measure Ω} [IsProbabilityMeasure P]
    {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ} {γ d : ℝ} {Q : Set ℂ} (hd : 1 ≤ d)
    (h : L311LevelInputV P W μ γ d Q) : DGLem311ScaledV P W μ γ d Q := by
  intro ζ₁ h0 h1
  obtain ⟨C, εs, a₂, a₃, hC, hεs, ha₂, ha₃, hh⟩ := h ζ₁ h0 h1
  set β : ℝ := 1 / (d - ζ₁) with hβdef
  have hdz : 0 < d - ζ₁ := by linarith
  have hβ : 0 < β := by rw [hβdef]; exact one_div_pos.2 hdz
  set k₀ : ℤ := ⌊Real.log εs⌋
  set n₀ : ℕ := ⌈(2 * Real.log (2048 * C * Real.exp β)) ^ 2⌉₊
  refine ⟨max (32 + a₂) (Real.exp (min (Real.log 2) a₃ * n₀)), min (Real.log 2) a₃,
    2048 * (C * Real.exp (-(β * k₀))), lt_min (Real.log_pos (by norm_num)) ha₃,
    fun j n b hQ ε hε => ?_⟩
  refine l311_final prob_le_one (by norm_num) ha₂ ha₃.le n₀ n fun hn => ?_
  obtain ⟨hT, Fg, E, Z, hZ, hEm, hindT, hgood, hind, hpath⟩ := hh j n b hQ ε hε
  set T := l311TV P W γ ε j n b with hTdef
  set c : ℝ := Real.exp (-((d - ζ₁) / 2 * √(n : ℝ)))
  have hTpos : ∀ ω, 0 < T ω * c := fun ω => mul_pos (l311TV_pos hε j n b ω) (Real.exp_pos _)
  set κ : Ω → ℤ := fun ω => l311Lev k₀ (T ω * c)
  have hk₀ : Real.exp k₀ ≤ εs := by
    calc Real.exp k₀ ≤ Real.exp (Real.log εs) := Real.exp_le_exp.2 (Int.floor_le _)
      _ = εs := Real.exp_log hεs
  have hmin : ∀ k : ℤ, Real.exp (min k k₀ : ℤ) ≤ εs := fun k =>
    (Real.exp_le_exp.2 (Int.cast_le.2 (min_le_right k k₀))).trans hk₀
  have hs4 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ j / 32 := by positivity
  have hmeas : Measurable fun t : ℝ => l311Lev k₀ (t * c) :=
    (measurable_l311Lev k₀).comp (measurable_id.mul_const c)
  have hP := dg_lemma311_level P (fun ω => (μ ω).map swapC) (ε := ε) hs4 (swapC b) (32 * n) κ (hmeas.comp hT)
    (fun k => C * Real.exp (-(k / (d - ζ₁)))) Fg
    (fun k x => E (min k k₀) x) (fun k x => hEm _ x)
    (fun k A hA => by
      have e : {ω | κ ω = k} = T ⁻¹' ((fun t : ℝ => l311Lev k₀ (t * c)) ⁻¹' {k}) := rfl
      rw [e]
      exact hindT _ (hmeas (measurableSet_singleton k)) A hA) Z
    (by
      filter_upwards [hpath] with ω hp hZω k x hk hx
      have hkk : min k k₀ = k := min_eq_left (hk ▸ l311Lev_le k₀ (T ω * c))
      have := hp hZω (min k k₀) x (by rw [hkk, ← hk]; exact exp_l311Lev_le k₀ (hTpos ω)) hx
      rwa [hkk] at this)
    (fun k x hx => hgood _ (hmin k) x hx) (fun k F hF hfar => hind _ (hmin k) F hF hfar)
  obtain ⟨r1, r2, r3⟩ := rect_quarter ((2 : ℝ)⁻¹ ^ j) (swapC b) n
  rw [r1, r2, r3] at hP
  refine (measure_mono ?_).trans (hP.trans (add_le_add_right hZ _))
  intro ω hω hle
  refine hω ?_
  -- the threshold: `2 (32n)² C e^{−κ/(d−ζ)} ≤ n² max{A, e^{√n} T^{−1/(d−ζ)}}`
  refine (ENat.toENNReal_le.2 (l313Set_V_le (μ ω) ε ((2 : ℝ)⁻¹ ^ j) b n)).trans
    (hle.trans ?_)
  rw [show (2 * ((32 * n : ℕ) : ℝ≥0∞) ^ 2) * ENNReal.ofReal (C * Real.exp (-((κ ω : ℝ) /
      (d - ζ₁)))) = ENNReal.ofReal ((n : ℝ) ^ 2 * (2048 * (C * Real.exp (-((κ ω : ℝ) /
      (d - ζ₁)))))) by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; push_cast; ring]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hthr := l311Lev_thr hβ.le hC.le k₀ (hTpos ω)
  have e3 : -((κ ω : ℝ) / (d - ζ₁)) = -(β * (l311Lev k₀ (T ω * c) : ℝ)) := by
    simp only [κ, hβdef]; ring
  rw [e3]
  have e4 : (T ω * c) ^ (-β) = T ω ^ (-β) * Real.exp (√(n : ℝ) / 2) := by
    rw [rpow_mul_exp_neg (l311TV_pos hε j n b ω)]
    congr 2; rw [hβdef]; field_simp
  have hsq : 2048 * C * Real.exp β * Real.exp (√(n : ℝ) / 2) ≤ Real.exp √(n : ℝ) := by
    have hpos : 0 < 2048 * C * Real.exp β := by positivity
    rw [← Real.exp_log hpos, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h5 : (2 * Real.log (2048 * C * Real.exp β)) ^ 2 ≤ n := by
      have := Nat.le_ceil ((2 * Real.log (2048 * C * Real.exp β)) ^ 2)
      exact this.trans (by exact_mod_cast hn)
    have h6 : 2 * Real.log (2048 * C * Real.exp β) ≤ √(n : ℝ) :=
      calc 2 * Real.log (2048 * C * Real.exp β) ≤ |2 * Real.log (2048 * C * Real.exp β)| :=
            le_abs_self _
        _ = √((2 * Real.log (2048 * C * Real.exp β)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt h5
    linarith
  have hTβ : 0 ≤ T ω ^ (-β) := Real.rpow_nonneg (l311TV_pos hε j n b ω).le _
  calc 2048 * (C * Real.exp (-(β * (l311Lev k₀ (T ω * c) : ℝ))))
      ≤ 2048 * max (C * Real.exp (-(β * k₀))) (Real.exp β * C * (T ω * c) ^ (-β)) := by gcongr
    _ = max (2048 * (C * Real.exp (-(β * k₀))))
          (2048 * C * Real.exp β * Real.exp (√(n : ℝ) / 2) * T ω ^ (-β)) := by
        rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2048), e4]; ring_nf
    _ ≤ max (2048 * (C * Real.exp (-(β * k₀)))) (Real.exp √(n : ℝ) * T ω ^ (-β)) := by
        gcongr
    _ = _ := by rw [hβdef]; rfl

end DG
end LQGMetric
