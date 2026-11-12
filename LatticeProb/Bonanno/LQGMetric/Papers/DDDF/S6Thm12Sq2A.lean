/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm12Sq2A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P29SqA
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm12Sq2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS zero-boundary step with DDDF Theorem 1 (2) on the square (task P2-DDDF6f)

Copy of `Papers/DFGPS/P29SqA.lean` (from `zb_step'` on) with `Blueprint.DDDFThm1_2` replaced by `DDDF.DDDFThm1_2Sq` (DDDF Theorem 1 (2)
for `D = (−1,2)²` only; DFGPS T:877–881 applies Theorem 1 (2) only to that domain, and `zb_step'`
reads only its tightness there). Same names in the namespace `LQGMetric.DFGPS.Q12`; proofs
verbatim. Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS.Q12

open Blueprint LFPP HeatSq WhiteNoise DDDF

/-- **The zero-boundary step** (DFGPS T:877–881). -/
theorem zb_step' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (W' : WNSpace → Ω' → ℝ) (hW' : IsWhiteNoise P' W') {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ)
    (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P) :
    ∃ Y : ℝ → ℂ → Ω → ℝ,
      (∀ δ ∈ Ioo (0 : ℝ) 1,
        IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (δ / 2) x)) (Y δ) P) ∧
      IsTightMeasureSet {μ | ∃ δ ∈ Ioo (0 : ℝ) 1, μ = P.map fun ω =>
        sqMetricC (xiGamma γ) (lambdaDelta (xiGamma γ) W' P' (Real.sqrt δ))
          (fun x => Y δ x ω)} ∧
      ∀ (δn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ))
        (μ : ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ)),
        (∀ n, δn n ∈ Ioo (0 : ℝ) 1 ∧ (ν n : Measure _) = P.map fun ω =>
          sqMetricC (xiGamma γ) (lambdaDelta (xiGamma γ) W' P' (Real.sqrt (δn n)))
            (fun x => Y (δn n) x ω)) →
        Tendsto δn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
        ∀ᵐ d ∂(μ : Measure C(closedUnitSquare × closedUnitSquare, ℝ)), IsPosOffDiag d := by
  obtain ⟨Y, hY⟩ := exists_heat_contVersion_sq (by norm_num : (0 : ℝ) < 3) hX
  have hT := (h12 γ hγ hγ2 P' W' hW' P Xh hX Y hY).2
  refine ⟨Y, hY, hT, fun δn ν μ hν hδ hμ => ?_⟩
  have hUc : closure (sqOpen (-1 / 2) 2) ⊆ sqOpen (-1) 3 := fun z hz => by
    obtain ⟨h1, h2, h3, h4⟩ := closure_sqOpen_subset _ _ hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  exact zb_lim_posOffDiag' h11 h29 hγ hγ2 P' W' hW' (sqOpens (-1) 3) (isBounded_sqOpen (-1) 3)
    rfl
    (sqOpen (-1 / 2) 2) (isOpen_sqOpen _ _) (isBounded_sqOpen _ _).isCompact_closure hUc
    (fun z ⟨h1, h2, h3, h4⟩ => ⟨by linarith, by linarith, by linarith, by linarith⟩)
    P Xh hX Y hY δn ν μ hν hδ hμ

/-- **The setup of DFGPS Lemma 2.8 on `[0,1]²`.** -/
theorem unitSq_setup' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq) (hLM : LMLem2_1)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : Ω → DistC) (hg : IsWholePlaneGFF g P) :
    ∃ (lam : ℝ → ℝ) (C εb : ℝ) (Y : ℝ → ℂ → Ω → ℝ), 0 < C ∧ 0 < εb ∧
      (∀ ε, 0 < ε → ε ≤ 1 → 0 ≤ lam ε) ∧
      (∀ ε, 0 < ε → ε < εb → 0 < lam ε ∧ C⁻¹ * lam ε ≤ aEpsDF (xiGamma γ) ε ∧
        aEpsDF (xiGamma γ) ε ≤ C * lam ε) ∧
      (∀ δ ∈ Ioo (0 : ℝ) 1, (∀ ω, Continuous fun x => Y δ x ω) ∧ ∀ x, Measurable (Y δ x)) ∧
      IsTightMeasureSet {μ | ∃ δ ∈ Ioo (0 : ℝ) 1, μ = P.map fun ω =>
        sqMetricC (xiGamma γ) (lam (Real.sqrt δ)) (fun x => Y δ x ω)} ∧
      (∀ (δn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ))
        (μ : ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ)),
        (∀ n, δn n ∈ Ioo (0 : ℝ) 1 ∧ (ν n : Measure _) = P.map fun ω =>
          sqMetricC (xiGamma γ) (lam (Real.sqrt (δn n))) (fun x => Y (δn n) x ω)) →
        Tendsto δn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
        ∀ᵐ d ∂(μ : Measure C(closedUnitSquare × closedUnitSquare, ℝ)), IsPosOffDiag d) ∧
      (∀ ζ > 0, ∃ M : ℝ, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
        P {ω | ∃ x ∈ closedUnitSquare, M < |heatMollify ε (g ω) x - Y (ε ^ 2) x ω|} ≤
          ENNReal.ofReal ζ) := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  haveI := hW.isProbabilityMeasure
  have hVb : Bornology.IsBounded ((sqOpens (-1) 3 : Opens ℂ) : Set ℂ) := isBounded_sqOpen (-1) 3
  have hVd : Disjoint ((sqOpens (-1) 3 : Opens ℂ) : Set ℂ) (sphere (0 : ℂ) 4) :=
    disjoint_sqOpen_sphere
  -- the normalized field and its coupling: bounds on `𝔞_ε / λ_ε`
  obtain ⟨hgw, hgn⟩ := isNormalizedAt_recenter hg one_pos (0 : ℂ)
  set g' : Ω → DistC := fun ω => addConst (g ω) (-circleAvg (g ω) 1 0)
  have hg' : IsNormalizedWPGFF g' P := ⟨hgw, hgn⟩
  obtain ⟨hh', hz', Xh', hsum', hharm', -, hX', hlink'⟩ :=
    markov_zb_coupling hLM P g' hgw (by norm_num : (0 : ℝ) < 4) 0 (sqOpens (-1) 3) hVb hVd
  obtain ⟨Y', hY', hT', hpos'⟩ := zb_step' h11 h12 h29 hγ hγ2 _ W hW P Xh' hX'
  obtain ⟨C, hC, εb, hεb, hb⟩ := aEps_lambda_bounds hg' hsum' hharm' hX' hlink' hY' hT' hpos'
  -- the coupling of `g` itself
  obtain ⟨hh, hz, Xh, hsum, hharm, -, hX, hlink⟩ :=
    markov_zb_coupling hLM P g hg (by norm_num : (0 : ℝ) < 4) 0 (sqOpens (-1) 3) hVb hVd
  obtain ⟨Y, hY, hT, hpos⟩ := zb_step' h11 h12 h29 hγ hγ2 _ W hW P Xh hX
  refine ⟨lambdaDelta (xiGamma γ) W LQGDimension.ExistAsm.stdP, C, εb, Y, hC, hεb,
    fun ε hε hε1 => lambdaDelta_nonneg hW _ hε hε1, hb, fun δ hδ => ⟨(hY δ hδ).1, (hY δ hδ).2.1⟩,
    hT, hpos, gff_zb_field_prob hg hsum hharm hX hlink hY⟩

/-- `𝔞_ε ≍ λ_ε` for the white-noise normalization `λ` of a fixed white noise `W` on the
standard space (`aEps_lambda_bounds`, as in `unitSq_setup'`). -/
theorem aEps_lambda_W' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq) (hLM : LMLem2_1)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : Ω → DistC) (hg : IsWholePlaneGFF g P) :
    ∃ W : WNSpace → (ℕ → ℝ) → ℝ, IsWhiteNoise LQGDimension.ExistAsm.stdP W ∧
      ∃ C > 0, ∃ εb > 0, ∀ ε, 0 < ε → ε < εb →
        0 < lambdaDelta (xiGamma γ) W LQGDimension.ExistAsm.stdP ε ∧
        C⁻¹ * lambdaDelta (xiGamma γ) W LQGDimension.ExistAsm.stdP ε ≤ aEpsDF (xiGamma γ) ε ∧
        aEpsDF (xiGamma γ) ε ≤ C * lambdaDelta (xiGamma γ) W LQGDimension.ExistAsm.stdP ε := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  have := hW.isProbabilityMeasure
  have hVb : Bornology.IsBounded ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) := isBounded_sqOpen (-1) 3
  have hVd : Disjoint ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) (Metric.sphere (0 : ℂ) 4) :=
    disjoint_sqOpen_sphere
  obtain ⟨hgw, hgn⟩ := isNormalizedAt_recenter hg one_pos (0 : ℂ)
  set g' : Ω → DistC := fun ω => addConst (g ω) (-circleAvg (g ω) 1 0)
  have hg' : IsNormalizedWPGFF g' P := ⟨hgw, hgn⟩
  obtain ⟨hh', hz', Xh', hsum', hharm', -, hX', hlink'⟩ :=
    markov_zb_coupling hLM P g' hgw (by norm_num : (0 : ℝ) < 4) 0 (sqOpens (-1) 3) hVb hVd
  obtain ⟨Y', hY', hT', hpos'⟩ := zb_step' h11 h12 h29 hγ hγ2 _ W hW P Xh' hX'
  exact ⟨W, hW, aEps_lambda_bounds hg' hsum' hharm' hX' hlink' hY' hT' hpos'⟩

/-- **The normalization ratio** (item 5b of handoff/P2-DFB34e.md; decision D73):
for fixed `s > 0`, `C⁻¹ ≤ 𝔞_{ε/s} / 𝔞_ε ≤ C` for all small `ε`, with both positive. -/
theorem aEpsDF_ratio_bdd' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq)
    (hLM : LMLem2_1) (h699 : DDDFEq6_99) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → DistC)
    (hg : IsWholePlaneGFF g P) {s : ℝ} (hs : 0 < s) :
    ∃ C > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      0 < aEpsDF (xiGamma γ) ε ∧ 0 < aEpsDF (xiGamma γ) (ε / s) ∧
      C⁻¹ ≤ aEpsDF (xiGamma γ) (ε / s) / aEpsDF (xiGamma γ) ε ∧
        aEpsDF (xiGamma γ) (ε / s) / aEpsDF (xiGamma γ) ε ≤ C := by
  obtain ⟨W, hW, C₁, hC₁, εb, hεb, hb⟩ := aEps_lambda_W' h11 h12 h29 hLM hγ hγ2 P g hg
  have := hW.isProbabilityMeasure
  obtain ⟨C₂, hC₂, hM⟩ := h699 γ hγ hγ2 LQGDimension.ExistAsm.stdP W hW
  set Λ := lambdaDelta (xiGamma γ) W LQGDimension.ExistAsm.stdP
  set A := aEpsDF (xiGamma γ)
  have hposΛ : ∀ δ, 0 < δ → δ < εb → 0 < Λ δ := fun δ h0 h1 => (hb δ h0 h1).1
  -- the ratio of `A` is controlled by the ratio of `Λ`
  have key : ∀ x y, 0 < x → x < εb → 0 < y → y < εb → ∀ K > 0,
      K⁻¹ * Λ y ≤ Λ x → Λ x ≤ K * Λ y →
      0 < A x ∧ 0 < A y ∧ (C₁ ^ 2 * K)⁻¹ ≤ A x / A y ∧ A x / A y ≤ C₁ ^ 2 * K := by
    intro x y hx0 hx hy0 hy K hK hl hu
    obtain ⟨hΛx, hxl, hxu⟩ := hb x hx0 hx
    obtain ⟨hΛy, hyl, hyu⟩ := hb y hy0 hy
    have hAx : 0 < A x := lt_of_lt_of_le (by positivity) hxl
    have hAy : 0 < A y := lt_of_lt_of_le (by positivity) hyl
    refine ⟨hAx, hAy, ?_, ?_⟩
    · rw [le_div_iff₀ hAy]
      calc (C₁ ^ 2 * K)⁻¹ * A y ≤ (C₁ ^ 2 * K)⁻¹ * (C₁ * Λ y) :=
            mul_le_mul_of_nonneg_left hyu (by positivity)
        _ = C₁⁻¹ * (K⁻¹ * Λ y) := by field_simp
        _ ≤ C₁⁻¹ * Λ x := mul_le_mul_of_nonneg_left hl (by positivity)
        _ ≤ A x := hxl
    · rw [div_le_iff₀ hAy]
      calc A x ≤ C₁ * Λ x := hxu
        _ ≤ C₁ * (K * Λ y) := mul_le_mul_of_nonneg_left hu hC₁.le
        _ = C₁ ^ 2 * K * (C₁⁻¹ * Λ y) := by field_simp
        _ ≤ C₁ ^ 2 * K * A y := mul_le_mul_of_nonneg_left hyl (by positivity)
  rcases lt_trichotomy s 1 with hs1 | rfl | hs1
  · -- `s < 1`: `ε = (ε/s) · s`
    obtain ⟨K, hK, hK'⟩ := ratio_of_mulCont hC₂ hM ⟨hs, hs1⟩ hεb hposΛ
    refine ⟨C₁ ^ 2 * K, by positivity, s * min εb s, by positivity, fun ε hε hε₀ => ?_⟩
    have hεs : ε / s < min εb s := by rw [div_lt_iff₀ hs, mul_comm]; exact hε₀
    have hεs0 : 0 < ε / s := div_pos hε hs
    have e : ε / s * s = ε := div_mul_cancel₀ ε hs.ne'
    obtain ⟨hl, hu⟩ := hK' _ hεs0 hεs
    rw [e] at hl hu
    have hεb' : ε / s < εb := hεs.trans_le (min_le_left _ _)
    have hε' : ε < εb := by
      have : ε ≤ ε / s := by rw [le_div_iff₀ hs]; nlinarith
      linarith
    -- `Λ(ε/s) ≍ Λ(ε)` with constant `K`
    have hΛε := hposΛ ε hε hε'
    obtain ⟨h1, h2, h3, h4⟩ := key (ε / s) ε hεs0 hεb' hε hε' K hK
      ((inv_mul_le_iff₀ hK).2 hu) ((inv_mul_le_iff₀ hK).1 hl)
    exact ⟨h2, h1, h3, h4⟩
  · refine ⟨1, one_pos, εb, hεb, fun ε hε hε₀ => ?_⟩
    obtain ⟨hΛ, hl, -⟩ := hb ε hε hε₀
    have hA : 0 < A ε := lt_of_lt_of_le (by positivity) hl
    rw [div_one, div_self hA.ne', inv_one]
    exact ⟨hA, hA, le_rfl, le_rfl⟩
  · -- `s > 1`: `ε/s = ε · s⁻¹`
    have ht : s⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.2 hs, inv_lt_one_of_one_lt₀ hs1⟩
    obtain ⟨K, hK, hK'⟩ := ratio_of_mulCont hC₂ hM ht hεb hposΛ
    refine ⟨C₁ ^ 2 * K, by positivity, min εb s⁻¹, lt_min hεb ht.1, fun ε hε hε₀ => ?_⟩
    obtain ⟨hl, hu⟩ := hK' _ hε hε₀
    rw [← div_eq_mul_inv] at hl hu
    have hε' : ε < εb := hε₀.trans_le (min_le_left _ _)
    have hεs : ε / s < εb := lt_of_le_of_lt (div_le_self hε.le hs1.le) hε'
    obtain ⟨h1, h2, h3, h4⟩ := key (ε / s) ε (div_pos hε hs) hεs hε hε' K hK hl hu
    exact ⟨h2, h1, h3, h4⟩


end LQGMetric.DFGPS.Q12
