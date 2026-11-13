/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.TwoD.LemmaA1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.RemainderVar
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.CoupledGFF
import LatticeProb.Bonanno.HigherDimLFPP.Field.OscBlock
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.ZeroRegBoundary

/-!
# Lemma A.1 for circle averages (packet P-X10, target T3)

Source: `source/higher-dimensional-lfpp-limit.pdf`, App. A.2, Lemma A.1 ("In dimension two the
same conclusion holds for circle averages of radius ε, including the normalization that the
unit-circle average at the origin is zero"), (A.3); planning audit HA5, Details D12, Claim 3 and
the statement `LemmaA1Circle` of Details (c); ruling H12.

**Statement** (`lemmaA1_circle`, `lemmaA1Circle`).  Let `W` be a white noise on `L²(ℝ × ℝ²)`, `H ε`
continuous versions of `H_{ε,1}` (`ε ∈ (0,1)`) and `h r` continuous versions of the circle
averages `W(circVec κ r ·)` (`r > 0`), all on the same probability space.  Then
`sup_{x ∈ [-3,3]²} |h_ε(x) - H_{ε,1}(x)| = O_P(√(log ε⁻¹))` uniformly in `ε ∈ (0, 1/2)`: for every
`η > 0` there is `M` with
`P(M √(log ε⁻¹) < sup_{[-3,3]²} |h_ε - H_{ε,1}|) ≤ η` for all `ε ∈ (0, 1/2)`
(outer measure).

**Proof.**  Cover `[-3,3]²` by the grid of mesh `ε` (`Osc.grid 0 3 ε`, at most `49/ε²` points,
every point within `√2 ε` of its grid point `g`).  With `R = h_ε - H_{ε,1}`,
`|R(x)| ≤ |R(g)| + |h_ε(x) - h_ε(g)| + |H_{ε,1}(x) - H_{ε,1}(g)|`, and each term has a Gaussian
tail, uniformly in `g` and `ε`:

* `R(g)` is centered Gaussian with variance `‖circVec - bandVec‖² ≤ V` (the point variance bound
  `norm_circVec_sub_bandVec_sq_le`), so `P(|R(g)| > T) ≤ 2 e^{-T²/(2V)}`;
* the circle-average block: `h` is an `IsGFFCircleAverage` process (Claim 2), and
  `LQGDimension.Osc37.block_event_bound` (chaining with `Var(h_ε(z) - h_ε(w)) ≤ 2|z - w|/ε`)
  gives `P(∃ u, |u - g| < 10ε, |h_ε(u) - h_ε(g)| > T) ≤ 2 e^{-2(T - c₁)²/(20π²)}`;
* the band block: `Osc.block_tail` (P-OSC; `‖k_z - k_w‖² ≤ L|z - w|²/ε²`) gives
  `P(∃ y ∈ B̄(g, √2 ε), |H(y) - H(g)| > T) ≤ 2 e^{-(T - c₂)²/(4L)}`.

A union bound over the grid with `T = M √(log ε⁻¹)/3` gives
`≤ (49/ε²) · 6 e^{-c (T - c₀)²} ≤ η` once `M` is large (`LemmaA1.exists_M`).  The paper's entropy integral
of the difference field is replaced by the two block bounds of the separate fields, which are
already proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Real
open scoped RealInnerProductSpace

namespace HigherDimLFPP

namespace LemmaA1

/-- **The choice of `M`**: for `c > 0`, `c₀ ≥ 0`, `η > 0` there is `M > 0` such that for every
`ε ∈ (0, 1/2)`, with `T = M √(log ε⁻¹)/3`: `2c₀ ≤ T` and `(49/ε²) · 6 e^{-c (T - c₀)²} ≤ η`. -/
theorem exists_M {c c₀ η : ℝ} (hc : 0 < c) (hc₀ : 0 ≤ c₀) (hη : 0 < η) :
    ∃ M > 0, ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹,
      2 * c₀ ≤ M * √(Real.log ε⁻¹) / 3 ∧
      49 / ε ^ 2 * (6 * Real.exp (-(c * (M * √(Real.log ε⁻¹) / 3 - c₀) ^ 2))) ≤ η := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K : ℝ := 2 + |Real.log (294 / η)| / Real.log 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set M : ℝ := max (√(36 * K / c)) (6 * c₀ / √(Real.log 2) + 1) with hM
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨M, hM0, fun ε hε => ?_⟩
  obtain ⟨hε0, hε2⟩ := hε
  set ℓ := Real.log ε⁻¹ with hℓdef
  have h2le : 2 ≤ ε⁻¹ := by
    rw [le_inv_comm₀ two_pos hε0]
    exact hε2.le
  have hℓ : Real.log 2 ≤ ℓ := Real.log_le_log two_pos h2le
  have hℓ0 : 0 < ℓ := hl2.trans_le hℓ
  set T := M * √ℓ / 3 with hT
  have hsq : √(Real.log 2) ≤ √ℓ := Real.sqrt_le_sqrt hℓ
  have hsl2 : 0 < √(Real.log 2) := Real.sqrt_pos.2 hl2
  have hT2c : 2 * c₀ ≤ T := by
    have h1 : 6 * c₀ / √(Real.log 2) ≤ M := (le_max_right _ _).trans' (by linarith)
    have h2 : 6 * c₀ ≤ M * √(Real.log 2) := by
      rw [div_le_iff₀ hsl2] at h1
      exact h1
    have h3 : M * √(Real.log 2) ≤ M * √ℓ := mul_le_mul_of_nonneg_left hsq hM0.le
    rw [hT]
    linarith
  refine ⟨hT2c, ?_⟩
  -- the exponent
  have hTc : T / 2 ≤ T - c₀ := by linarith
  have hT0 : 0 ≤ T / 2 := by linarith
  have hsqT : T ^ 2 / 4 ≤ (T - c₀) ^ 2 := by
    have := pow_le_pow_left₀ hT0 hTc 2
    calc T ^ 2 / 4 = (T / 2) ^ 2 := by ring
      _ ≤ (T - c₀) ^ 2 := this
  have hT2 : T ^ 2 = M ^ 2 * ℓ / 9 := by
    rw [hT, div_pow, mul_pow, Real.sq_sqrt hℓ0.le]
    norm_num
  have hM2 : 36 * K / c ≤ M ^ 2 := by
    have h1 : √(36 * K / c) ≤ M := le_max_left _ _
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hexp1 : K * ℓ ≤ c * (T - c₀) ^ 2 := by
    have h1 : c * (M ^ 2 * ℓ / 36) ≤ c * (T - c₀) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      rw [hT2] at hsqT
      linarith
    have h2 : K * ℓ ≤ c * (M ^ 2 * ℓ / 36) := by
      have h3 : 36 * K ≤ c * M ^ 2 := by
        rw [div_le_iff₀ hc] at hM2
        linarith
      nlinarith
    linarith
  -- `49/ε² = 49 e^{2ℓ}`
  have hε2' : 49 / ε ^ 2 = 49 * Real.exp (2 * ℓ) := by
    rw [show 2 * ℓ = ℓ + ℓ by ring, Real.exp_add, hℓdef, Real.exp_log (by positivity)]
    field_simp
  rw [hε2']
  have hkey : 2 * ℓ - K * ℓ ≤ -|Real.log (294 / η)| := by
    have h1 : |Real.log (294 / η)| ≤ |Real.log (294 / η)| / Real.log 2 * ℓ := by
      have : 1 ≤ ℓ / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
      calc |Real.log (294 / η)| = |Real.log (294 / η)| * 1 := (mul_one _).symm
        _ ≤ |Real.log (294 / η)| * (ℓ / Real.log 2) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = |Real.log (294 / η)| / Real.log 2 * ℓ := by ring
    rw [hK]
    nlinarith
  have hexp2 : Real.exp (-|Real.log (294 / η)|) ≤ η / 294 := by
    calc Real.exp (-|Real.log (294 / η)|) ≤ Real.exp (-Real.log (294 / η)) :=
          Real.exp_le_exp.2 (neg_le_neg (le_abs_self _))
      _ = η / 294 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  calc 49 * Real.exp (2 * ℓ) * (6 * Real.exp (-(c * (T - c₀) ^ 2)))
      = 294 * Real.exp (2 * ℓ - c * (T - c₀) ^ 2) := by
        rw [show 2 * ℓ - c * (T - c₀) ^ 2 = 2 * ℓ + -(c * (T - c₀) ^ 2) by ring, Real.exp_add]
        ring
    _ ≤ 294 * Real.exp (-|Real.log (294 / η)|) := by
        gcongr
        linarith
    _ ≤ 294 * (η / 294) := by gcongr
    _ = η := by field_simp

end LemmaA1

/-! ### The three tails -/

section Main

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN 2 → Ω → ℝ} {κ : Rd 2 → ℝ}

/-- **Gaussian tail of the remainder at a point**: `R(g) = h_ε(g) - H_{ε,1}(g)` is centered
Gaussian with variance `‖circVec κ ε g - bandVec κ ε 1 g‖² ≤ V`, so
`P(T < |R(g)|) ≤ 2 e^{-T²/(2V)}`. -/
theorem remainder_point_tail (hW : IsWhiteNoise P W) {ε : ℝ} {Hε : Rd 2 → Ω → ℝ}
    (hHε : IsBandVersion P W κ ε 1 Hε) {hε : ℂ → Ω → ℝ} (hhε : IsCircleVersion P W κ ε hε)
    (g : Rd 2) {V : ℝ}
    (hV : ‖circVec κ ε (cToR2.symm g) - bandVec κ ε 1 g‖ ^ 2 ≤ V) {T : ℝ} (hT : 0 ≤ T) :
    P {ω | T < |hε (cToR2.symm g) ω - Hε g ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-T ^ 2 / (2 * V))) := by
  have := hW.isProbabilityMeasure
  set f : WN 2 := circVec κ ε (cToR2.symm g) - bandVec κ ε 1 g with hf
  set Y : Ω → ℝ := fun ω => hε (cToR2.symm g) ω - Hε g ω with hY
  have hYm : Measurable Y := (hhε.measurable _).sub (hHε.measurable g)
  have hYW : Y =ᵐ[P] W f := by
    filter_upwards [hhε.ae_eq (cToR2.symm g), hHε.ae_eq g,
      hW.sub_ae (circVec κ ε (cToR2.symm g)) (bandVec κ ε 1 g)] with ω h1 h2 h3
    rw [hY]
    simp only
    rw [h1, h2, h3]
  have hlaw : P.map Y = gaussianReal 0 (‖f‖ ^ 2).toNNReal := by
    rw [Measure.map_congr hYW, (hW.hasLaw_single f).map_eq]
  have hV0 : 0 ≤ V := (sq_nonneg _).trans hV
  have hVc : (‖f‖ ^ 2).toNNReal ≤ V.toNNReal := Real.toNNReal_le_toNNReal hV
  have h := QuantumZipper.ZeroRegBdry.zrb_measureReal_abs_ge_le hYm hlaw hVc hT
  rw [Real.coe_toNNReal _ hV0] at h
  calc P {ω | T < |hε (cToR2.symm g) ω - Hε g ω|} ≤ P {ω | T ≤ |Y ω|} :=
        measure_mono fun ω (hω : T < |Y ω|) => hω.le
    _ = ENNReal.ofReal (P.real {ω | T ≤ |Y ω|}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-T ^ 2 / (2 * V))) := ENNReal.ofReal_le_ofReal h

/-- **Lemma A.1, circle part** (target T3; HA5 D12, Claim 3): in the coupled realization,
`sup_{x ∈ [-3,3]²} |h_ε(x) - H_{ε,1}(x)| = O_P(√(log ε⁻¹))` uniformly in `ε ∈ (0, 1/2)`. -/
theorem lemmaA1_circle (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {H : ℝ → Rd 2 → Ω → ℝ} (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε))
    {h : ℝ → ℂ → Ω → ℝ} (hh : ∀ r > 0, IsCircleVersion P W κ r (h r)) :
    ∀ η > 0, ∃ M > 0, ∀ ε ∈ Ioo (0 : ℝ) 2⁻¹,
      P {ω | M * √(Real.log ε⁻¹) <
        ⨆ x : {x : Rd 2 // ∀ i, |x i| ≤ 3}, |h ε (cToR2.symm x.1) ω - H ε x.1 ω|} ≤
        ENNReal.ofReal η := by
  intro η hη
  have hG := isGFFCircleAverage_of_isCircleVersion hκ hW hh
  obtain ⟨C, hC⟩ := norm_circVec_sub_bandVec_sq_le hκ
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_sq_le hκ
  set V : ℝ := max (C + 30) 1 with hVdef
  have hV0 : 0 < V := lt_of_lt_of_le one_pos (le_max_right _ _)
  set L' : ℝ := max L 1 with hL'def
  have hL'0 : 0 < L' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hL' : ∀ a : ℝ, 0 < a → ∀ (b : ℝ) (z w : Rd 2),
      ‖bandVec κ a b z - bandVec κ a b w‖ ^ 2 ≤ L' * ‖z - w‖ ^ 2 / a ^ 2 := by
    intro a ha b z w
    refine (hL a ha b z w).trans ?_
    gcongr
    exact le_max_left _ _
  set c₁ : ℝ := LQGDimension.Osc37.chainConst with hc₁
  set r₂ : ℝ := √(2 : ℝ) with hr₂
  have hr₂0 : 0 ≤ r₂ := Real.sqrt_nonneg _
  set c₂ : ℝ := Osc.blockConst 2 L' r₂ with hc₂
  have hc₁0 : 0 ≤ c₁ := LQGDimension.Osc37.chainConst_nonneg
  have hc₂0 : 0 ≤ c₂ := Osc.blockConst_nonneg 2 hr₂0
  set c₀ : ℝ := max c₁ c₂ with hc₀
  have hc₀0 : 0 ≤ c₀ := le_max_of_le_left hc₁0
  set c : ℝ := min (1 / (2 * V)) (min (2 / (π ^ 2 * 20)) (1 / (2 * (r₂ ^ 2 * L')))) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨M, hM0, hM⟩ := LemmaA1.exists_M hc0 hc₀0 hη
  refine ⟨M, hM0, fun ε hε => ?_⟩
  obtain ⟨hT2c, hbound⟩ := hM ε hε
  obtain ⟨hε0, hε2⟩ := hε
  have hε1 : ε < 1 := hε2.trans (by norm_num)
  set T : ℝ := M * √(Real.log ε⁻¹) / 3 with hT
  have hTc₀ : c₀ ≤ T := by linarith
  have hTc₁ : c₁ ≤ T := (le_max_left _ _).trans hTc₀
  have hTc₂ : c₂ ≤ T := (le_max_right _ _).trans hTc₀
  have hT0 : 0 ≤ T := hc₀0.trans hTc₀
  set e : ℝ := Real.exp (-(c * (T - c₀) ^ 2)) with he
  -- the grid and the three events
  set G : Finset (Rd 2) := Osc.grid 0 3 ε with hGdef
  set E₁ : Rd 2 → Set Ω := fun g => {ω | T < |h ε (cToR2.symm g) ω - H ε g ω|} with hE₁
  set E₂ : Rd 2 → Set Ω := fun g => {ω | ∃ u : ℂ, ‖u - cToR2.symm g‖ < 10 * ε ∧
    T < |h ε u ω - h ε (cToR2.symm g) ω|} with hE₂
  set E₃ : Rd 2 → Set Ω := fun g => {ω | ∃ z ∈ closedBall g (r₂ * ε),
    c₂ + (T - c₂) < |H ε z ω - H ε g ω|} with hE₃
  -- the event is covered
  have hsub : {ω | M * √(Real.log ε⁻¹) <
      ⨆ x : {x : Rd 2 // ∀ i, |x i| ≤ 3}, |h ε (cToR2.symm x.1) ω - H ε x.1 ω|} ⊆
      ⋃ g ∈ G, (E₁ g ∪ E₂ g ∪ E₃ g) := by
    intro ω hω
    have : Nonempty {x : Rd 2 // ∀ i, |x i| ≤ 3} := ⟨⟨0, fun i => by simp⟩⟩
    rw [mem_ofPred_eq] at hω
    obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup hω
    have hxbox : x.1 ∈ Osc.box 0 3 := fun i => by
      simpa only [PiLp.zero_apply, sub_zero] using x.2 i
    set g := Osc.gridOf 0 3 ε x.1 with hg
    have hgG : g ∈ G := Osc.gridOf_mem_grid 0 hε0 hxbox
    have hxg : ‖x.1 - g‖ ≤ r₂ * ε := by
      have := Osc.norm_sub_gridOf_le (0 : Rd 2) hε0 hxbox
      simpa only [Nat.cast_ofNat] using this
    refine mem_iUnion₂.2 ⟨g, hgG, ?_⟩
    by_contra hn
    simp only [mem_union, not_or, hE₁, hE₂, hE₃, mem_ofPred_eq, not_lt, not_exists,
      not_and] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    have hr₂ε : r₂ * ε < 10 * ε := by
      have : r₂ < 10 := by
        rw [hr₂, Real.sqrt_lt' (by norm_num)]
        norm_num
      exact mul_lt_mul_of_pos_right this hε0
    have h2' := h2 (cToR2.symm x.1) (by
      rw [norm_cToR2_symm_sub]
      exact hxg.trans_lt hr₂ε)
    have h3' := h3 x.1 (by rw [mem_closedBall, dist_eq_norm]; exact hxg)
    rw [add_sub_cancel] at h3'
    have htri : |h ε (cToR2.symm x.1) ω - H ε x.1 ω| ≤
        |h ε (cToR2.symm g) ω - H ε g ω| +
          |h ε (cToR2.symm x.1) ω - h ε (cToR2.symm g) ω| + |H ε x.1 ω - H ε g ω| := by
      have e : h ε (cToR2.symm x.1) ω - H ε x.1 ω =
          (h ε (cToR2.symm g) ω - H ε g ω) +
            (h ε (cToR2.symm x.1) ω - h ε (cToR2.symm g) ω) - (H ε x.1 ω - H ε g ω) := by ring
      rw [e]
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have : M * √(Real.log ε⁻¹) = 3 * T := by rw [hT]; ring
    rw [this] at hx
    linarith
  -- each grid point
  have hpt : ∀ g ∈ G, P (E₁ g ∪ E₂ g ∪ E₃ g) ≤ ENNReal.ofReal (6 * e) := by
    intro g hgG
    have hgbox : g ∈ Osc.box 0 3 := Osc.grid_subset_box 0 (by norm_num) hε0 hgG
    have hgn : ‖g‖ ≤ 5 := by
      have h1 := Osc.norm_sub_le_of_mem_box (by norm_num : (0 : ℝ) ≤ 3) hgbox
      rw [sub_zero, Nat.cast_ofNat] at h1
      have h2 : √(2 : ℝ) ≤ 5 / 3 := by
        have := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (5 / 3) ^ 2 by norm_num)
        rwa [Real.sqrt_sq (by norm_num)] at this
      nlinarith
    -- the point tail
    have hVg : ‖circVec κ ε (cToR2.symm g) - bandVec κ ε 1 g‖ ^ 2 ≤ V := by
      have h1 := hC ε ⟨hε0, hε1⟩ (cToR2.symm g)
      rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map] at h1
      refine h1.trans ?_
      rw [hVdef]
      refine le_max_of_le_left ?_
      linarith
    have t₁ := remainder_point_tail hW (hH ε ⟨hε0, hε1⟩) (hh ε hε0) g hVg hT0
    have t₂ := LQGDimension.Osc37.block_event_bound hG hε0 (cToR2.symm g) hTc₁
    have t₃ := Osc.block_tail hW hε0 (hH ε ⟨hε0, hε1⟩) hL'0.le (hL' ε hε0 1) g hr₂0
      (sub_nonneg.2 hTc₂)
    -- comparison of the exponents
    have hTd : 0 ≤ T - c₀ := sub_nonneg.2 hTc₀
    have e₁ : Real.exp (-T ^ 2 / (2 * V)) ≤ e := by
      rw [he, Real.exp_le_exp, neg_div, neg_le_neg_iff]
      have h1 : (T - c₀) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hTd (by linarith) 2
      have h2 : c ≤ 1 / (2 * V) := min_le_left _ _
      calc c * (T - c₀) ^ 2 ≤ 1 / (2 * V) * T ^ 2 :=
            mul_le_mul h2 h1 (sq_nonneg _) (by positivity)
        _ = T ^ 2 / (2 * V) := by ring
    have e₂ : Real.exp (-2 * (T - c₁) ^ 2 / (π ^ 2 * 20)) ≤ e := by
      rw [he, Real.exp_le_exp, neg_mul, neg_div, neg_le_neg_iff]
      have h1 : (T - c₀) ^ 2 ≤ (T - c₁) ^ 2 :=
        pow_le_pow_left₀ hTd (by linarith [le_max_left c₁ c₂]) 2
      have h2 : c ≤ 2 / (π ^ 2 * 20) := (min_le_right _ _).trans (min_le_left _ _)
      calc c * (T - c₀) ^ 2 ≤ 2 / (π ^ 2 * 20) * (T - c₁) ^ 2 :=
            mul_le_mul h2 h1 (sq_nonneg _) (by positivity)
        _ = 2 * (T - c₁) ^ 2 / (π ^ 2 * 20) := by ring
    have e₃ : Real.exp (-(T - c₂) ^ 2 / (2 * (r₂ ^ 2 * L'))) ≤ e := by
      rw [he, Real.exp_le_exp, neg_div, neg_le_neg_iff]
      have h1 : (T - c₀) ^ 2 ≤ (T - c₂) ^ 2 :=
        pow_le_pow_left₀ hTd (by linarith [le_max_right c₁ c₂]) 2
      have h2 : c ≤ 1 / (2 * (r₂ ^ 2 * L')) := (min_le_right _ _).trans (min_le_right _ _)
      calc c * (T - c₀) ^ 2 ≤ 1 / (2 * (r₂ ^ 2 * L')) * (T - c₂) ^ 2 :=
            mul_le_mul h2 h1 (sq_nonneg _) (by positivity)
        _ = (T - c₂) ^ 2 / (2 * (r₂ ^ 2 * L')) := by ring
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    calc P (E₁ g ∪ E₂ g ∪ E₃ g) ≤ P (E₁ g) + P (E₂ g) + P (E₃ g) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (2 * e) + ENNReal.ofReal (2 * e) + ENNReal.ofReal (2 * e) := by
          gcongr
          · exact t₁.trans (ENNReal.ofReal_le_ofReal (by linarith))
          · exact t₂.trans (ENNReal.ofReal_le_ofReal (by linarith))
          · exact t₃.trans (ENNReal.ofReal_le_ofReal (by linarith))
      _ = ENNReal.ofReal (6 * e) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  -- the union bound
  have hcard : (G.card : ℝ) ≤ 49 / ε ^ 2 := by
    have h1 := Osc.card_grid_le (0 : Rd 2) (by norm_num : (0 : ℝ) ≤ 3) hε0
    refine h1.trans ?_
    have h2 : 2 * 3 / ε + 1 ≤ 7 / ε := by
      rw [div_add_one hε0.ne', div_le_div_iff_of_pos_right hε0]
      linarith
    calc (2 * 3 / ε + 1) ^ 2 ≤ (7 / ε) ^ 2 := by gcongr
      _ = 49 / ε ^ 2 := by ring
  calc P {ω | M * √(Real.log ε⁻¹) <
        ⨆ x : {x : Rd 2 // ∀ i, |x i| ≤ 3}, |h ε (cToR2.symm x.1) ω - H ε x.1 ω|}
      ≤ P (⋃ g ∈ G, (E₁ g ∪ E₂ g ∪ E₃ g)) := measure_mono hsub
    _ ≤ ∑ g ∈ G, P (E₁ g ∪ E₂ g ∪ E₃ g) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _g ∈ G, ENNReal.ofReal (6 * e) := Finset.sum_le_sum hpt
    _ = ENNReal.ofReal (G.card * (6 * e)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal η := by
        refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hcard
          (by positivity)).trans ?_)
        exact hbound

end Main

end HigherDimLFPP
