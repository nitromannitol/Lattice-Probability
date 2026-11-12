/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P22A4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P22A3

/-!
# DG Proposition 3.22 for `ĥ` at `𝕍`-scale (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Proposition 3.22
(`prop-lfpp-upper0`, DG:1722–1771), the white-noise half (eqn-lfpp-upper-show): with polynomially
high probability as `ε → 0`, for all `z, w ∈ 𝕊`,
`D^{LFPP}_{ĥ_{ε^β}}(z, w; U) ≤ ε^{β(1 − 2/d − γ²/(2d)) − ζ}` (`dg_prop322_hat`), at `𝕍`-scale
(DV-D105-3: `𝕊 = c + [0,L]²`, `U = c + [−r, L+r]²`, cells of Lemma 3.21 inside `Q'`).
Inputs (DG:1739–1744, 1768): Prop. 3.9 (`dg_prop39`), Lemma 3.21 (`dg_lemma321`), Lemma 3.8 lower
half (`DGL38Lower` for one `β' > β`), Lemma 3.5 (`dg_lemma35`). The passage from `ĥ_{ε^β}` to
`h^{𝕊(1)}_δ` (Lemma 3.7, DG:1729) and the change of scale are not done here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DG Proposition 3.22, white-noise form** (DG:1722–1771, (eqn-lfpp-upper-show)) -/
theorem dg_prop322_hat (hW : IsWhiteNoise P W) {γ d : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hd : 1 ≤ d) {μ : Ω → Measure ℂ} (c : ℂ) {L r r' : ℝ} (hL0 : 0 ≤ L) (hr : 0 < r)
    (hr' : 0 < r') (h0 : 0 ≤ c.re - r) (h0' : 0 ≤ c.im - r) (h1 : c.re + L + r < 1)
    (h1' : c.im + L + r < 1) {Q' : Set ℂ} (hQ'c : IsCompact Q')
    (hQ' : Icc (c.re - r - r') (c.re + L + r + r') ×ℂ Icc (c.im - r - r') (c.im + L + r + r') ⊆
      Q')
    (h311 : DGLem311Scaled P W μ γ d (p39Box c L r))
    (h311v : DGLem311ScaledV P W μ γ d (p39Box c L r)) (h319 : DGLem319Scaled P W μ γ d Q')
    {βb : ℝ} (hβb : 0 < βb) (hU38 : DGL38Upper P μ (p39Sq c L) βb) {β β' : ℝ} (hβ : 0 < β)
    (hββ' : β < β') (hβγ : β < 2 / (2 + γ) ^ 2) (hL38 : DGL38Lower P μ (p39Box c L r) β')
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      P {ω | ¬ ∀ z ∈ p39Sq c L, ∀ w ∈ p39Sq c L,
        dgLFPP (γ / d) (fun x => DDDF.phiVer W P (ε ^ β) 1 x ω) (p39Box c L r) z w ≤
          ε ^ (β * (1 - 2 / d - γ ^ 2 / (2 * d)) - ζ)} ≤ ENNReal.ofReal (C * ε ^ p) := by
  have hLr : L + r ≤ 1 := by linarith
  have hd0 : 0 < d := by linarith
  -- parameters
  set ζ₁ := min (1 / 2) (ζ / 8) with hζ₁
  have hζ₁0 : 0 < ζ₁ := lt_min (by norm_num) (by linarith)
  have hζ₁h : ζ₁ ≤ 1 / 2 := min_le_left _ _
  have hζ₁8 : ζ₁ ≤ ζ / 8 := min_le_right _ _
  have hdz : 1 / 2 ≤ d - ζ₁ := by linarith
  have k1 : 1 / (d - ζ₁) - 1 / d ≤ ζ / 4 := by
    have e : 1 / (d - ζ₁) - 1 / d = ζ₁ / (d * (d - ζ₁)) := by
      field_simp; ring
    have hdd : 1 / 2 ≤ d * (d - ζ₁) := by nlinarith
    rw [e, div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hdd (by linarith : (0 : ℝ) ≤ ζ / 4)]
  set ζ₃ := ζ * d / (2 * γ * β) with hζ₃
  have hζ₃0 : 0 < ζ₃ := by positivity
  have k3 : γ * ζ₃ * β / d ≤ ζ / 2 := by
    rw [hζ₃]; field_simp; ring_nf; rfl
  -- the four estimates
  obtain ⟨p₁, C₁, ε₁, hp₁, hε₁, e1⟩ := dg_prop39 hW hγ hγ2 hd
    (isCompact_Icc.reProdIm isCompact_Icc).isBounded c hL0 hr hLr subset_rfl h311 h311v hβb
    hU38 hζ₁0 (by linarith)
  obtain ⟨p₂, C₂, ε₂, hp₂, hε₂, e2⟩ := dg_lemma321 hW hγ hd hβ hβγ hQ'c.isBounded 0 h319
    (ζ := ζ / 4) (by positivity)
  obtain ⟨p₃, C₃, ε₃, hp₃, hε₃, e3⟩ := hL38
  obtain ⟨K, δ₀, hδ₀, e4⟩ := dg_lemma35 hW hQ'c.isBounded (P := P) hζ₃0
  -- the thresholds
  set ε₇ := (4 * (2 : ℝ) ^ β') ^ (-(1 / (β' - β))) with hε₇
  have hbb : 0 < β' - β := by linarith
  have h4 : 0 < 4 * (2 : ℝ) ^ β' := by positivity
  have hε₇0 : 0 < ε₇ := Real.rpow_pos_of_pos h4 _
  have hδ₀' : 0 < δ₀ ^ β⁻¹ := Real.rpow_pos_of_pos hδ₀ _
  have hr'' : 0 < (r' / 2) ^ β⁻¹ := Real.rpow_pos_of_pos (by positivity) _
  have h14' : 0 < (14 : ℝ) ^ (-(2 / ζ)) := Real.rpow_pos_of_pos (by norm_num) _
  set p := min p₁ (min p₂ (min p₃ (β * ζ₃))) with hp
  have hp0 : 0 < p := lt_min hp₁ (lt_min hp₂ (lt_min hp₃ (by positivity)))
  refine ⟨p, |C₁| + |C₂| + |C₃ * (2 : ℝ) ^ p₃| + |K|,
    min (min (min 1 ε₁) (min ε₂ (ε₃ / 2))) (min (min (δ₀ ^ β⁻¹) ((r' / 2) ^ β⁻¹))
      (min ((14 : ℝ) ^ (-(2 / ζ))) ε₇)), hp0, by positivity, fun ε hε hεlt => ?_⟩
  simp only [lt_min_iff] at hεlt
  obtain ⟨⟨⟨hε1, hεa⟩, hεb, hεc⟩, ⟨hεd, hεe⟩, hεf, hεg⟩ := hεlt
  have hεβ0 : 0 < ε ^ β := Real.rpow_pos_of_pos hε _
  have hεδ : ε ^ β < δ₀ := by
    calc ε ^ β < (δ₀ ^ β⁻¹) ^ β := Real.rpow_lt_rpow hε.le hεd hβ
      _ = δ₀ := Real.rpow_inv_rpow hδ₀.le hβ.ne'
  have hεr : ε ^ β ≤ r' / 2 := by
    calc ε ^ β ≤ ((r' / 2) ^ β⁻¹) ^ β := Real.rpow_le_rpow hε.le hεe.le hβ.le
      _ = r' / 2 := Real.rpow_inv_rpow (by positivity) hβ.ne'
  have h14 : 14 * ε ^ (ζ / 2) ≤ 1 := by
    have : ε ^ (ζ / 2) ≤ ((14 : ℝ) ^ (-(2 / ζ))) ^ (ζ / 2) :=
      Real.rpow_le_rpow hε.le hεf.le (by positivity)
    rw [← Real.rpow_mul (by norm_num)] at this
    have e : -(2 / ζ) * (ζ / 2) = -1 := by field_simp
    rw [e, Real.rpow_neg_one] at this
    linarith
  have hrad : (2 * ε) ^ β' ≤ ε ^ β / 4 := by
    rw [Real.mul_rpow (by norm_num) hε.le]
    have e : ε ^ β' = ε ^ β * ε ^ (β' - β) := by rw [← Real.rpow_add hε]; ring_nf
    have k : ε ^ (β' - β) ≤ (4 * (2 : ℝ) ^ β')⁻¹ := by
      calc ε ^ (β' - β) ≤ ε₇ ^ (β' - β) := Real.rpow_le_rpow hε.le hεg.le hbb.le
        _ = (4 * (2 : ℝ) ^ β')⁻¹ := by
          rw [hε₇, ← Real.rpow_mul h4.le]
          have : -(1 / (β' - β)) * (β' - β) = -1 := by field_simp
          rw [this, Real.rpow_neg_one]
    rw [e]
    have h2 : 0 < (2 : ℝ) ^ β' := by positivity
    calc (2 : ℝ) ^ β' * (ε ^ β * ε ^ (β' - β)) ≤ (2 : ℝ) ^ β' * (ε ^ β * (4 * (2 : ℝ) ^ β')⁻¹) := by
          gcongr
      _ = ε ^ β / 4 := by field_simp
  have hM := l321M_le hβ hε hε1
  -- the good event
  have hsub : {ω | ¬ ∀ z ∈ p39Sq c L, ∀ w ∈ p39Sq c L,
      dgLFPP (γ / d) (fun x => DDDF.phiVer W P (ε ^ β) 1 x ω) (p39Box c L r) z w ≤
        ε ^ (β * (1 - 2 / d - γ ^ 2 / (2 * d)) - ζ)} ⊆
      (({ω | ¬ ∀ z ∈ p39Sq c L, ∀ w ∈ p39Sq c L, (dgLGD (μ ω) ε (p39Box c L r) z w : ℝ≥0∞) ≤
          ENNReal.ofReal (ε ^ (-(1 / (d - ζ₁))))} ∪
        {ω | ∃ x ∈ l321Grid Q' 0 β ε, (l313Set (μ ω) ε univ
          (l321In ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner 0 (l321M β ε) x) 1)
          (frontier (l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner 0 (l321M β ε) x) 1)) : ℝ≥0∞) <
        ENNReal.ofReal (l321Tgt γ d (ζ / 4) β ε (sSup ((fun z => DDDF.phiVer W P (ε ^ β) 1 z ω) ''
          l321Out ((2 : ℝ)⁻¹ ^ l321M β ε) (l313Corner 0 (l321M β ε) x) 1)))}) ∪
        {ω | ¬ ∀ z ∈ p39Box c L r, ENNReal.ofReal (2 * ε) ≤ μ ω (ball z ((2 * ε) ^ β'))}) ∪
        {ω | ∃ z ∈ Q', (2 + ζ₃) * Real.log (ε ^ β)⁻¹ < |DDDF.phiVer W P (ε ^ β) 1 z ω|} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hcon
    apply hω
    have hT := not_not.1 n1
    have hcross : ∀ i ∈ l321Grid Q' 0 β ε, _ := fun i hi => not_lt.1 (fun h => n2 ⟨i, hi, h⟩)
    have hm := not_not.1 n3
    have hb4 : ∀ z ∈ Q', |DDDF.phiVer W P (ε ^ β) 1 z ω| ≤ (2 + ζ₃) * Real.log (ε ^ β)⁻¹ :=
      fun z hz => not_lt.1 (fun h => n4 ⟨z, hz, h⟩)
    have hcont := (DDDF.isPhiVersion_phiVer hW hεβ0
      (Real.rpow_le_one hε.le hε1.le hβ.le)).cont ω
    have hlog : Real.log (ε ^ β)⁻¹ = β * Real.log ε⁻¹ := by
      rw [Real.log_inv, Real.log_rpow hε, Real.log_inv]; ring
    have hlog0 : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε, hε1.le⟩)
    have hmass : ∀ x ∈ p39Box c L r,
        ENNReal.ofReal ε < μ ω (ball x ((2 : ℝ)⁻¹ ^ l321M β ε / 2)) := by
      intro x hx
      refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
        ((hm x hx).trans (measure_mono (ball_subset_ball ?_)))
      linarith [hM.2]
    have hgood := p322a_good (μ := μ ω) hcont hγ hd0 hε (T := ε ^ (-(1 / (d - ζ₁))))
      (Real.rpow_pos_of_pos hε _).le hQ'c h0 h0' h1 h1' (r' := r') (by linarith [hM.1]) hQ'
      hcross hmass hT
    intro z hz w hw
    refine (hgood z hz w hw).trans (p322a_exp hε hε1.le hβ hγ hd0 (by linarith) hζ
      (by positivity) hM.1 ?_ k1 k3 h14)
    refine Real.sSup_le ?_ (by positivity)
    rintro _ ⟨y, hy, rfl⟩
    exact (le_abs_self _).trans ((hb4 y hy).trans_eq (by rw [hlog]; ring))
  -- the union bound
  have hb : ∀ (Ci q : ℝ), p ≤ q →
      ENNReal.ofReal (Ci * ε ^ q) ≤ ENNReal.ofReal (|Ci| * ε ^ p) := by
    intro Ci q hq
    apply ENNReal.ofReal_le_ofReal
    have := Real.rpow_le_rpow_of_exponent_ge hε hε1.le hq
    have h0 : 0 ≤ ε ^ q := (Real.rpow_pos_of_pos hε q).le
    calc Ci * ε ^ q ≤ |Ci| * ε ^ q := mul_le_mul_of_nonneg_right (le_abs_self Ci) h0
      _ ≤ _ := mul_le_mul_of_nonneg_left this (abs_nonneg Ci)
  have hpp : 0 ≤ ε ^ p := (Real.rpow_pos_of_pos hε _).le
  have f3 : C₃ * (2 * ε) ^ p₃ = (C₃ * (2 : ℝ) ^ p₃) * ε ^ p₃ := by
    rw [Real.mul_rpow (by norm_num) hε.le]; ring
  have f4 : K * (ε ^ β) ^ ζ₃ = K * ε ^ (β * ζ₃) := by rw [← Real.rpow_mul hε.le]
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ ENNReal.ofReal (C₁ * ε ^ p₁) + ENNReal.ofReal (C₂ * ε ^ p₂) +
        ENNReal.ofReal (C₃ * (2 * ε) ^ p₃) + ENNReal.ofReal (K * (ε ^ β) ^ ζ₃) :=
        add_le_add (add_le_add (add_le_add (e1 ε hε hεa) (e2 ε hε hεb))
          (e3 (2 * ε) (by positivity) (by linarith))) (e4 _ ⟨hεβ0, hεδ⟩)
    _ ≤ ENNReal.ofReal (|C₁| * ε ^ p) + ENNReal.ofReal (|C₂| * ε ^ p) +
        ENNReal.ofReal (|C₃ * (2 : ℝ) ^ p₃| * ε ^ p) + ENNReal.ofReal (|K| * ε ^ p) := by
        rw [f3, f4]
        exact add_le_add (add_le_add (add_le_add (hb _ _ (min_le_left _ _))
          (hb _ _ ((min_le_right _ _).trans (min_le_left _ _))))
          (hb _ _ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
          (hb _ _ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end DG
end LQGMetric
