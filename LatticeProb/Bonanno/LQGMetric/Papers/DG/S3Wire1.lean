/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3Wire1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18R4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.22 with DG L3.19 on `[1/6,5/6]²` (task P2-DGWIRE)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, Prop 3.22 (DG:1722–1772),
DG:1774–1777.

**Box mismatch.** `dg_prop322_V` (S3P18C) takes DG L3.19 (`DGLem319Scaled`) on
`p39Box p18c0 (1/3) (1/4) = [1/12,11/12]²`, because it calls `dg_prop322_hat` with `r = 1/6`,
`r' = 1/12`. For `μ = μ_ĥ = muHat … p18_hK0` (the measure of the whole chain) this hypothesis is
not available: `μ_ĥ` is the restriction to `K₀ = [1/10,9/10]²`, so on annuli in the strip
`[1/12,1/10) × [1/12,11/12]` it vanishes and the LGD across them is bounded, contradicting the
lower bound of `DGLem319Scaled` for large `n`. The producer `l319LevelInput_muHat` (S3L19R6)
gives L3.19 on boxes `Q ⊆ [1/6,5/6]²`.

Fix (no new mathematics): run `dg_prop322_hat` with `r = r' = 1/12`, so that L3.19 is needed on
`[1/6,5/6]² = p39Box p18c0 (1/3) (1/6)` only; the L3.11 inputs and L3.8's lower bound restrict
from `[1/6,5/6]²` to `[1/4,3/4]²`, and `D(z,w;[1/6,5/6]²) ≤ D(z,w;[1/4,3/4]²)` (more paths).

* `wire_dgLFPP_mono`, `wire_dgLem311Scaled_mono`, `wire_dgLem311ScaledV_mono`,
  `wire_dgL38Lower_mono` — monotonicity in the box.
* `wire_prop322_V`, `wire_prop322_sqOne`, `wire_prop322_sqOne_muHat` — `dg_prop322_V`,
  `dg_prop322_sqOne`, `dg_prop322_sqOne_muHat` with `h319` on `[1/6,5/6]²` (same proofs).
* `wire_r18P322_of` — `R18P322` (`r18P322_of` with `h319` on `[1/6,5/6]²`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise SupTail

variable {Ω : Type} [MeasurableSpace Ω]

/-- the LFPP distance decreases when the box grows (if the small box has a path) -/
lemma wire_dgLFPP_mono {ξ : ℝ} {φ : ℂ → ℝ} {S S' : Set ℂ} (h : S' ⊆ S) {z w : ℂ}
    {q : ℝ → ℂ} (hq : IsDGPath S' z w q) : dgLFPP ξ φ S z w ≤ dgLFPP ξ φ S' z w := by
  have : Nonempty {p : ℝ → ℂ // IsDGPath S' z w p} := ⟨⟨q, hq⟩⟩
  exact le_ciInf fun p => ciInf_le (bddBelow_dg ξ φ S z w)
    ⟨p.1, ⟨p.2.source, p.2.target, p.2.mapsTo.mono_right h, p.2.continuousOn,
      p.2.piecewise_contDiff⟩⟩

lemma wire_dgLem311Scaled_mono {P : Measure Ω} {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ}
    {γ d : ℝ} {Q Q' : Set ℂ} (hQ : Q' ⊆ Q) (h : DGLem311Scaled P W μ γ d Q) :
    DGLem311Scaled P W μ γ d Q' := fun ζ₁ h0 h1 => by
  obtain ⟨a₀, a₁, A, ha₁, hh⟩ := h ζ₁ h0 h1
  exact ⟨a₀, a₁, A, ha₁, fun j n b hb => hh j n b (hb.trans hQ)⟩

lemma wire_dgLem311ScaledV_mono {P : Measure Ω} {W : WNSpace → Ω → ℝ} {μ : Ω → Measure ℂ}
    {γ d : ℝ} {Q Q' : Set ℂ} (hQ : Q' ⊆ Q) (h : DGLem311ScaledV P W μ γ d Q) :
    DGLem311ScaledV P W μ γ d Q' := fun ζ₁ h0 h1 => by
  obtain ⟨a₀, a₁, A, ha₁, hh⟩ := h ζ₁ h0 h1
  exact ⟨a₀, a₁, A, ha₁, fun j n b hb => hh j n b (hb.trans hQ)⟩

lemma wire_dgL38Lower_mono {P : Measure Ω} {μ : Ω → Measure ℂ} {S S' : Set ℂ} (hS : S' ⊆ S)
    {β : ℝ} (h : DGL38Lower P μ S β) : DGL38Lower P μ S' β := by
  obtain ⟨p, C, ε₀, hp, hε₀, hb⟩ := h
  refine ⟨p, C, ε₀, hp, hε₀, fun ε hε hεε => (measure_mono fun ω hω => ?_).trans (hb ε hε hεε)⟩
  simp only [mem_ofPred_eq] at hω ⊢
  exact fun h => hω fun z hz => h z (hS hz)

lemma wire_box12_sub : p39Box p18c0 (1 / 3) (1 / 12) ⊆ p39Box p18c0 (1 / 3) (1 / 6) := by
  intro x hx
  simp only [p39Box, p18c0, Complex.mem_reProdIm, mem_Icc] at hx ⊢
  norm_num at hx ⊢
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2]

lemma wire_sq_sub_box12 : p39Sq p18c0 (1 / 3) ⊆ p39Box p18c0 (1 / 3) (1 / 12) := by
  intro x hx
  simp only [p39Sq, p39Box, Complex.mem_reProdIm, mem_Icc] at hx ⊢
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2]

/-- **`dg_prop322_V` with DG L3.19 on `[1/6,5/6]²`** (DG:1722–1772; `r = r' = 1/12`) -/
theorem wire_prop322_V {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ}
    (h311 : DGLem311Scaled P W μ γ (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (h311v : DGLem311ScaledV P W μ γ (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (h319 : DGLem319Scaled P W μ γ (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    {βb : ℝ} (hβb : 0 < βb) (hU38 : DGL38Upper P μ (p39Sq p18c0 (1 / 3)) βb) {β β' : ℝ}
    (hβ : 0 < β) (hββ' : β < β') (hβγ : β < 2 / (2 + γ) ^ 2)
    (hL38 : DGL38Lower P μ (p39Box p18c0 (1 / 3) (1 / 6)) β')
    {hV : ℝ → ℂ → Ω → ℝ} (h37 : DGLem37V P W hV (p39Box p18c0 (1 / 3) (1 / 6)))
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ z ∈ p39Sq p18c0 (1 / 3), ∀ w ∈ p39Sq p18c0 (1 / 3),
        dgLFPP (xiGamma γ) (fun x => hV δ x ω) (p39Box p18c0 (1 / 3) (1 / 6)) z w ≤
          δ ^ (dgLambda γ - ζ)} ≤ ENNReal.ofReal (C * δ ^ p) := by
  have hd := one_le_dGamma chiLeTwo hγ hγ2
  have hξ : 0 < xiGamma γ := xiGamma_pos hγ
  set B := p39Box p18c0 (1 / 3) (1 / 6)
  set B' := p39Box p18c0 (1 / 3) (1 / 12)
  obtain ⟨p₁, C₁, ε₁, hp₁, hε₁, e1⟩ := dg_prop322_hat hW hγ hγ2 hd p18c0 (L := 1 / 3)
    (r := 1 / 12) (r' := 1 / 12) (by norm_num) (by norm_num) (by norm_num)
    (by simp [p18c0]; norm_num) (by simp [p18c0]; norm_num) (by simp [p18c0]; norm_num)
    (by simp [p18c0]; norm_num) (Q' := B)
    (isCompact_Icc.reProdIm isCompact_Icc)
    (by
      intro x hx
      simp only [B, p39Box, Complex.mem_reProdIm, mem_Icc] at hx ⊢
      norm_num [p18c0] at hx ⊢
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2])
    (wire_dgLem311Scaled_mono wire_box12_sub h311) (wire_dgLem311ScaledV_mono wire_box12_sub h311v)
    h319 hβb hU38 hβ hββ' hβγ (wire_dgL38Lower_mono wire_box12_sub hL38)
    (ζ := β * (ζ / 2)) (by positivity)
  obtain ⟨p₂, K₂, δ₂, hp₂, hδ₂, e2⟩ := h37 (ζ / (2 * xiGamma γ)) (by positivity)
  refine ⟨min (p₁ / β) p₂, |C₁| + |K₂|, min (min (ε₁ ^ β) δ₂) 1,
    lt_min (div_pos hp₁ hβ) hp₂, lt_min (lt_min (Real.rpow_pos_of_pos hε₁ _) hδ₂) one_pos,
    fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδδ⟩ := hδ
  have hδ1 : δ < 1 := hδδ.trans_le (min_le_right _ _)
  have hδε : δ < ε₁ ^ β := hδδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ < δ₂ := hδδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  set ε := δ ^ (1 / β) with hεd
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hδ0 _
  have hεβ : ε ^ β = δ := by
    rw [hεd, ← Real.rpow_mul hδ0.le, one_div_mul_cancel hβ.ne', Real.rpow_one]
  have hεε : ε < ε₁ := by
    have := Real.rpow_lt_rpow hδ0.le hδε (by positivity : 0 < 1 / β)
    rwa [← Real.rpow_mul hε₁.le, mul_one_div_cancel hβ.ne', Real.rpow_one] at this
  set E1 := {ω | ¬ ∀ z ∈ p39Sq p18c0 (1 / 3), ∀ w ∈ p39Sq p18c0 (1 / 3),
        dgLFPP (γ / dGamma γ) (fun x => DDDF.phiVer W P (ε ^ β) 1 x ω) B' z w ≤
          ε ^ (β * (1 - 2 / dGamma γ - γ ^ 2 / (2 * dGamma γ)) - β * (ζ / 2))}
  set E2 := {ω | ¬ ∀ x ∈ B, |hV δ x ω - DDDF.phiVer W P δ 1 x ω| ≤
      ζ / (2 * xiGamma γ) * Real.log δ⁻¹}
  have hsub : {ω | ¬ ∀ z ∈ p39Sq p18c0 (1 / 3), ∀ w ∈ p39Sq p18c0 (1 / 3),
      dgLFPP (xiGamma γ) (fun x => hV δ x ω) B z w ≤ δ ^ (dgLambda γ - ζ)} ⊆ E1 ∪ E2 := by
    intro ω hω
    by_contra hn
    simp only [mem_union, not_or, E1, E2, mem_ofPred_eq, not_not] at hn
    obtain ⟨n1, n2⟩ := hn
    apply hω
    intro z hz w hw
    have hcont : ContinuousOn (fun x => DDDF.phiVer W P δ 1 x ω) B :=
      ((DDDF.isPhiVersion_phiVer hW hδ0 hδ1.le).cont ω).continuousOn
    have hcmp := p18_lfpp_compare hξ.le hcont
      (a := ζ / (2 * xiGamma γ) * Real.log δ⁻¹) (φ := fun x => hV δ x ω)
      (fun x hx => by have := (abs_le.1 (n2 x hx)).2; linarith) z w
    have h1 := (wire_dgLFPP_mono wire_box12_sub (t18_isDGPath_segment (p39Box_convex _ _ _)
      (wire_sq_sub_box12 hz) (wire_sq_sub_box12 hw))).trans (n1 z hz w hw)
    rw [hεβ] at h1
    have e3 : ε ^ (β * (1 - 2 / dGamma γ - γ ^ 2 / (2 * dGamma γ)) - β * (ζ / 2)) =
        δ ^ (dgLambda γ - ζ / 2) := by
      rw [← hεβ, ← Real.rpow_mul hε0.le]; unfold dgLambda; ring_nf
    have e4 : Real.exp (xiGamma γ * (ζ / (2 * xiGamma γ) * Real.log δ⁻¹)) = δ ^ (-(ζ / 2)) := by
      rw [Real.rpow_def_of_pos hδ0, Real.log_inv]; congr 1; field_simp
    rw [e3] at h1
    have hxi : xiGamma γ = γ / dGamma γ := rfl
    rw [← hxi] at h1
    calc dgLFPP (xiGamma γ) (fun x => hV δ x ω) B z w
        ≤ δ ^ (-(ζ / 2)) * dgLFPP (xiGamma γ) (fun x => DDDF.phiVer W P δ 1 x ω) B z w := by
          rw [← e4]; exact hcmp
      _ ≤ δ ^ (-(ζ / 2)) * δ ^ (dgLambda γ - ζ / 2) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hδ0.le _)
      _ = δ ^ (dgLambda γ - ζ) := by rw [← Real.rpow_add hδ0]; ring_nf
  have hpw : ∀ q : ℝ, min (p₁ / β) p₂ ≤ q → δ ^ q ≤ δ ^ (min (p₁ / β) p₂) :=
    fun q hq => Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hq
  have hεp : ε ^ p₁ = δ ^ (p₁ / β) := by
    rw [hεd, ← Real.rpow_mul hδ0.le]; ring_nf
  calc P _ ≤ P (E1 ∪ E2) := measure_mono hsub
    _ ≤ P E1 + P E2 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * ε ^ p₁) + ENNReal.ofReal (K₂ * δ ^ p₂) := by
        refine add_le_add (e1 ε hε0 hεε) ?_
        have := e2 δ ⟨hδ0, hδ2⟩
        exact this
    _ ≤ ENNReal.ofReal (|C₁| * δ ^ (min (p₁ / β) p₂)) +
          ENNReal.ofReal (|K₂| * δ ^ (min (p₁ / β) p₂)) := by
        rw [hεp]
        exact add_le_add
          (ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self _) (hpw _ (min_le_left _ _))
            (Real.rpow_nonneg hδ0.le _) (abs_nonneg _)))
          (ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self _) (hpw _ (min_le_right _ _))
            (Real.rpow_nonneg hδ0.le _) (abs_nonneg _)))
    _ = ENNReal.ofReal ((|C₁| + |K₂|) * δ ^ (min (p₁ / β) p₂)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- **`dg_prop322_sqOne` with DG L3.19 on `[1/6,5/6]²`** (same proof) -/
theorem wire_prop322_sqOne {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ}
    (h311 : DGLem311Scaled P W μ γ (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (h311v : DGLem311ScaledV P W μ γ (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (h319 : DGLem319Scaled P W μ γ (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    {βb : ℝ} (hβb : 0 < βb) (hU38 : DGL38Upper P μ (p39Sq p18c0 (1 / 3)) βb) {β β' : ℝ}
    (hβ : 0 < β) (hββ' : β < β') (hβγ : β < 2 / (2 + γ) ^ 2)
    (hL38 : DGL38Lower P μ (p39Box p18c0 (1 / 3) (1 / 6)) β')
    {hc : ℝ → ℂ → Ω → ℝ} (h37 : DGLem37V P W (p18Vfield hc) (p39Box p18c0 (1 / 3) (1 / 6)))
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ z ∈ Blueprint.closedUnitSquare, ∀ w ∈ Blueprint.closedUnitSquare,
        dgLFPP (xiGamma γ) (fun x => hc δ x ω) p18Half z w ≤ δ ^ (dgLambda γ - ζ)} ≤
        ENNReal.ofReal (C * δ ^ p) := by
  obtain ⟨p, C, δ₀, hp, hδ₀, hb⟩ := wire_prop322_V hW hγ hγ2 h311 h311v h319 hβb hU38 hβ hββ'
    hβγ hL38 h37 (ζ := ζ / 2) (by positivity)
  set e := dgLambda γ - ζ / 2
  set A := max ((3 : ℝ) ^ (1 - e)) 1
  have hA : 1 ≤ A := le_max_right _ _
  set δ₁ := min (3 * δ₀) (min 1 (A⁻¹ ^ (2 / ζ)))
  have hδ₁ : 0 < δ₁ := lt_min (by positivity) (lt_min one_pos (by positivity))
  refine ⟨p, |C|, δ₁, hp, hδ₁, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδδ⟩ := hδ
  have hδ3 : δ / 3 < δ₀ := by have := hδδ.trans_le (min_le_left _ _); linarith
  have hδA : δ ≤ A⁻¹ ^ (2 / ζ) := hδδ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hscale : 3 * (δ / 3) ^ e ≤ δ ^ (dgLambda γ - ζ) := by
    have e1 : 3 * (δ / 3) ^ e = (3 : ℝ) ^ (1 - e) * δ ^ e := by
      rw [Real.div_rpow hδ0.le (by norm_num), Real.rpow_sub (by norm_num : (0 : ℝ) < 3) 1 e,
        Real.rpow_one]
      field_simp
    rw [e1]
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδ0.le _)).trans
      (t18_absorb hA hζ hδ0 hδA)
  calc P _ ≤ P {ω | ¬ ∀ z ∈ p39Sq p18c0 (1 / 3), ∀ w ∈ p39Sq p18c0 (1 / 3),
        dgLFPP (xiGamma γ) (fun x => p18Vfield hc (δ / 3) x ω) (p39Box p18c0 (1 / 3) (1 / 6))
          z w ≤ (δ / 3) ^ e} := by
        refine measure_mono fun ω hω h => hω fun z hz w hw => ?_
        exact (p18_dgLFPP_scale _ hc δ ω hz hw).trans ((mul_le_mul_of_nonneg_left
          (h _ (p18_T_mem_sq hz) _ (p18_T_mem_sq hw)) (by norm_num)).trans hscale)
    _ ≤ ENNReal.ofReal (C * (δ / 3) ^ p) := hb (δ / 3) ⟨by positivity, hδ3⟩
    _ ≤ ENNReal.ofReal (|C| * δ ^ p) := ENNReal.ofReal_le_ofReal (mul_le_mul (le_abs_self _)
        (Real.rpow_le_rpow (by positivity) (by linarith) hp.le) (by positivity) (abs_nonneg _))

/-- **`dg_prop322_sqOne_muHat` with DG L3.19 on `[1/6,5/6]²`** (same proof) -/
theorem wire_prop322_sqOne_muHat {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h311 : DGLem311Scaled P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
      (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (h311v : DGLem311ScaledV P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
      (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (h319 : DGLem319Scaled P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
      (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    {hc : ℝ → ℂ → Ω → ℝ} (h37 : DGLem37V P W (p18Vfield hc) (p39Box p18c0 (1 / 3) (1 / 6)))
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ p C δ₀ : ℝ, 0 < p ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ z ∈ Blueprint.closedUnitSquare, ∀ w ∈ Blueprint.closedUnitSquare,
        dgLFPP (xiGamma γ) (fun x => hc δ x ω) p18Half z w ≤ δ ^ (dgLambda γ - ζ)} ≤
        ENNReal.ofReal (C * δ ^ p) := by
  set βs := 2 / (2 + γ) ^ 2
  have hβs : 0 < βs := by positivity
  have hb2 : 0 < 2 / (2 - γ) ^ 2 + 1 := by
    have : 0 < (2 - γ) ^ 2 := by nlinarith
    positivity
  exact wire_prop322_sqOne hW hγ hγ2 h311 h311v h319 hb2
    (p18_dgL38Upper_sq_muHat hW hγ hγ2 (by linarith)) (β := βs / 3) (β' := βs / 2)
    (by positivity) (by linarith) (by linarith)
    (p18_dgL38Lower_box_muHat hW hγ hγ2 p18_hK0 (by positivity) (by linarith)) h37 hζ

/-- **`R18P322`** (`r18P322_of`) with DG L3.19 on `[1/6,5/6]²` -/
theorem wire_r18P322_of
    (hcpl : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W W' : WNSpace → Ω → ℝ)
      (hz : Ω → DistC) (hc : ℝ → ℂ → Ω → ℝ), IsDGCoupling P W hz hc ∧ IsWhiteNoise P W' ∧
      DGLem37V P W' (p18Vfield hc) (p39Box p18c0 (1 / 3) (1 / 6)) ∧
      (∀ δ ∈ Ioo (0 : ℝ) (1 / 2), ∀ ω, ContinuousOn (fun x => hc δ x ω) p18Half) ∧
      ∀ δ ∈ Ioo (0 : ℝ) (1 / 2), ∀ x ∈ p18Half, hc δ x =ᵐ[P] fun ω => circleAvg (hz ω) δ x)
    (h311 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ)
      (hW : IsWhiteNoise P W) (γ : ℝ), 0 < γ → γ < 2 →
      DGLem311Scaled P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
        (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (h311v : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ)
      (hW : IsWhiteNoise P W) (γ : ℝ), 0 < γ → γ < 2 →
      DGLem311ScaledV P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
        (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6)))
    (h319 : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ)
      (hW : IsWhiteNoise P W) (γ : ℝ), 0 < γ → γ < 2 →
      DGLem319Scaled P W (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) γ
        (dGamma γ) (p39Box p18c0 (1 / 3) (1 / 6))) :
    R18P322 := by
  obtain ⟨Ω, _, P, W, W', hz, hc, hcp, hW', h37, hcont, hver⟩ := hcpl
  exact ⟨Ω, _, P, hz, hc, hcp.2.2.1.1, hcont, hver, fun γ hγ hγ2 ζ hζ =>
    wire_prop322_sqOne_muHat hW' hγ hγ2 (h311 P W' hW' γ hγ hγ2) (h311v P W' hW' γ hγ hγ2)
      (h319 P W' hW' γ hγ hγ2) h37 hζ⟩

end LQGMetric.DG
