/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P16D3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P16D2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.16 (corrected, D126) from DG Lemma 3.7 (packet P-126)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.16
(DG:1443–1512). DG couple `ĥ` and `h^{𝕊(1)}` by Lemma 3.7 (DG:1445–1449): with superpolynomially
high probability `|h^{𝕊(1)}_δ(z) − ĥ_δ(w)| ≤ (ζ/2ξ) log δ⁻¹` for `|z − w| ≤ 4δ` (here `6δ`,
DV-D126-2); the regularity of `ĥ_δ` itself at scale `6δ` is DG Lemma 3.4 (`dg_lemma34C`). On
both events the deterministic bounds `p16_lower_det` (S3P16D2) and `p16_upper_det` (S3P16B) hold;
the constants `72` and `2` are absorbed into `δ^{−ζ}` for small `δ` (DG:1456 "up to a
deterministic constant factor which can be ignored by slightly shrinking `ζ`").

* `p16_lower_of_coupling`: the corrected lower bound `δ^ζ (D̂ − δ^{1−ζ} e^{ξ ĥ_δ(v_{S_z})}) ≤ D`
  in a coupling satisfying the conclusion of L3.7 (the probability wrapper copies
  `p16_upper_of_lem37`, S3P16C, with `p16_const` generalized to `p16d_const`).
* `p16_upper_for`: `p16_upper_of_lem37` for a given coupling (copy of its proof).
* `dgProp3_16_of_lem37 : Blueprint.DGLem3_7 → Blueprint.DGProp3_16`.
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric.DG

open Blueprint

/-- `K e^{ξ η log δ⁻¹} ≤ δ^{−ζ}` once `ξ η ≤ ζ/2` and `log δ⁻¹ ≥ 2 log K / ζ` (generalizes
`p16_const`, `K = 2`) -/
lemma p16d_const {δ ξ η ζ K : ℝ} (hδ0 : 0 < δ) (hζ : 0 < ζ) (hK : 0 < K) (hξη : ξ * η ≤ ζ / 2)
    (hL : 2 * Real.log K / ζ ≤ Real.log δ⁻¹) (hL0 : 0 ≤ Real.log δ⁻¹) :
    K * Real.exp (ξ * (η * Real.log δ⁻¹)) ≤ δ ^ (-ζ) := by
  have e : δ ^ (-ζ) = Real.exp (ζ * Real.log δ⁻¹) := by
    rw [Real.rpow_def_of_pos hδ0, Real.log_inv]; ring_nf
  rw [e, show K = Real.exp (Real.log K) from (Real.exp_log hK).symm, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [div_le_iff₀ hζ] at hL
  nlinarith

/-- union bound with real constants of any sign -/
lemma p16d_union_bound {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {A B C : Set Ω}
    (h : A ⊆ B ∪ C) {x y : ℝ} (hB : P B ≤ ENNReal.ofReal x) (hC : P C ≤ ENNReal.ofReal y) :
    P A ≤ ENNReal.ofReal (max x 0 + max y 0) := by
  rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
  exact (measure_mono h).trans ((measure_union_le B C).trans (add_le_add
    (hB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    (hC.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))))

/-- **DG Proposition 3.16, corrected lower bound** (D126; DG:1458–1512) in a coupling with the
conclusion of DG Lemma 3.7, with superpolynomially high probability -/
theorem p16_lower_of_coupling {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WhiteNoise.WNSpace → Ω → ℝ} {hz : Ω → DistC} {hc : ℝ → ℂ → Ω → ℝ}
    (hcp : IsDGCoupling P W hz hc)
    (H : ∀ C : ℝ, 0 < C → ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ p : ℝ, 0 < p → ∃ K δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        P {ω | ¬ ∀ z ∈ sqHalf, ∀ w ∈ sqHalf, ‖z - w‖ ≤ C * δ →
          |hc δ z ω - DDDF.phiVer W P δ 1 w ω| ≤ ζ * Real.log δ⁻¹} ≤ ENNReal.ofReal (K * δ ^ p))
    {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1) {ξ : ℝ} (hξ : 0 < ξ) {p : ℝ} (hp : 0 < p) :
    ∃ K δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        δ ^ ζ * (dgApproxLFPP ξ δ (fun x => DDDF.phiVer W P δ 1 x ω) z w -
            δ ^ (1 - ζ) * Real.exp (ξ * dgMaxSq δ (fun x => DDDF.phiVer W P δ 1 x ω) z)) ≤
          dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w} ≤ ENNReal.ofReal (K * δ ^ p) := by
  set η : ℝ := min (ζ / (2 * ξ)) (1 / 2) with hη_def
  have hη : 0 < η := lt_min (div_pos hζ.1 (by positivity)) (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hξη : ξ * η ≤ ζ / 2 := by
    have : η ≤ ζ / (2 * ξ) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; nlinarith
  obtain ⟨K, δ₁, hδ₁, hb⟩ := H 6 (by norm_num) η ⟨hη, hη1⟩ p hp
  have hbdd : Bornology.IsBounded closedUnitSquare := p16_isCompact_sq.isBounded
  obtain ⟨δ₃, hδ₃, hb3⟩ := dg_lemma34C hcp.2.1 hbdd hη (C := 6) (by norm_num) hp
  set δ₂ : ℝ := Real.exp (-(2 * Real.log 72 / ζ)) with hδ₂_def
  refine ⟨max K 0 + 1, min (min δ₁ δ₃) (min (1 / 2) δ₂),
    lt_min (lt_min hδ₁ hδ₃) (lt_min (by norm_num) (Real.exp_pos _)), fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδm⟩ := hδ
  have hδδ₁ : δ < δ₁ := hδm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδδ₃ : δ < δ₃ := hδm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδh : δ < 1 / 2 := hδm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₂ : δ < δ₂ := hδm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hL0 : 0 ≤ Real.log δ⁻¹ := (Real.log_pos ((one_lt_inv₀ hδ0).2 (by linarith))).le
  have hL : 2 * Real.log 72 / ζ ≤ Real.log δ⁻¹ := by
    have := Real.log_lt_log hδ0 hδ₂
    rw [hδ₂_def, Real.log_exp] at this
    rw [Real.log_inv]; linarith
  have hsub : closedUnitSquare ⊆ sqHalf := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2.1], by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
  have hpos : 0 ≤ δ ^ p := Real.rpow_nonneg hδ0.le _
  refine (p16d_union_bound (fun ω hω => ?_) (hb δ ⟨hδ0, hδδ₁⟩) (hb3 δ ⟨hδ0, hδδ₃⟩)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · by_contra hn
    simp only [mem_union, mem_setOf_eq, not_or, not_not, not_exists, not_and, not_lt] at hn
    obtain ⟨hn1, hn2⟩ := hn
    simp only [mem_setOf_eq] at hω
    apply hω
    intro z hzS w hwS
    have hcont : ContinuousOn (fun x => hc δ x ω) closedUnitSquare :=
      (hcp.2.2.2.1 δ ⟨hδ0, hδh⟩ ω).mono hsub
    have Hd : ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare, ‖x - y‖ ≤ 6 * δ →
        DDDF.phiVer W P δ 1 y ω ≤ hc δ x ω + η * Real.log δ⁻¹ := fun x hx y hy hxy => by
      have := hn1 x (hsub hx) y (hsub hy) hxy
      linarith [neg_abs_le (hc δ x ω - DDDF.phiVer W P δ 1 y ω)]
    have Hd' : ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare, ‖x - y‖ ≤ 6 * δ →
        DDDF.phiVer W P δ 1 y ω ≤ DDDF.phiVer W P δ 1 x ω + η * Real.log δ⁻¹ :=
      fun x hx y hy hxy => by
        have := hn2 x hx y hy hxy
        linarith [neg_abs_le (DDDF.phiVer W P δ 1 x ω - DDDF.phiVer W P δ 1 y ω)]
    have hdet := p16_lower_det hδ0 (by linarith) hξ hη.le hcont Hd Hd' hzS hwS
    have hc72 := p16d_const hδ0 hζ.1 (by norm_num : (0 : ℝ) < 72) hξη hL hL0
    have hD : 0 ≤ dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w :=
      Real.iInf_nonneg fun q => lfppLength_nonneg _ _ _
    set D := dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w
    set Dh := dgApproxLFPP ξ δ (fun x => DDDF.phiVer W P δ 1 x ω) z w
    set e := Real.exp (ξ * dgMaxSq δ (fun x => DDDF.phiVer W P δ 1 x ω) z)
    have he : 0 < e := Real.exp_pos _
    have h1 : Dh ≤ δ ^ (-ζ) * (D + δ * e) :=
      hdet.trans (mul_le_mul_of_nonneg_right hc72 (by positivity))
    have hz1 : δ ^ ζ * δ ^ (-ζ) = 1 := by
      rw [← Real.rpow_add hδ0, add_neg_cancel, Real.rpow_zero]
    have hz2 : δ ^ ζ * δ ^ (1 - ζ) = δ := by
      rw [← Real.rpow_add hδ0, add_sub_cancel, Real.rpow_one]
    have hζpos : 0 ≤ δ ^ ζ := Real.rpow_nonneg hδ0.le _
    have h2 : δ ^ ζ * Dh ≤ D + δ * e := by
      calc δ ^ ζ * Dh ≤ δ ^ ζ * (δ ^ (-ζ) * (D + δ * e)) := mul_le_mul_of_nonneg_left h1 hζpos
        _ = D + δ * e := by rw [← mul_assoc, hz1, one_mul]
    calc δ ^ ζ * (Dh - δ ^ (1 - ζ) * e) = δ ^ ζ * Dh - (δ ^ ζ * δ ^ (1 - ζ)) * e := by ring
      _ = δ ^ ζ * Dh - δ * e := by rw [hz2]
      _ ≤ D := by linarith
  · have h1 : max (K * δ ^ p) 0 ≤ max K 0 * δ ^ p :=
      max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
        (mul_nonneg (le_max_right _ _) hpos)
    rw [max_eq_left hpos]
    linarith

/-- **DG Proposition 3.16, upper bound** for a given coupling with the conclusion of DG
Lemma 3.7 (copy of the proof of `p16_upper_of_lem37`, S3P16C) -/
theorem p16_upper_for {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WhiteNoise.WNSpace → Ω → ℝ} {hz : Ω → DistC} {hc : ℝ → ℂ → Ω → ℝ}
    (hcp : IsDGCoupling P W hz hc)
    (H : ∀ C : ℝ, 0 < C → ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ p : ℝ, 0 < p → ∃ K δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        P {ω | ¬ ∀ z ∈ sqHalf, ∀ w ∈ sqHalf, ‖z - w‖ ≤ C * δ →
          |hc δ z ω - DDDF.phiVer W P δ 1 w ω| ≤ ζ * Real.log δ⁻¹} ≤ ENNReal.ofReal (K * δ ^ p))
    {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1) {ξ : ℝ} (hξ : 0 < ξ) {p : ℝ} (hp : 0 < p) :
    ∃ K δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ ∀ z ∈ closedUnitSquare, ∀ w ∈ closedUnitSquare,
        dgLFPP ξ (fun x => hc δ x ω) closedUnitSquare z w ≤
          δ ^ (-ζ) * dgApproxLFPP ξ δ (fun x => DDDF.phiVer W P δ 1 x ω) z w} ≤
        ENNReal.ofReal (K * δ ^ p) := by
  set η : ℝ := min (ζ / (2 * ξ)) (1 / 2) with hη_def
  have hη : 0 < η := lt_min (div_pos hζ.1 (by positivity)) (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hξη : ξ * η ≤ ζ / 2 := by
    have : η ≤ ζ / (2 * ξ) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; nlinarith
  obtain ⟨K, δ₁, hδ₁, hb⟩ := H 1 one_pos η ⟨hη, hη1⟩ p hp
  set δ₂ : ℝ := Real.exp (-(2 * Real.log 2 / ζ)) with hδ₂_def
  refine ⟨K, min δ₁ (min (1 / 2) δ₂), lt_min hδ₁ (lt_min (by norm_num) (Real.exp_pos _)),
    fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδm⟩ := hδ
  have hδδ₁ : δ < δ₁ := hδm.trans_le (min_le_left _ _)
  have hδh : δ < 1 / 2 := hδm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₂ : δ < δ₂ := hδm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hL0 : 0 ≤ Real.log δ⁻¹ := (Real.log_pos ((one_lt_inv₀ hδ0).2 (by linarith))).le
  have hL : 2 * Real.log 2 / ζ ≤ Real.log δ⁻¹ := by
    have := Real.log_lt_log hδ0 hδ₂
    rw [hδ₂_def, Real.log_exp] at this
    rw [Real.log_inv]; linarith
  refine (measure_mono fun ω hω => ?_).trans (hb δ ⟨hδ0, hδδ₁⟩)
  simp only [mem_setOf_eq] at hω ⊢
  intro hgood
  apply hω
  intro z hzS w hwS
  have hsub : closedUnitSquare ⊆ sqHalf := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2.1], by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
  have hcont : ContinuousOn (fun x => hc δ x ω) closedUnitSquare :=
    (hcp.2.2.2.1 δ ⟨hδ0, hδh⟩ ω).mono hsub
  have Hd : ∀ x ∈ closedUnitSquare, ∀ y ∈ closedUnitSquare, ‖x - y‖ ≤ δ →
      hc δ x ω ≤ DDDF.phiVer W P δ 1 y ω + η * Real.log δ⁻¹ := fun x hx y hy hxy => by
    have := hgood x (hsub hx) y (hsub hy) (by rwa [one_mul])
    linarith [le_abs_self (hc δ x ω - DDDF.phiVer W P δ 1 y ω)]
  refine (p16_upper_det hδ0 (by linarith) hξ.le hcont Hd hzS hwS).trans ?_
  exact mul_le_mul_of_nonneg_right (p16_const hδ0 hζ.1 hξη hL hL0)
    (p16_dgApprox_nonneg _ _ hδ0.le _ _ _)

/-- **DG Proposition 3.16, corrected (D126)**, from DG Lemma 3.7: both halves hold in L3.7's
coupling, with superpolynomially (in particular polynomially, `p = 1`) high probability -/
theorem dgProp3_16_of_lem37 (h37 : Blueprint.DGLem3_7) : Blueprint.DGProp3_16 := by
  obtain ⟨Ω, _, P, W, hz, hc, hcp, H⟩ := h37
  refine ⟨Ω, _, P, W, hz, hc, hcp, fun ζ hζ ξ hξ => ?_⟩
  obtain ⟨K₁, d₁, hd₁, h₁⟩ := p16_lower_of_coupling hcp H hζ hξ one_pos
  obtain ⟨K₂, d₂, hd₂, h₂⟩ := p16_upper_for hcp H hζ hξ one_pos
  refine ⟨1, max K₁ 0 + max K₂ 0, min d₁ d₂, one_pos, lt_min hd₁ hd₂, fun δ hδ => ?_⟩
  have hδ1 : δ ∈ Ioo (0 : ℝ) d₁ := ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩
  have hδ2 : δ ∈ Ioo (0 : ℝ) d₂ := ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩
  have hpos : 0 ≤ δ ^ (1 : ℝ) := Real.rpow_nonneg hδ.1.le _
  refine (p16d_union_bound (fun ω hω => ?_) (h₁ δ hδ1) (h₂ δ hδ2)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · by_contra hn
    simp only [mem_union, mem_setOf_eq, not_or, not_not] at hn
    simp only [mem_setOf_eq] at hω
    exact hω fun z hzS w hwS => ⟨hn.1 z hzS w hwS, hn.2 z hzS w hwS⟩
  · have a1 : max (K₁ * δ ^ (1 : ℝ)) 0 ≤ max K₁ 0 * δ ^ (1 : ℝ) :=
      max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
        (mul_nonneg (le_max_right _ _) hpos)
    have a2 : max (K₂ * δ ^ (1 : ℝ)) 0 ≤ max K₂ 0 * δ ^ (1 : ℝ) :=
      max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
        (mul_nonneg (le_max_right _ _) hpos)
    nlinarith

end LQGMetric.DG
