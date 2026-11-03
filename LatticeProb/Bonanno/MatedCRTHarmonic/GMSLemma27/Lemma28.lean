/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSLemma27.Lemma28 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Gaussian
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Grid
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Bookkeeping

/-!
# [18] Lemma 2.8: LQG mass of small balls

[18] Lemma 2.8: for `δ ∈ (0, 1)`, `p > 2γ` and `ρ ∈ (0, 1)`,
`P[inf_{z ∈ B_ρ(0)} μ_h(B_δ(z)) ≥ δ^{2+γ²/2+p}] ≥ 1 − δ^{p²/(2γ²) − 2 + o_δ(1)}`, with the proof `[18]` as
corrected by absorbing the grid's constant factor through a smaller `p` and using the ζ-form of
[GHM15, Lemma 3.12] by substituting `δ ↦ δ^ζ`).

* `measure_ball_lt_le` — (2.11) before sending `ζ → 0`: for a whole-plane GFF, `P[μ(B_r(z)) < r^{2+γ²/2+p}] ≤
  r^{ζN} + r^{(p−ζ)²/(2γ²)}` (from `GMCLowerTail` and the Gaussian tail `measure_exp_circleAvg_lt_le`).
* `lemma28_wholePlane_strict` — the union bound over `ballGrid`, for a whole-plane GFF, in the strict form
  `P[∃ z ∈ B_ρ, μ(B_δ(z)) ≤ δ^{2+γ²/2+p}] ≤ C δ^e` for every `e < p²/(2γ²) − 2` (the meaning of the `o_δ(1)`).
* `lemma28_strict`, `lemma28` — the same for the cell model's area measure (cone case), through
  `AreaDominatesWholePlaneGFF`; `lemma28` is (2.10) as printed.

Inputs: `GMCLowerTail γ` and `AreaDominatesWholePlaneGFF M` (SLE-free, to prove; `GMCInterfaces.lean`). No SLE input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMSLemma27

section WholePlane

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {H : ℝ → ℂ → Ω → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}

/-- **(2.11) at fixed `ζ`**. For a whole-plane GFF with circle averages `H` and LQG measure `μ`, and
`0 < ζ ≤ p`, `N ∈ ℝ`: for all small `r` and every `z` with `|z| + r ≤ 1`,
`P[μ(B_r(z)) < r^{2+γ²/2+p}] ≤ r^{ζN} + r^{(p−ζ)²/(2γ²)}`. -/
theorem measure_ball_lt_le (hGMC : GMCLowerTail γ) (hγ : 0 < γ)
    (hH : LQGDimension.IsGFFCircleAverage H P) (hμ : IsLQGAreaOf γ H μ P) {p ζ N : ℝ}
    (hζ : 0 < ζ) (hζp : ζ ≤ p) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ z : ℂ, ‖z‖ + r ≤ 1 →
      P {ω | μ ω (ball z r) < ENNReal.ofReal (r ^ (2 + γ ^ 2 / 2 + p))} ≤
        ENNReal.ofReal (r ^ (ζ * N)) + ENNReal.ofReal (r ^ ((p - ζ) ^ 2 / (2 * γ ^ 2))) := by
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hGMC Ω P H μ hH hμ N 1 one_pos
  refine ⟨min 1 (δ₀ ^ ζ⁻¹), lt_min one_pos (Real.rpow_pos_of_pos hδ₀ _), fun r hr z hz => ?_⟩
  have hr1 : r < 1 := hr.2.trans_le (min_le_left _ _)
  have hrζ : r ^ ζ < δ₀ := by
    have h := Real.rpow_lt_rpow hr.1.le (hr.2.trans_le (min_le_right _ _)) hζ
    rwa [Real.rpow_inv_rpow hδ₀.le hζ.ne'] at h
  have hsub : {ω | μ ω (ball z r) < ENNReal.ofReal (r ^ (2 + γ ^ 2 / 2 + p))} ⊆
      {ω | μ ω (ball z r) <
          ENNReal.ofReal (r ^ ζ * r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H r z ω))} ∪
        {ω | Real.exp (γ * H r z ω) < r ^ (p - ζ)} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hcon hω
    obtain ⟨h1, h2⟩ := hcon
    have h3 : r ^ (2 + γ ^ 2 / 2 + p) ≤ r ^ ζ * r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * H r z ω) := by
      calc r ^ (2 + γ ^ 2 / 2 + p) = r ^ ζ * r ^ (2 + γ ^ 2 / 2) * r ^ (p - ζ) := by
            rw [← Real.rpow_add hr.1, ← Real.rpow_add hr.1]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2
            (mul_nonneg (Real.rpow_nonneg hr.1.le _) (Real.rpow_nonneg hr.1.le _))
    exact absurd (h1.trans_lt hω) (not_lt.mpr (ENNReal.ofReal_le_ofReal h3))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
  · refine measure_le_ofReal_of_toReal_le ((hδ₀' (r ^ ζ) ⟨Real.rpow_pos_of_pos hr.1 _, hrζ⟩ z r
      ⟨hr.1, hr1⟩).trans (le_of_eq ?_))
    rw [one_mul, ← Real.rpow_mul hr.1.le]
  · exact measure_exp_circleAvg_lt_le hH hγ hr.1 hz (sub_nonneg.mpr hζp)

/-- Choice of the exponent `θ ∈ [0, p)` with `e ≤ θ²/(2γ²) − 2`, possible when `e < p²/(2γ²) − 2`. -/
theorem exists_exponent_lt {γ p e : ℝ} (hp : 0 < p) (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < p ∧ e ≤ θ ^ 2 / (2 * γ ^ 2) - 2 := by
  have hc : Continuous fun θ : ℝ => θ ^ 2 / (2 * γ ^ 2) - 2 := by fun_prop
  have h1 : ∀ᶠ θ in 𝓝[<] p, e < θ ^ 2 / (2 * γ ^ 2) - 2 :=
    (hc.continuousAt.tendsto.eventually (lt_mem_nhds he)).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ θ in 𝓝[<] p, 0 < θ := (lt_mem_nhds hp).filter_mono nhdsWithin_le_nhds
  obtain ⟨θ, ⟨hθ1, hθ2⟩, hθ3⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  exact ⟨θ, hθ2.le, hθ3, hθ1.le⟩

/-- **[18] Lemma 2.8 for a whole-plane GFF, strict form** ([18], with the grid correction). For `γ > 0`, `p > 0`,
`ρ ∈ (0, 1)` and every `e < p²/(2γ²) − 2` there is `C` with, for all `δ ∈ (0, 1)`,
`P[∃ z ∈ B_ρ(0), μ(B_δ(z)) ≤ δ^{2+γ²/2+p}] ≤ C δ^e`. -/
theorem lemma28_wholePlane_strict (hGMC : GMCLowerTail γ) (hγ : 0 < γ)
    (hH : LQGDimension.IsGFFCircleAverage H P) (hμ : IsLQGAreaOf γ H μ P) {p ρ e : ℝ} (hp : 0 < p)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ, μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (2 + γ ^ 2 / 2 + p))} ≤
        ENNReal.ofReal (C * δ ^ e) := by
  obtain ⟨θ, hθ0, hθp, heθ⟩ := exists_exponent_lt hp he
  set E : ℝ := θ ^ 2 / (2 * γ ^ 2) with hE
  have hE0 : 0 ≤ E := by positivity
  set ζ : ℝ := (p - θ) / 2 with hζ
  have hζ0 : 0 < ζ := by rw [hζ]; linarith
  set p₁ : ℝ := θ + ζ with hp₁
  have hp₁p : p₁ < p := by rw [hp₁, hζ]; linarith
  set N : ℝ := E / ζ with hN
  have hζN : ζ * N = E := by rw [hN]; field_simp
  have hp₁ζ : p₁ - ζ = θ := by rw [hp₁]; ring
  set x₀ : ℝ := 2 + γ ^ 2 / 2 with hx₀
  have hx₀0 : 0 < x₀ := by positivity
  obtain ⟨r₀, hr₀, hbd⟩ := measure_ball_lt_le (p := p₁) (N := N) hGMC hγ hH hμ hζ0
    (by rw [hp₁]; linarith)
  -- smallness conditions on `δ`
  have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 := eventually_lt_nhdsGT_zero one_pos
  have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < r₀ := eventually_lt_nhdsGT_zero hr₀
  have hev3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 - ρ := eventually_lt_nhdsGT_zero (by linarith)
  have hev4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ (p - p₁) < (2 : ℝ) ^ (-(x₀ + p₁)) :=
    eventually_rpow_lt (by linarith) (Real.rpow_pos_of_pos two_pos _)
  refine exists_bound_of_eventually (C₀ := 338) (fun δ => prob_le_one) ?_
  filter_upwards [hev1, hev2, hev3, hev4, self_mem_nhdsWithin] with δ h1 h2 h3 h4 hδ0
  have hδ0' : 0 < δ := hδ0
  -- the grid absorbs the factor `2^{x₀ + p₁}`
  have habs : δ ^ (x₀ + p) < (δ / 2) ^ (x₀ + p₁) := by
    have e1 : δ ^ (x₀ + p) = δ ^ (x₀ + p₁) * δ ^ (p - p₁) := by
      rw [← Real.rpow_add hδ0']; congr 1; ring
    have e2 : (δ / 2) ^ (x₀ + p₁) = δ ^ (x₀ + p₁) * (2 : ℝ) ^ (-(x₀ + p₁)) := by
      rw [Real.div_rpow hδ0'.le zero_le_two, Real.rpow_neg zero_le_two, div_eq_mul_inv]
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left h4 (Real.rpow_pos_of_pos hδ0' _)
  set S : ℤ × ℤ → Set Ω := fun i =>
    {ω | μ ω (ball (ballGridPt (δ / 4) i) (δ / 2)) < ENNReal.ofReal ((δ / 2) ^ (x₀ + p₁))} with hS
  have hcover : {ω | ∃ z ∈ ball (0 : ℂ) ρ, μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (x₀ + p))} ⊆
      ⋃ i ∈ ballGrid δ ρ, S i := by
    rintro ω ⟨z, hz, hle⟩
    obtain ⟨i, hi, hzi⟩ := exists_mem_ballGrid hδ0' hz
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    have hsub : ball (ballGridPt (δ / 4) i) (δ / 2) ⊆ ball z δ := by
      intro y hy
      rw [mem_ball, dist_eq_norm] at hy ⊢
      calc ‖y - z‖ ≤ ‖y - ballGridPt (δ / 4) i‖ + ‖z - ballGridPt (δ / 4) i‖ := by
            calc ‖y - z‖ = ‖(y - ballGridPt (δ / 4) i) - (z - ballGridPt (δ / 4) i)‖ := by ring_nf
              _ ≤ _ := norm_sub_le _ _
        _ < δ := by linarith
    exact (measure_mono hsub).trans_lt
      (hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr habs))
  have hS_le : ∀ i ∈ ballGrid δ ρ, P (S i) ≤ ENNReal.ofReal (2 * δ ^ E) := by
    intro i hi
    have hiw : ‖ballGridPt (δ / 4) i‖ < ρ + δ / 4 := (Finset.mem_filter.mp hi).2
    have hb := hbd (δ / 2) ⟨by positivity, by linarith⟩ (ballGridPt (δ / 4) i) (by linarith)
    rw [hζN, hp₁ζ] at hb
    refine hb.trans ?_
    have hle : (δ / 2) ^ E ≤ δ ^ E := Real.rpow_le_rpow (by positivity) (by linarith) hE0
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hcard := card_ballGrid_le hδ0' h1.le hρ0.le hρ1.le
  calc P {ω | ∃ z ∈ ball (0 : ℂ) ρ, μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (x₀ + p))}
      ≤ P (⋃ i ∈ ballGrid δ ρ, S i) := measure_mono hcover
    _ ≤ ∑ i ∈ ballGrid δ ρ, P (S i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ ballGrid δ ρ, ENNReal.ofReal (2 * δ ^ E) := Finset.sum_le_sum hS_le
    _ = ENNReal.ofReal ((ballGrid δ ρ).card * (2 * δ ^ E)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (338 * δ ^ e) := by
        apply ENNReal.ofReal_le_ofReal
        have hδE : δ ^ E / δ ^ 2 ≤ δ ^ e := by
          rw [← Real.rpow_natCast, ← Real.rpow_sub hδ0']
          exact Real.rpow_le_rpow_of_exponent_ge hδ0' h1.le (by push_cast; linarith)
        have hpos : 0 ≤ 2 * δ ^ E := by positivity
        calc ((ballGrid δ ρ).card : ℝ) * (2 * δ ^ E) ≤ 169 / δ ^ 2 * (2 * δ ^ E) :=
              mul_le_mul_of_nonneg_right hcard hpos
          _ = 338 * (δ ^ E / δ ^ 2) := by ring
          _ ≤ 338 * δ ^ e := by linarith

end WholePlane

section Model

variable {γ : ℝ}

/-- **[18] Lemma 2.8 for the cell model, strict form.** For the area measure of the cell model (cone case, via the
SLE-free comparison `AreaDominatesWholePlaneGFF`, `[18]`): for `γ > 0`, `p > 0`, `ρ ∈ (0, 1)` and every
`e < p²/(2γ²) − 2` there is `C` with `P[∃ z ∈ B_ρ(0), μ_h(B_δ(z)) ≤ δ^{2+γ²/2+p}] ≤ C δ^e` for all `δ ∈ (0, 1)`. -/
theorem lemma28_strict (M : CellModel γ) (hGMC : GMCLowerTail γ) (hdom : AreaDominatesWholePlaneGFF M)
    (hγ : 0 < γ) {p ρ e : ℝ} (hp : 0 < p) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
      M.P {ω | ∃ z ∈ ball (0 : ℂ) ρ, M.area ω (ball z δ) ≤ ENNReal.ofReal (δ ^ (2 + γ ^ 2 / 2 + p))} ≤
        ENNReal.ofReal (C * δ ^ e) := by
  obtain ⟨H, μ, hH, hμ, hle⟩ := hdom
  obtain ⟨C₁, hC₁⟩ := lemma28_wholePlane_strict hGMC hγ hH hμ hp hρ0 hρ1 he
  refine exists_bound_of_eventually (C₀ := C₁) (fun δ => prob_le_one) ?_
  have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 - ρ := eventually_lt_nhdsGT_zero (by linarith)
  filter_upwards [hev1, self_mem_nhdsWithin] with δ h1 hδ0
  have hδ0' : 0 < δ := hδ0
  refine le_trans (measure_mono_ae ?_) (hC₁ δ ⟨hδ0', by linarith⟩)
  filter_upwards [hle] with ω hω
  rintro ⟨z, hz, hzle⟩
  refine ⟨z, hz, le_trans (hω _ measurableSet_ball ?_) hzle⟩
  intro y hy
  rw [mem_ball_zero_iff] at hz ⊢
  rw [mem_ball, dist_eq_norm] at hy
  calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
    _ < 1 := by linarith

/-- **[18] Lemma 2.8** ((2.10), `[18]`), for the cell model's `γ`-LQG area measure: for `δ ∈ (0, 1)`,
`p > 2γ`, `ρ ∈ (0, 1)`, `P[inf_{z ∈ B_ρ(0)} μ_h(B_δ(z)) ≥ δ^{2+γ²/2+p}] ≥ 1 − δ^{p²/(2γ²)−2+o_δ(1)}`, the `o_δ(1)` read
as: for every `e < p²/(2γ²) − 2` there is `C` (depending on `p, ρ, γ, e`) with the bound `1 − C δ^e` for all
`δ ∈ (0, 1)`. Inputs: `GMCLowerTail γ`, `AreaDominatesWholePlaneGFF M` (SLE-free, to prove). -/
theorem lemma28 (M : CellModel γ) (hGMC : GMCLowerTail γ) (hdom : AreaDominatesWholePlaneGFF M)
    (hγ : 0 < γ) {p ρ : ℝ} (hp : 2 * γ < p) (hρ : ρ ∈ Ioo (0 : ℝ) 1) {e : ℝ}
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
      1 - ENNReal.ofReal (C * δ ^ e) ≤
        M.P {ω | ∀ z ∈ ball (0 : ℂ) ρ, ENNReal.ofReal (δ ^ (2 + γ ^ 2 / 2 + p)) ≤ M.area ω (ball z δ)} := by
  obtain ⟨C, hC⟩ := lemma28_strict M hGMC hdom hγ (by linarith) hρ.1 hρ.2 he
  refine ⟨C, fun δ hδ => one_sub_le_measure_of_compl_le ((measure_mono ?_).trans (hC δ hδ))⟩
  intro ω hω
  simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨z, hz, hlt⟩ := hω
  exact ⟨z, hz, hlt.le⟩

end Model

end MatedCRTHarmonic.GMSLemma27
