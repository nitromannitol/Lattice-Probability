/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1GaussMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1GaussMom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.1, Step 4: the circle-average sum estimate (4.5) for Gaussian vectors

Source: Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380, `lqg-metric-estimates-final.tex`,
proof of Proposition 4.1, Step 4 (T:2507–2582): after Paley–Zygmund (`probB_ge`), DFGPS Lemma 4.2
(= DZZ Lemma 2.1, `GaussConc.dzz_lemma21_strong`) is applied with
`B = {x : ∑ e^{ξ x_k} ≥ a ε^{-1-ξ²/2}}`, `σ² = max Var X_k ≤ log ε⁻¹ + O(1)` and
`λ = (p/ξ) log ε⁻¹` (T:2565–2580; here `λ = (p log ε⁻¹ + min(log a, 0))/ξ`, which absorbs the
constant `a` exactly as the "≥ a ε^{p-1-ξ²/2}" of T:2578 does into the `o_ε(1)`).

`sumExp_lower`: for a centered Gaussian vector `(X_k)_{k<n}` with `n ≥ κ/ε`,
`Var X_k ≥ log ε⁻¹ - A₀` and `Cov(X_j,X_k) ≤ log ε⁻¹ - log(|j-k|+1) + A₀`,
`P[∑_k e^{ξ X_k} < ε^{p-1-ξ²/2}] ≤ ε^{p²/(2ξ²) - ζ}` for `ε < ε₀(ξ,κ,A₀,p,ζ)`
(this is (4.5), T:2496–2499, for `X_k = h_{ε𝕣}(z_k) - h_𝕣(0)`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped NNReal

namespace LQGMetric.DFGPS.P41

lemma amgm_le {a C u : ℝ} (ha : 0 < a) : C * u ≤ a * u ^ 2 + C ^ 2 / (4 * a) := by
  rw [← sub_nonneg]
  have : a * u ^ 2 + C ^ 2 / (4 * a) - C * u = (2 * a * u - C) ^ 2 / (4 * a) := by
    field_simp; ring
  rw [this]; positivity

/-- **DFGPS (4.5)** for Gaussian vectors (T:2496–2582). -/
theorem sumExp_lower {ξ κ A0 p ζ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hκ : 0 < κ) (hA0 : 0 ≤ A0)
    (hp : 0 < p) (hζ : 0 < ζ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
        (X : Ω → Fin n → ℝ), Measurable X → HasGaussianLaw X P → (∀ i, ∫ ω, X ω i ∂P = 0) →
        κ / ε ≤ n → (∀ i, log ε⁻¹ - A0 ≤ Var[fun ω => X ω i; P]) →
        (∀ i j : Fin n, cov[fun ω => X ω i, fun ω => X ω j; P] ≤
          log ε⁻¹ - log ((dN i j : ℝ) + 1) + A0) →
        P.real {ω | sumExp X ξ ω < ε ^ (p - 1 - ξ ^ 2 / 2)} ≤
          ε ^ (p ^ 2 / (2 * ξ ^ 2) - ζ) := by
  set q := p / ξ with hqdef
  have hq0 : 0 < q := div_pos hp hξ0
  have hqe : p ^ 2 / (2 * ξ ^ 2) = q ^ 2 / 2 := by rw [hqdef, div_pow]; field_simp
  rw [hqe]
  by_cases htr : q ^ 2 / 2 - ζ ≤ 0
  · refine ⟨1, one_pos, fun ε hε Ω _ P _ n X _ _ _ _ _ _ => ?_⟩
    refine (measureReal_mono (μ := P) (subset_univ _)).trans ?_
    rw [probReal_univ]
    exact one_le_rpow_of_pos_of_le_one_of_nonpos hε.1 hε.2.le htr
  push Not at htr
  set s := ξ ^ 2 with hs
  have hs0 : 0 ≤ s := sq_nonneg ξ
  have hs1 : s < 1 := by nlinarith
  set a1 := κ * exp (-s * A0 / 2) / 2 with ha1
  have ha1p : 0 < a1 := by positivity
  set a2 := κ ^ s * exp (-3 * s * A0) * (1 - s) / 8 with ha2
  have ha2p : 0 < a2 := by
    have : 0 < 1 - s := by linarith
    have : 0 < κ ^ s := rpow_pos_of_pos hκ s
    positivity
  obtain ⟨C, hC1, hC⟩ := GaussConc.dzz_lemma21_strong a2 ha2p
  have hC0 : 0 < C := by linarith
  set b := -min (log a1) 0 / ξ with hb
  have hb0 : 0 ≤ b := div_nonneg (neg_nonneg.2 (min_le_right _ _)) hξ0.le
  set L2 := 2 * (q * A0 + 2 * b + 2 * q * C ^ 2 / ζ + 1) / q
  set L3 := (q ^ 2 * A0 + 2 * q * b + 2 * C ^ 2 * q ^ 2 / ζ) / ζ + 1
  set ℓ₀ := max (A0 + 1) (max L2 L3)
  refine ⟨exp (-ℓ₀), exp_pos _, fun ε hε Ω _ P _ n X hXm hX h0 hn hvar hcov => ?_⟩
  set ℓ := log ε⁻¹ with hℓ
  have hε0 := hε.1
  have hℓε : ℓ = -log ε := by rw [hℓ, log_inv]
  have hℓ₀ : ℓ₀ < ℓ := by
    have := log_lt_log hε0 hε.2
    rw [log_exp] at this; linarith
  have hℓA : A0 + 1 < ℓ := lt_of_le_of_lt (le_max_left _ _) hℓ₀
  have hℓ2 : L2 < ℓ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hℓ₀
  have hℓ3 : L3 < ℓ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hℓ₀
  have hexpℓ : exp ℓ = ε⁻¹ := exp_log (inv_pos.2 hε0)
  have hn' : κ * exp ℓ ≤ n := by rw [hexpℓ, ← div_eq_mul_inv]; exact hn
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) hn'
  have : Nonempty (Fin n) := ⟨⟨0, by exact_mod_cast hn0⟩⟩
  -- the set `B`
  set B : Set (Fin n → ℝ) := {x | a1 * exp ((1 + s / 2) * ℓ) ≤ ∑ i, exp (ξ * x i)}
  have hB : a2 ≤ P.real {ω | X ω ∈ B} :=
    probB_ge hXm hX h0 hξ0 hξ1 hκ hn' hvar hcov
  have hBne : B.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    simp [hne] at hB; linarith
  -- `σ`
  have hvle : ∀ i : Fin n, Var[fun ω => X ω i; P] ≤ ℓ + A0 := by
    intro i
    have := hcov i i
    rw [covariance_self (eval_gauss hX i).aemeasurable] at this
    simpa [dN] using this
  set V := ⨆ i, Var[fun ω => X ω i; P]
  have hVle : V ≤ ℓ + A0 := ciSup_le hvle
  have hVge : ℓ - A0 ≤ V := (hvar ⟨0, by exact_mod_cast hn0⟩).trans
    (le_ciSup (f := fun i => Var[fun ω => X ω i; P]) (Finite.bddAbove_range _) _)
  have hVpos : 0 < V := by linarith
  set σ := sqrt V
  have hσ0 : 0 ≤ σ := sqrt_nonneg _
  have hσ2 : σ ^ 2 = V := sq_sqrt hVpos.le
  set s0 := sqrt (ℓ + A0)
  have hs02 : s0 ^ 2 = ℓ + A0 := sq_sqrt (by linarith)
  have hσs0 : σ ≤ s0 := sqrt_le_sqrt hVle
  -- `C s0 ≤ ζ/(4q) (ℓ+A0) + q C²/ζ`
  have hz4 : 0 < ζ / (4 * q) := by positivity
  have hCs0 : C * s0 ≤ ζ / (4 * q) * (ℓ + A0) + q * C ^ 2 / ζ := by
    have := amgm_le (C := C) (u := s0) hz4
    rw [hs02] at this
    have e : C ^ 2 / (4 * (ζ / (4 * q))) = q * C ^ 2 / ζ := by field_simp
    linarith
  set lam := q * ℓ - b
  set Eb := b + ζ / (4 * q) * (ℓ + A0) + q * C ^ 2 / ζ
  have hzq : ζ / (4 * q) ≤ q / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hμ : 0 ≤ q * ℓ - Eb := by
    have h1 := mul_le_mul_of_nonneg_right hzq (by linarith : (0 : ℝ) ≤ ℓ + A0)
    have h2 : q * L2 = 2 * (q * A0 + 2 * b + 2 * q * C ^ 2 / ζ + 1) := by
      simp only [L2]; field_simp
    have h3 := mul_lt_mul_of_pos_left hℓ2 hq0
    have h4 : q * C ^ 2 / ζ = q * (C ^ 2 / ζ) := by ring
    have h5 : 2 * q * C ^ 2 / ζ = 2 * (q * (C ^ 2 / ζ)) := by ring
    have h6 : 0 ≤ q * (C ^ 2 / ζ) := by positivity
    have h7 : 0 ≤ q * A0 := mul_nonneg hq0.le hA0
    simp only [Eb]
    rw [h4]
    rw [h2, h5] at h3
    linarith
  have hlamσ : q * ℓ - Eb ≤ lam - C * σ := by
    have := mul_le_mul_of_nonneg_left hσs0 hC0.le
    simp only [lam, Eb]; linarith
  have hlam : C * σ ≤ lam := by linarith
  have hD := hC Ω P n X hX h0 σ hσ0 (by rw [hσ2]) B hB lam hlam
  -- inclusion of events
  have hsub : {ω | sumExp X ξ ω < ε ^ (p - 1 - s / 2)} ⊆ {ω | lam ≤ infDist (X ω) B} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hyB, hy⟩ := (infDist_lt_iff hBne).1 hlt
    have hcoord : ∀ i, y i - lam ≤ X ω i := by
      intro i
      have := (dist_le_pi_dist (X ω) y i).trans hy.le
      rw [Real.dist_eq, abs_le] at this
      linarith [this.1]
    have hsum : exp (-(ξ * lam)) * ∑ i, exp (ξ * y i) ≤ sumExp X ξ ω := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← exp_add]
      have := mul_le_mul_of_nonneg_left (hcoord i) hξ0.le
      rw [mul_sub] at this
      exact exp_le_exp.2 (by linarith only [this])
    have hyB' : a1 * exp ((1 + s / 2) * ℓ) ≤ ∑ i, exp (ξ * y i) := by
      simpa only [B, Set.mem_ofPred_eq] using hyB
    have hfin : ε ^ (p - 1 - s / 2) ≤ exp (-(ξ * lam)) * (a1 * exp ((1 + s / 2) * ℓ)) := by
      rw [rpow_def_of_pos hε0, ← exp_log ha1p, ← exp_add, ← exp_add]
      refine exp_le_exp.2 ?_
      have hξl : ξ * lam = p * ℓ + min (log a1) 0 := by
        simp only [lam, b, q]; field_simp; ring
      rw [hξl]
      have := min_le_left (log a1) 0
      have hlε : log ε = -ℓ := by linarith only [hℓε]
      rw [hlε]
      linarith only [this]
    have := mul_le_mul_of_nonneg_left hyB' (exp_pos (-(ξ * lam))).le
    linarith
  refine (measureReal_mono hsub).trans (hD.trans ?_)
  -- the tail bound
  rw [rpow_def_of_pos hε0]
  refine exp_le_exp.2 ?_
  rw [← neg_neg (log ε), ← hℓε, hσ2]
  have hσpos : 0 < V := hVpos
  have hsq : (q * ℓ - Eb) ^ 2 ≤ (lam - C * σ) ^ 2 := pow_le_pow_left₀ hμ hlamσ 2
  have hfrac : (q * ℓ - Eb) ^ 2 / (2 * (ℓ + A0)) ≤ (lam - C * σ) ^ 2 / (2 * V) :=
    div_le_div₀ (sq_nonneg _) hsq (by positivity) (by linarith)
  have hmain : ℓ * (q ^ 2 / 2 - ζ) ≤ (q * ℓ - Eb) ^ 2 / (2 * (ℓ + A0)) := by
    rw [le_div_iff₀ (by linarith)]
    have hL3 : ζ * L3 = q ^ 2 * A0 + 2 * q * b + 2 * C ^ 2 * q ^ 2 / ζ + ζ := by
      simp only [L3]; field_simp
    have h3 := mul_lt_mul_of_pos_left hℓ3 hζ
    have hEb : 2 * q * Eb = 2 * q * b + ζ / 2 * (ℓ + A0) + 2 * C ^ 2 * q ^ 2 / ζ := by
      simp only [Eb]; field_simp; ring
    have hℓ0 : 0 < ℓ := by linarith
    have hkey : 2 * q * Eb + (q ^ 2 - 2 * ζ) * A0 ≤ 2 * ζ * ℓ := by
      have : 0 ≤ ζ * A0 := mul_nonneg hζ.le hA0
      have : 0 ≤ ζ * ℓ := mul_nonneg hζ.le hℓ0.le
      have e1 : 2 * q * Eb + (q ^ 2 - 2 * ζ) * A0 =
          (2 * q * b + 2 * C ^ 2 * q ^ 2 / ζ + q ^ 2 * A0) + ζ * ℓ / 2 - 3 / 2 * (ζ * A0) := by
        rw [hEb]; ring
      have e2 : 2 * q * b + 2 * C ^ 2 * q ^ 2 / ζ + q ^ 2 * A0 < ζ * ℓ := by
        rw [hL3] at h3; linarith only [h3, hζ]
      rw [e1]
      have e3 : 2 * ζ * ℓ = 2 * (ζ * ℓ) := by ring
      rw [e3]
      linarith only [e2, this, ‹0 ≤ ζ * A0›]
    have H := mul_le_mul_of_nonneg_left hkey hℓ0.le
    have H2 := sq_nonneg Eb
    linear_combination H + H2
  have := hmain.trans hfrac
  have e : -(lam - C * σ) ^ 2 / (2 * V) = -((lam - C * σ) ^ 2 / (2 * V)) := by ring
  rw [e]; linarith

end LQGMetric.DFGPS.P41
