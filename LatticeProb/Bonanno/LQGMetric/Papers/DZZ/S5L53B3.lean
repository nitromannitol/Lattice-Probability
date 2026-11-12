/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53B3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B1

/-!
# DZZ Lemma 5.3, part 1: from the good event to near-subadditivity (P2-DZZ53b)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.3 (`lem-existence-exponent`),
l. 2392–2420). With `δ = 2^{-k}`, `δ̃ = 2^{-l}` (`l ≤ k`) and `X_n = log D̃_{2^{-n}}(u,v)`:

* (Eq.calD1), (eq-triangle-inequality) and (eq-union-bound-distance) (l. 2382–2397) give an
  event `𝒟 = 𝒟₁ ∩ 𝒟₂` with `P(𝒟ᶜ) ≤ e^{−(log δ⁻¹)^{0.22}} + e^{−c(log δ⁻¹)^{0.51}}` on which
  `X_{k+l} ≤ E X_k + E X_l + 5 (log δ⁻¹)^{0.98}` (this is how (eq-040418) is obtained). This is
  the open node **`DZZLem53Event`** (with `P(𝒟ᶜ) ≤ 2e^{−(log δ⁻¹)^{0.22}}`, which DZZ's bound
  implies for `δ` small).
* The rest of DZZ's argument (l. 2405–2420) is proved here: the bad event is controlled by the
  second moment (eq-very-crude) (DZZ: "an analogue of (eq-very-crude) … Jensen's inequality",
  l. 2411; we use `x ≤ x²/M + M 1_{𝒟ᶜ}` on `𝒟ᶜ` with `M = e^{(log δ⁻¹)^{0.22}/2}` instead of
  Jensen), and dividing by `log(δδ̃)⁻¹` gives
  `χ_{δδ̃} ≤ (log δ⁻¹ χ_δ + log δ̃⁻¹ χ_δ̃)/log(δδ̃)⁻¹ + (log δ⁻¹)^{−0.01}`
  (`dzzLem53Subadd_of_event`).
* `dzzLem53Exp_dzzMuIn_of_event`: DZZ Lemma 5.3 at `μIn` from `DZZLem53Event` (part 1) and
  `hindep` (part 3) only; `hmeas` is discharged by `aemeasurable_wickQArea_ball` (S5L53B1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ L5.3 part 1, the good event** (l. 2382–2404: (Eq.calD1), (eq-triangle-inequality),
(eq-union-bound-distance)): for `δ = 2^{-k}`, `δ̃ = 2^{-l}`, `1 ≤ l ≤ k`, `k ≥ k₀`, outside an
event of probability `≤ 2e^{−(log δ⁻¹)^{0.22}}`,
`log D̃_{δδ̃}(u,v) ≤ E log D̃_δ(u,v) + E log D̃_δ̃(u,v) + 5 (log δ⁻¹)^{0.98}`. -/
def DZZLem53Event (P : Measure Ω) (ν : Ω → Measure ℂ) (u v : ℂ) : Prop :=
  ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
    P {ω | (∫ ω', logMinLGD (ν ω') ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P) +
        (∫ ω', logMinLGD (ν ω') ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) +
        5 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ) <
        logMinLGD (ν ω) ((2 : ℝ)⁻¹ ^ (k + l)) {u} {v}} ≤
      ENNReal.ofReal (2 * Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)))

/-- the error terms are `o(L^{0.99})` -/
lemma l53_err_asym (A B : ℝ) : ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    5 * L ^ (0.98 : ℝ) + (A + 4 * B * L ^ 2 + 2) * Real.exp (-(1 / 2) * L ^ (0.22 : ℝ)) ≤
      L ^ (0.99 : ℝ) := by
  have hy : Tendsto (fun L : ℝ => L ^ (0.22 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / 2) (by norm_num)).comp hy
  have hs := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (100 / 11) (1 / 2)
    (by norm_num)).comp hy
  have hg : Tendsto (fun L : ℝ => (A + 4 * B * L ^ 2 + 2) *
      Real.exp (-(1 / 2) * L ^ (0.22 : ℝ))) atTop (𝓝 0) := by
    have := (h0.const_mul (A + 2)).add (hs.const_mul (4 * B))
    rw [mul_zero, mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    simp only [Function.comp, Real.rpow_zero, one_mul]
    rw [← Real.rpow_mul hL, show (0.22 : ℝ) * (100 / 11) = (2 : ℕ) by norm_num,
      Real.rpow_natCast]
    ring
  have ht : Tendsto (fun L : ℝ => L ^ (-(0.01 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 ((hg.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by
    norm_num))).and (ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 10 by norm_num))))
  refine ⟨max L₁ 1, le_max_right _ _, fun L hL => ?_⟩
  obtain ⟨h1, h2⟩ := hL₁ L ((le_max_left _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := by linarith
  have e : L ^ (0.98 : ℝ) = L ^ (0.99 : ℝ) * L ^ (-(0.01 : ℝ)) := by
    rw [← Real.rpow_add hL0]; norm_num
  have h99 : 1 ≤ L ^ (0.99 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hp : 0 ≤ L ^ (0.99 : ℝ) := by positivity
  rw [e]
  nlinarith

/-- **DZZ l. 2405–2420**: the good event `DZZLem53Event` and the second moment
(eq-very-crude) give the near-subadditive inequality `DZZLem53Subadd` with `θ = 0.01`. -/
theorem dzzLem53Subadd_of_event [IsProbabilityMeasure P] {ν : Ω → Measure ℂ} {u v : ℂ}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hint : ∀ k : ℕ, Integrable (fun ω => logMinLGD (ν ω) ((2 : ℝ)⁻¹ ^ k) {u} {v}) P)
    (hsq : ∀ k : ℕ, 1 ≤ k → ∫⁻ ω, ENNReal.ofReal (logMinLGD (ν ω) ((2 : ℝ)⁻¹ ^ k) {u} {v}) ^ 2
      ∂P ≤ ENNReal.ofReal (A + B * ((k : ℝ) * Real.log 2) ^ 2))
    (hev : DZZLem53Event P ν u v) : DZZLem53Subadd P ν u v 0.01 := by
  obtain ⟨k₀, hk₀⟩ := hev
  obtain ⟨L₀, hL₀1, hL₀⟩ := l53_err_asym A B
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨k₁, hk₁⟩ := exists_nat_ge (L₀ / Real.log 2)
  refine ⟨max k₀ k₁, fun k l hk hl hlk => ?_⟩
  set X : ℕ → Ω → ℝ := fun n ω => logMinLGD (ν ω) ((2 : ℝ)⁻¹ ^ n) {u} {v} with hX
  have hX0 : ∀ n ω, 0 ≤ X n ω := fun n ω => logMinLGD_nonneg _ _ _ _
  set L : ℝ := (k : ℝ) * Real.log 2 with hLdef
  have hLL₀ : L₀ ≤ L := by
    have : L₀ / Real.log 2 ≤ k := hk₁.trans (by exact_mod_cast le_of_max_le_right hk)
    rw [div_le_iff₀ hl2] at this; exact this
  have hL1 : 1 ≤ L := hL₀1.trans hLL₀
  have hL0 : 0 < L := by linarith
  have hk1 : (1 : ℝ) ≤ k := by
    have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    exact this.trans (by exact_mod_cast hlk)
  set n := k + l with hn
  set Ln : ℝ := (n : ℝ) * Real.log 2 with hLn
  have hLnL : L ≤ Ln := by
    simp only [hLdef, hLn, hn, Nat.cast_add]; nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  have hLn2 : Ln ≤ 2 * L := by
    have : (l : ℝ) ≤ k := by exact_mod_cast hlk
    simp only [hLdef, hLn, hn, Nat.cast_add]; nlinarith
  set R : ℝ := (∫ ω, X k ω ∂P) + (∫ ω, X l ω ∂P) + 5 * L ^ (0.98 : ℝ) with hR
  have hR0 : 0 ≤ R := by
    have := integral_nonneg (μ := P) (f := X k) (fun ω => hX0 k ω)
    have := integral_nonneg (μ := P) (f := X l) (fun ω => hX0 l ω)
    have : 0 ≤ L ^ (0.98 : ℝ) := by positivity
    linarith
  set Bd : Set Ω := {ω | R < X n ω} with hBd
  set T := toMeasurable P Bd with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable P _
  have hPT : P T ≤ ENNReal.ofReal (2 * Real.exp (-L ^ (0.22 : ℝ))) := by
    rw [hT, measure_toMeasurable]; exact hk₀ k l (le_of_max_le_left hk) hl hlk
  set M : ℝ := Real.exp ((1 / 2) * L ^ (0.22 : ℝ)) with hM
  have hM0 : 0 < M := Real.exp_pos _
  -- pointwise: `X_n ≤ R + X_n²/M + M 1_T`
  have hpt : ∀ ω, X n ω ≤ R + X n ω ^ 2 / M + M * T.indicator 1 ω := by
    intro ω
    have hq : 0 ≤ X n ω ^ 2 / M := by positivity
    by_cases hω : ω ∈ Bd
    · have hiT : T.indicator (1 : Ω → ℝ) ω = 1 := by
        rw [indicator_of_mem (subset_toMeasurable P _ hω), Pi.one_apply]
      rw [hiT, mul_one]
      by_cases hxM : X n ω ≤ M
      · linarith
      · push Not at hxM
        have : X n ω ≤ X n ω ^ 2 / M := by
          rw [le_div_iff₀ hM0, sq]
          exact mul_le_mul_of_nonneg_left hxM.le (hX0 n ω)
        linarith
    · have : X n ω ≤ R := not_lt.1 hω
      have : 0 ≤ M * T.indicator (1 : Ω → ℝ) ω :=
        mul_nonneg hM0.le (indicator_nonneg (fun _ _ => zero_le_one) _)
      linarith
  -- the second moment
  have hn1 : 1 ≤ n := by omega
  have hsqn := hsq n hn1
  have hX2m : AEStronglyMeasurable (fun ω => X n ω ^ 2) P := (hint n).aestronglyMeasurable.pow 2
  have eofr : ∀ ω, ENNReal.ofReal (X n ω ^ 2) = ENNReal.ofReal (X n ω) ^ 2 := fun ω =>
    ENNReal.ofReal_pow (hX0 n ω) 2
  have hX2 : Integrable (fun ω => X n ω ^ 2) P := by
    refine ⟨hX2m, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
    simp only [eofr]
    exact hsqn.trans_lt ENNReal.ofReal_lt_top
  have hI2 : ∫ ω, X n ω ^ 2 ∂P ≤ A + B * Ln ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _) hX2m]
    simp only [eofr]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsqn
  have hPTr : P.real T ≤ 2 * Real.exp (-L ^ (0.22 : ℝ)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hPT
  -- integrate
  have hIn : ∫ ω, X n ω ∂P ≤ R + (A + B * Ln ^ 2) / M + M * (2 * Real.exp (-L ^ (0.22 : ℝ))) := by
    have hi1 : Integrable (fun ω => X n ω ^ 2 / M) P := hX2.div_const M
    have hi2 : Integrable (fun ω => M * T.indicator (1 : Ω → ℝ) ω) P :=
      ((integrable_const (1 : ℝ)).indicator hTm).const_mul M
    calc ∫ ω, X n ω ∂P ≤ ∫ ω, (R + X n ω ^ 2 / M + M * T.indicator 1 ω) ∂P :=
          integral_mono (hint n) (((integrable_const R).add hi1).add hi2) hpt
      _ = R + (∫ ω, X n ω ^ 2 ∂P) / M + M * P.real T := by
          have h1 := integral_add ((integrable_const R).add hi1) hi2
          have h2 := integral_add (integrable_const R) hi1
          simp only [Pi.add_apply] at h1 h2
          rw [h1, h2, integral_const, integral_div, integral_const_mul, integral_indicator_one hTm]
          simp
      _ ≤ _ := by
          gcongr
  have hexp : M * (2 * Real.exp (-L ^ (0.22 : ℝ))) = 2 * Real.exp (-(1 / 2) * L ^ (0.22 : ℝ)) := by
    rw [hM, ← mul_assoc, mul_comm _ 2, mul_assoc, ← Real.exp_add]; ring_nf
  have hdiv : (A + B * Ln ^ 2) / M ≤ (A + 4 * B * L ^ 2) * Real.exp (-(1 / 2) * L ^ (0.22 : ℝ)) := by
    rw [div_eq_mul_inv, hM, ← Real.exp_neg, neg_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have : Ln ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    nlinarith
  have herr := hL₀ L hLL₀
  have hIn' : ∫ ω, X n ω ∂P ≤ (∫ ω, X k ω ∂P) + (∫ ω, X l ω ∂P) + L ^ (0.99 : ℝ) := by
    rw [hexp] at hIn
    have : R + (A + 4 * B * L ^ 2) * Real.exp (-(1 / 2) * L ^ (0.22 : ℝ)) +
        2 * Real.exp (-(1 / 2) * L ^ (0.22 : ℝ)) ≤
        (∫ ω, X k ω ∂P) + (∫ ω, X l ω ∂P) + L ^ (0.99 : ℝ) := by
      simp only [hR]; nlinarith
    linarith
  -- divide by `log (δδ̃)⁻¹`
  have hLn0 : 0 < Ln := lt_of_lt_of_le hL0 hLnL
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  have hl2' : 0 < (l : ℝ) * Real.log 2 := by positivity
  show (∫ ω, X n ω ∂P) / Ln ≤ (k : ℝ) / (k + l) * ((∫ ω, X k ω ∂P) / (k * Real.log 2)) +
    (l : ℝ) / (k + l) * ((∫ ω, X l ω ∂P) / (l * Real.log 2)) +
    ((k : ℝ) * Real.log 2) ^ (-(0.01 : ℝ))
  have e1 : (k : ℝ) / (k + l) * ((∫ ω, X k ω ∂P) / (k * Real.log 2)) =
      (∫ ω, X k ω ∂P) / Ln := by
    simp only [hLn, hn, Nat.cast_add]; field_simp
  have e2 : (l : ℝ) / (k + l) * ((∫ ω, X l ω ∂P) / (l * Real.log 2)) =
      (∫ ω, X l ω ∂P) / Ln := by
    simp only [hLn, hn, Nat.cast_add]; field_simp
  rw [e1, e2]
  have h99 : L ^ (0.99 : ℝ) / Ln ≤ L ^ (-(0.01 : ℝ)) := by
    rw [div_le_iff₀ hLn0]
    have e : L ^ (0.99 : ℝ) = L ^ (-(0.01 : ℝ)) * L := by
      rw [← Real.rpow_add_one hL0.ne']; norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_left hLnL (by positivity)
  have hfin : (∫ ω, X n ω ∂P) / Ln ≤ (∫ ω, X k ω ∂P) / Ln + (∫ ω, X l ω ∂P) / Ln +
      L ^ (0.99 : ℝ) / Ln := by
    rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right hIn' hLn0.le
  have : L ^ (-(0.01 : ℝ)) = ((k : ℝ) * Real.log 2) ^ (-(0.01 : ℝ)) := rfl
  linarith

/-- **DZZ Lemma 5.3 at `μIn`** from its part 1 in the good-event form `DZZLem53Event`
(DZZ l. 2382–2404) and part 3 (`hindep`, l. 2423); measurability, the crude bounds, the bad
event and Hammersley's lemma are discharged. -/
theorem dzzLem53Exp_dzzMuIn_of_event (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2)
    (hev : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v →
      DZZLem53Event P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v)
    (hindep : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ u' ∈ dzzVbar, ∀ v' ∈ dzzVbar, u' ≠ v' →
      Tendsto (fun δ => (∫ ω, logMinLGD (dzzWall (tildeBox u' v') (dzzMuIn γ W ω)) δ {u'} {v'}
        ∂P) / Real.log δ⁻¹ - (∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v}
        ∂P) / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 0)) :
    ∃ χ, DZZLem53Exp P (dzzMuIn γ W) χ := by
  have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hmeas := aemeasurable_wickQArea_ball hW hγ hγ2
  obtain ⟨A, B, hA, hB, hsq⟩ := lintegral_sq_log_tilde_le (P := P) hW hγ hγ2
  refine dzzLem53Exp_dzzMuIn_of_subadd hW hγ hγ2 hmeas (fun u hu v hv huv => ?_) hindep
  refine dzzLem53Subadd_of_event (A := A) hA hB
    (fun k => integrable_log_tilde hW hγ hγ2 hmeas hu hv huv (by positivity))
    (fun k hk => ?_) (hev u hu v hv huv)
  have hδ2 : (2 : ℝ)⁻¹ ^ k ≤ 1 / 2 := by
    rw [one_div]; exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hL : Real.log ((2 : ℝ)⁻¹ ^ k)⁻¹ = k * Real.log 2 := by
    rw [inv_pow, inv_inv, Real.log_pow]
  have := hsq u hu v hv huv _ (by positivity) hδ2
  rwa [hL] at this

end DZZ
end LQGMetric
