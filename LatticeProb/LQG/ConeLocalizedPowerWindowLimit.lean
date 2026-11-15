import LatticeProb.LQG.ConeLocalizedTwoScale
import LatticeProb.LQG.ConeLocalizedPowerWindow
import LatticeProb.LQG.ConeScaleTailParameters

/-! # Localized diameter probabilities on power-law windows -/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Set Metric LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped Topology NNReal ENNReal

namespace LatticeProb.LQG

private theorem explicit_scale_tail_parameters {γ d ell b : ℝ}
    (hγ : 0 < γ) (hd : 0 < d) (hell : 0 < ell) (hb : 0 < b) (hb1 : b < 1) :
    ∃ (u : ℝ) (T : ℝ≥0), 0 < u ∧ 0 < T ∧
      (T : ℝ) = (γ⁻¹ * Real.log 1 - γ⁻¹ * Real.log b) / d + u ∧
      Real.exp (-((d * u) ^ 2 / (2 * T))) =
        b ^ (d * ell ^ 2 / (2 * γ * (1 + ell))) ∧
      (T : ℝ) = ((1 + ell) / (γ * d)) * (-Real.log b) := by
  have hlog : Real.log b < 0 := Real.log_neg hb hb1
  let A : ℝ := -Real.log b / (γ * d)
  have hA : 0 < A := div_pos (neg_pos.mpr hlog) (mul_pos hγ hd)
  let u : ℝ := ell * A
  let T : ℝ≥0 := ⟨(1 + ell) * A, (mul_pos (by linarith) hA).le⟩
  have hu : 0 < u := mul_pos hell hA
  have hT : 0 < (T : ℝ) := mul_pos (by linarith) hA
  refine ⟨u, T, hu, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hT
  · change (1 + ell) * A = (γ⁻¹ * Real.log 1 - γ⁻¹ * Real.log b) / d + ell * A
    dsimp [A]
    rw [Real.log_one]
    field_simp [ne_of_gt hγ, ne_of_gt hd]
    ring
  · change Real.exp (-((d * (ell * A)) ^ 2 / (2 * ((1 + ell) * A)))) = _
    rw [Real.rpow_def_of_pos hb]
    congr 1
    field_simp [ne_of_gt hA, ne_of_gt hγ, ne_of_gt hd,
      ne_of_gt (show 0 < 1 + ell by linarith)]
    dsimp [A]
    field_simp [ne_of_gt hγ, ne_of_gt hd]
  · change (1 + ell) * (-Real.log b / (γ * d)) = _
    ring

/-- Uniform forward and backward exit bounds imply convergence of the localized
 diameter failure probability along power-law windows. -/
theorem tendsto_measure_cone_localized_diameter
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    (F : C(ℝ, ℂ) → C(ℝ, EuclideanSpace ℝ (Fin 2))) (hFm : Measurable F)
    (hF : ∀ (v : C(ℝ, ℂ)) t, F v t = Complex.orthonormalBasisOneI.repr (v t))
    {p q ρ r e s a ell : ℝ} (hp : 0 < p) (hq : 0 < q) (hqρ : q < ρ)
    (hρ1 : ρ < 1) (hr : r ∈ Ioo (0 : ℝ) 1) {M : ℕ} (hM : 0 < M)
    (he : 0 < e) (heupper : e < p ^ 2 / (2 * γ ^ 2) - 2)
    (hs : 0 < s) (hsγ : s < 4 / γ ^ 2 - 1) (ha : 0 < a) (hell : 0 < ell)
    (Cforward Cback : ℝ) (hf : 0 ≤ Cforward) (hb : 0 ≤ Cback)
    (hforward : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ k,
      P (forwardExitBallFailure (F ∘ ηL) δ k) ≤ ENNReal.ofReal (Cforward * δ ^ p))
    (hback : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ k,
      P (backwardExitBallFailure (F ∘ ηL) δ k) ≤ ENNReal.ofReal (Cback * δ ^ p)) :
    Tendsto (fun δ : ℝ =>
      P {ω | ENNReal.ofReal ((2 * Real.exp 1) ^ 2 * (4 / (Real.pi * δ ^ 2))) <
        MatedCRTHarmonic.GMS4b.locDA (δ ^ (2 + γ ^ 2 / 2 + p) / 4) (η ω) 0})
      (𝓝[>] 0) (𝓝 0) := by
  let d := CellScaling.lqgQ γ - γ
  let C := (1 + ell) / (γ * d)
  let β := d * ell ^ 2 / (2 * γ * (1 + ell))
  let k := 2 + γ ^ 2 / 2 + p
  have hd : 0 < d := CellScaling.lqgQ_sub_pos hγ.1 hγ.2
  have hC : 0 < C := div_pos (by linarith) (mul_pos hγ.1 hd)
  have hβ : 0 < β := div_pos (mul_pos hd (sq_pos_of_pos hell)) (mul_pos (mul_pos (by norm_num) hγ.1) (by linarith))
  have hka : 0 < k + a := by dsimp [k]; positivity
  obtain ⟨Cexit, Carea, Cinner, hfinite, hbound⟩ :=
    measure_cone_localized_diameter_le_two_scale D hstd hγ μ hμ F hFm hF
      hp hq hqρ hρ1 hr M heupper hs hsγ
  have ht := tendsto_localized_power_window_bound hka hC hp hβ ha he hs hM
    Cforward Cback Cexit Carea hf hb (ne_of_lt hfinite)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Filter.Eventually.of_forall fun _ => zero_le
  · filter_upwards [eventually_power_window_parameters (k := k) (a := a) hq hr.2,
        (tendsto_power_window_inner_scale hka).eventually (Ioo_mem_nhdsGT one_pos),
        hforward, hback] with δ hδ hbδ hfw hbw
    let w := δ ^ k / 4
    let b := w * δ ^ a
    obtain ⟨u, T, hu, hT, hTid, hexp, hTC⟩ :=
      explicit_scale_tail_parameters hγ.1 hd hell hbδ.1 hbδ.2
    let N := ⌈C * (-Real.log b) + 3⌉₊
    have hN : (T : ℝ) + 3 ≤ (N : ℝ) := by
      rw [hTC]
      exact Nat.le_ceil _
    have h := hbound hδ.1 hδ.2.1 hδ.2.2.1 hδ.2.2.2.1 hbδ.1 hbδ.2
      hu hT hTid (ENNReal.ofReal (Cforward * δ ^ p))
      (ENNReal.ofReal (Cback * δ ^ p)) N hN hfw hbw
    rw [hexp] at h
    simpa only [k, C, β, w, b, N, d, add_assoc] using h

end LatticeProb.LQG
