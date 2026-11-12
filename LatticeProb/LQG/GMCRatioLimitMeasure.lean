import LatticeProb.LQG.GMCRatioLimit
import LatticeProb.LQG.GMCAffineCovariance
import LatticeProb.Analysis.VagueLimitSequence

/-!
# The γ-LQG measure as the vague limit along every ratio of the dyadic scales

For a whole-plane Gaussian free field `h` with circle averages `h_s(z)`, `0 < γ < 2`, and its γ-LQG measure `μ`
(the almost sure vague limit of `2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz`), we show that almost surely, for every ratio
`r ∈ [1/2, 1]` simultaneously, the approximations `(r 2^{-k})^{γ²/2} e^{γ h_{r 2^{-k}}(z)} dz` converge vaguely to `μ`.

Consequently the coordinate change rule of the γ-LQG measure under all complex affine maps simultaneously
(`LQGMeasureCoordChangeLP` with `α₀ = 0`) holds for every whole-plane GFF (`lqgMeasureCoordChangeLP_zero`).

The proof: a countable convergence-determining family `D` of continuous compactly supported functions
(`VagueLimit.exists_countable_determining`); almost surely, for every `g ∈ D` the approximations along all ratios converge
to the dyadic limit `∫ g dμ` (`IsWholePlaneGFF.ae_tendsto_integral_lqgApprox_ratio`); for a fixed ratio `r` the
interleaved scales `2^{-k}, r 2^{-k}` then give a vaguely convergent sequence whose even subsequence identifies the limit.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb.LQG.GMCRatioLimit

open LatticeProb.LQG

/-- A real sequence converges if its even and odd subsequences converge to the same limit. -/
theorem tendsto_of_tendsto_even_odd {a : ℕ → ℝ} {ℓ : ℝ} (h0 : Tendsto (fun k => a (2 * k)) atTop (𝓝 ℓ))
    (h1 : Tendsto (fun k => a (2 * k + 1)) atTop (𝓝 ℓ)) : Tendsto a atTop (𝓝 ℓ) := by
  rw [Metric.tendsto_atTop] at h0 h1 ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := h0 ε hε
  obtain ⟨N1, hN1⟩ := h1 ε hε
  refine ⟨2 * max N0 N1 + 1, fun n hn => ?_⟩
  have h0' := le_max_left N0 N1
  have h1' := le_max_right N0 N1
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hN0 k (by omega)
  · exact hN1 k (by omega)

/-- The approximation `s^{γ²/2} e^{γ h_s(z)} dz` is finite on compact sets when `h_s` is continuous. -/
theorem isFiniteMeasureOnCompacts_lqgApprox {γ s : ℝ} {h : ℝ → ℂ → ℝ} (hc : Continuous (h s)) :
    IsFiniteMeasureOnCompacts (lqgApprox γ h s) := by
  have : IsLocallyFiniteMeasure (lqgApprox γ h s) := by
    unfold lqgApprox
    exact IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc)))
  infer_instance

/-- **Identification of the limit along one ratio.** Let `D` be a countable convergence-determining family of
continuous compactly supported functions, `m` the vague limit of the dyadic approximations of `h`, and `r > 0`. If the
approximations along the scales `r 2^{-k}` converge to `∫ g dm` for every `g ∈ D`, then they converge vaguely to `m`. -/
theorem isLQGLimitAlong_mul_of_determining {D : Set (ℂ → ℝ)}
    (hDcc : ∀ g ∈ D, Continuous g ∧ HasCompactSupport g)
    (hD : ∀ m : ℕ → Measure ℂ, (∀ k, IsFiniteMeasureOnCompacts (m k)) →
      (∀ g ∈ D, ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, g x ∂(m k)) atTop (𝓝 ℓ)) →
      ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
        ∃ ℓ : ℝ, Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 ℓ))
    {γ r : ℝ} {h : ℝ → ℂ → ℝ} (hc : ∀ s, 0 < s → Continuous (h s)) (hr : 0 < r) {m : Measure ℂ}
    (hm : IsLQGLimit γ h m)
    (hDr : ∀ g ∈ D, Tendsto (fun k => ∫ z, g z ∂(lqgApprox γ h (r * dyadicScale k))) atTop
      (𝓝 (∫ z, g z ∂m))) :
    IsLQGLimitAlong γ h (fun k => r * dyadicScale k) m := by
  refine ⟨hm.isLocallyFiniteMeasure, fun f hfc hfs => ?_⟩
  have hMf : ∀ n, IsFiniteMeasureOnCompacts (lqgApprox γ h (interleavedScale r n)) := fun n =>
    isFiniteMeasureOnCompacts_lqgApprox (hc _ (interleavedScale_pos hr n))
  have hev : ∀ F : ℂ → ℝ, (fun k => ∫ z, F z ∂(lqgApprox γ h (interleavedScale r (2 * k)))) =
      fun k => ∫ z, F z ∂(lqgApprox γ h (dyadicScale k)) := fun F => by
    simp only [interleavedScale_two_mul]
  have hod : ∀ F : ℂ → ℝ, (fun k => ∫ z, F z ∂(lqgApprox γ h (interleavedScale r (2 * k + 1)))) =
      fun k => ∫ z, F z ∂(lqgApprox γ h (r * dyadicScale k)) := fun F => by
    simp only [interleavedScale_two_mul_add_one]
  have hconv : ∀ g ∈ D, ∃ ℓ : ℝ,
      Tendsto (fun n => ∫ z, g z ∂(lqgApprox γ h (interleavedScale r n))) atTop (𝓝 ℓ) := fun g hg =>
    ⟨_, tendsto_of_tendsto_even_odd (by rw [hev]; exact hm.tendsto_integral g (hDcc g hg).1 (hDcc g hg).2)
      (by rw [hod]; exact hDr g hg)⟩
  obtain ⟨L, hL⟩ := hD (fun n => lqgApprox γ h (interleavedScale r n)) hMf hconv f hfc hfs
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    StrictMono.tendsto_atTop fun a b hab => by omega
  have h2' : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    StrictMono.tendsto_atTop fun a b hab => by omega
  have hLe : Tendsto (fun k => ∫ z, f z ∂(lqgApprox γ h (dyadicScale k))) atTop (𝓝 L) := by
    rw [← hev]
    exact hL.comp h2
  have hLeq : L = ∫ z, f z ∂m := tendsto_nhds_unique hLe (hm.tendsto_integral f hfc hfs)
  rw [← hLeq, ← hod]
  exact hL.comp h2'

end LatticeProb.LQG.GMCRatioLimit

namespace LatticeProb.Gauss.IsWholePlaneGFF

open LatticeProb.LQG LatticeProb.LQG.GMCRatioLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Vague convergence along every ratio.** For a whole-plane GFF, `0 < γ < 2` and its γ-LQG measure `μ`, almost
surely, for every ratio `r ∈ [1/2, 1]` simultaneously, the approximations `lqgApprox γ h (r 2^{-k})` converge vaguely
to `μ`. -/
theorem ae_isLQGLimitAlong_ratio_of_isLQGMeasure (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ r ∈ Icc (1 / 2 : ℝ) 1,
      IsLQGLimitAlong γ (hcirc ω) (fun k => r * dyadicScale k) (μ ω) := by
  obtain ⟨D, hDc, hDcc, hD⟩ := LatticeProb.VagueLimit.exists_countable_determining (X := ℂ)
  have hall : ∀ᵐ ω ∂P, ∀ g ∈ D, ∃ ℓ : ℝ,
      Tendsto (fun k => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) atTop (𝓝 ℓ) ∧
      ∀ r ∈ Icc (1 / 2 : ℝ) 1,
        Tendsto (fun k => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (r * dyadicScale k))) atTop (𝓝 ℓ) :=
    (ae_ball_iff hDc).2 fun g hg =>
      hh.ae_tendsto_integral_lqgApprox_ratio hγ0 hγ2 (hDcc g hg).1 (hDcc g hg).2
  filter_upwards [hall, hμ, hh.ae_continuousOn_circle] with ω hω hmω hcont r hr
  refine isLQGLimitAlong_mul_of_determining hDcc hD (fun s hs => continuous_slice hcont hs)
    (by linarith [hr.1]) hmω fun g hg => ?_
  obtain ⟨ℓ, hℓ, hℓr⟩ := hω g hg
  rw [← tendsto_nhds_unique hℓ (hmω.tendsto_integral g (hDcc g hg).1 (hDcc g hg).2)]
  exact hℓr r hr

/-- The `α₀ = 0` case for the field-circle-average form: almost surely, for every ratio `r ∈ (1/2, 1]`, the
approximations of `fieldCircleAverage 0 (hcirc ω)` along `r 2^{-k}` converge vaguely to the γ-LQG measure. -/
theorem ae_isLQGLimitAlong_ratio_fieldCircleAverage_zero (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ r ∈ Ioc (1 / 2 : ℝ) 1,
      IsLQGLimitAlong γ (fieldCircleAverage 0 (hcirc ω)) (fun k => r * dyadicScale k) (μ ω) := by
  have hf : ∀ ω, fieldCircleAverage 0 (hcirc ω) = hcirc ω := fun ω => by
    funext s z
    simp [fieldCircleAverage]
  have hf' : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := funext hf
  have hμ' : IsLQGMeasure P γ hcirc μ := by
    rw [IsLQGMeasureOfField, hf'] at hμ
    exact hμ
  filter_upwards [hh.ae_isLQGLimitAlong_ratio_of_isLQGMeasure hγ0 hγ2 hμ'] with ω hω r hr
  rw [hf]
  exact hω r (Ioc_subset_Icc_self hr)

end LatticeProb.Gauss.IsWholePlaneGFF

namespace LatticeProb.LQG

/-- **Coordinate change of the γ-LQG measure of a whole-plane GFF under all complex affine maps simultaneously**
(the case `α₀ = 0` of `LQGMeasureCoordChangeLP`): for every whole-plane GFF, `0 < γ < 2` and its γ-LQG measure `μ`,
almost surely, for all `a ≠ 0` and `b`, the pushforward of `μ` under `x ↦ (x - b) / a` is the γ-LQG measure of the
field `z ↦ h(a z + b) + Q log |a|` (Duplantier-Sheffield 2011, Proposition 2.1). -/
theorem lqgMeasureCoordChangeLP_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : LQGMeasureCoordChangeLP P γ 0 hC hcirc :=
  coordChangeLP_of_ratio_limit P γ 0 hC hcirc fun hG hγ0 hγ2 _ _ hμ =>
    hG.ae_isLQGLimitAlong_ratio_fieldCircleAverage_zero hγ0 hγ2 hμ

end LatticeProb.LQG
