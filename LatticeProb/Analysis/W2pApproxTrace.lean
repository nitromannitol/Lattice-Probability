import LatticeProb.Analysis.W2pApprox
import LatticeProb.Analysis.WeakLaplaceW2p

/-!
# The trace of the limit Hessian of smooth approximate solutions of `Δ u = s`

Let `uε n` be smooth approximations of `u` on an open set `U` whose Hessians converge to `G` in
`L^p` on compact subsets of `U` (`IsW2pApprox`). If `Δ (uε n) = sε n` on
`{x | closedBall x (ε n) ⊆ U}` and `sε n → s` in `L^p` on compact subsets of `U`, then the trace
`hessianTrace (G x) = ∑ i, G x (b i) (b i)` of `G` in the standard orthonormal basis `b` equals
`s x` for almost every `x ∈ U` (`ae_trace_eq_of_w2pApprox`). Together with the weak Hessian
identity of `weakHessianW2p_meas`, this is the equation `Δ u = s` almost everywhere of
Pegden–Smart, Proposition 2.4.
-/

open MeasureTheory Metric Filter Topology Set
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace LatticeProb.PegdenSmart

section Trace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The trace `∑ i, H (b i) (b i)` of a bilinear form `H` in the standard orthonormal basis `b`. -/
noncomputable def hessianTrace (H : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  ∑ i, H (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)

theorem hessianTrace_sub (H K : E →L[ℝ] E →L[ℝ] ℝ) :
    hessianTrace (H - K) = hessianTrace H - hessianTrace K := by
  simp [hessianTrace, Finset.sum_sub_distrib]

theorem hessianTrace_zero : hessianTrace (0 : E →L[ℝ] E →L[ℝ] ℝ) = 0 := by
  simp [hessianTrace]

theorem norm_hessianTrace_le (H : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖hessianTrace H‖ ≤ Module.finrank ℝ E * ‖H‖ := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖H (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)‖
      ≤ ∑ _i : Fin (Module.finrank ℝ E), ‖H‖ := Finset.sum_le_sum fun i _ => by
        simpa [(stdOrthonormalBasis ℝ E).orthonormal.1 i] using
          H.le_opNorm₂ (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)
    _ = Module.finrank ℝ E * ‖H‖ := by simp

/-- The Laplacian is the trace of the Hessian. -/
theorem laplacian_eq_hessianTrace (f : E → ℝ) (x : E) :
    Δ f x = hessianTrace (fderiv ℝ (fderiv ℝ f) x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [hessianTrace, iteratedFDeriv_two_apply]

theorem measurable_hessianTrace_comp {α : Type*} [MeasurableSpace α]
    {f : α → E →L[ℝ] E →L[ℝ] ℝ} (hf : Measurable f) : Measurable fun a => hessianTrace (f a) :=
  Finset.measurable_sum _ fun _ _ =>
    (hf.apply_continuousLinearMap _).apply_continuousLinearMap _

/-- The difference between the Hessian of a function and a measurable field of bilinear forms is
measurable. -/
theorem measurable_fderiv_fderiv_sub [MeasurableSpace E] [BorelSpace E] (f : E → ℝ)
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} (hG : Measurable G) :
    Measurable fun x => fderiv ℝ (fderiv ℝ f) x - G x := by
  have : ContinuousSub (E →L[ℝ] E →L[ℝ] ℝ) :=
    IsTopologicalAddGroup.to_continuousSub (G := E →L[ℝ] E →L[ℝ] ℝ)
  exact (measurable_fderiv ℝ (fderiv ℝ f)).sub hG

end Trace

/-- **The trace of a `W^{2,p}` limit Hessian.** If `uε n → u` with Hessians converging to `G` in
`L^p` on compact subsets of `U`, `Δ (uε n) = sε n` on `{x | closedBall x (ε n) ⊆ U}` and
`sε n → s` in `L^p` on compact subsets of `U`, then `∑ i, G x (b i) (b i) = s x` for almost every
`x ∈ U`, where `b` is the standard orthonormal basis. The measurability of `s` is not used. -/
theorem ae_trace_eq_of_w2pApprox {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {p : ℝ≥0∞} (hp : 1 ≤ p) {U : Set E} {u s : E → ℝ}
    {uε sε : ℕ → E → ℝ} {ε : ℕ → ℝ} {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : IsW2pApprox μ p U u uε ε G)
    (hΔ : ∀ n, ∀ x ∈ {x | closedBall x (ε n) ⊆ U}, Δ (uε n) x = sε n x)
    (_hs : AEStronglyMeasurable s (μ.restrict U))
    (hsε : ∀ C : Set E, IsCompact C → C ⊆ U →
      Tendsto (fun n => eLpNorm (C.indicator fun x => sε n x - s x) p μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂(μ.restrict U),
      ∑ i, G x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) = s x := by
  obtain ⟨hU, -, hε, -, -, hG, hL⟩ := hA
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hcpt : ∀ C : Set E, IsCompact C → C ⊆ U →
      ∀ᵐ x ∂μ, x ∈ C → hessianTrace (G x) = s x := by
    intro C hC hCU
    obtain ⟨V, -, hCV, hVev⟩ := exists_isOpen_eventually_subset hC hU hCU hε
    have hL' : Tendsto (fun n => eLpNorm (C.indicator fun x =>
        ‖fderiv ℝ (fderiv ℝ (uε n)) x - G x‖) p μ) atTop (𝓝 0) :=
      (hL C hC hCU).congr fun n => by
        exact (eLpNorm_indicator_norm_eq (f := fun x => fderiv ℝ (fderiv ℝ (uε n)) x - G x)
          hC.measurableSet (measurable_fderiv_fderiv_sub (uε n) hG).aestronglyMeasurable).symm
    have hbd : ∀ᶠ n in atTop, eLpNorm (C.indicator fun x => hessianTrace (G x) - s x) p μ ≤
        eLpNorm (C.indicator fun x => sε n x - s x) p μ + ENNReal.ofReal (Module.finrank ℝ E) *
          eLpNorm (C.indicator fun x => ‖fderiv ℝ (fderiv ℝ (uε n)) x - G x‖) p μ := by
      filter_upwards [hVev] with n hn
      have heq : (C.indicator fun x => hessianTrace (G x) - s x) =
          (C.indicator fun x => sε n x - s x) -
            C.indicator fun x => hessianTrace (fderiv ℝ (fderiv ℝ (uε n)) x - G x) := by
        funext x
        by_cases hx : x ∈ C
        · simp only [Pi.sub_apply, indicator_of_mem hx]
          rw [hessianTrace_sub, ← hΔ n x (hn (hCV hx)), laplacian_eq_hessianTrace]
          ring
        · simp only [Pi.sub_apply, indicator_of_notMem hx, sub_zero]
      rw [heq]
      refine (eLpNorm_sub_le hp).trans (add_le_add le_rfl
        (eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          ((measurable_hessianTrace_comp (measurable_fderiv_fderiv_sub (uε n) hG)).indicator
            hC.measurableSet).aestronglyMeasurable
          (Eventually.of_forall fun x => ?_) p))
      by_cases hx : x ∈ C
      · simp only [indicator_of_mem hx]
        exact (norm_hessianTrace_le (fderiv ℝ (fderiv ℝ (uε n)) x - G x)).trans_eq
          (congrArg (fun t => (Module.finrank ℝ E : ℝ) * t)
            (norm_norm (fderiv ℝ (fderiv ℝ (uε n)) x - G x)).symm)
      · simp [indicator_of_notMem hx]
    have hlim : Tendsto (fun n => eLpNorm (C.indicator fun x => sε n x - s x) p μ +
        ENNReal.ofReal (Module.finrank ℝ E) *
          eLpNorm (C.indicator fun x => ‖fderiv ℝ (fderiv ℝ (uε n)) x - G x‖) p μ)
        atTop (𝓝 0) := by
      have h := (hsε C hC hCU).add
        (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Module.finrank ℝ E)) hL'
          (Or.inr ENNReal.ofReal_ne_top))
      rw [mul_zero, add_zero] at h
      exact h
    have hae := (eLpNorm_eq_zero_iff hp0).mp (le_zero_iff.mp (ge_of_tendsto hlim hbd))
    filter_upwards [hae] with x hx hxC
    simp only [Pi.zero_apply, indicator_of_mem hxC, sub_eq_zero] at hx
    exact hx
  obtain ⟨K, hK, hKU, hcov⟩ := exists_isCompact_cover_of_isOpen hU
  filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr fun j => hcpt (K j) (hK j) (hKU j)),
    ae_restrict_mem hU.measurableSet] with x hx hxU
  obtain ⟨j, hj⟩ := hcov {x} isCompact_singleton (singleton_subset_iff.mpr hxU)
  exact hx j (hj rfl)

end LatticeProb.PegdenSmart
