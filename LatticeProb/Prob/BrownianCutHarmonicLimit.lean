import LatticeProb.Prob.BrownianCutExitConvergence

/-! # Harmonic Brownian exit identities at a half-plane boundary -/

set_option autoImplicit false

open MeasureTheory Set Filter InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- A continuous function harmonic in the open right half-plane satisfies the
Brownian exit identity on the intersection of a bounded open set with that
half-plane, including exits at the boundary. -/
theorem integral_openExit_positive_re_of_harmonic {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2}
    (hB : IsBrownianSpace 2 x B P) {U : Set (Euc 2)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : Euc 2 → ℝ} (hf : Continuous f)
    (hh : ∀ y : Euc 2, 0 < (Complex.orthonormalBasisOneI.repr.symm y).re →
      HarmonicAt f y) :
    ∫ ω, f (B (openExitTime B (U ∩ {y | 0 <
      (Complex.orthonormalBasisOneI.repr.symm y).re}) ω).toNNReal ω) ∂P = f x := by
  have := hB.isProbabilityMeasure
  let V : ℕ → Set (Euc 2) := fun n => U ∩ {y | (1 : ℝ) / (n + 1) <
    (Complex.orthonormalBasisOneI.repr.symm y).re}
  have hc : Continuous (fun y : Euc 2 => (Complex.orthonormalBasisOneI.repr.symm y).re) :=
    Complex.continuous_re.comp Complex.orthonormalBasisOneI.repr.symm.continuous
  have hV : ∀ n, IsOpen (V n) := fun n => hU.inter (isOpen_lt continuous_const hc)
  have hVb : ∀ n, Bornology.IsBounded (V n) := fun n => hUb.subset inter_subset_left
  have hidentity : ∀ n, ∫ ω, f (B (openExitTime B (V n) ω).toNNReal ω) ∂P = f x := by
    intro n
    apply integral_openExit_harmonicNearClosure (by norm_num) hB (hV n) (hVb n)
    apply harmonicNearClosure_iff.mpr
    intro y hy
    apply hh
    have hy' : (1 : ℝ) / (n + 1) ≤ (Complex.orthonormalBasisOneI.repr.symm y).re :=
      closure_minimal (fun z hz => (show (1 : ℝ) / (n + 1) <
        (Complex.orthonormalBasisOneI.repr.symm z).re from hz.2).le)
        (isClosed_le continuous_const hc) hy
    exact lt_of_lt_of_le (by positivity) hy'
  obtain ⟨M, hM⟩ := (hUb.isCompact_closure.insert x).bddAbove_image
    (hf.norm.continuousOn)
  have hbound : ∀ n, ∀ᵐ ω ∂P, ‖f (B (openExitTime B (V n) ω).toNNReal ω)‖ ≤ M := by
    intro n
    filter_upwards [hB.start, hB.cont, ae_openExitTime_ne_top (by norm_num) hB (hVb n)]
      with ω hstart hcont hfin
    apply hM
    refine ⟨_, ?_, rfl⟩
    by_cases hx : x ∈ V n
    · right
      exact closure_mono (show V n ⊆ U from inter_subset_left)
        (frontier_subset_closure (openExitTime_mem_frontier (hV n) hcont (by rwa [hstart]) hfin))
    · left
      have hzero : openExitTime B (V n) ω = 0 :=
        openExitTime_eq_zero_of_not_mem (by rwa [hstart])
      simp [hzero, hstart]
  obtain ⟨C, hCm, hC, -, hCW, -, -⟩ := hB.exists_continuousVersion
  have hsd : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun ω => f (B (openExitTime B (V n) ω).toNNReal ω)) P := by
    intro n
    have hF : Measurable (pathMap C hC) := measurable_pathMap C hCm hC
    have hVo : IsOpen ((fun w : Euc 2 => x + (Real.sqrt 2)⁻¹ • w) ⁻¹' V n) :=
      (hV n).preimage (by fun_prop)
    have hτ := measurable_continuousExitTime hVo 0
    have hG : Measurable (fun γ : BrownianPath 2 =>
        f (x + (Real.sqrt 2)⁻¹ • γ (continuousExitTime
          ((fun w : Euc 2 => x + (Real.sqrt 2)⁻¹ • w) ⁻¹' V n) 0 γ).toNNReal)) := by
      exact hf.measurable.comp ((by fun_prop : Measurable (fun v : Euc 2 =>
        x + (Real.sqrt 2)⁻¹ • v)).comp (measurable_eval_random_time hτ))
    apply (hG.comp hF).aestronglyMeasurable.congr
    filter_upwards [ae_openExitTime_eq_continuousExitTime (by norm_num) hC hCW, hCW] with ω h1 h2
    rw [h1]
    simp only [Function.comp_apply]
    congr 1
    simp [h2, inv_smul_smul₀ hsd]
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n => f (B (openExitTime B (V n) ω).toNNReal ω)) atTop
      (𝓝 (f (B (openExitTime B (U ∩ {y | 0 <
        (Complex.orthonormalBasisOneI.repr.symm y).re}) ω).toNNReal ω))) := by
    filter_upwards [ae_tendsto_openExitPosition_positive_re_cuts hB hU hUb] with ω hω
    exact hf.continuousAt.tendsto.comp hω
  have ht := tendsto_integral_of_dominated_convergence (fun _ => M) hmeas
    (integrable_const M) hbound hlim
  have hconst : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)) := tendsto_const_nhds
  have heq : (fun n => ∫ ω, f (B (openExitTime B (V n) ω).toNNReal ω) ∂P) =
      (fun _ : ℕ => f x) := funext hidentity
  rw [heq] at ht
  exact tendsto_nhds_unique ht hconst

end LatticeProb
