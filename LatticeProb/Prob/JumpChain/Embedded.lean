import LatticeProb.Prob.JumpChain.History
import LatticeProb.Prob.JumpChain.Uniformization

/-!
# Marginals of the embedded discrete chain

The state recorded at index `n` has the initial law transported through the `n`th
power of the uniformized transition kernel. This conclusion is derived from the
finite-prefix law of the existing infinite history construction.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Preorder Function

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

namespace BoundedRates

/-- The state marginal of a history step is exactly the embedded transition kernel. -/
theorem historyStep_map_state (rates : BoundedRates S) (n : ℕ) :
    (rates.historyStep n).map Prod.fst =
      rates.kernel.comap (fun h ↦ (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1) (by fun_prop) := by
  ext h : 1
  rw [Kernel.map_apply _ measurable_fst]
  unfold historyStep
  rw [Kernel.prod_apply, Measure.map_fst_prod, measure_univ, one_smul]

/-- A recorded state advances by one application of the embedded transition kernel. -/
theorem historyLaw_map_state_succ (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (rates.historyLaw μ).map (fun h ↦ (h (n + 1)).1) =
      rates.kernel ∘ₘ (rates.historyLaw μ).map (fun h ↦ (h n).1) := by
  let ν := (rates.historyLaw μ).map (frestrictLe n)
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
  have hpair : ν ⊗ₘ rates.historyStep n =
      (rates.historyLaw μ).map (fun h ↦ (frestrictLe n h, h (n + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have hnext := congrArg (fun ξ ↦ ξ.map Prod.snd) hpair
  change (ν ⊗ₘ rates.historyStep n).snd = _ at hnext
  rw [Measure.snd_compProd, Measure.map_map measurable_snd (by fun_prop)] at hnext
  have hstate := congrArg (fun ξ ↦ ξ.map Prod.fst) hnext
  rw [Measure.map_comp _ _ measurable_fst, rates.historyStep_map_state,
    Measure.map_map measurable_fst (by fun_prop)] at hstate
  change _ = (rates.historyLaw μ).map (fun h ↦ (h (n + 1)).1) at hstate
  rw [← hstate]
  ext a ha
  rw [Measure.bind_apply ha (Kernel.aemeasurable _),
    Measure.bind_apply ha (Kernel.aemeasurable _)]
  conv_rhs => rw [lintegral_map (rates.kernel.measurable_coe ha) (by fun_prop)]
  change (∫⁻ h, rates.kernel (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1 a
      ∂((rates.historyLaw μ).map (frestrictLe n))) = _
  rw [lintegral_map (by fun_prop) (measurable_frestrictLe n)]
  rfl

/-- The index-`n` embedded state has the exact `n`-step transition law from the initial law. -/
theorem historyLaw_map_state (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (rates.historyLaw μ).map (fun h ↦ (h n).1) = (rates.kernel ^ n) ∘ₘ μ := by
  induction n with
  | zero =>
    rw [rates.historyLaw_map_initialState]
    exact Measure.id_comp.symm
  | succ n ih =>
    rw [rates.historyLaw_map_state_succ, ih, Measure.comp_assoc, pow_succ']
    rfl

end BoundedRates

end

end LatticeProb.JumpChain
