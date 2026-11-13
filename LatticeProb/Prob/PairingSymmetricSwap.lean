import Mathlib
import LatticeProb.Prob.ProductTestFunctionsDetermine
import LatticeProb.Prob.LawFieldPairingContinuous
import LatticeProb.Prob.ConditionalLawCriterion

/-!
# A symmetric reversibility pairing makes the space-time measure swap invariant

For a law field `P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))` (a continuous family `z ↦ P_z` of laws of
paths), a time `s` and a locally finite measure `μ` on `ℂ`, the space-time measure
`m_s(dz, dw) = μ(dz) P_z(X_s ∈ dw)` is `μ ⊗ₘ evalLawKernel P s`, where `evalLawKernel P s` is the Markov
kernel `z ↦ P_z ∘ X_s⁻¹`. If the pairing is symmetric,
`∫ f(z) E_{P_z}[g(X_s)] dμ(z) = ∫ g(z) E_{P_z}[f(X_s)] dμ(z)` for Lipschitz compactly supported `f, g`
(or only for `f, g` in a fixed countable family), then `m_s` equals its image under the swap
`(z, w) ↦ (w, z)`.

Indeed `∫ f(z) g(w) dm_s = ∫ f(z) E_{P_z}[g(X_s)] dμ(z)` and the same integral against the swapped measure
is `∫ g(z) E_{P_z}[f(X_s)] dμ(z)`, so the two measures agree on products of Lipschitz compactly supported
functions; both are locally finite (the measure of `B̄(z, 1) × ℂ` is `μ(B̄(z, 1))`), so they are equal by
`ext_of_integral_mul_lipschitz_compactSupport`.

* `compProd_evalLawKernel_swap_of_pairing_symm`: the symmetric pairing for all Lipschitz compactly
  supported `f, g` gives `(μ ⊗ₘ evalLawKernel P s).map Prod.swap = μ ⊗ₘ evalLawKernel P s`.
* `exists_countable_compProd_evalLawKernel_swap_of_pairing_symm`: a countable family of Lipschitz
  compactly supported `f, g` suffices, uniformly in `μ`, `P` and `s`.
-/

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- The law of the position at time `s` under `P_z` depends measurably on `z`. -/
theorem measurable_map_eval_lawField (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))) (s : ℝ≥0) :
    Measurable fun z => (P z : Measure C(ℝ≥0, ℂ)).map fun X : C(ℝ≥0, ℂ) => X s := by
  have hev : Measurable fun X : C(ℝ≥0, ℂ) => X s := (continuous_eval_const s).measurable
  have hprob : ∀ z, IsProbabilityMeasure
      ((P z : Measure C(ℝ≥0, ℂ)).map fun X : C(ℝ≥0, ℂ) => X s) :=
    fun z => (Measure.isProbabilityMeasure_map_iff hev.aemeasurable).2 inferInstance
  refine measurable_measure_of_measurable_integral_boundedContinuous fun f => ?_
  have hF : Continuous fun ν : ProbabilityMeasure C(ℝ≥0, ℂ) =>
      ∫ X, f (X s) ∂(ν : Measure C(ℝ≥0, ℂ)) :=
    continuous_iff_continuousAt.2 fun _ => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
      tendsto_id (f.compContinuous ⟨fun X : C(ℝ≥0, ℂ) => X s, continuous_eval_const s⟩)
  have h1 : Continuous fun z => ∫ X, f (X s) ∂(P z : Measure C(ℝ≥0, ℂ)) := hF.comp P.continuous
  have h2 : Continuous fun z =>
      ∫ x, f x ∂((P z : Measure C(ℝ≥0, ℂ)).map fun X : C(ℝ≥0, ℂ) => X s) := by
    refine h1.congr fun z => ?_
    rw [integral_map hev.aemeasurable f.continuous.aestronglyMeasurable]
  exact h2.measurable

/-- The Markov kernel `z ↦ P_z ∘ X_s⁻¹` of the position at time `s` under the law field `P`. -/
noncomputable def evalLawKernel (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))) (s : ℝ≥0) : Kernel ℂ ℂ where
  toFun z := (P z : Measure C(ℝ≥0, ℂ)).map fun X : C(ℝ≥0, ℂ) => X s
  measurable' := measurable_map_eval_lawField P s

theorem evalLawKernel_apply (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))) (s : ℝ≥0) (z : ℂ) :
    evalLawKernel P s z = (P z : Measure C(ℝ≥0, ℂ)).map fun X : C(ℝ≥0, ℂ) => X s :=
  rfl

instance (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))) (s : ℝ≥0) : IsMarkovKernel (evalLawKernel P s) :=
  ⟨fun z => by
    rw [evalLawKernel_apply]
    exact (Measure.isProbabilityMeasure_map_iff
      (continuous_eval_const s).measurable.aemeasurable).2 inferInstance⟩

section SpaceTime

variable (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ)))
  (s : ℝ≥0)

theorem compProd_evalLawKernel_closedBall_prod_univ_lt_top (c : ℂ) (r : ℝ) :
    (μ ⊗ₘ evalLawKernel P s) (closedBall c r ×ˢ univ) < ∞ := by
  rw [Measure.compProd_apply_prod measurableSet_closedBall MeasurableSet.univ]
  simp only [measure_univ, lintegral_const, Measure.restrict_apply_univ, one_mul]
  exact measure_closedBall_lt_top

/-- The space-time measure `μ(dz) P_z(X_s ∈ dw)` is locally finite. -/
theorem isLocallyFiniteMeasure_compProd_evalLawKernel :
    IsLocallyFiniteMeasure (μ ⊗ₘ evalLawKernel P s) :=
  ⟨fun p => ⟨closedBall p.1 1 ×ˢ univ, prod_mem_nhds (closedBall_mem_nhds _ one_pos) univ_mem,
    compProd_evalLawKernel_closedBall_prod_univ_lt_top μ P s p.1 1⟩⟩

/-- The swapped space-time measure `μ(dw) P_w(X_s ∈ dz)` is locally finite. -/
theorem isLocallyFiniteMeasure_map_swap_compProd_evalLawKernel :
    IsLocallyFiniteMeasure ((μ ⊗ₘ evalLawKernel P s).map Prod.swap) := by
  refine ⟨fun p => ⟨univ ×ˢ closedBall p.2 1, prod_mem_nhds univ_mem (closedBall_mem_nhds _ one_pos),
    ?_⟩⟩
  rw [Measure.map_apply measurable_swap (MeasurableSet.univ.prod measurableSet_closedBall),
    preimage_swap_prod]
  exact compProd_evalLawKernel_closedBall_prod_univ_lt_top μ P s p.2 1

variable {μ}

/-- `∫ f(z) g(w) dm_s(z, w) = ∫ f(z) E_{P_z}[g(X_s)] dμ(z)`. -/
theorem integral_mul_compProd_evalLawKernel {f g : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ p, f p.1 * g p.2 ∂(μ ⊗ₘ evalLawKernel P s) =
      ∫ z, f z * ∫ X, g (X s) ∂(P z : Measure C(ℝ≥0, ℂ)) ∂μ := by
  have hlf := isLocallyFiniteMeasure_compProd_evalLawKernel μ P s
  have hint : Integrable (fun p : ℂ × ℂ => f p.1 * g p.2) (μ ⊗ₘ evalLawKernel P s) :=
    ((hf.comp continuous_fst).mul (hg.comp continuous_snd)).integrable_of_hasCompactSupport
      (hasCompactSupport_mul_fst_snd hfc hgc)
  rw [Measure.integral_compProd hint]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show ∫ w, f z * g w ∂(evalLawKernel P s z) = f z * ∫ X, g (X s) ∂(P z : Measure C(ℝ≥0, ℂ))
  rw [evalLawKernel_apply, integral_const_mul,
    integral_map (continuous_eval_const s).measurable.aemeasurable hg.aestronglyMeasurable]

/-- `∫ f(z) g(w) d(m_s ∘ swap⁻¹)(z, w) = ∫ g(z) E_{P_z}[f(X_s)] dμ(z)`. -/
theorem integral_mul_map_swap_compProd_evalLawKernel {f g : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ p, f p.1 * g p.2 ∂((μ ⊗ₘ evalLawKernel P s).map Prod.swap) =
      ∫ z, g z * ∫ X, f (X s) ∂(P z : Measure C(ℝ≥0, ℂ)) ∂μ := by
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => f p.1 * g p.2)
      ((μ ⊗ₘ evalLawKernel P s).map Prod.swap) :=
    ((hf.comp continuous_fst).mul (hg.comp continuous_snd)).aestronglyMeasurable
  rw [integral_map measurable_swap.aemeasurable hm,
    ← integral_mul_compProd_evalLawKernel P s hg hgc hf hfc]
  exact integral_congr_ae (Eventually.of_forall fun p => mul_comm (f p.2) (g p.1))

end SpaceTime

/-- **A symmetric reversibility pairing makes the space-time measure swap invariant.** If
`∫ f(z) E_{P_z}[g(X_s)] dμ(z) = ∫ g(z) E_{P_z}[f(X_s)] dμ(z)` for all Lipschitz compactly supported
`f, g : ℂ → ℝ`, then `m_s = μ ⊗ₘ evalLawKernel P s` equals its image under `(z, w) ↦ (w, z)`. -/
theorem compProd_evalLawKernel_swap_of_pairing_symm {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))) (s : ℝ≥0)
    (h : ∀ f g : ℂ → ℝ, (∃ K, LipschitzWith K f) → HasCompactSupport f → (∃ K, LipschitzWith K g) →
      HasCompactSupport g →
      ∫ z, f z * (∫ X, g (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ =
        ∫ z, g z * (∫ X, f (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ) :
    (μ ⊗ₘ evalLawKernel P s).map Prod.swap = μ ⊗ₘ evalLawKernel P s := by
  have h1 := isLocallyFiniteMeasure_compProd_evalLawKernel μ P s
  have h2 := isLocallyFiniteMeasure_map_swap_compProd_evalLawKernel μ P s
  refine ext_of_integral_mul_lipschitz_compactSupport fun f g hfL hfc hgL hgc => ?_
  obtain ⟨Kf, hKf⟩ := hfL
  obtain ⟨Kg, hKg⟩ := hgL
  rw [integral_mul_map_swap_compProd_evalLawKernel P s hKf.continuous hfc hKg.continuous hgc,
    integral_mul_compProd_evalLawKernel P s hKf.continuous hfc hKg.continuous hgc]
  exact (h f g ⟨Kf, hKf⟩ hfc ⟨Kg, hKg⟩ hgc).symm

/-- **The countable form.** There is a countable family `𝓕` of Lipschitz compactly supported functions
such that, for every locally finite `μ`, law field `P` and time `s`, the symmetry of the pairing for
`f, g ∈ 𝓕` makes `m_s = μ ⊗ₘ evalLawKernel P s` swap invariant. -/
theorem exists_countable_compProd_evalLawKernel_swap_of_pairing_symm :
    ∃ 𝓕 : Set (ℂ → ℝ), 𝓕.Countable ∧
      (∀ f ∈ 𝓕, (∃ K, LipschitzWith K f) ∧ HasCompactSupport f) ∧
      ∀ (μ : Measure ℂ), IsLocallyFiniteMeasure μ →
        ∀ (P : C(ℂ, ProbabilityMeasure C(ℝ≥0, ℂ))) (s : ℝ≥0),
          (∀ f ∈ 𝓕, ∀ g ∈ 𝓕, ∫ z, f z * (∫ X, g (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ =
            ∫ z, g z * (∫ X, f (X s) ∂(P z : Measure C(ℝ≥0, ℂ))) ∂μ) →
          (μ ⊗ₘ evalLawKernel P s).map Prod.swap = μ ⊗ₘ evalLawKernel P s := by
  obtain ⟨𝓕, hcount, h𝓕, hdet⟩ := exists_countable_lipschitz_compactSupport_determining
  refine ⟨𝓕, hcount, h𝓕, fun μ hμ P s h => ?_⟩
  refine hdet _ _ (isLocallyFiniteMeasure_map_swap_compProd_evalLawKernel μ P s)
    (isLocallyFiniteMeasure_compProd_evalLawKernel μ P s) fun f hf g hg => ?_
  obtain ⟨⟨Kf, hKf⟩, hfc⟩ := h𝓕 f hf
  obtain ⟨⟨Kg, hKg⟩, hgc⟩ := h𝓕 g hg
  rw [integral_mul_map_swap_compProd_evalLawKernel P s hKf.continuous hfc hKg.continuous hgc,
    integral_mul_compProd_evalLawKernel P s hKf.continuous hfc hKg.continuous hgc]
  exact (h f hf g hg).symm

end LatticeProb
