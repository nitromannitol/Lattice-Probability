/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.CondIndepAEDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepDetermined
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import Mathlib.MeasureTheory.Function.FactorsThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge: σ-algebra form of "determined by" and `AEDeterminedBy`

For a standard Borel target `β`, `σ(Y)` is a.s. determined by `σ(X)`
(`LQGMetric.AEDeterminedSigma`) iff `Y = F ∘ X` a.s. for a measurable `F`
(`LQGMetric.AEDeterminedBy`, FOUNDATIONS §4 and §9a). With this the two-copies criterion
(LM S5.d) and LM S5.c conclude "`D` is a.s. determined by `h`" in the project's statement form:
`LQGMetric.aeDeterminedBy_of_condIndepEv_of_ae_eq`, `LQGMetric.aeDeterminedBy_of_indep_of_sup`.

Proof: a measurable injection `ψ : β → (ℕ → Bool)` (mathlib
`measurable_injection_nat_bool_of_countablySeparated`, a measurable embedding since `β` is
standard Borel) codes `Y` by countably many events `{ψ (Y ·) n}`; replacing each by an a.s.
equal `G`-event gives a `G`-measurable code `Φ`, and `Y = g ∘ Φ` a.s. for a measurable left
inverse `g` of `ψ`. Then Doob–Dynkin (mathlib `Measurable.exists_eq_measurable_comp`).
Own elementary argument (standard).
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace LQGMetric

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `σ(Y)` is a.s. determined by `G` and `β` is standard Borel, then `Y` is a.s. equal to a
`G`-measurable random variable. -/
theorem exists_ae_eq_measurable_of_aeDeterminedSigma {β : Type*} [mβ : MeasurableSpace β]
    [StandardBorelSpace β] [Nonempty β] {G : MeasurableSpace Ω} {Y : Ω → β}
    (h : AEDeterminedSigma (mβ.comap Y) G μ) :
    ∃ Y' : Ω → β, Measurable[G] Y' ∧ Y =ᵐ[μ] Y' := by
  classical
  obtain ⟨ψ, hψm, hψi⟩ := measurable_injection_nat_bool_of_countablySeparated β
  have hψe : MeasurableEmbedding ψ := hψm.measurableEmbedding hψi
  obtain ⟨g, hgm, hg⟩ := hψe.exists_measurable_extend measurable_id fun _ => inferInstance
  have hB : ∀ n, MeasurableSet[mβ] {b | ψ b n = true} := fun n =>
    ((measurable_pi_apply n).comp hψm) (measurableSet_singleton true)
  choose C hC hYC using fun n => h (Y ⁻¹' {b | ψ b n = true}) ⟨_, hB n, rfl⟩
  let Φ : Ω → ℕ → Bool := fun ω n => decide (ω ∈ C n)
  have hΦ : Measurable[G] Φ := by
    refine measurable_pi_iff.2 fun n => measurable_to_countable' fun x => ?_
    cases x
    · convert (hC n).compl using 1
      ext ω; simp [Φ]
    · convert hC n using 1
      ext ω; simp [Φ]
  have hae : ∀ᵐ ω ∂μ, ψ (Y ω) = Φ ω := by
    have hall : ∀ᵐ ω ∂μ, ∀ n, (ω ∈ Y ⁻¹' {b | ψ b n = true} ↔ ω ∈ C n) :=
      ae_all_iff.2 fun n => eventuallyEqSet_iff.1 (hYC n)
    filter_upwards [hall] with ω hω
    funext n
    have := hω n
    simp only [mem_preimage, mem_ofPred_eq] at this
    by_cases hc : ω ∈ C n
    · simpa [Φ, this.2 hc] using hc
    · have : ψ (Y ω) n ≠ true := fun h' => hc (this.1 h')
      simp [Φ, hc] at this ⊢
      exact this
  refine ⟨g ∘ Φ, hgm.comp hΦ, ?_⟩
  filter_upwards [hae] with ω hω
  simp only [Function.comp_apply, ← hω]
  exact (congrFun hg (Y ω)).symm

/-- **Bridge.** For a standard Borel target, `σ(Y)` a.s. determined by `σ(X)` gives
`AEDeterminedBy Y X`. -/
theorem aeDeterminedBy_of_aeDeterminedSigma {α β : Type*} [mα : MeasurableSpace α]
    [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] {X : Ω → α} {Y : Ω → β}
    (h : AEDeterminedSigma (mβ.comap Y) (mα.comap X) μ) : AEDeterminedBy Y X μ := by
  obtain ⟨Y', hY'm, hYY'⟩ := exists_ae_eq_measurable_of_aeDeterminedSigma h
  obtain ⟨F, hF, rfl⟩ := hY'm.exists_eq_measurable_comp
  exact ⟨F, hF, hYY'⟩

/-- **LM S5.d** (two-copies criterion) in `AEDeterminedBy` form: if `D` and `D'` are
conditionally independent given `σ(X)` and `D = D'` a.s., then `D` is a.s. determined by `X`. -/
theorem aeDeterminedBy_of_condIndepEv_of_ae_eq [IsProbabilityMeasure μ] {α β : Type*}
    [mα : MeasurableSpace α] [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    {X : Ω → α} (hX : Measurable[mΩ] X) {D D' : Ω → β} (hD : Measurable[mΩ] D)
    (hDD' : CondIndepEv (mα.comap X) (mβ.comap D) (mβ.comap D') μ) (heq : D =ᵐ[μ] D') :
    AEDeterminedBy D X μ :=
  aeDeterminedBy_of_aeDeterminedSigma
    (aeDeterminedSigma_of_condIndepEv_of_ae_eq hX.comap_le hD hDD' heq)

end LQGMetric
