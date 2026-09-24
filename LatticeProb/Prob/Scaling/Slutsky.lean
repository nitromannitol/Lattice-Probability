/-
The Slutsky lemma, generic: if `X_R` converges in law to `X`, tested against every bounded
continuous function of a finite real product, and `Y_R → 0` in probability (in the sup norm of
a finite real product), then `(X_R, Y_R) ⇒ (X, 0)`, and, when `Y_R` lives in the SAME product as
`X_R`, `X_R + Y_R ⇒ X`, again tested against every bounded continuous function: a coordinate
converging to zero in probability does not change a joint limit in law.

Only the real finite-dimensional case is treated (`Fin m → ℝ`, or a product of such). No fresh
construction is needed: Mathlib's own
`MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const` and
`.add_of_tendstoInMeasure_const` (`Mathlib.MeasureTheory.Function.ConvergenceInDistribution`)
ARE Slutsky's theorem, proved in full generality (an arbitrary `SeminormedAddCommGroup` target,
no tightness hypothesis anywhere, the proof goes through a Lipschitz-function approximation of
every bounded continuous test function, in the Portmanteau style) for
`MeasureTheory.TendstoInDistribution` (weak convergence of the pushed-forward laws) and
`MeasureTheory.TendstoInMeasure` (convergence in probability). This module is the short
adaptation layer between those Mathlib structures and the convention of stating a
weak-convergence clause as "tested against every bounded continuous `F`" (matching
`LatticeProb.Scaling.CramerWold.tendsto_integral_of_tendstoInDistribution`) and stating
convergence-in-probability-to-zero with a strict `<` on the tail measure, rather than Mathlib's
own `≤`.

Moved from Parking-Sharpness.
-/
import Mathlib
import LatticeProb.Prob.Scaling.CramerWoldFilter

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace LatticeProb.Scaling.Slutsky

variable {ι : Type*} {l : Filter ι}
  {Ω'' : Type*} [MeasurableSpace Ω''] {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
  {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-! ### The two adaptation lemmas -/

/-- This project's own convention of stating convergence in law as "tested against every bounded
continuous `F`" is exactly Mathlib's `TendstoInDistribution`. -/
theorem tendstoInDistribution_of_tendsto_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {X : ι → Ω'' → E} {Z : Ω' → E}
    (hXm : ∀ i, AEMeasurable (X i) μ'') (hZm : AEMeasurable Z μ')
    (h : ∀ F : BoundedContinuousFunction E ℝ,
      Tendsto (fun i => ∫ ω, F (X i ω) ∂μ'') l (𝓝 (∫ ω', F (Z ω') ∂μ'))) :
    TendstoInDistribution X l Z (fun _ : ι => μ'') μ' := by
  refine ⟨hXm, hZm, ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  simp only [ProbabilityMeasure.coe_mk]
  have heq1 : ∀ i, ∫ x, F x ∂(μ''.map (X i)) = ∫ ω, F (X i ω) ∂μ'' := fun i =>
    integral_map (hXm i) F.continuous.aestronglyMeasurable
  have heq2 : ∫ x, F x ∂(μ'.map Z) = ∫ ω', F (Z ω') ∂μ' :=
    integral_map hZm F.continuous.aestronglyMeasurable
  simpa only [heq1, heq2] using h F

/-- This project's own convention of stating convergence in probability to zero with a strict
`<` on the tail measure is exactly Mathlib's `TendstoInMeasure` at the constant limit `0`. -/
theorem tendstoInMeasure_zero_of_forall_lt {E : Type*} [SeminormedAddCommGroup E]
    {Y : ι → Ω'' → E}
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun i => (μ'' {ω | ε < ‖Y i ω‖}).toReal) l (𝓝 0)) :
    TendstoInMeasure μ'' Y l (fun _ => (0 : E)) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  simp only [sub_zero]
  have hb : Tendsto (fun i => μ''.real {ω | ε / 2 < ‖Y i ω‖}) l (𝓝 0) := by
    simp only [measureReal_def]
    exact h (ε / 2) (by linarith)
  have hle : ∀ i, μ''.real {ω | ε ≤ ‖Y i ω‖} ≤ μ''.real {ω | ε / 2 < ‖Y i ω‖} := by
    intro i
    refine measureReal_mono (fun ω hω => ?_)
    simp only [Set.mem_setOf_eq] at hω ⊢
    linarith
  exact squeeze_zero (fun _ => measureReal_nonneg) hle hb

/-! ### Slutsky's theorem, real finite-dimensional case -/

/-- **Slutsky's theorem, pairing form, real finite-dimensional case.** If `X_R` converges in
law to `X` (tested against every bounded continuous function of `E`) and `Y_R → 0` in
probability (the norm of `E'`), then the pair `(X_R, Y_R)` converges in law to `(X, 0)`, tested
against every bounded continuous function of the product `E × E'`. Stated for abstract `E`, `E'`
carrying the instances a finite real product (`Fin m → ℝ`, or a product of such, e.g.
`(Fin m → ℝ) × (Fin p → ℝ)`) always has; the intended instantiations are exactly those (the real
finite-dimensional case), even though the proof itself only uses the listed instances. -/
theorem tendsto_prodMk_of_tendsto_zero {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    [SecondCountableTopology E'] [l.IsCountablyGenerated]
    {X : ι → Ω'' → E} {Y : ι → Ω'' → E'} {Z : Ω' → E}
    (hXm : ∀ i, AEMeasurable (X i) μ'') (hYm : ∀ i, AEMeasurable (Y i) μ'') (hZm : AEMeasurable Z μ')
    (hX : ∀ F : BoundedContinuousFunction E ℝ,
      Tendsto (fun i => ∫ ω, F (X i ω) ∂μ'') l (𝓝 (∫ ω', F (Z ω') ∂μ')))
    (hY : ∀ ε : ℝ, 0 < ε → Tendsto (fun i => (μ'' {ω | ε < ‖Y i ω‖}).toReal) l (𝓝 0)) :
    ∀ G : BoundedContinuousFunction (E × E') ℝ,
      Tendsto (fun i => ∫ ω, G (X i ω, Y i ω) ∂μ'') l (𝓝 (∫ ω', G (Z ω', 0) ∂μ')) := by
  have hXZ : TendstoInDistribution X l Z (fun _ : ι => μ'') μ' :=
    tendstoInDistribution_of_tendsto_integral hXm hZm hX
  have hYzero : TendstoInMeasure μ'' Y l (fun _ => (0 : E')) :=
    tendstoInMeasure_zero_of_forall_lt hY
  have hpair : TendstoInDistribution (fun i ω => (X i ω, Y i ω)) l (fun ω' => (Z ω', (0 : E')))
      (fun _ : ι => μ'') μ' :=
    TendstoInDistribution.prodMk_of_tendstoInMeasure_const X Y Z hXZ hYzero hYm
  intro G
  exact LatticeProb.Scaling.CramerWold.tendsto_integral_of_tendstoInDistribution hpair G

/-- **Slutsky's theorem, additive form, real finite-dimensional case.** If `X_R` converges in
law to `X` and `Y_R → 0` in probability, both valued in the SAME `E`, then `X_R + Y_R` converges
in law to `X`, tested against every bounded continuous function. Same scope note as
`tendsto_prodMk_of_tendsto_zero`. -/
theorem tendsto_add_of_tendsto_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [l.IsCountablyGenerated]
    {X Y : ι → Ω'' → E} {Z : Ω' → E}
    (hXm : ∀ i, AEMeasurable (X i) μ'') (hYm : ∀ i, AEMeasurable (Y i) μ'') (hZm : AEMeasurable Z μ')
    (hX : ∀ F : BoundedContinuousFunction E ℝ,
      Tendsto (fun i => ∫ ω, F (X i ω) ∂μ'') l (𝓝 (∫ ω', F (Z ω') ∂μ')))
    (hY : ∀ ε : ℝ, 0 < ε → Tendsto (fun i => (μ'' {ω | ε < ‖Y i ω‖}).toReal) l (𝓝 0)) :
    ∀ F : BoundedContinuousFunction E ℝ,
      Tendsto (fun i => ∫ ω, F (X i ω + Y i ω) ∂μ'') l (𝓝 (∫ ω', F (Z ω') ∂μ')) := by
  have hXZ : TendstoInDistribution X l Z (fun _ : ι => μ'') μ' :=
    tendstoInDistribution_of_tendsto_integral hXm hZm hX
  have hYzero : TendstoInMeasure μ'' Y l (fun _ => (0 : E)) :=
    tendstoInMeasure_zero_of_forall_lt hY
  have hsum : TendstoInDistribution (fun i ω => X i ω + Y i ω) l (fun ω' => Z ω' + 0)
      (fun _ : ι => μ'') μ' :=
    TendstoInDistribution.add_of_tendstoInMeasure_const hXZ hYzero hYm
  intro F
  have h := LatticeProb.Scaling.CramerWold.tendsto_integral_of_tendstoInDistribution hsum F
  simpa only [add_zero] using h

/-! ### Combining finitely many scalar convergences to zero into one vector convergence -/

/-- **Finitely many scalar convergences-to-zero-in-probability combine into one
sup-norm convergence-to-zero.** Needed to package `q` separate scalar clauses (one per test
function) into the single vector-valued hypothesis `tendsto_prodMk_of_tendsto_zero`/
`tendsto_add_of_tendsto_zero` consume. -/
theorem tendsto_zero_pi_of_forall_tendsto_zero {q : ℕ} {Y : ι → Ω'' → Fin q → ℝ}
    (h : ∀ c : Fin q, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun i => (μ'' {ω | ε < |Y i ω c|}).toReal) l (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun i => (μ'' {ω | ε < ‖Y i ω‖}).toReal) l (𝓝 0) := by
  intro ε hε
  have hset : ∀ i, {ω : Ω'' | ε < ‖Y i ω‖} = ⋃ c : Fin q, {ω | ε < |Y i ω c|} := by
    intro i
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hlt
      by_contra hc
      push Not at hc
      have hall : ∀ c, ‖Y i ω c‖ ≤ ε := fun c => by rw [Real.norm_eq_abs]; exact hc c
      exact absurd hlt (not_lt.2 ((pi_norm_le_iff_of_nonneg hε.le).2 hall))
    · rintro ⟨c, hc⟩
      have h1 : ‖Y i ω c‖ ≤ ‖Y i ω‖ := norm_le_pi_norm (Y i ω) c
      rw [Real.norm_eq_abs] at h1
      linarith
  have htop : ∀ i c, μ'' {ω | ε < |Y i ω c|} ≠ ⊤ := fun i c => measure_ne_top _ _
  have hub : ∀ i, (μ'' {ω | ε < ‖Y i ω‖}).toReal
      ≤ ∑ c : Fin q, (μ'' {ω | ε < |Y i ω c|}).toReal := by
    intro i
    rw [hset i, ← ENNReal.toReal_sum (fun c _ => htop i c)]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 (fun c _ => htop i c))
      (measure_iUnion_fintype_le _ _)
  have hb : Tendsto (fun i => ∑ c : Fin q, (μ'' {ω | ε < |Y i ω c|}).toReal) l (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin q)) (fun c _ => h c ε hε)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hub hb

end LatticeProb.Scaling.Slutsky
end
