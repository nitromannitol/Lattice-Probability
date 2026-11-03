/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovIndep at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Independence passes to almost sure limits (task P2-MARKOV, part 3)

`indep_comap_of_tendsto_ae`: if `Zₙ → Z` almost surely (values in a separable Banach space) and
every `Zₙ` is independent of a σ-algebra `m`, then so is `Z`. Used for the germ σ-algebra
`⋂_ε σ(h|_{B_ε(ℂ∖U)})` in the Markov property: the zero-boundary part is a limit of Dirichlet
pairings `(h, fₙ)_∇` with `supp fₙ ⋐ U`, each independent of `σ(h|_{B_ε(ℂ∖U)})` for small `ε`.

Proof: for `t ∈ m`, `(P|_t)∘Zₙ⁻¹ = P(t) · P∘Zₙ⁻¹`; take characteristic functions and pass to
the limit by dominated convergence (`|e^{iL(x)}| = 1`); conclude by `Measure.ext_of_charFunDual`.
Standard (e.g. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Lemma 3.6 ff., where
independence is characterized by characteristic functions); own write-up of the textbook
argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Complex

namespace LQGMetric
namespace MarkovIndep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

/-- the law of `Y` on the event `t` (unnormalized) -/
def resMap (P : Measure Ω) (t : Set Ω) (Y : Ω → E) : Measure E := (P.restrict t).map Y

/-- the law of `Y` -/
def lawMap (P : Measure Ω) (Y : Ω → E) : Measure E := P.map Y

instance (t : Set Ω) (Y : Ω → E) : IsFiniteMeasure (resMap P t Y) := by
  unfold resMap; infer_instance

instance (c : ENNReal) [Fact (c ≠ ⊤)] (Y : Ω → E) : IsFiniteMeasure (c • lawMap P Y) := by
  unfold lawMap; exact Measure.smul_finite _ Fact.out

lemma map_restrict_eq_of_indep {Y : Ω → E} (hY : Measurable Y) {m : MeasurableSpace Ω}
    (hind : Indep (MeasurableSpace.comap Y inferInstance) m P) {t : Set Ω}
    (ht : MeasurableSet[m] t) : resMap P t Y = P t • lawMap P Y := by
  ext B hB
  rw [resMap, lawMap, Measure.map_apply hY hB, Measure.restrict_apply (hY hB),
    Measure.smul_apply, Measure.map_apply hY hB, smul_eq_mul, (Indep_iff _ _ _).1 hind _ _ ⟨B, hB, rfl⟩ ht,
    mul_comm]

lemma indep_of_map_restrict_eq {Z : Ω → E} (hZ : Measurable Z) {m : MeasurableSpace Ω}
    (h : ∀ t, MeasurableSet[m] t → resMap P t Z = P t • lawMap P Z) :
    Indep (MeasurableSpace.comap Z inferInstance) m P := by
  rw [Indep_iff]
  rintro _ t ⟨B, hB, rfl⟩ ht
  have := congrArg (fun μ : Measure E => μ B) (h t ht)
  simp only [resMap, lawMap, Measure.map_apply hZ hB, Measure.restrict_apply (hZ hB),
    Measure.smul_apply, smul_eq_mul] at this
  rw [this, mul_comm]

lemma tendsto_setIntegral_char {Z : Ω → E} {Zn : ℕ → Ω → E} (hZ : Measurable Z)
    (hZn : ∀ n, Measurable (Zn n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (Z ω))) (L : StrongDual ℝ E)
    (t : Set Ω) :
    Tendsto (fun n => ∫ ω in t, exp (L (Zn n ω) * I) ∂P) atTop
      (𝓝 (∫ ω in t, exp (L (Z ω) * I) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
    (integrable_const _) (fun n => Eventually.of_forall fun ω => ?_) ?_
  · exact (Measurable.cexp ((Complex.measurable_ofReal.comp
      (L.continuous.measurable.comp (hZn n))).mul_const _)).aestronglyMeasurable
  · rw [norm_exp_ofReal_mul_I]
  · refine ae_restrict_of_ae ?_
    filter_upwards [hlim] with ω hω
    exact ((continuous_exp.comp ((continuous_ofReal.comp L.continuous).mul
      continuous_const)).tendsto _).comp hω

/-- **Independence passes to a.s. limits.** -/
theorem indep_comap_of_tendsto_ae {Z : Ω → E} {Zn : ℕ → Ω → E} (hZ : Measurable Z)
    (hZn : ∀ n, Measurable (Zn n)) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (Z ω)))
    (hind : ∀ n, Indep (MeasurableSpace.comap (Zn n) inferInstance) m P) :
    Indep (MeasurableSpace.comap Z inferInstance) m P := by
  refine indep_of_map_restrict_eq hZ fun t ht => ?_
  have : Fact (P t ≠ ⊤) := ⟨measure_ne_top P t⟩
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [resMap, lawMap, charFunDual_apply, charFunDual_apply, integral_map hZ.aemeasurable
    (by fun_prop), integral_smul_measure, integral_map hZ.aemeasurable (by fun_prop)]
  have key : ∀ n, ∫ ω in t, exp (L (Zn n ω) * I) ∂P =
      (P t).toReal • ∫ ω, exp (L (Zn n ω) * I) ∂P := by
    intro n
    have h1 := congrArg (fun μ : Measure E => ∫ x, exp (L x * I) ∂μ)
      (map_restrict_eq_of_indep (hZn n) (hind n) ht)
    simp only [resMap, lawMap] at h1
    rwa [integral_map (hZn n).aemeasurable (by fun_prop), integral_smul_measure,
      integral_map (hZn n).aemeasurable (by fun_prop)] at h1
  have hA := tendsto_setIntegral_char hZ hZn hlim L t
  have hB : Tendsto (fun n => (P t).toReal • ∫ ω, exp (L (Zn n ω) * I) ∂P) atTop
      (𝓝 ((P t).toReal • ∫ ω, exp (L (Z ω) * I) ∂P)) := by
    have := tendsto_setIntegral_char hZ hZn hlim L Set.univ
    simp only [Measure.restrict_univ] at this
    exact this.const_smul _
  simp_rw [key] at hA
  exact tendsto_nhds_unique hA hB

/-- **Independence passes to limits in probability.** -/
theorem indep_comap_of_tendstoInMeasure {Z : Ω → E} {Zn : ℕ → Ω → E} (hZ : Measurable Z)
    (hZn : ∀ n, Measurable (Zn n)) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hlim : TendstoInMeasure P Zn atTop Z)
    (hind : ∀ n, Indep (MeasurableSpace.comap (Zn n) inferInstance) m P) :
    Indep (MeasurableSpace.comap Z inferInstance) m P := by
  obtain ⟨ns, -, hns⟩ := hlim.exists_seq_tendsto_ae
  exact indep_comap_of_tendsto_ae hZ (fun k => hZn (ns k)) hm hns fun k => hind (ns k)

omit [IsProbabilityMeasure P] in
/-- coordinatewise convergence in probability of finitely many coordinates -/
theorem tendstoInMeasure_pi [IsFiniteMeasure P] {ι : Type*} [Fintype ι] {Z : Ω → ι → ℝ}
    {Zn : ℕ → Ω → ι → ℝ}
    (h : ∀ i, TendstoInMeasure P (fun n ω => Zn n ω i) atTop (fun ω => Z ω i)) :
    TendstoInMeasure P Zn atTop Z := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hsub : ∀ n, {ω | ε ≤ ‖Zn n ω - Z ω‖} ⊆ ⋃ i, {ω | ε ≤ ‖Zn n ω i - Z ω i‖} := by
    intro n ω hω
    by_contra hc
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hc
    exact (not_le.2 ((pi_norm_lt_iff hε).2 fun i => by simpa using hc i)) hω
  have hsum : Tendsto (fun n => ∑ i, P {ω | ε ≤ ‖Zn n ω i - Z ω i‖}) atTop (𝓝 0) := by
    rw [show (0 : ENNReal) = ∑ _i : ι, 0 by simp]
    exact tendsto_finset_sum _ fun i _ => (tendstoInMeasure_iff_norm.1 (h i)) ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => zero_le)
    fun n => (measure_mono (hsub n)).trans (measure_iUnion_fintype_le _ _)

end MarkovIndep
end LQGMetric
