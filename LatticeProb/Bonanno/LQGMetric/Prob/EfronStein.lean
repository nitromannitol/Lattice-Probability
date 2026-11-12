/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.EfronStein at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.CondVar
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G3SchemeCI

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Efron–Stein inequality (σ-algebra form)

Let `G i` (`i ∈ s`, `s` a finite set) be independent sub-σ-algebras and let `F ∈ L²` be measurable
with respect to `⨆ i ∈ s, G i`. Then
`Var F ≤ ∑ i ∈ s, E[(F - E[F | ⨆ j ∈ s \ {i}, G j])²]`
(`LQGMetric.efronStein_sigma`). This is LM (5.1) (Gwynne–Miller, *Local metrics of the Gaussian
free field*, arXiv:1905.00379, `local-metrics-final.tex` lines 893–896): the right side is
`∑ i E[Var[F | {X_j}_{j ≠ i}]]` with `G j = σ(X_j)`. The σ-algebra form covers independent blocks
(DDDF, arXiv:1904.08021, `tightness.tex` lines 1081–1090). The resampling forms are in
`LQGMetric.Prob.EfronSteinResample`.

## Source

Efron–Stein, *The jackknife estimate of variance*, Ann. Statist. 9 (1981); Steele, *An Efron–Stein
inequality for nonsymmetric statistics*, Ann. Statist. 14 (1986); R. van Handel, *Probability in
High Dimension* (lecture notes, Princeton, 2016), §2.1 (tensorization of variance; theorem
numbers not checked), whose proof writes `F - E F` as a sum of martingale increments
`E[F | G_1..G_k] - E[F | G_1..G_{k-1}]` and bounds each increment by Jensen, after the identity
`E[E_k F | G_1..G_k] = E[F | G_1..G_{k-1}]` (independence). We follow this proof, organised as an
induction on `s`: the first increment is split off with the law of total variance (mathlib
`integral_condVar_add_variance_condExp`) and the rest is the induction hypothesis applied to
`E[F | ⨆ j ∈ s, G j]`.

The independence identity is `condExp_sup_indep_eq`: if `Y` is `H`-measurable, `A ≤ H` and `G` is
independent of `H`, then `E[Y | G ⊔ A] = E[Y | A]` (Kallenberg, *Foundations of Modern
Probability*, 2nd ed., Prop. 6.6). Its π-λ proof is ported from QuantumZipper
`QuantumZipper.Thm18Asm.condExp_indicator_sup_eq` (`Proofs/Thm18/G3SchemeCI.lean`, indicator case),
generalised to integrable `Y`; the π-system `interPi` is reused from there.

The public project `YuanheZ/lean-stat-learning-theory` (Apache 2.0, commit `d0f506f`,
`SLT/EfronStein.lean`) proves Efron–Stein for product measures on `Fin n → Ω` (one common
coordinate space); it does not cover independent σ-algebras / heterogeneous blocks, so we do not
port it.
-/

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal

namespace LQGMetric

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}

/-- For `f` measurable w.r.t. `H` and `G` independent of `H`: `∫_{g ∩ a} f = P(g) ∫_a f`. -/
lemma es_setIntegral_inter_indep [IsProbabilityMeasure μ] {G H : MeasurableSpace Ω}
    (hH : H ≤ m₀) (hG : G ≤ m₀) (hind : Indep G H μ) {f : Ω → ℝ}
    (hfm : StronglyMeasurable[H] f) (hfi : Integrable f μ) {a g : Set Ω}
    (ha : MeasurableSet[H] a) (hg : MeasurableSet[G] g) :
    ∫ x in g ∩ a, f x ∂μ = μ.real g * ∫ x in a, f x ∂μ := by
  have ha0 : MeasurableSet[m₀] a := hH a ha
  have hg0 : MeasurableSet[m₀] g := hG g hg
  have hI : IndepFun (g.indicator (fun _ => (1 : ℝ))) (a.indicator f) μ := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
    · exact measurable_iff_comap_le.1 (measurable_const.indicator hg)
    · exact measurable_iff_comap_le.1 (hfm.measurable.indicator ha)
  have hmul := hI.integral_mul_eq_mul_integral
    ((measurable_const.indicator hg0).aestronglyMeasurable)
    ((hfi.indicator ha0).aestronglyMeasurable)
  have e1 : (fun x => g.indicator (fun _ => (1 : ℝ)) x * a.indicator f x) =
      (g ∩ a).indicator f := by
    funext x; by_cases hxa : x ∈ a <;> by_cases hxg : x ∈ g <;> simp [hxa, hxg]
  rw [← integral_indicator (hg0.inter ha0), ← e1, ← Pi.mul_def, hmul,
    integral_indicator ha0, integral_indicator hg0, setIntegral_const, smul_eq_mul, mul_one]

/-- **Conditioning on an independent σ-algebra.** If `Y` is `H`-measurable and integrable,
`A ≤ H`, and `G` is independent of `H`, then `E[Y | G ⊔ A] = E[Y | A]` a.e. -/
theorem condExp_sup_indep_eq [IsProbabilityMeasure μ] {A G H : MeasurableSpace Ω}
    (hAH : A ≤ H) (hH : H ≤ m₀) (hG : G ≤ m₀) (hind : Indep G H μ) {Y : Ω → ℝ}
    (hYm : StronglyMeasurable[H] Y) (hYi : Integrable Y μ) :
    μ[Y | G ⊔ A] =ᵐ[μ] μ[Y | A] := by
  have hA : A ≤ m₀ := hAH.trans hH
  have hsup : G ⊔ A ≤ m₀ := sup_le hG hA
  have hgi : Integrable (μ[Y | A]) μ := integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hsup hYi (fun s _ _ => hgi.integrableOn)
    ?_ (((stronglyMeasurable_condExp (m := A) (f := Y) (μ := μ)).mono
      (le_sup_right : A ≤ G ⊔ A)).aestronglyMeasurable)).symm
  intro S hS _
  refine induction_on_inter (C := fun S _ => ∫ x in S, (μ[Y | A]) x ∂μ = ∫ x in S, Y x ∂μ)
    QuantumZipper.Thm18Asm.sup_eq_generateFrom_interPi
    QuantumZipper.Thm18Asm.isPiSystem_interPi (by simp) ?_ ?_ ?_ S hS
  · rintro _ ⟨g, a, hg, ha, rfl⟩
    rw [es_setIntegral_inter_indep hH hG hind (stronglyMeasurable_condExp.mono hAH) hgi
        (hAH a ha) hg, es_setIntegral_inter_indep hH hG hind hYm hYi (hAH a ha) hg,
      setIntegral_condExp hA hYi ha]
  · intro t htm ht
    have ht0 : MeasurableSet[m₀] t := hsup t htm
    have e1 := integral_add_compl ht0 hgi
    have e2 := integral_add_compl ht0 hYi
    have e3 : ∫ x, (μ[Y | A]) x ∂μ = ∫ x, Y x ∂μ := integral_condExp hA
    linarith
  · intro s hd hsm hs
    have hs0 : ∀ i, MeasurableSet[m₀] (s i) := fun i => hsup _ (hsm i)
    rw [integral_iUnion hs0 hd hgi.integrableOn, integral_iUnion hs0 hd hYi.integrableOn]
    exact tsum_congr hs

/-- Jensen in `L²` for conditional expectations: `E[(E[Z | m])²] ≤ E[Z²]`. -/
lemma es_integral_condExp_sq_le [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) :
    ∫ ω, (μ[Z | m] ω) ^ 2 ∂μ ≤ ∫ ω, (Z ω) ^ 2 ∂μ := by
  have htot := integral_condVar_add_variance_condExp hm hZ
  have hnn : 0 ≤ μ[Var[Z; μ | m]] := by
    rw [condVar, integral_condExp hm]
    exact integral_nonneg fun ω => sq_nonneg _
  rw [variance_eq_sub (hZ.condExp one_le_two), variance_eq_sub hZ, integral_condExp hm] at htot
  have : μ[μ[Z | m] ^ 2] ≤ μ[Z ^ 2] := by linarith
  simpa using this

/-- Law of total variance in the form `Var F = E[(F - E[F | m])²] + Var E[F | m]`. -/
lemma es_variance_eq_add [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    variance F μ = ∫ ω, (F ω - μ[F | m] ω) ^ 2 ∂μ + variance (μ[F | m]) μ := by
  rw [← integral_condVar_add_variance_condExp hm hF, condVar, integral_condExp hm]
  rfl

/-- **Efron–Stein inequality**, σ-algebra form (LM (5.1)). For independent sub-σ-algebras
`G i` and `F ∈ L²` measurable w.r.t. `⨆ i ∈ s, G i` (`s` finite),
`Var F ≤ ∑ i ∈ s, E[(F - E[F | ⨆ j ∈ s \ {i}, G j])²]`. -/
theorem efronStein_sigma [IsProbabilityMeasure μ] {ι : Type*} [DecidableEq ι]
    (G : ι → MeasurableSpace Ω) (hle : ∀ i, G i ≤ m₀) (hind : iIndep G μ) (s : Finset ι)
    {F : Ω → ℝ} (hFm : StronglyMeasurable[⨆ i ∈ s, G i] F) (hF : MemLp F 2 μ) :
    variance F μ ≤
      ∑ i ∈ s, ∫ ω, (F ω - μ[F | ⨆ j ∈ s.erase i, G j] ω) ^ 2 ∂μ := by
  have hsuple : ∀ t : Finset ι, (⨆ j ∈ t, G j) ≤ m₀ := fun t => iSup₂_le fun j _ => hle j
  induction s using Finset.induction_on generalizing F with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset ι), G i) = ⊥ := by simp
    rw [hbot] at hFm
    obtain ⟨c, rfl⟩ := stronglyMeasurable_bot_iff.1 hFm
    rw [variance_eq_sub (memLp_const c)]
    simp
  | @insert a s ha ih =>
    set B : MeasurableSpace Ω := ⨆ j ∈ s, G j with hBdef
    have hB : B ≤ m₀ := hsuple s
    set M : Ω → ℝ := μ[F | B] with hMdef
    have hMm : StronglyMeasurable[⨆ j ∈ s, G j] M := stronglyMeasurable_condExp
    have hM : MemLp M 2 μ := hF.condExp one_le_two
    have hIH := ih hMm hM
    rw [es_variance_eq_add hB hF, Finset.sum_insert ha, Finset.erase_insert ha]
    refine add_le_add le_rfl (hIH.trans (Finset.sum_le_sum fun i hi => ?_))
    -- the increment for `i ∈ s`
    set Hi : MeasurableSpace Ω := ⨆ j ∈ s.erase i, G j with hHi
    set Hi' : MeasurableSpace Ω := ⨆ j ∈ (insert a s).erase i, G j with hHi'
    have hHi0 : Hi ≤ m₀ := hsuple _
    have hHi'0 : Hi' ≤ m₀ := hsuple _
    have hsub : Hi ≤ Hi' := iSup₂_mono' fun j hj =>
      ⟨j, Finset.erase_subset_erase i (Finset.subset_insert a s) hj, le_rfl⟩
    have hBeq : B = G i ⊔ Hi := by
      rw [hBdef, hHi, ← Finset.iSup_insert, Finset.insert_erase hi]
    have hindi : Indep (G i) Hi' μ := by
      have h := indep_iSup_of_disjoint hle hind
        (S := {i}) (T := ↑((insert a s).erase i)) (by simp)
      simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left, Finset.mem_coe] using h
    set Y : Ω → ℝ := μ[F | Hi'] with hYdef
    have hYi : Integrable Y μ := integrable_condExp
    have hFi : Integrable F μ := hF.integrable one_le_two
    have key : μ[Y | B] =ᵐ[μ] μ[F | Hi] := by
      have h1 := condExp_sup_indep_eq (μ := μ) hsub hHi'0 (hle i) hindi
        (stronglyMeasurable_condExp (m := Hi') (f := F)) hYi
      rw [← hBeq] at h1
      exact h1.trans (condExp_condExp_of_le hsub hHi'0)
    have hMHi : μ[M | Hi] =ᵐ[μ] μ[F | Hi] := by
      have : Hi ≤ B := by rw [hBeq]; exact le_sup_right
      exact condExp_condExp_of_le this hB
    have hZ : MemLp (F - Y) 2 μ := hF.sub (hF.condExp one_le_two)
    have hdiff : (fun ω => (M ω - μ[M | Hi] ω) ^ 2) =ᵐ[μ]
        fun ω => (μ[F - Y | B] ω) ^ 2 := by
      filter_upwards [condExp_sub hFi hYi B, key, hMHi] with ω h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    calc ∫ ω, (M ω - μ[M | Hi] ω) ^ 2 ∂μ = ∫ ω, (μ[F - Y | B] ω) ^ 2 ∂μ :=
          integral_congr_ae hdiff
      _ ≤ ∫ ω, ((F - Y) ω) ^ 2 ∂μ := es_integral_condExp_sq_le hB hZ
      _ = ∫ ω, (F ω - μ[F | Hi'] ω) ^ 2 ∂μ := rfl

end LQGMetric
