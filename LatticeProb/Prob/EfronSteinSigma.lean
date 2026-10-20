/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/EfronStein.lean.
-/

import Mathlib.Probability.CondVar
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import LatticeProb.Prob.CondIndepEv

/-!
# The Efron–Stein inequality for independent σ-algebras

Let `G i` (`i ∈ s`, `s` a finite set) be independent sub-σ-algebras of the ambient σ-algebra, and
let `F ∈ L²` be measurable with respect to `⨆ i ∈ s, G i`. Then
`Var F ≤ ∑ i ∈ s, E[(F - E[F | ⨆ j ∈ s \ {i}, G j])²]`
(`LatticeProb.efronStein_sigma`). When `G i = σ(X i)` for random variables `X i`, the right-hand
side is `∑ i E[(F - E[F | σ(X j : j ≠ i)])²]`, the sum over `i` of the expected conditional
variances of `F` given all the other coordinates.

This is the σ-algebra form: the blocks `G i` are arbitrary independent sub-σ-algebras of an
arbitrary probability space. It is not the product-space form. `LatticeProb.Prob.EfronSteinCov`
bounds the variance of a function on a product measure `Measure.pi μ` by resampling energies, and
`LatticeProb.Prob.EfronStein` proves exponential concentration for product measures. Neither is a
special case of this file, and this file changes neither of them.

## Proof

The proof is by induction on `s`. The first increment is split off with the law of total variance
(mathlib's `integral_condVar_add_variance_condExp`), and the remaining terms are the induction
hypothesis applied to `E[F | ⨆ j ∈ s, G j]`. The Jensen step `E[(E[Z | m])²] ≤ E[Z²]` is
`es_integral_condExp_sq_le`. The independence step is `condExp_sup_indep_eq`: if `Y` is
`H`-measurable, `A ≤ H`, and `G` is independent of `H`, then `E[Y | G ⊔ A] = E[Y | A]`. Its
π–λ argument uses the π-system `interPi` of `LatticeProb.Prob.CondIndepEv`.

References: Efron and Stein, *The jackknife estimate of variance*, Ann. Statist. 9 (1981); Steele,
*An Efron–Stein inequality for nonsymmetric statistics*, Ann. Statist. 14 (1986); van Handel,
*Probability in High Dimension* (lecture notes, 2016), §2.1, whose martingale-increment proof this
follows.
-/

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace

namespace LatticeProb

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
    sup_eq_generateFrom_interPi isPiSystem_interPi (by simp) ?_ ?_ ?_ S hS
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

/-- **Efron–Stein inequality**, σ-algebra form. For independent sub-σ-algebras `G i` and `F ∈ L²`
measurable w.r.t. `⨆ i ∈ s, G i` (`s` finite),
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

/-! ### Nonvacuity

Two independent fair coins on `Fin 2 → Bool`, with the coordinate σ-algebras, satisfy the
hypotheses of `efronStein_sigma` for `F = X₀ + X₁`, with the full index set. -/

namespace EfronSteinSigmaExample

/-- A fair coin on `Bool`. -/
def coin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coin := by
  unfold coin; infer_instance

/-- Two independent fair coins: the product of two copies of `coin` on `Fin 2 → Bool`. -/
def coins : Measure (Fin 2 → Bool) := Measure.pi fun _ : Fin 2 => coin

instance : IsProbabilityMeasure coins := by
  unfold coins; infer_instance

/-- The σ-algebra generated by the `i`-th coordinate on `Fin 2 → Bool`. -/
abbrev coinSigma (i : Fin 2) : MeasurableSpace (Fin 2 → Bool) :=
  MeasurableSpace.comap (fun ω : Fin 2 → Bool => ω i) inferInstance

/-- The value of a coin: `1` on `true`, `0` on `false`. -/
def coinVal (b : Bool) : ℝ := if b then 1 else 0

/-- The sum of the two coin values, as a function on `Fin 2 → Bool`. -/
def coinSum (ω : Fin 2 → Bool) : ℝ := coinVal (ω 0) + coinVal (ω 1)

/-- `coinSum` is measurable with respect to the σ-algebra of all the coins. -/
lemma coinSum_stronglyMeasurable :
    StronglyMeasurable[⨆ i ∈ (Finset.univ : Finset (Fin 2)), coinSigma i] coinSum := by
  have h : ∀ i : Fin 2, Measurable[⨆ j ∈ (Finset.univ : Finset (Fin 2)), coinSigma j]
      (fun ω : Fin 2 → Bool => ω i) := fun i =>
    Measurable.of_comap_le (le_iSup₂ (f := fun j (_ : j ∈ Finset.univ) => coinSigma j) i
      (Finset.mem_univ i))
  exact (((measurable_of_countable coinVal).comp (h 0)).add
    ((measurable_of_countable coinVal).comp (h 1))).stronglyMeasurable

/-- `coinSum` is bounded, hence square-integrable, under the two-coin measure. -/
lemma coinSum_memLp : MemLp coinSum 2 coins := by
  refine MemLp.of_bound ?_ 2 (Filter.Eventually.of_forall fun ω => ?_)
  · exact (((measurable_of_countable coinVal).comp (measurable_pi_apply 0)).add
      ((measurable_of_countable coinVal).comp (measurable_pi_apply 1))).aestronglyMeasurable
  · simp only [coinSum, coinVal, Real.norm_eq_abs]
    split_ifs <;> norm_num

/-- The coordinate σ-algebras are independent under the two-coin measure. -/
lemma coins_iIndep : iIndep coinSigma coins :=
  (iIndepFun_iff_iIndep (fun _ => (inferInstance : MeasurableSpace Bool)) _ _).1
    (iIndepFun_pi (μ := fun _ : Fin 2 => coin) (X := fun _ => (id : Bool → Bool))
      (fun _ => measurable_id.aemeasurable))

/-- Nonvacuity: the hypotheses of `efronStein_sigma` hold for two independent fair coins and
`F = X₀ + X₁`, with the full index set. -/
example : variance coinSum coins ≤
    ∑ i ∈ Finset.univ, ∫ ω, (coinSum ω - coins[coinSum | ⨆ j ∈ Finset.univ.erase i, coinSigma j] ω)
      ^ 2 ∂coins :=
  efronStein_sigma coinSigma (fun i => (measurable_pi_apply i).comap_le) coins_iIndep Finset.univ
    coinSum_stronglyMeasurable coinSum_memLp

end EfronSteinSigmaExample

end LatticeProb
