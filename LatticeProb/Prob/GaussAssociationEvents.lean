/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/AssociationEvents.lean.
Source: LQGMetric/Gaussian/AssociationSqrt.lean.
-/
import LatticeProb.Prob.GaussAssociationSets
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Positive association of measurable increasing events of a Gaussian vector

For `X : Ω → (ι → ℝ)` with Gaussian law (any mean, possibly degenerate covariance) and
`cov(X i, X j) ≥ 0` for all `i, j`, and measurable upper sets `U, V, Uᵢ` of `ι → ℝ`:

* `LatticeProb.Pitt.measureReal_mul_le_inter`: `P(X ∈ U) P(X ∈ V) ≤ P(X ∈ U ∩ V)`;
* `LatticeProb.Pitt.prod_prob_le_biInter`: `∏ᵢ P(X ∈ Uᵢ) ≤ P(⋂ᵢ {X ∈ Uᵢ})` for finitely many.

This is Pitt's inequality for indicators of increasing events (Pitt, *Positively correlated normal
variables are associated*, Ann. Probab. 10 (1982) 496–499), extended from closed to measurable
upper sets. The passage uses inner regularity of the law by compact sets `K ⊆ U`: the set
`K + [0, ∞)^ι` is a closed upper set between `K` and `U`.

The file also proves `LatticeProb.Pitt.exists_measure_compl_ge_of_prod_le`: if finitely many
events `Aᵢ` satisfy `∏ᵢ P(Aᵢ) ≤ P(⋂ᵢ Aᵢ)`, then some complement `Aᵢᶜ` has probability at least
`1 - (1 - P(⋃ᵢ Aᵢᶜ))^{1/k}`, where `k` is the number of events.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Pointwise

namespace LatticeProb

namespace Pitt

variable {ι : Type*} [Fintype ι]

/-- Inner approximation of a measurable upper set by closed upper sets, for a finite measure:
for every `δ > 0` there is a closed upper set `W ⊆ U` with `μ(U) ≤ μ(W) + δ`. -/
lemma exists_closed_upper_approx (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {U : Set (ι → ℝ)} (hUm : MeasurableSet U) (hU : IsUpperSet U) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W, IsClosed W ∧ IsUpperSet W ∧ W ⊆ U ∧ μ.real U ≤ μ.real W + δ := by
  obtain ⟨K, hKU, hK, hμK⟩ := hUm.exists_isCompact_lt_add (measure_ne_top μ U)
    (ENNReal.ofReal_pos.2 hδ).ne'
  refine ⟨K + Ici 0, isClosed_Ici.add_left_of_isCompact hK, ?_, ?_, ?_⟩
  · rintro a b hab ⟨k, hk, c, hc, rfl⟩
    refine ⟨k, hk, b - k, ?_, by simp⟩
    have hc' : (0 : ι → ℝ) ≤ c := hc
    show 0 ≤ b - k
    exact sub_nonneg.2 ((le_add_of_nonneg_right hc').trans hab)
  · rintro _ ⟨k, hk, c, hc, rfl⟩
    exact hU (le_add_of_nonneg_right (show (0 : ι → ℝ) ≤ c from hc)) (hKU hk)
  · have hKW : K ⊆ K + Ici 0 := fun k hk => ⟨k, hk, 0, mem_Ici.2 le_rfl, add_zero k⟩
    have h1 : μ U ≤ μ (K + Ici 0) + ENNReal.ofReal δ :=
      hμK.le.trans (by gcongr)
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      ENNReal.ofReal_ne_top⟩) h1
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hδ.le] at h2

variable [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Pitt's inequality for measurable increasing events**, in terms of the law. -/
theorem measureReal_mul_le_inter {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hcov : ∀ i j, 0 ≤ cov[fun ω => X ω i, fun ω => X ω j; P])
    {U V : Set (ι → ℝ)} (hUm : MeasurableSet U) (hVm : MeasurableSet V) (hU : IsUpperSet U)
    (hV : IsUpperSet V) :
    (P.map X).real U * (P.map X).real V ≤ (P.map X).real (U ∩ V) := by
  have := hX.isProbabilityMeasure
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  set μ := P.map X
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨WU, hWUc, hWU, hWUU, hμU⟩ := exists_closed_upper_approx μ hUm hU (half_pos hε)
  obtain ⟨WV, hWVc, hWV, hWVV, hμV⟩ := exists_closed_upper_approx μ hVm hV (half_pos hε)
  have hW := measureReal_mul_le_inter_of_isClosed hX hcov hWUc hWVc hWU hWV
  have hmono : μ.real (WU ∩ WV) ≤ μ.real (U ∩ V) :=
    measureReal_mono (inter_subset_inter hWUU hWVV)
  have a0 : 0 ≤ μ.real WU := measureReal_nonneg
  have a1 : μ.real WU ≤ 1 := measureReal_le_one
  have b0 : 0 ≤ μ.real V := measureReal_nonneg
  have b1 : μ.real V ≤ 1 := measureReal_le_one
  have e1 : (μ.real U - μ.real WU) * μ.real V ≤ ε / 2 * 1 :=
    mul_le_mul (by linarith) b1 b0 (by linarith)
  have hd0 : 0 ≤ μ.real V - μ.real WV := sub_nonneg.2 (measureReal_mono hWVV)
  have e2 : μ.real WU * (μ.real V - μ.real WV) ≤ 1 * (ε / 2) :=
    mul_le_mul a1 (by linarith) hd0 zero_le_one
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- The law of `X` gives the probability of `X ∈ U` for a measurable set `U`. -/
lemma map_real_eq {X : Ω → ι → ℝ} (hX : AEMeasurable X P) {U : Set (ι → ℝ)}
    (hU : MeasurableSet U) : (P.map X).real U = P.real (X ⁻¹' U) := by
  rw [measureReal_def, measureReal_def, Measure.map_apply_of_aemeasurable hX hU]

/-- **Positive association of finitely many increasing events** `{X ∈ Uᵢ}`, `i ∈ s`. -/
theorem prod_prob_le_biInter {κ : Type*} {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P)
    (hcov : ∀ i j, 0 ≤ cov[fun ω => X ω i, fun ω => X ω j; P])
    {U : κ → Set (ι → ℝ)} (hUm : ∀ a, MeasurableSet (U a)) (hU : ∀ a, IsUpperSet (U a))
    (s : Finset κ) :
    ∏ a ∈ s, P.real (X ⁻¹' U a) ≤ P.real (⋂ a ∈ s, X ⁻¹' U a) := by
  classical
  have := hX.isProbabilityMeasure
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have key : ∏ a ∈ s, (P.map X).real (U a) ≤ (P.map X).real (⋂ a ∈ s, U a) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert b s hb ih =>
      rw [Finset.prod_insert hb, Finset.set_biInter_insert]
      have hm : MeasurableSet (⋂ a ∈ s, U a) := Finset.measurableSet_biInter s fun a _ => hUm a
      have hup : IsUpperSet (⋂ a ∈ s, U a) := isUpperSet_iInter₂ fun a _ => hU a
      calc (P.map X).real (U b) * ∏ a ∈ s, (P.map X).real (U a)
          ≤ (P.map X).real (U b) * (P.map X).real (⋂ a ∈ s, U a) :=
            mul_le_mul_of_nonneg_left ih measureReal_nonneg
        _ ≤ _ := measureReal_mul_le_inter hX hcov (hUm b) hm (hU b) hup
  have hm : MeasurableSet (⋂ a ∈ s, U a) := Finset.measurableSet_biInter s fun a _ => hUm a
  rw [map_real_eq hX.aemeasurable hm, preimage_iInter₂] at key
  simpa only [map_real_eq hX.aemeasurable (hUm _)] using key

/-- If the events `A i` satisfy `∏ i, P(A i) ≤ P(⋂ i, A i)`, then some complement `(A i)ᶜ` has
probability at least `1 - (1 - P(⋃ i, (A i)ᶜ))^(1 / card κ)`.

Proof: `1 - P(⋃ i, (A i)ᶜ) = P(⋂ i, A i)`. If `m` is the least of the `P(A i)`, then
`m ^ card κ ≤ ∏ i, P(A i) ≤ P(⋂ i, A i)`, so `m ≤ P(⋂ i, A i) ^ (1 / card κ)`. -/
theorem exists_measure_compl_ge_of_prod_le [IsProbabilityMeasure P] {κ : Type*} [Fintype κ]
    [Nonempty κ] {A : κ → Set Ω} (hA : ∀ i, NullMeasurableSet (A i) P)
    (hass : ∏ i, P.real (A i) ≤ P.real (⋂ i, A i)) :
    ∃ i, 1 - (1 - P.real (⋃ i, (A i)ᶜ)) ^ (1 / (Fintype.card κ : ℝ)) ≤ P.real (A i)ᶜ := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => P.real (A i))
    Finset.univ_nonempty
  refine ⟨i₀, ?_⟩
  set m := P.real (A i₀)
  have hm : 0 ≤ m := measureReal_nonneg
  have hk : Fintype.card κ ≠ 0 := Fintype.card_ne_zero
  have hU : 1 - P.real (⋃ i, (A i)ᶜ) = P.real (⋂ i, A i) := by
    rw [← compl_iInter, probReal_compl_eq_one_sub₀ (NullMeasurableSet.iInter hA)]; ring
  have hprod : m ^ Fintype.card κ ≤ P.real (⋂ i, A i) := by
    refine le_trans ?_ hass
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hm) fun i _ => hi₀ i (Finset.mem_univ _)
  have hroot : m ≤ (P.real (⋂ i, A i)) ^ (1 / (Fintype.card κ : ℝ)) := by
    calc m = (m ^ Fintype.card κ) ^ ((Fintype.card κ : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast hm hk).symm
      _ ≤ _ := by
          rw [one_div]
          exact Real.rpow_le_rpow (by positivity) hprod (by positivity)
  rw [hU, probReal_compl_eq_one_sub₀ (hA i₀)]
  linarith

/-! ### Nonvacuity

The hypotheses of the lemmas above are satisfied by the Gaussian vector `ω ↦ (ω, …, ω)` on `ℝ`
(standard Gaussian `ω`) and by the closed upper half-line `{z | 0 ≤ z 0}`. -/

namespace Example

/-- The vector `ω ↦ (ω, ω)` of a standard Gaussian variable `ω` on `ℝ` has Gaussian law. -/
lemma hasGaussianLaw_diag :
    HasGaussianLaw (fun ω : ℝ => fun _ : Fin 2 => ω) (stdGaussian ℝ) :=
  (IsGaussian.hasGaussianLaw_id (μ := stdGaussian ℝ)).map_fun
    (ContinuousLinearMap.pi fun _ : Fin 2 => ContinuousLinearMap.id ℝ ℝ)

/-- The coordinates of the vector `ω ↦ (ω, ω)` have nonnegative covariances. -/
lemma cov_nonneg_diag : ∀ _ _ : Fin 2, 0 ≤ cov[fun ω : ℝ => ω, fun ω : ℝ => ω; stdGaussian ℝ] :=
  fun _ _ => by
    rw [covariance_self measurable_id'.aemeasurable]
    exact variance_nonneg _ _

/-- The closed upper half-line `{z | 0 ≤ z 0}` of `Fin 2 → ℝ` is closed. -/
lemma halfline_isClosed : IsClosed {z : Fin 2 → ℝ | 0 ≤ z 0} :=
  isClosed_Ici.preimage (continuous_apply 0)

/-- The closed upper half-line `{z | 0 ≤ z 0}` of `Fin 2 → ℝ` is measurable. -/
lemma halfline_measurable : MeasurableSet {z : Fin 2 → ℝ | 0 ≤ z 0} :=
  halfline_isClosed.measurableSet

/-- The half-line `{z | 0 ≤ z 0}` of `Fin 2 → ℝ` is an upper set. -/
lemma halfline_isUpperSet : IsUpperSet {z : Fin 2 → ℝ | 0 ≤ z 0} :=
  fun _ _ hab ha => le_trans ha (hab 0)

-- `P(X ∈ U) P(X ∈ V) ≤ P(X ∈ U ∩ V)` for the half-line and the diagonal Gaussian vector.
example :
    ((stdGaussian ℝ).map (fun ω : ℝ => fun _ : Fin 2 => ω)).real {z : Fin 2 → ℝ | 0 ≤ z 0} *
      ((stdGaussian ℝ).map (fun ω : ℝ => fun _ : Fin 2 => ω)).real {z : Fin 2 → ℝ | 0 ≤ z 0} ≤
    ((stdGaussian ℝ).map (fun ω : ℝ => fun _ : Fin 2 => ω)).real
      ({z : Fin 2 → ℝ | 0 ≤ z 0} ∩ {z : Fin 2 → ℝ | 0 ≤ z 0}) :=
  measureReal_mul_le_inter hasGaussianLaw_diag cov_nonneg_diag halfline_measurable
    halfline_measurable halfline_isUpperSet halfline_isUpperSet

-- Finitely many copies of the half-line event.
example := prod_prob_le_biInter (κ := Fin 2) (U := fun _ => {z : Fin 2 → ℝ | 0 ≤ z 0})
  hasGaussianLaw_diag cov_nonneg_diag (fun _ => halfline_measurable)
  (fun _ => halfline_isUpperSet) Finset.univ

-- Closed upper approximation of the half-line for a Dirac measure.
example := exists_closed_upper_approx (Measure.dirac (0 : Fin 2 → ℝ)) halfline_measurable
  halfline_isUpperSet one_pos

-- The product bound for two copies of `{ω | 0 ≤ ω}` under the standard Gaussian law.
example := exists_measure_compl_ge_of_prod_le (P := stdGaussian ℝ)
  (A := fun _ : Fin 2 => {ω : ℝ | 0 ≤ ω})
  (fun _ => (measurableSet_le measurable_const measurable_id).nullMeasurableSet)
  (by
    simp only [Set.iInter_const, Fin.prod_univ_two]
    exact mul_le_of_le_one_left measureReal_nonneg measureReal_le_one)

end Example

end Pitt

end LatticeProb
