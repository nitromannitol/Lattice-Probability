/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.AssociationEvents at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.AssociationSets

/-!
# Positive association of measurable increasing events of a Gaussian vector

For `X : Ω → (ι → ℝ)` with Gaussian law (any mean, possibly degenerate covariance) and
`cov(X i, X j) ≥ 0`, and measurable upper sets `U, V, Uᵢ`:

* `LQGMetric.Pitt.measureReal_mul_le_inter`: `P(X ∈ U) P(X ∈ V) ≤ P(X ∈ U ∩ V)`;
* `LQGMetric.Pitt.prob_mul_le_inter`: the same for the events `X ⁻¹' U`;
* `LQGMetric.Pitt.prod_prob_le_biInter`: `∏ᵢ P(X ∈ Uᵢ) ≤ P(⋂ᵢ {X ∈ Uᵢ})` for finitely many.

Pitt, *Positively correlated normal variables are associated*, Ann. Probab. 10 (1982) 496–499,
for indicators. Passage from closed to measurable upper sets: inner regularity of the law by
compact sets `K ⊆ U`, and `K + [0, ∞)^ι` is a closed upper set between `K` and `U`
(own elementary argument).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal Pointwise ENNReal

namespace LQGMetric

namespace Pitt

variable {ι : Type*} [Fintype ι]

/-- Inner approximation of a measurable upper set by closed upper sets, for a finite measure. -/
lemma exists_closed_upper_approx (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {U : Set (ι → ℝ)} (hUm : MeasurableSet U) (hU : IsUpperSet U) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W, IsClosed W ∧ IsUpperSet W ∧ W ⊆ U ∧ μ.real U ≤ μ.real W + δ := by
  obtain ⟨K, hKU, hK, hμK⟩ := hUm.exists_isCompact_lt_add (measure_ne_top μ U)
    (ENNReal.ofReal_pos.2 hδ).ne'
  refine ⟨K + Ici 0, isClosed_Ici.add_left_of_isCompact hK, ?_, ?_, ?_⟩
  · rintro a b hab ⟨k, hk, c, hc, rfl⟩
    refine ⟨k, hk, b - k, ?_, by abel⟩
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
  have : IsProbabilityMeasure (P.map X) := inferInstance
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

end Pitt

end LQGMetric
