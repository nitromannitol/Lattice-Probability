/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3Norm at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# Far normalization of the field: `σ(h|_K) = σ(h|_K mod constants)` (D79 (1))

Decision `decisions/DEC-79.md` (1), "T4.2 proof: far normalization" (open node, elementary; own
elementary proof): if `h(ψ₀) = 0` for a mass-one test function `ψ₀` supported in `K`, then every
pairing `h(ψ)`, `supp ψ ⊆ B_ε(K)`, equals the mean-zero pairing `h(ψ − (∫ψ)ψ₀)`, so the two
σ-algebras of `h|_K` (with and without additive constants) agree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open LQGMetric.Blueprint

namespace LQGMetric.GM

theorem gm_integrable_testC (φ : TestC) : Integrable (φ : ℂ → ℝ) :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- per neighbourhood: `σ(h|_V) = σ(h|_V mod constants)` when `h(ψ₀) = 0`, `supp ψ₀ ⊆ V` -/
theorem gm_fieldSigma_eq_fieldSigma0On {Ω : Type} {h : Ω → DistC} {ψ₀ : TestC}
    (hψ₀ : ∫ x, ψ₀ x = 1) (h0 : ∀ ω, h ω ψ₀ = 0) {V : Opens ℂ}
    (hV : tsupport (ψ₀ : ℂ → ℝ) ⊆ V) : fieldSigma h V = fieldSigma0On h V := by
  apply le_antisymm
  · letI : MeasurableSpace Ω := fieldSigma0On h V
    have hm : Measurable fun ω => restrictTo V (h ω) := by
      refine measurable_distOn_iff.2 fun φ => ?_
      set ψ : TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ
      set ψ' : TestC := ψ - (∫ x, ψ x) • ψ₀
      have hψs : tsupport (ψ : ℂ → ℝ) ⊆ V := by
        have : (ψ : ℂ → ℝ) = (φ : ℂ → ℝ) := by
          ext x; simp [ψ, TestFunction.monoCLM_apply]
        rw [this]; exact φ.tsupport_subset
      have hint : ∫ x, ψ' x = 0 := by
        have e : (ψ' : ℂ → ℝ) = fun x => ψ x - (∫ x, ψ x) * ψ₀ x := by
          ext x; simp [ψ']
        rw [e, integral_sub (gm_integrable_testC ψ) ((gm_integrable_testC ψ₀).const_mul _),
          integral_const_mul, hψ₀, mul_one, sub_self]
      have hsupp : tsupport (ψ' : ℂ → ℝ) ⊆ V := by
        have e : (ψ' : ℂ → ℝ) = (ψ : ℂ → ℝ) + fun x => (-(∫ x, ψ x)) * ψ₀ x := by
          ext x; simp [ψ']; ring
        rw [e]
        refine (tsupport_add _ _).trans (union_subset hψs ?_)
        exact (tsupport_mul_subset_right (f := fun _ => -(∫ x, ψ x))).trans hV
      have e : (fun ω => restrictTo V (h ω) φ) = fun ω => h ω ψ' := by
        funext ω
        show h ω ψ = h ω ψ'
        simp only [ψ', map_sub, map_smul, h0 ω, smul_zero, sub_zero]
      rw [e]
      exact (measurable_pi_apply
        (X := fun _ : {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ (V : Set ℂ)} => ℝ)
        ⟨⟨ψ', hint⟩, hsupp⟩).comp (comap_measurable _)
    exact hm.comap_le
  · letI : MeasurableSpace Ω := fieldSigma h V
    have hm : Measurable fun ω (ψ : {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ (V : Set ℂ)}) =>
        h ω ψ.1.1 :=
      measurable_pi_iff.2 fun ψ => measurable_pair_fieldSigma h ψ.1.1 ψ.2
    exact hm.comap_le

/-- **D79 (1), far normalization**: `σ(h|_K) = σ(h|_K mod constants)` when `h(ψ₀) = 0` for a
mass-one test function `ψ₀` supported in `K` -/
theorem fieldSigmaClosed_eq_fieldSigmaClosed0 {Ω : Type} [MeasurableSpace Ω] {h : Ω → DistC}
    {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1) (h0 : ∀ ω, h ω ψ₀ = 0) {K : Set ℂ}
    (hK : tsupport (ψ₀ : ℂ → ℝ) ⊆ K) : fieldSigmaClosed h K = fieldSigmaClosed0 h K := by
  unfold fieldSigmaClosed fieldSigmaClosed0
  refine iInf_congr fun ε => iInf_congr fun hε => ?_
  exact gm_fieldSigma_eq_fieldSigma0On hψ₀ h0 (V := nbhdO ε K)
    (hK.trans (self_subset_thickening hε K))

end LQGMetric.GM
