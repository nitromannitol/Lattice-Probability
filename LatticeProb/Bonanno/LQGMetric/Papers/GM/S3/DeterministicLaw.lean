/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DeterministicLaw at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.Measurable

/-!
# GM Lemma 3.1, ingredient: events of the field modulo additive constant (task P2-M2D)

GM, `literature/src/1905.00383/uniqueness-final.tex` l. 1200–1203 (proof of Lemma 3.1): "this
event is determined by `h|_{B_R(0)}` *viewed modulo additive constant* … By Axiom IV′ and the
translation invariance of the law of `h`, modulo additive constant, the probability of `E(z)` does
not depend on `z`."

* `GM.prob_eq_of_ae_addConst_iff`: an event `{h ∈ S}` of the field which is (a.s. along each of
  two whole-plane GFFs) invariant under adding constants has the same probability for both
  fields, even on different probability spaces. Proof: `S` agrees a.s. with the event
  `{recenter ρ h ∈ S}`, which is measurable for the σ-algebra `sigma0` of the field modulo
  constants, and the law on `sigma0` is unique (`GFFLaw.map_comp_eq_of_sigma0`, task P2-FINV).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric.GM

open GFFInv GFFLaw

/-- the test function `ρ = ψ_{0,0}` of integral one used for re-centring -/
def detRho : TestC := bumpTest 0 0

lemma integral_detRho : ∫ x, detRho x = 1 := integral_bumpTest 0 0

/-- **Law transfer for events modulo additive constants** (GM l. 1200–1203). -/
theorem prob_eq_of_ae_addConst_iff {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P') {S : Set DistC}
    (hS : MeasurableSet S) (hinv : ∀ᵐ ω ∂P, ∀ a : ℝ, addConst (h ω) a ∈ S ↔ h ω ∈ S)
    (hinv' : ∀ᵐ ω ∂P', ∀ a : ℝ, addConst (h' ω) a ∈ S ↔ h' ω ∈ S) :
    P (h ⁻¹' S) = P' (h' ⁻¹' S) := by
  have hmap := map_comp_eq_of_sigma0 (measurable_recenter_sigma0 integral_detRho) hh hh'
  have hle : sigma0 ≤ (inferInstance : MeasurableSpace DistC) := by
    rw [sigma0, ← measurable_iff_comap_le]
    exact measurable_pi_iff.2 fun φ => measurable_pair φ.1
  have hrm : Measurable (recenter detRho) :=
    (measurable_recenter_sigma0 integral_detRho).mono hle le_rfl
  have e1 : P (h ⁻¹' S) = P ((recenter detRho ∘ h) ⁻¹' S) := by
    refine measure_congr ?_
    filter_upwards [hinv] with ω hω
    exact propext ((hω _).symm)
  have e2 : P' (h' ⁻¹' S) = P' ((recenter detRho ∘ h') ⁻¹' S) := by
    refine measure_congr ?_
    filter_upwards [hinv'] with ω hω
    exact propext ((hω _).symm)
  rw [e1, e2, ← Measure.map_apply (hrm.comp hh.measurable) hS,
    ← Measure.map_apply (hrm.comp hh'.measurable) hS, hmap]

end LQGMetric.GM
