/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.ShiftNull at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The final step of MQ Theorem 1.2: random shift `h + Aφ`, `A` uniform (task P2-MQ)

MQ (Miller–Qian, arXiv:1812.03913, `lqg_geodesics.tex`, l. 505–506): "if we take `A` to be
uniform in `[0,1]` then the probability that `X_i^A = X_j` is equal to `0`. Since the … law of
`h + Aφ` … is mutually absolutely continuous with respect to the … law of `h` …, the probability
that `X_i = X_j` is also equal to `0`." In the unconditional form of decision D-C4 (repaired
step: Fubini over `A`, then the unconditional Cameron–Martin theorem `lawPair0_ac_addFun`):

* `measure_pair0_eq_zero_of_shift_null` : if a.s. the set of `a ∈ [0,1]` with
  `h + aφ ∈ C` (mean-zero pairings) is Lebesgue-null, then `P[h ∈ C] = 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.MQ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

lemma pair0_addFun_smul (g : DistC) (φ : TestC) (a : ℝ) :
    pair0 (addFun g (testCont (a • φ))) = fun ψ => pair0 g ψ + a * ∫ x, ψ.1 x * φ x := by
  funext ψ
  rw [pair0_addFun, ← integral_const_mul]
  congr 2; funext x
  rw [show (a • φ : TestC) x = a * φ x from rfl]; ring

/-- **MQ l. 505–506 (D-C4 form)**: Fubini over the uniform shift `A ∈ [0,1]` and Cameron–Martin. -/
theorem measure_pair0_eq_zero_of_shift_null [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P)
    (φ : TestC) {C : Set (TestC0 → ℝ)} (hC : MeasurableSet C)
    (hnull : ∀ᵐ ω ∂P, volume {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧
      pair0 (addFun (h ω) (testCont (a • φ))) ∈ C} = 0) :
    P {ω | pair0 (h ω) ∈ C} = 0 := by
  set I : TestC0 → ℝ := fun ψ => ∫ x, ψ.1 x * φ x
  set Φ : ℝ × Ω → (TestC0 → ℝ) := fun p ψ => pair0 (h p.2) ψ + p.1 * I ψ
  have hΦ : Measurable Φ := measurable_pi_iff.2 fun ψ =>
    ((measurable_pi_apply ψ).comp ((measurable_pair0_comp hh).comp measurable_snd)).add
      (measurable_fst.mul_const _)
  have hS : MeasurableSet (Φ ⁻¹' C) := hΦ hC
  set ν := volume.restrict (Icc (0 : ℝ) 1)
  -- Fubini: the product measure of `Φ⁻¹ C` is `0`
  have h0 : (ν.prod P) (Φ ⁻¹' C) = 0 := by
    rw [Measure.prod_apply_symm hS]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hnull] with ω hω
    rw [Measure.restrict_apply (measurable_prodMk_right hS)]
    refine measure_mono_null (fun a ha => ?_) hω
    refine ⟨ha.2, ?_⟩
    rw [pair0_addFun_smul]
    exact ha.1
  rw [Measure.prod_apply hS, lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)] at h0
  have hne : ν ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]; norm_num
  haveI : (ae ν).NeBot := ae_neBot.2 hne
  obtain ⟨a, ha⟩ := h0.exists
  have ha' : P {ω | pair0 (addFun (h ω) (testCont (a • φ))) ∈ C} = 0 := by
    have : {ω | pair0 (addFun (h ω) (testCont (a • φ))) ∈ C} = Prod.mk a ⁻¹' (Φ ⁻¹' C) := by
      ext ω; simp only [mem_setOf_eq, mem_preimage, pair0_addFun_smul, Φ, I]
    rw [this]; exact ha
  have hl : lawPair0 (fun ω => addFun (h ω) (testCont (a • φ))) P C = 0 := by
    rw [lawPair0, Measure.map_apply (measurable_pair0_addFun hh _) hC]; exact ha'
  have := lawPair0_ac_addFun hh (a • φ) hl
  rwa [lawPair0, Measure.map_apply (measurable_pair0_comp hh) hC] at this

end LQGMetric.MQ
