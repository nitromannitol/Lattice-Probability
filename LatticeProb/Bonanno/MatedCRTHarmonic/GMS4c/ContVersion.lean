/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.ContVersion at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib

/-!
# A measurable continuous version of a function `ℝ → ℂ`

The bundle's locality field S7 ([18] Lemma 2.4) gives the excursion segments as a measurable map into
`ℚ × ℚ → ℝ → ℂ` with the *product* σ-algebra on `ℝ → ℂ`, under which "continuous" is not a measurable condition.
`contVersion : (ℝ → ℂ) → C(ℝ, ℂ)` is measurable and is the identity on continuous functions: a continuous function is
determined by its values at the rationals, the restriction `C(ℝ, ℂ) → (ℚ → ℂ)` is a continuous injection from a
Polish space, hence a measurable embedding (Lusin–Souslin), and `contVersion` extends its inverse by `0`.

* `contVersion_coe`: `contVersion f = f` for continuous `f`.
* `measurable_contVersion`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace MatedCRTHarmonic.GMS4c

/-- Restriction of a continuous curve to the rational times. -/
def ratRestrict (c : C(ℝ, ℂ)) : ℚ → ℂ := fun q => c q

theorem continuous_ratRestrict : Continuous ratRestrict :=
  continuous_pi fun q => continuous_eval_const (q : ℝ)

theorem ratRestrict_injective : Function.Injective ratRestrict := by
  intro c c' h
  have hd : DenseRange (fun q : ℚ => (q : ℝ)) := Rat.isDenseEmbedding_coe_real.dense
  ext t
  have := hd.equalizer c.continuous c'.continuous (funext fun q => congrFun h q)
  exact congrFun this t

theorem measurableEmbedding_ratRestrict : MeasurableEmbedding ratRestrict :=
  continuous_ratRestrict.measurableEmbedding ratRestrict_injective

/-- **The continuous version** of `f : ℝ → ℂ`: the continuous curve agreeing with `f` at every rational time if there
is one, and `0` otherwise. -/
def contVersion (f : ℝ → ℂ) : C(ℝ, ℂ) :=
  Function.extend ratRestrict id (fun _ => 0) (fun q : ℚ => f q)

theorem contVersion_eq (c : C(ℝ, ℂ)) : contVersion c = c :=
  ratRestrict_injective.extend_apply id (fun _ => 0) c

/-- `contVersion` is the identity on continuous functions. -/
theorem contVersion_coe {f : ℝ → ℂ} (hf : Continuous f) : (contVersion f : ℝ → ℂ) = f := by
  have := contVersion_eq ⟨f, hf⟩
  exact congrArg (fun c : C(ℝ, ℂ) => (c : ℝ → ℂ)) this

theorem measurable_contVersion : Measurable contVersion := by
  have h1 : Measurable (Function.extend ratRestrict (id : C(ℝ, ℂ) → C(ℝ, ℂ)) (fun _ => (0 : C(ℝ, ℂ)))) :=
    measurableEmbedding_ratRestrict.measurable_extend measurable_id measurable_const
  have h2 : Measurable fun f : ℝ → ℂ => (fun q : ℚ => f q) :=
    measurable_pi_iff.mpr fun q => measurable_pi_apply (q : ℝ)
  exact h1.comp h2

end MatedCRTHarmonic.GMS4c
