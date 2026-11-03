/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovVer at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAdmCov
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The extension by zero as a random distribution: vanishing off `cl V` (task P2-MKH2, leaf (V))

`exists_vanishing_version_zbExt`: any measurable distribution-valued version `hz` of the
extension by zero `φ ↦ zbExt hh V φ` can be modified on a null set so that it vanishes off
`cl V` for **every** `ω`. Proof: `zbExt ψ = 0` a.s. for each `ψ` of the countable family
`comb W c` (`W = (cl V)ᶜ`, `MarkovExt.zbExt_ae_eq_zero`); a distribution on `W` vanishing on that
family is zero (`injective_pairJ`); set `hz := 0` on the (measurable, null) exceptional set.
This is the step "redefine on the null set where vanishing off `cl V` fails" of the route of
handoff/P2-MARKOV.md (own elementary argument; standard).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace

namespace LQGMetric
namespace MarkovVer

open MarkovGerm MarkovExt Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the open set `(cl V)ᶜ` -/
abbrev outV (V : Opens ℂ) : Opens ℂ :=
  toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl

/-- **Vanishing modification.** A measurable version of the extension by zero can be chosen to
vanish off `cl V` for every `ω`. -/
theorem exists_vanishing_version_zbExt (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    {hz : Ω → DistC} (hm : Measurable hz)
    (hv : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ) :
    ∃ hz' : Ω → DistC, Measurable hz' ∧
      (∀ φ : TestC, (fun ω => hz' ω φ) =ᵐ[P] zbExt hh V φ) ∧
      ∀ ω, restrictTo (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz' ω) = 0 := by
  set W := outV V
  set S : Set Ω := {ω | ∀ c : CoordJ, hz ω (extC W (comb W c)) = 0}
  have hS : MeasurableSet S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun c =>
      measurableSet_eq_fun ((measurable_distOn_apply _).comp hm) measurable_const
  have hvan : ∀ c : CoordJ, ∀ x ∈ (V : Set ℂ), (extC W (comb W c)) x = 0 := by
    intro c x hx
    rw [coe_extC]
    refine (comb W c).zero_on_compl fun hxW => ?_
    have : x ∉ closure (V : Set ℂ) := hxW
    exact this (subset_closure hx)
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    have : ∀ᵐ ω ∂P, ∀ c : CoordJ, hz ω (extC W (comb W c)) = 0 := by
      rw [ae_all_iff]
      intro c
      filter_upwards [hv (extC W (comb W c)), zbExt_ae_eq_zero hh (hvan c)] with ω h1 h2
      rw [h1, h2]; rfl
    exact this
  have hrS : ∀ ω ∈ S, restrictTo W (hz ω) = 0 := fun ω hω =>
    injective_pairJ W (funext fun c => by
      show restrictTo W (hz ω) (comb W c) = (0 : DistOn W) (comb W c)
      rw [ContinuousLinearMap.zero_apply]
      exact hω c)
  classical
  refine ⟨fun ω => if ω ∈ S then hz ω else 0, Measurable.ite hS hm measurable_const,
    fun φ => ?_, fun ω => ?_⟩
  · filter_upwards [hSae, hv φ] with ω h1 h2
    simp only [if_pos h1]
    exact h2
  · by_cases hω : ω ∈ S
    · simp only [if_pos hω]
      exact hrS ω hω
    · simp only [if_neg hω]
      exact ContinuousLinearMap.zero_comp _

end MarkovVer
end LQGMetric
