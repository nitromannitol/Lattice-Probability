import LatticeProb.Analysis.DerivativeRepresentative
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Classical zero-boundary interval gradient -/

set_option autoImplicit false

open MeasureTheory Set Filter

namespace LatticeProb

/-- The graph of the classical derivative on continuous zero-boundary
representatives of complex L² classes on an open interval. -/
def classicalIntervalGradientGraph (a b : ℝ) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioo a b)) ×
      Lp ℂ 2 (volume.restrict (Ioo a b))) where
  carrier := {p | ∃ f g : ℝ → ℂ,
    (fun t => p.1 t) =ᵐ[volume.restrict (Ioo a b)] f ∧
    (fun t => p.2 t) =ᵐ[volume.restrict (Ioo a b)] g ∧
    ContinuousOn f (Icc a b) ∧ f a = 0 ∧ f b = 0 ∧
    ∀ t ∈ Ioo a b, HasDerivAt f (g t) t}
  zero_mem' := by
    refine ⟨0, 0, Lp.coeFn_zero _ _ _, Lp.coeFn_zero _ _ _, ?_, rfl, rfl, ?_⟩
    · exact continuousOn_const
    · intro t ht
      exact hasDerivAt_const t 0
  add_mem' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨f, g, hf, hg, hc, ha, hb, hd⟩
      ⟨f', g', hf', hg', hc', ha', hb', hd'⟩
    refine ⟨f + f', g + g', ?_, ?_, hc.add hc', ?_, ?_, ?_⟩
    · exact (Lp.coeFn_add x x').trans (hf.add hf')
    · exact (Lp.coeFn_add y y').trans (hg.add hg')
    · simp [ha, ha']
    · simp [hb, hb']
    · intro t ht
      exact (hd t ht).add (hd' t ht)
  smul_mem' := by
    rintro c ⟨x, y⟩ ⟨f, g, hf, hg, hc, ha, hb, hd⟩
    refine ⟨c • f, c • g, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (Lp.coeFn_smul c x).trans (hf.const_smul c)
    · exact (Lp.coeFn_smul c y).trans (hg.const_smul c)
    · exact continuousOn_const.smul hc
    · simp [ha]
    · simp [hb]
    · intro t ht
      exact (hd t ht).const_smul c

/-- The graph is single-valued, by uniqueness of classical derivative
representatives on the open interval. -/
theorem classicalIntervalGradientGraph_singleValued (a b : ℝ)
    (p : Lp ℂ 2 (volume.restrict (Ioo a b)) ×
      Lp ℂ 2 (volume.restrict (Ioo a b)))
    (hp : p ∈ classicalIntervalGradientGraph a b) (hz : p.1 = 0) : p.2 = 0 := by
  obtain ⟨f, g, hf, hg, hc, ha, hb, hd⟩ := hp
  have hfzero : f =ᵐ[volume.restrict (Ioo a b)] (0 : ℝ → ℂ) := by
    rw [hz] at hf
    exact hf.symm.trans (Lp.coeFn_zero _ _ _)
  have hgzero : g =ᵐ[volume.restrict (Ioo a b)] (0 : ℝ → ℂ) :=
    ae_eq_derivative_of_ae_eq isOpen_Ioo hfzero hd (fun t _ => hasDerivAt_const t 0)
  apply Lp.ext
  exact (hg.trans hgzero).trans (Lp.coeFn_zero _ _ _).symm

/-- The partial classical derivative with zero boundary values. -/
noncomputable def classicalIntervalGradient (a b : ℝ) :
    Lp ℂ 2 (volume.restrict (Ioo a b)) →ₗ.[ℂ]
      Lp ℂ 2 (volume.restrict (Ioo a b)) :=
  (classicalIntervalGradientGraph a b).toLinearPMap

/-- The partial derivative has exactly the graph described by its classical
representatives. -/
theorem classicalIntervalGradient_graph (a b : ℝ) :
    (classicalIntervalGradient a b).graph = classicalIntervalGradientGraph a b :=
  Submodule.toLinearPMap_graph_eq _ (classicalIntervalGradientGraph_singleValued a b)

end LatticeProb
