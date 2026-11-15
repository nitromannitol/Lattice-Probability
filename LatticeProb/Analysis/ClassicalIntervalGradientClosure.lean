import LatticeProb.Analysis.ClassicalIntervalGradientParts
import LatticeProb.Analysis.ClassicalIntervalGradientDense
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # Closability of the classical interval gradient -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ComplexConjugate

namespace LatticeProb

open LQGMetric.HeatSq

/-- Sine tests satisfy the weak derivative identity for each graph pair. -/
theorem classicalIntervalGradientGraph_sine_pairing {a b : ℝ} (hab : a < b)
    (p : Lp ℂ 2 (volume.restrict (Ioo a b)) × Lp ℂ 2 (volume.restrict (Ioo a b)))
    (hp : p ∈ classicalIntervalGradientGraph a b) (n : ℕ) :
    inner ℂ ((intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n)) p.2 =
      -inner ℂ ((intervalSineDerivative_memLp a b n).toLp
        (intervalSineDerivative a (b - a) n)) p.1 := by
  have hv : Continuous (intervalSineMode a (b - a) n) := by
    unfold intervalSineMode sinMode
    fun_prop
  have hd : ∀ x ∈ Ioo a b, HasDerivAt (intervalSineMode a (b - a) n)
      (intervalSineDerivative a (b - a) n x) x := by
    intro x hx
    convert (hasDerivAt_const_mul_sinMode a (b - a) 1 (n + 1) x).ofReal_comp using 1 <;>
      simp only [intervalSineDerivative, one_mul]
    funext y
    rfl
  have hc : Continuous (intervalSineDerivative a (b - a) n) := by
    unfold intervalSineDerivative
    fun_prop
  obtain ⟨f, g, hf, hg, hparts⟩ := classicalIntervalGradientGraph_parts hab p hp
    hv.continuousOn hd (hc.intervalIntegrable a b)
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 : (fun x => inner ℂ (((intervalSineMode_memLp a b n).toLp
      (intervalSineMode a (b - a) n)) x) (p.2 x)) =ᵐ[volume.restrict (Ioo a b)]
      (fun x => g x * intervalSineMode a (b - a) n x) := by
    filter_upwards [(intervalSineMode_memLp a b n).coeFn_toLp, hg] with x hx hy
    rw [hx, hy]
    simp only [intervalSineMode, sinMode, RCLike.inner_apply', Complex.conj_ofReal, mul_comm]
  have h2 : (fun x => inner ℂ (((intervalSineDerivative_memLp a b n).toLp
      (intervalSineDerivative a (b - a) n)) x) (p.1 x)) =ᵐ[volume.restrict (Ioo a b)]
      (fun x => f x * intervalSineDerivative a (b - a) n x) := by
    filter_upwards [(intervalSineDerivative_memLp a b n).coeFn_toLp, hf] with x hx hy
    rw [hx, hy]
    simp only [intervalSineDerivative, RCLike.inner_apply', Complex.conj_ofReal, mul_comm]
  rw [integral_congr_ae h1, integral_congr_ae h2]
  rw [intervalIntegral.integral_of_le hab.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    intervalIntegral.integral_of_le hab.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hparts
  linear_combination hparts

/-- The classical zero-boundary derivative admits a closed extension. -/
theorem classicalIntervalGradient_isClosable {a b : ℝ} (hab : a < b) :
    (classicalIntervalGradient a b).IsClosable := by
  let T := classicalIntervalGradient a b
  let G := T.graph.topologicalClosure
  have hsingle : ∀ p, p ∈ G → p.1 = 0 → p.2 = 0 := by
    intro p hp hp0
    have hcoeff : ∀ n : ℕ, (∫ x in a..b,
        (Real.sin (Real.pi * (n : ℝ) * (x - a) / (b - a)) : ℂ) * p.2 x) = 0 := by
      intro n
      cases n with
      | zero => simp
      | succ n =>
        let s := (intervalSineMode_memLp a b n).toLp (intervalSineMode a (b - a) n)
        let d := (intervalSineDerivative_memLp a b n).toLp
          (intervalSineDerivative a (b - a) n)
        have hclosed : IsClosed {q : _ × _ | inner ℂ s q.2 = -inner ℂ d q.1} :=
          isClosed_eq (by fun_prop) (by fun_prop)
        have hsub : (T.graph : Set (_ × _)) ⊆
            {q : _ × _ | inner ℂ s q.2 = -inner ℂ d q.1} := by
          intro q hq
          apply classicalIntervalGradientGraph_sine_pairing hab q _ n
          simpa [T, classicalIntervalGradient_graph] using hq
        have h := closure_minimal hsub hclosed hp
        have hi : inner ℂ s p.2 = 0 := by simpa [hp0] using h
        rw [MeasureTheory.L2.inner_def] at hi
        have heq : (fun x => inner ℂ (s x) (p.2 x)) =ᵐ[volume.restrict (Ioo a b)]
            (fun x : ℝ => (Real.sin (Real.pi * ((n + 1 : ℕ) : ℝ) *
              (x - a) / (b - a)) : ℂ) * p.2 x) := by
          filter_upwards [(intervalSineMode_memLp a b n).coeFn_toLp] with x hx
          change s x = _ at hx
          rw [hx]
          simp only [intervalSineMode, sinMode, RCLike.inner_apply', Complex.conj_ofReal]
        rw [integral_congr_ae heq] at hi
        rw [intervalIntegral.integral_of_le hab.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        exact hi
    have hends : a + (b - a) = b := by ring
    have hz := ae_eq_zero_of_translated_interval_sine_integrals_eq_zero
      (a := a) (θ := b - a) (by linarith) (f := p.2)
      (by simpa only [hends] using Lp.memLp p.2)
      (by simpa only [hends] using hcoeff)
    rw [hends] at hz
    apply Lp.ext
    exact hz.trans (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioo a b))).symm
  refine ⟨G.toLinearPMap, ?_⟩
  exact (Submodule.toLinearPMap_graph_eq G hsingle).symm

end LatticeProb
