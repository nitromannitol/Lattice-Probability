/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SpectralSemigroup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ComplexResolvent
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupMultiplier
import LatticeProb.Bonanno.ReflectedGMS.Forms.StrongContinuity
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! The spectral semigroup is obtained from the existing continuous functional
calculus of complex Hilbert-space operators. Its full-form specialization uses
the checked complex extension of the actual full-domain resolvent. Association
with the reflected process and the Markov property are separate obligations. -/

set_option autoImplicit false

open Filter
open scoped Topology NNReal

namespace ReflectedGMS.FullNetworkForm

open SemigroupMultiplier ComplexSequenceSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Apply the continuous scalar multiplier to a self-adjoint resolvent. -/
noncomputable def spectralSemigroup (R : H →L[ℂ] H) (t : ℝ≥0) : H →L[ℂ] H :=
  cfc (k t) R

theorem spectralSemigroup_zero (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    spectralSemigroup R 0 = 1 := by
  simp only [spectralSemigroup, k_zero]
  exact cfc_const_one ℝ R hR

theorem spectralSemigroup_add (R : H →L[ℂ] H) (s t : ℝ≥0) :
    spectralSemigroup R (s + t) = spectralSemigroup R s * spectralSemigroup R t := by
  simp only [spectralSemigroup, k_add]
  exact cfc_mul (k s) (k t) R (continuous_k s).continuousOn (continuous_k t).continuousOn

theorem spectralSemigroup_isSelfAdjoint (R : H →L[ℂ] H) (t : ℝ≥0) :
    IsSelfAdjoint (spectralSemigroup R t) := IsSelfAdjoint.cfc

theorem spectralSemigroup_norm_le_one (R : H →L[ℂ] H)
    (hspec : spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) :
    ‖spectralSemigroup R t‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (k_nonneg t x)]
  exact k_le_one (hspec hx).1 (hspec hx).2

/-- Multiplying by the resolvent removes the spectral singularity at zero. -/
theorem spectralSemigroup_range_error (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1) (t : ℝ≥0) (y : H) :
    ‖spectralSemigroup R t (R y) - R y‖ ≤ (t : ℝ) * ‖y‖ := by
  have hid : cfc (fun x : ℝ => x) R = R := cfc_id' ℝ R hR
  have heq : spectralSemigroup R t * R - R =
      cfc (fun x : ℝ => k t x * x - x) R := by
    rw [cfc_sub (fun x : ℝ => k t x * x) (fun x : ℝ => x) R
      ((continuous_k t).mul continuous_id).continuousOn continuous_id.continuousOn,
      cfc_mul (k t) (fun x : ℝ => x) R
        (continuous_k t).continuousOn continuous_id.continuousOn, hid]
    rfl
  have hn : ‖spectralSemigroup R t * R - R‖ ≤ (t : ℝ) := by
    rw [heq]
    apply norm_cfc_le t.property
    intro x hx
    change |k t x * x - x| ≤ (t : ℝ)
    rw [mul_comm (k t x) x]
    exact abs_mul_k_sub_le (t := t) (x := x) (hspec hx).1 (hspec hx).2
  calc
    _ = ‖(spectralSemigroup R t * R - R) y‖ := rfl
    _ ≤ ‖spectralSemigroup R t * R - R‖ * ‖y‖ :=
      (spectralSemigroup R t * R - R).le_opNorm y
    _ ≤ (t : ℝ) * ‖y‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg y)

/-- Strong continuity at zero holds even when zero belongs to the spectrum. -/
theorem spectralSemigroup_tendsto_zero (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1) (hdense : DenseRange R) (x : H) :
    Tendsto (fun t => spectralSemigroup R t x) (𝓝 0) (𝓝 x) :=
  contraction_tendsto_of_range_error (spectralSemigroup R) R
    (spectralSemigroup_norm_le_one R hspec) hdense
    (spectralSemigroup_range_error R hR hspec) x

/-- The concrete spectral construction uses the actual full finite-energy form. -/
noncomputable def fullFormSemigroupComplex {V : Type*}
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (t : ℝ≥0) :
    ComplexL2 V →L[ℂ] ComplexL2 V :=
  spectralSemigroup (complexOneResolvent G m) t

theorem fullFormSemigroupComplex_tendsto_zero {V : Type*}
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (x : ComplexL2 V) :
    Tendsto (fun t => fullFormSemigroupComplex G m t x) (𝓝 0) (𝓝 x) :=
  spectralSemigroup_tendsto_zero (complexOneResolvent G m)
    (complexOneResolvent_isSelfAdjoint G m) (complexOneResolvent_spectrum_subset G m)
    (denseRange_complexOneResolvent G m hm) x

end ReflectedGMS.FullNetworkForm
