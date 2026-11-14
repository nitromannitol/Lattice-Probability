import LatticeProb.Walk.ConstantStepMeasurable
import LatticeProb.Topology.KnotReparametrization
import Mathlib.Topology.LocallyFinite
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! # Continuous constant-step interpolation -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- Constant-step interpolation is continuous, including at its knots. -/
theorem continuous_path (m : ℝ) (p : ℕ → ℂ) : Continuous (path m p) := by
  by_cases hm : 0 < m
  · let a : ℝ≥0 := ⟨m, hm.le⟩
    have ha : 0 < a := hm
    let τ := knot a
    have hmono : StrictMono τ := knot_strictMono ha
    have hzero : τ 0 = 0 := knot_zero a
    have hunb : ∀ b, ∃ n, b < τ n := knot_unbounded ha
    have hloc : LocallyFinite (fun n : ℕ => Icc (τ n) (τ (n + 1))) := by
      intro t
      obtain ⟨N, hN⟩ := hunb t
      refine ⟨Iio (τ N), Iio_mem_nhds hN, (finite_lt_nat N).subset ?_⟩
      intro n hn
      obtain ⟨x, hx, hx'⟩ := hn
      change n < N
      by_contra h
      have hle := hmono.monotone (Nat.le_of_not_gt h)
      exact (not_lt_of_ge (hle.trans hx.1)) hx'
    have hcover : (⋃ n : ℕ, Icc (τ n) (τ (n + 1))) = univ := by
      apply eq_univ_of_forall
      intro t
      obtain ⟨n, hn, hn'⟩ := LatticeProb.KnotReparam.exists_knot_bracket hzero hunb t
      exact mem_iUnion.mpr ⟨n, hn, hn'.le⟩
    apply hloc.continuous hcover (fun _ => isClosed_Icc)
    intro n
    let f : ℝ≥0 → ℂ := fun t => AffineMap.lineMap (p n) (p (n + 1))
      (((t : ℝ) - τ n) / ((τ (n + 1) : ℝ) - τ n))
    have hf : Continuous f := by
      dsimp [f, AffineMap.lineMap_apply_module']
      fun_prop
    apply hf.continuousOn.congr
    intro t ht
    change path (a : ℝ) p t = f t
    rcases ht.2.lt_or_eq with ht' | ht'
    · exact path_eq_lineMap ha p n t ht.1 ht'
    · subst t
      change path (a : ℝ) p (knot a (n + 1)) = f (τ (n + 1))
      rw [path_knot ha p (n + 1)]
      dsimp [f]
      have hne : ((τ (n + 1) : ℝ) - τ n) ≠ 0 := by
        have h := NNReal.coe_lt_coe.mpr (hmono (Nat.lt_succ_self n))
        linarith
      simp [hne]
  · have hm' : m ≤ 0 := le_of_not_gt hm
    have heq : path m p = fun t : ℝ≥0 => AffineMap.lineMap (p 0) (p 1) (m * (t : ℝ)) := by
      funext t
      change AffineMap.lineMap (p ⌊m * (t : ℝ)⌋₊) (p (⌊m * (t : ℝ)⌋₊ + 1))
        (m * (t : ℝ) - (⌊m * (t : ℝ)⌋₊ : ℝ)) = _
      have hfloor : ⌊m * (t : ℝ)⌋₊ = 0 :=
        Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hm' t.2)
      rw [hfloor]
      simp only [Nat.cast_zero, sub_zero, zero_add]
    rw [heq]
    simp only [AffineMap.lineMap_apply_module']
    fun_prop

/-- Constant-step interpolation as a continuous path. -/
def continuousPath (m : ℝ) (p : ℕ → ℂ) : C(ℝ≥0, ℂ) :=
  ⟨path m p, continuous_path m p⟩

@[simp] theorem continuousPath_apply (m : ℝ) (p : ℕ → ℂ) (t : ℝ≥0) :
    continuousPath m p t = path m p t := rfl

end LatticeProb.ConstantStepInterpolation
