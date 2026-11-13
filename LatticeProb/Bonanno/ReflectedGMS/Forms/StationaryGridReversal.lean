/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryGridReversal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryFiniteGridLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationarySpeedMeasure
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Algebra.BigOperators.Intervals

/-! Reversal of finite constant-step grids for the actual reflected process
under the unnormalized stationary speed law. -/

-- Merged from `ReflectedGMS/Forms/ReversiblePathWeights.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ReversiblePathWeights

/-! Finite path-weight reversal from the proved full-semigroup detailed
balance identity. This is the algebraic component of stationary grid reversal. -/
set_option autoImplicit false
open scoped NNReal BigOperators

namespace ReflectedGMS.FullNetworkForm
variable {V : Type*} [DecidableEq V]
  (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)

include hm

theorem semigroup_path_weight_balance (v : ℕ → V) (τ : ℕ → ℝ≥0) (n : ℕ) :
    m (v 0) * (∏ i ∈ Finset.range n, semigroupKernel G m (τ i) (v i) (v (i + 1))) =
      m (v n) * (∏ i ∈ Finset.range n, semigroupKernel G m (τ i) (v (i + 1)) (v i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← mul_assoc, ih]
    calc
      _ = (∏ i ∈ Finset.range n, semigroupKernel G m (τ i) (v (i + 1)) (v i)) *
          (m (v n) * semigroupKernel G m (τ n) (v n) (v (n + 1))) := by ring
      _ = (∏ i ∈ Finset.range n, semigroupKernel G m (τ i) (v (i + 1)) (v i)) *
          (m (v (n + 1)) * semigroupKernel G m (τ n) (v (n + 1)) (v n)) := by
        rw [semigroupKernel_detailedBalance G m hm]
      _ = _ := by ring

theorem semigroup_grid_path_weight_reverse (v : ℕ → V) (δ : ℝ≥0) (n : ℕ) :
    m (v 0) * (∏ i ∈ Finset.range n, semigroupKernel G m δ (v i) (v (i + 1))) =
      m (v n) * (∏ i ∈ Finset.range n,
        semigroupKernel G m δ (v (n - i)) (v (n - (i + 1)))) := by
  rw [semigroup_path_weight_balance G m hm v (fun _ ↦ δ) n]
  congr 1
  rw [← Finset.prod_range_reflect
    (fun i ↦ semigroupKernel G m δ (v (i + 1)) (v i)) n]
  apply Finset.prod_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  congr 2 <;> omega

end ReflectedGMS.FullNetworkForm

end Merged_ReversiblePathWeights

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The first `n + 1` positions on a constant-time-step grid. -/
def reflectedGridPath (PF : ProcessFamily V) (δ : ℝ≥0) (n : ℕ) (ω : PF.Ω) :
    Fin (n + 1) → Option V :=
  fun i => PF.X ((i.1 : ℝ≥0) * δ) ω

/-- The same finite grid, read in reverse order. -/
def reflectedReverseGridPath (PF : ProcessFamily V) (δ : ℝ≥0) (n : ℕ) (ω : PF.Ω) :
    Fin (n + 1) → Option V :=
  fun i => PF.X ((i.rev.1 : ℝ≥0) * δ) ω

lemma measurable_reflectedGridPath (PF : ProcessFamily V) (δ : ℝ≥0) (n : ℕ) :
    Measurable (reflectedGridPath PF δ n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact PF.measurable_X ((i.1 : ℝ≥0) * δ)

lemma measurable_reflectedReverseGridPath (PF : ProcessFamily V) (δ : ℝ≥0) (n : ℕ) :
    Measurable (reflectedReverseGridPath PF δ n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact PF.measurable_X ((i.rev.1 : ℝ≥0) * δ)

/-- Reversing a specified vertex cylinder preserves its stationary mass. -/
theorem reflectedSpeedLaw_reflectedGridEvent_reverse
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun x => G.pi x / m x) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ x, 0 < m x)
    (hmsum : Summable m) (δ : ℝ≥0) (n : ℕ) (v : ℕ → V) :
    reflectedSpeedLaw PF m (reflectedGridEvent PF δ n v) =
      reflectedSpeedLaw PF m
        (reflectedGridEvent PF δ n (fun i => v (n - i))) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (reflectedSpeedLaw PF m) _) (measure_ne_top (reflectedSpeedLaw PF m) _)).mp
  rw [← measureReal_def, ← measureReal_def,
    reflectedSpeedLaw_reflectedGridEvent_real h hG hm hmsum,
    reflectedSpeedLaw_reflectedGridEvent_real h hG hm hmsum]
  simpa using semigroup_grid_path_weight_reverse G m hm v δ n

private lemma reflectedSpeedLaw_position_none
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun x => G.pi x / m x) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ x, 0 < m x)
    (hmsum : Summable m) (t : ℝ≥0) :
    reflectedSpeedLaw PF m {ω | PF.X t ω = none} = 0 := by
  have he := congrArg (fun μ : Measure (Option V) => μ {none})
    (reflectedSpeedLaw_map_position h hG hm hmsum t)
  rw [Measure.map_apply (PF.measurable_X t) (measurableSet_singleton none),
    Measure.map_apply (measurable_of_countable (some : V → Option V))
      (measurableSet_singleton none)] at he
  have hemp : (some : V → Option V) ⁻¹' {none} = ∅ := by
    ext x
    simp
  rw [hemp, measure_empty] at he
  exact he

/-- The finite-dimensional distribution of the actual stationary reflected
process is invariant under reversal of every constant-step grid. -/
theorem reflectedSpeedLaw_map_reflectedGridPath_reverse
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun x => G.pi x / m x) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ x, 0 < m x)
    (hmsum : Summable m) (δ : ℝ≥0) (n : ℕ) :
    (reflectedSpeedLaw PF m).map (reflectedGridPath PF δ n) =
      (reflectedSpeedLaw PF m).map (reflectedReverseGridPath PF δ n) := by
  classical
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.map_apply (measurable_reflectedGridPath PF δ n)
      (measurableSet_singleton q),
    Measure.map_apply (measurable_reflectedReverseGridPath PF δ n)
      (measurableSet_singleton q)]
  by_cases hnone : ∃ i, q i = none
  · obtain ⟨i, hi⟩ := hnone
    have hforward :
        reflectedGridPath PF δ n ⁻¹' {q} ⊆
          {ω | PF.X ((i.1 : ℝ≥0) * δ) ω = none} := by
      intro ω hω
      have := congrFun (Set.mem_singleton_iff.mp hω) i
      simpa [reflectedGridPath, hi] using this
    have hreverse :
        reflectedReverseGridPath PF δ n ⁻¹' {q} ⊆
          {ω | PF.X ((i.rev.1 : ℝ≥0) * δ) ω = none} := by
      intro ω hω
      have := congrFun (Set.mem_singleton_iff.mp hω) i
      simpa [reflectedReverseGridPath, hi] using this
    rw [measure_mono_null hforward
        (reflectedSpeedLaw_position_none h hG hm hmsum _),
      measure_mono_null hreverse
        (reflectedSpeedLaw_position_none h hG hm hmsum _)]
  · push_neg at hnone
    let default : V := Classical.choice (inferInstance : Nonempty V)
    let v : ℕ → V := fun i =>
      if hi : i < n + 1 then (q ⟨i, hi⟩).getD default else default
    have hq (i : Fin (n + 1)) : q i = some (v i.1) := by
      simp only [v, i.2, dite_true]
      cases hqi : q i with
      | none => exact (hnone i hqi).elim
      | some x => simp [hqi]
    have hpre_forward :
        reflectedGridPath PF δ n ⁻¹' {q} = reflectedGridEvent PF δ n v := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, reflectedGridEvent,
        Set.mem_setOf_eq]
      constructor
      · intro hw i hi
        have hil : i < n + 1 := Finset.mem_range.mp hi
        have := congrFun hw (⟨i, hil⟩ : Fin (n + 1))
        simpa [reflectedGridPath, hq] using this
      · intro hw
        funext i
        exact (hw i.1 (Finset.mem_range.mpr i.2)).trans (hq i).symm
    have hpre_reverse :
        reflectedReverseGridPath PF δ n ⁻¹' {q} =
          reflectedGridEvent PF δ n (fun i => v (n - i)) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, reflectedGridEvent,
        Set.mem_setOf_eq]
      constructor
      · intro hw j hj
        have hjle : j ≤ n := by
          have := Finset.mem_range.mp hj
          omega
        let i : Fin (n + 1) := ⟨n - j, by omega⟩
        have hval : i.rev.1 = j := by
          change n + 1 - ((n - j) + 1) = j
          omega
        have := congrFun hw i
        rw [reflectedReverseGridPath, hval] at this
        have hqi := hq i
        simpa [i] using this.trans hqi
      · intro hw
        funext i
        have hval : n - i.rev.1 = i.1 := by
          change n - (n + 1 - (i.1 + 1)) = i.1
          have := i.2
          omega
        have hx := hw i.rev.1 (Finset.mem_range.mpr i.rev.2)
        rw [hval] at hx
        exact hx.trans (hq i).symm
    rw [hpre_forward, hpre_reverse]
    exact reflectedSpeedLaw_reflectedGridEvent_reverse h hG hm hmsum δ n v

end ReflectedGMS
