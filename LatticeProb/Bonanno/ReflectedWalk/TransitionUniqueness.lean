/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.TransitionUniqueness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.StrongMarkov

/-!
# Uniqueness in law reduces to the transition function (Gwynne–Sung, Theorem 1.6)

The uniqueness clause of `Theorem16Statement` is `IdentDistrib` of the trajectories, i.e.
equality of the laws on the path space with its cylinder σ-algebra, i.e. equality of all
finite-dimensional distributions.  This file shows that, for processes satisfying property
(iv) (the Markov property at deterministic times) and property (i), the finite-dimensional
distributions are determined by the **transition function**

  `p_t(z, y) := P_z(X_t = y)`  (`ProcessFamily.transition`)

alone: `P_z(X_{t₁} = y₁, …, X_{tₙ} = yₙ) = p_{t₁}(z, y₁) p_{t₂-t₁}(y₁, y₂) ⋯ p_{tₙ-tₙ₋₁}(yₙ₋₁, yₙ)`
(Chapman–Kolmogorov, `fdd_insert_max`), and the value `∞` never carries mass at a fixed time
(property (i)).  Hence two process families with the properties of Theorem 1.6 and the same
transition function have identically distributed trajectories (`identDistrib_of_transition`).

This is the law-side reduction of the uniqueness half of Theorem 1.6: whatever argument
identifies the laws of two processes satisfying (i)–(vi) (the paper's Section 3.4, through
`X̃ⁿ → X̃` in `L¹_loc`, or any other) only has to identify `P_z(X_t = y)` for all `z, t, y`.
The proof uses only (i) and (iv); the vertex cylinders of `StrongMarkov.lean` serve as the
generating π-system of the cylinder σ-algebra.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

universe u

namespace ReflectedWalk

variable {V : Type u}

namespace ProcessFamily

variable (𝓧 : ProcessFamily V)

/-- The transition function `p_t(z, y) := P_z(X_t = y)` of the family. -/
noncomputable def transition (z : V) (t : ℝ≥0) (y : V) : ℝ≥0∞ :=
  𝓧.P z {ω | 𝓧.X t ω = some y}

lemma measurable_trajectory : Measurable 𝓧.trajectory :=
  measurable_pi_iff.2 𝓧.measurable_X

/-- The one-time marginal of the law `P_x` is the transition function. -/
lemma law_eval (x : V) (s : ℝ≥0) (y : V) :
    𝓧.law x ((fun f : Trajectory V => f s) ⁻¹' {some y}) = 𝓧.transition x s y := by
  rw [ProcessFamily.law, Measure.map_apply 𝓧.measurable_trajectory
    (measurable_pi_apply s (Theorem16.measurableSet_option {some y}))]
  rfl

end ProcessFamily

namespace Theorem16

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- Property (i): at a fixed time the process is a.s. not at `∞`. -/
lemma measure_none_eq_zero {P : Measure Ω} {X : ℝ≥0 → Ω → Option V}
    (hi : AlmostEverywhereDefined P X) (t : ℝ≥0) : P {ω | X t ω = none} = 0 := by
  have h := hi t
  rw [ae_iff] at h
  refine measure_mono_null (fun ω hω => ?_) h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rintro ⟨⟨x, hx⟩, -⟩
  rw [hω] at hx
  exact Option.some_ne_none x hx.symm

/-- **Chapman–Kolmogorov step.**  For a finite set of times `s` with maximum `t'` and a later
time `a`, the finite-dimensional distribution at `insert a s` is the one at `s` times the
transition `p_{a - t'}(X_{t'}, X_a)`; the factor is `0` if either prescribed value is `∞`
(property (i)).  Uses property (iv) at the deterministic time `t'`. -/
lemma fdd_insert_max [Countable V] (𝓧 : ProcessFamily V)
    (hi : ∀ x, AlmostEverywhereDefined (𝓧.P x) 𝓧.X)
    (hM : ∀ z, MarkovProperty 𝓧.law (𝓧.P z) 𝓧.X)
    (z : V) {s : Finset ℝ≥0} (hs : s.Nonempty) {a : ℝ≥0} (ha : ∀ i ∈ s, i < a)
    (g : ℝ≥0 → Option V) :
    𝓧.P z {ω | ∀ i ∈ insert a s, 𝓧.X i ω = g i} =
      𝓧.P z {ω | ∀ i ∈ s, 𝓧.X i ω = g i} *
        (g (s.max' hs)).elim 0 (fun x => (g a).elim 0 fun y => 𝓧.transition x (a - s.max' hs) y) := by
  classical
  set t' := s.max' hs with ht'
  have ht's : t' ∈ s := s.max'_mem hs
  have ht'a : t' < a := ha t' ht's
  have hle : ∀ i ∈ s, i ≤ t' := fun i hi => s.le_max' i hi
  have hsub : {ω | ∀ i ∈ insert a s, 𝓧.X i ω = g i} ⊆ {ω | 𝓧.X t' ω = g t'} :=
    fun ω hω => hω t' (Finset.mem_insert_of_mem ht's)
  have hsub' : {ω | ∀ i ∈ insert a s, 𝓧.X i ω = g i} ⊆ {ω | 𝓧.X a ω = g a} :=
    fun ω hω => hω a (Finset.mem_insert_self a s)
  cases hgt : g t' with
  | none =>
    simp only [Option.elim_none, mul_zero]
    refine measure_mono_null hsub ?_
    rw [hgt]
    exact measure_none_eq_zero (hi z) t'
  | some x =>
    cases hga : g a with
    | none =>
      simp only [Option.elim_some, Option.elim_none, mul_zero]
      refine measure_mono_null hsub' ?_
      rw [hga]
      exact measure_none_eq_zero (hi z) a
    | some y =>
      simp only [Option.elim_some]
      -- the rectangle for the Markov property at `t'`
      let S : Set (Set.Iic t' → Option V) := ⋂ i ∈ s, {p | ∀ hi : i ≤ t', p ⟨i, hi⟩ = g i}
      have hS : MeasurableSet S := by
        refine MeasurableSet.biInter s.countable_toSet fun i _ => ?_
        by_cases hi : i ≤ t'
        · have : {p : Set.Iic t' → Option V | ∀ hi : i ≤ t', p ⟨i, hi⟩ = g i} =
              (fun p : Set.Iic t' → Option V => p ⟨i, hi⟩) ⁻¹' {g i} := by
            ext p; simp [hi]
          rw [this]
          exact measurable_pi_apply _ (measurableSet_option _)
        · have : {p : Set.Iic t' → Option V | ∀ hi : i ≤ t', p ⟨i, hi⟩ = g i} = Set.univ := by
            ext p; simp [hi]
          rw [this]
          exact MeasurableSet.univ
      have hpre : pastPath 𝓧.X t' ⁻¹' S = {ω | ∀ i ∈ s, 𝓧.X i ω = g i} := by
        ext ω
        simp only [Set.mem_preimage, S, Set.mem_iInter, Set.mem_ofPred_eq, pastPath]
        exact ⟨fun h i hi => h i hi (hle i hi), fun h i hi _ => h i hi⟩
      have hshift : shiftedPath 𝓧.X t' ⁻¹' ((fun f : Trajectory V => f (a - t')) ⁻¹' {some y}) =
          {ω | 𝓧.X a ω = some y} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, shiftedPath,
          tsub_add_cancel_of_le ht'a.le]
      have hset : {ω | ∀ i ∈ insert a s, 𝓧.X i ω = g i} =
          pastPath 𝓧.X t' ⁻¹' S ∩ {ω | 𝓧.X t' ω = some x} ∩
            shiftedPath 𝓧.X t' ⁻¹' ((fun f : Trajectory V => f (a - t')) ⁻¹' {some y}) := by
        rw [hpre, hshift]
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_insert, forall_eq_or_imp, hga]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h2, by rw [h2 t' ht's, hgt]⟩, h1⟩
        · rintro ⟨⟨h2, -⟩, h1⟩
          exact ⟨h1, h2⟩
      have hset2 : pastPath 𝓧.X t' ⁻¹' S ∩ {ω | 𝓧.X t' ω = some x} =
          {ω | ∀ i ∈ s, 𝓧.X i ω = g i} := by
        rw [hpre]
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨fun h => h.1, fun h => ⟨h, by rw [h t' ht's, hgt]⟩⟩
      rw [hset, markov_rectangle 𝓧.measurable_X (hM z) t' x hS
        (measurable_pi_apply (a - t') (measurableSet_option {some y})), hset2,
        ProcessFamily.law_eval]

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {𝓧 𝓧' : ProcessFamily V}

/-- **Finite-dimensional distributions are determined by the transition function.**  Two
process families satisfying the properties of Theorem 1.6 with the same transition function
`P_z(X_t = y)` have the same finite-dimensional distributions.  By induction on the finite set
of times (largest time first), using `fdd_insert_max`. -/
theorem fdd_eq_of_transition [Countable V] (h : IsReflectedWalk G w hmin 𝓧)
    (h' : IsReflectedWalk G w hmin 𝓧')
    (hp : ∀ x t y, 𝓧.transition x t y = 𝓧'.transition x t y) (z : V) (I : Finset ℝ≥0)
    (g : ℝ≥0 → Option V) :
    𝓧.P z {ω | ∀ i ∈ I, 𝓧.X i ω = g i} = 𝓧'.P z {ω | ∀ i ∈ I, 𝓧'.X i ω = g i} := by
  classical
  have hi : ∀ x, AlmostEverywhereDefined (𝓧.P x) 𝓧.X := fun x => (h x).2.1
  have hM : ∀ x, MarkovProperty 𝓧.law (𝓧.P x) 𝓧.X := fun x => (h x).2.2.2.2.2.1
  have hi' : ∀ x, AlmostEverywhereDefined (𝓧'.P x) 𝓧'.X := fun x => (h' x).2.1
  have hM' : ∀ x, MarkovProperty 𝓧'.law (𝓧'.P x) 𝓧'.X := fun x => (h' x).2.2.2.2.2.1
  induction I using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp only [Finset.mem_insert, Finset.notMem_empty, or_false, forall_eq]
      cases hga : g a with
      | none => rw [measure_none_eq_zero (hi z), measure_none_eq_zero (hi' z)]
      | some y => exact hp z a y
    · rw [fdd_insert_max 𝓧 hi hM z hs ha g, fdd_insert_max 𝓧' hi' hM' z hs ha g, ih]
      congr 1
      cases g (s.max' hs) <;> cases g a <;> simp [hp]

/-- **Uniqueness in law reduces to the transition function.**  Two process families with the
properties of Theorem 1.6 and the same transition function `P_z(X_t = y)` for all `z, t, y`
have identically distributed trajectories — the conclusion of the uniqueness clause of
`Theorem16Statement`.  The path-space laws agree on the vertex cylinders
(`fdd_eq_of_transition`), which form a π-system generating the cylinder σ-algebra. -/
theorem identDistrib_of_transition [Countable V] (h : IsReflectedWalk G w hmin 𝓧)
    (h' : IsReflectedWalk G w hmin 𝓧')
    (hp : ∀ x t y, 𝓧.transition x t y = 𝓧'.transition x t y) (z : V) :
    IdentDistrib 𝓧'.trajectory 𝓧.trajectory (𝓧'.P z) (𝓧.P z) := by
  refine ⟨𝓧'.measurable_trajectory.aemeasurable, 𝓧.measurable_trajectory.aemeasurable, ?_⟩
  refine ext_of_generate_finite (vertexCylinders V) generateFrom_vertexCylinders
    isPiSystem_vertexCylinders ?_ ?_
  · rintro _ ⟨I, g, rfl⟩
    rw [Measure.map_apply 𝓧'.measurable_trajectory (measurableSet_vertexCylinder I g),
      Measure.map_apply 𝓧.measurable_trajectory (measurableSet_vertexCylinder I g)]
    exact (fdd_eq_of_transition h h' hp z I fun i => some (g i)).symm
  · rw [Measure.map_apply 𝓧'.measurable_trajectory MeasurableSet.univ,
      Measure.map_apply 𝓧.measurable_trajectory MeasurableSet.univ]
    simp

end Theorem16

end ReflectedWalk
