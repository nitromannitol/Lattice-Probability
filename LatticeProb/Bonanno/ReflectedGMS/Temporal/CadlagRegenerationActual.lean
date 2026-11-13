/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CadlagRegenerationActual at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CadlagRegenerationCoding

/-!
# The actual reflected walk is cycle-ergodic on the regenerative coding

This module attaches the checked one-step whole-cycle regeneration of the **actual** reflected
walk (`Temporal/ActualExcursionErgodicIdentification.map_futureAt_firstReturnTime`,
`indepFun_killedPathAt_futureAt`, both on the sample space `PF.Ω` with the future read into the
raw `Trajectory V`) to the regenerative coding `RegenPath v` of
`Temporal/CadlagRegenerationCoding`, where the cycle shift is a measurable self-map, and closes
the forward half of the first paragraph of `p:lem:regeninvariant`'s proof.

## Results

* `ae_isRegenPath` — **the actual trajectory lies in the coding almost surely**: under
  `PF.P v`, the path is right-regular ((ii)+(R)), starts at `v`, is at `v` at arbitrarily large
  times (property (v)), is off `v` at arbitrarily large times (`ae_leaves`: property (iv) at the
  integer times plus the a.s. finiteness of the exponential exit time), and has dense vertex
  times (property (i) along a dense sequence).
* `exists_regenLaw` — the law of the actual walk from `v` **lifts** to a probability law `μ` on the
  coding (`μ.map Subtype.val = PF.law v`) under which `μ.map (regenShift v) = μ` and
  `IndepFun (regenCycle v) (regenShift v) μ`: the two actual-process regeneration facts,
  transported to the coding.  The lift is unique (`eq_of_map_val_eq`).
* `cycleErgodic_actualWalk` — **the law of the actual reflected walk from `v`, on the regenerative
  coding, is ergodic under the cycle shift**: every bounded measurable functional of the coded
  path that is invariant under re-rooting at the first return to `v` is `μ`-a.s. constant.
  Hypotheses: `IsReflectedWalk` and connectivity of the graph only.

## What this is, and what it is not

This is the forward half of clause 1 of the handoff's four clauses (two-sided i.i.d. cycle law):
forward cycles are i.i.d. (`iIndep_cycleSigma`) and the forward cycle shift is ergodic.  It is a
statement about the **forward, fixed-start, fixed-environment** law.  The two-sided law
`ℙ_H^v`, the reversal of the complete stopped cycle (clause 2), the `L_v/h_v` size-biasing
(clause 3) and the start-vertex independence (clause 4) are not addressed here, and nothing here
certifies `p:lem:regeninvariant`, `p:prop:timeergodic`, `p:lem:bracketlimit`, `p:thm:areaclt` or
either main theorem.

The coding is the **right-regular, forward** coding, not `TrajectoryCoding.CadlagPath`: see the
module docstring of `Temporal/CadlagRegenerationCoding` (forward regeneration needs right
regularity only; the two-sided coding will need the a.s. left limits of
`Forms/VertexIndicatorLeftLimits`).
-/

set_option autoImplicit false

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CadlagRegeneration

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.TargetReturnRecursion
open ReflectedGMS.Temporal.ActualExcursionErgodicIdentification
open ReflectedGMS.RegenerativeInvarianceFiberwise

universe u

variable {V : Type u}

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Nontrivial V]
variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}

theorem measurable_trajectory : Measurable PF.trajectory :=
  measurable_pi_iff.2 fun t => PF.measurable_X t

/-! ### The actual trajectory lies in the coding almost surely -/

/-- **The actual walk leaves `v` at arbitrarily large times.**  At each integer time `n`,
property (iv) makes the future after `n` on `{X_n = v}` a fresh copy of the walk from `v`, whose
exit time from `v` is a.s. finite (property (iii)); by right regularity the exit is seen along a
dense sequence of times. -/
theorem ae_leaves (h : IsReflectedWalk G w hmin PF) (v : V) :
    ∀ᵐ ω ∂PF.P v, ∀ T : ℝ≥0, ∃ t, T ≤ t ∧ PF.X t ω ≠ some v := by
  set d : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0 with hd
  set B : Set (Trajectory V) := {y | ∀ n : ℕ, y (d n) = some v} with hBdef
  have hB : MeasurableSet B := by
    have hBeq : B = ⋂ n : ℕ, (fun y : Trajectory V => y (d n)) ⁻¹' {some v} := by
      ext y
      simp [hBdef]
    rw [hBeq]
    exact MeasurableSet.iInter fun n => measurable_pi_apply (d n) (measurableSet_option _)
  -- the walk from `v` never stays at `v` along the whole dense sequence
  have hlawB : PF.law v B = 0 := by
    rw [ProcessFamily.law, Measure.map_apply measurable_trajectory hB]
    have hfin : ∀ᵐ ω ∂PF.P v, exitTime PF.X v ω ≠ ⊤ := by
      have h0 := measure_exitTime_eq_top h v
      rw [ae_iff]
      simpa using h0
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hfin, ae_rightRegularAt (h v).2.2.1 (h v).2.2.2.1] with ω hω hreg
    intro hωB
    have hωB' : ∀ n : ℕ, PF.X (d n) ω = some v := hωB
    cases he : exitTime PF.X v ω with
    | top => exact hω he
    | coe e =>
      have he' : MeasureTheory.hittingAfter PF.X {s : Option V | s ≠ some v} 0 ω = e := he
      have hmem : PF.X e ω ∈ {s : Option V | s ≠ some v} :=
        mem_of_hittingAfter_eq_of_rightRegular hreg (admissibleTarget_ne v) he'
      obtain ⟨ε, hε, hεs⟩ := exists_Ico_iff_mem_of_rightRegular hreg (admissibleTarget_ne v) e
      obtain ⟨c, ⟨n, rfl⟩, hec, hcε⟩ :=
        Dense.exists_between (TopologicalSpace.denseRange_denseSeq ℝ≥0)
          (lt_add_of_pos_right e hε)
      have hdn : PF.X (d n) ω ∈ {s : Option V | s ≠ some v} :=
        (hεs (d n) ⟨hec.le, hcε⟩).2 hmem
      exact hdn (hωB' n)
  -- at each integer time, staying at `v` forever is null
  have hnull : ∀ n : ℕ, ∀ᵐ ω ∂PF.P v,
      ¬ ∀ t : ℝ≥0, (n : ℝ≥0) ≤ t → PF.X t ω = some v := by
    intro n
    rw [ae_iff]
    simp only [not_not]
    have hm := markov_rectangle (μ := PF.law) PF.measurable_X (h v).2.2.2.2.2.1 (n : ℝ≥0) v
      (S := Set.univ) MeasurableSet.univ hB
    simp only [Set.preimage_univ, Set.univ_inter, hlawB, mul_zero] at hm
    refine measure_mono_null ?_ hm
    intro ω hω
    refine ⟨hω (n : ℝ≥0) le_rfl, ?_⟩
    intro k
    exact hω (d k + n) le_add_self
  filter_upwards [ae_all_iff.2 hnull] with ω hω T
  have h1 := hω ⌈T⌉₊
  simp only [not_forall, exists_prop] at h1
  obtain ⟨t, hnt, ht⟩ := h1
  exact ⟨t, (Nat.le_ceil T).trans hnt, ht⟩

/-- **The actual trajectory lies in the regenerative coding almost surely.** -/
theorem ae_isRegenPath (h : IsReflectedWalk G w hmin PF) (v : V) :
    ∀ᵐ ω ∂PF.P v, IsRegenPath v (PF.trajectory ω) := by
  have hdense : ∀ᵐ ω ∂PF.P v, ∀ n : ℕ,
      PF.X (TopologicalSpace.denseSeq ℝ≥0 n) ω ≠ none := by
    refine ae_all_iff.2 fun n => ?_
    filter_upwards [(h v).2.1 (TopologicalSpace.denseSeq ℝ≥0 n)] with ω hω
    obtain ⟨⟨x, hx⟩, -⟩ := hω
    rw [hx]
    exact fun h' => nomatch h'
  filter_upwards [ae_rightRegularAt (h v).2.2.1 (h v).2.2.2.1, (h v).1, ae_leaves h v,
    (h v).2.2.2.2.2.2.1, hdense] with ω hreg hstart hleave hrec hden
  refine ⟨hreg, hstart, hleave, hrec, fun a b hab => ?_⟩
  obtain ⟨c, ⟨n, rfl⟩, hac, hcb⟩ :=
    Dense.exists_between (TopologicalSpace.denseRange_denseSeq ℝ≥0) hab
  exact ⟨_, hac, hcb, hden n⟩

/-! ### Transport of the two regeneration facts to the coding -/

end ReflectedGMS.CadlagRegeneration
