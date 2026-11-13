/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CadlagRegenerationAbstract at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerativeInvarianceFiberwise
import Mathlib.Probability.BorelCantelli

/-!
# Cycle ergodicity when the cycles generate the path only on a full-measure event

`Temporal/RegenerativeInvarianceFiberwise.cycleErgodic_of_regeneration` proves ergodicity of the
cycle shift `ρ` from one-step regeneration (`μ.map ρ = μ`, `IndepFun C ρ μ`) and the **exact**
generation clause `⨆ k, cycleSigma ρ C k = ⊤`.  For an actual path the exact clause is false: a
path is the splice of its cycles only when the cycle lengths sum to `∞`, and on a path space that
is an almost-sure statement, not a pointwise one.  This module removes that gap.

* `cycleErgodic_of_regeneration_on` — the same conclusion when the cycles generate the path
  σ-algebra **on** a `ρ`-invariant event `E` that is itself cycle-measurable and has full
  measure: `∀ s measurable, s ∩ E ∈ ⨆ k, cycleSigma ρ C k`.
* `ae_mem_longRun` — **the second Borel–Cantelli lemma for regenerative cycles**: if the cycle
  length `len (C x)` is strictly positive, then almost surely the cycle lengths sum to `∞`
  (`longRun`).  The independence is `iIndep_cycleSigma`, so nothing beyond one-step regeneration
  is used.
* `measurableSet_longRun`, `shift_mem_longRun_iff` — `longRun` is cycle-measurable and, when
  every cycle length is finite, exactly `ρ`-invariant.  So `longRun` is an admissible `E`.
* `cycleErgodic_of_regeneration_longRun` — the composition: cycle ergodicity from one-step
  regeneration, positive finite cycle lengths, and generation on `longRun`.

Everything here is abstract measure theory; the actual reflected walk is attached in
`Temporal/CadlagRegenerationActual`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal

namespace ReflectedGMS.CadlagRegeneration

open ReflectedGMS.RegenerativeInvarianceFiberwise

section Abstract

variable {X Cyc : Type*} [mX : MeasurableSpace X] [mC : MeasurableSpace Cyc]

/-- The total length of the first `k` cycles, for a cycle-length functional `len`. -/
noncomputable def cycleSum (ρ : X → X) (C : X → Cyc) (len : Cyc → ℝ≥0∞) (k : ℕ) (x : X) :
    ℝ≥0∞ :=
  ∑ j ∈ Finset.range k, len (cycleCoord ρ C j x)

/-- The **long-run event**: the cycle lengths sum to `∞`. -/
def longRun (ρ : X → X) (C : X → Cyc) (len : Cyc → ℝ≥0∞) : Set X :=
  {x | ∀ n : ℕ, ∃ k : ℕ, (n : ℝ≥0∞) ≤ cycleSum ρ C len k x}

omit mX mC in
theorem cycleSum_succ_right (ρ : X → X) (C : X → Cyc) (len : Cyc → ℝ≥0∞) (k : ℕ) (x : X) :
    cycleSum ρ C len (k + 1) x = cycleSum ρ C len k x + len (cycleCoord ρ C k x) := by
  unfold cycleSum
  rw [Finset.sum_range_succ]

omit mX mC in
theorem cycleSum_mono (ρ : X → X) (C : X → Cyc) (len : Cyc → ℝ≥0∞) (x : X) :
    Monotone fun k => cycleSum ρ C len k x := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)

omit mX in
/-- Infinitely many cycles of length at least `δ > 0` make the cycle sums unbounded. -/
theorem mem_longRun_of_frequently {ρ : X → X} {C : X → Cyc} {len : Cyc → ℝ≥0∞} {δ : ℝ≥0∞}
    (hδ : δ ≠ 0) {x : X} (hfreq : ∃ᶠ j in atTop, δ ≤ len (cycleCoord ρ C j x)) :
    x ∈ longRun ρ C len := by
  have hstep : ∀ m : ℕ, ∃ k : ℕ, (m : ℝ≥0∞) * δ ≤ cycleSum ρ C len k x := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨j, hjk, hj⟩ := Filter.frequently_atTop.1 hfreq k
      refine ⟨j + 1, ?_⟩
      have hsub : cycleSum ρ C len k x + len (cycleCoord ρ C j x)
          ≤ cycleSum ρ C len (j + 1) x := by
        rw [cycleSum_succ_right]
        gcongr
        exact cycleSum_mono ρ C len x hjk
      calc ((m + 1 : ℕ) : ℝ≥0∞) * δ = (m : ℝ≥0∞) * δ + δ := by
            push_cast
            ring
        _ ≤ cycleSum ρ C len k x + len (cycleCoord ρ C j x) := add_le_add hk hj
        _ ≤ cycleSum ρ C len (j + 1) x := hsub
  intro n
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_mul_gt hδ (ENNReal.natCast_ne_top n)
  obtain ⟨k, hk⟩ := hstep m
  exact ⟨k, hm.le.trans hk⟩

/-- **Second Borel–Cantelli for regenerative cycles.**  If every cycle has strictly positive
length, then almost surely the cycle lengths sum to `∞`.  The independence of the cycles is
`iIndep_cycleSigma`, i.e. one-step regeneration alone. -/
theorem ae_mem_longRun {ρ : X → X} {C : X → Cyc} (μ : Measure X) [IsProbabilityMeasure μ]
    (hρ : Measurable ρ) (hC : Measurable C) (hlaw : μ.map ρ = μ) (hind : IndepFun C ρ μ)
    {len : Cyc → ℝ≥0∞} (hlen : Measurable len) (hpos : ∀ x, 0 < len (C x)) :
    ∀ᵐ x ∂μ, x ∈ longRun ρ C len := by
  -- a threshold `δ > 0` that the first cycle exceeds with positive probability
  obtain ⟨n, hn⟩ : ∃ n : ℕ, μ {x | (n : ℝ≥0∞)⁻¹ ≤ len (C x)} ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hU : (⋃ n : ℕ, {x | (n : ℝ≥0∞)⁻¹ ≤ len (C x)}) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x).ne'
      exact Set.mem_iUnion.2 ⟨n, hn.le⟩
    have h0 : μ (⋃ n : ℕ, {x | (n : ℝ≥0∞)⁻¹ ≤ len (C x)}) = 0 := measure_iUnion_null hcon
    rw [hU, measure_univ] at h0
    exact one_ne_zero h0
  set δ : ℝ≥0∞ := (n : ℝ≥0∞)⁻¹ with hδdef
  have hδ : δ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)
  set s : ℕ → Set X := fun j => {x | δ ≤ len (cycleCoord ρ C j x)} with hsdef
  have hA : MeasurableSet {c : Cyc | δ ≤ len c} := hlen measurableSet_Ici
  have hsσ : ∀ j, MeasurableSet[cycleSigma ρ C j] (s j) := fun j =>
    ⟨_, hA, rfl⟩
  have hsm : ∀ j, MeasurableSet (s j) := fun j => cycleSigma_le hρ hC j _ (hsσ j)
  -- the events are independent
  have hindep : iIndepSet s μ := by
    rw [iIndepSet_iff]
    intro S f hf
    have hI := (iIndep_iff _ μ).1 (iIndep_cycleSigma μ hρ hC hlaw hind) S (f := f)
      (fun i hi => MeasurableSpace.generateFrom_le
        (fun t ht => by rw [Set.mem_singleton_iff.1 ht]; exact hsσ i) _ (hf i hi))
    exact hI
  -- the events are identically distributed
  have hpres : MeasurePreserving ρ μ μ := ⟨hρ, hlaw⟩
  have hsame : ∀ j, μ (s j) = μ (s 0) := by
    intro j
    have hpre : s j = (ρ^[j]) ⁻¹' (s 0) := by
      ext x
      simp only [hsdef, Set.mem_ofPred_eq, Set.mem_preimage]
      rfl
    rw [hpre, (hpres.iterate j).measure_preimage (hsm 0).nullMeasurableSet]
  have hs0 : μ (s 0) ≠ 0 := hn
  have hsum : (∑' j, μ (s j)) = ∞ := by
    simp_rw [hsame]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hs0
  have hlim := measure_limsup_eq_one hsm hindep hsum
  have hlimm : MeasurableSet (limsup s atTop) := MeasurableSet.measurableSet_limsup hsm
  have hae : ∀ᵐ x ∂μ, x ∈ limsup s atTop := (mem_ae_iff_prob_eq_one hlimm).2 hlim
  filter_upwards [hae] with x hx
  exact mem_longRun_of_frequently hδ (mem_limsup_iff_frequently_mem.1 hx)

end Abstract

end ReflectedGMS.CadlagRegeneration
