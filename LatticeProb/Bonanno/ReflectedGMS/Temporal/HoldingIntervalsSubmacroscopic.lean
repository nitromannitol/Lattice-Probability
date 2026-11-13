/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.HoldingIntervalsSubmacroscopic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.LabelHoldingIntervals
import LatticeProb.Bonanno.ReflectedGMS.Temporal.ParabolicTemporalTransport

/-!
# Lemma 17.1: holding intervals are submacroscopic

Section 17 of the singular-set manuscript (`work/singular/manuscript-text.txt:2039-2086`).

**Lemma 17.1.** Almost surely, for every `K > 0`, `#{I ∈ 𝓘 : dist(0, I) ≤ K|I|} < ∞`, where `𝓘` is the
family of holding intervals of the label path.  *Proof.* Apply the temporal mass transport (16.2) to
`V(Ω, s, t) = |I_s|⁻¹ 1{dist(t, I_s) ≤ K|I_s|}`; the outgoing integral is `1 + 2K`, the incoming
integral counts the intervals in question.

This module proves exactly that, on the flow carrier `FlowSpace = Env × (CadlagPath ℕ∞ × CadlagPath
Plane)` of `TwoSidedRegenerationFlow`, from the transport predicate
`ParabolicTransport.ParabolicTemporalTransport Q reRootFlow reScale` (the checked Lean form of (16.2),
`p:lem:timeMTP`) for any finite law `Q`:

* `flowHold ω s`, `flowEntry ω s`, `flowExit ω s` — the holding length, age and residual lifetime of
  the label path at `s`, covariant under the flow (`flowHold_shift`) and the scaling
  (`flowHold_scale`), jointly measurable (`measurable_flowHold`).
* `subKernel K` — the manuscript kernel, with "values at nonvertex source times set to zero" and zero
  at an unbounded holding interval; `timeShiftCovariant_subKernel`, `parabolicCovariant_subKernel`,
  `measurable_subKernel`.
* `lintegral_subKernel_outgoing`: the outgoing integral is `1 + 2K` when the origin lies in a bounded
  holding interval (else `0`); `lintegral_subKernel_incoming`: the incoming integral is the number of
  bounded holding intervals `I` with `0 ∈ [inf I − K|I|, sup I + K|I|]` (`subCount K ω`).
* **`ae_forall_finite_submacroscopic`** — Lemma 17.1.
* (17.2) as pathwise consequences (`windowSup`, `windowSup_lt_top_of_finite`,
  `windowSup_le_of_finite`): the supremal length of the holding intervals meeting `[-T, T)` is finite
  for every `T` and is `o(T)`, given the counting property and finiteness of the holding intervals.

Nothing here constructs the annealed law or proves the transport predicate for it; nothing here
certifies either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.HoldingIntervalsSubmacroscopic

open ReflectedGMS.LabelHoldingIntervals ReflectedGMS.TrajectoryCoding
open ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TemporalMassTransport ReflectedGMS.ParabolicTransport

/-! ## 1. Holding lengths along the flow carrier -/

/-- The residual lifetime of the label path at `s`. -/
noncomputable def flowExit (ω : FlowSpace) (s : ℝ) : ℝ≥0∞ := exitLen ω.2.1 s

/-- The age of the label path at `s`. -/
noncomputable def flowEntry (ω : FlowSpace) (s : ℝ) : ℝ≥0∞ := entryLen ω.2.1 s

/-- The length of the holding interval of the label path through `s` (`0` at a cemetery time). -/
noncomputable def flowHold (ω : FlowSpace) (s : ℝ) : ℝ≥0∞ := holdLen ω.2.1 s

/-- The holding interval of the label path through `s`. -/
def flowHoldSet (ω : FlowSpace) (s : ℝ) : Set ℝ := holdSet ω.2.1 s

theorem flowExit_shift (r : ℝ) (ω : FlowSpace) (s : ℝ) :
    flowExit (reRootFlow r ω) s = flowExit ω (s + r) :=
  exitLen_of_shift (simLabel_injective _ _ _ _) (reRootFlow_label r ω) s

theorem flowEntry_shift (r : ℝ) (ω : FlowSpace) (s : ℝ) :
    flowEntry (reRootFlow r ω) s = flowEntry ω (s + r) :=
  entryLen_of_shift (simLabel_injective _ _ _ _) (reRootFlow_label r ω) s

/-- **Flow covariance of the holding length, at every point.** -/
theorem flowHold_shift (r : ℝ) (ω : FlowSpace) (s : ℝ) :
    flowHold (reRootFlow r ω) s = flowHold ω (s + r) :=
  holdLen_of_shift (simLabel_injective _ _ _ _) (reRootFlow_label r ω) s

theorem flowExit_scale {C : ℝ} (hC : 0 < C) (ω : FlowSpace) (s : ℝ) :
    flowExit (reScale C ω) (C ^ 2 * s) = ENNReal.ofReal (C ^ 2) * flowExit ω s :=
  exitLen_of_dilate (simLabel_injective _ _ _ _) (pow_pos hC 2) (reScale_label hC ω) s

theorem flowEntry_scale {C : ℝ} (hC : 0 < C) (ω : FlowSpace) (s : ℝ) :
    flowEntry (reScale C ω) (C ^ 2 * s) = ENNReal.ofReal (C ^ 2) * flowEntry ω s :=
  entryLen_of_dilate (simLabel_injective _ _ _ _) (pow_pos hC 2) (reScale_label hC ω) s

/-- **Parabolic covariance of the holding length, at every point.** -/
theorem flowHold_scale {C : ℝ} (hC : 0 < C) (ω : FlowSpace) (s : ℝ) :
    flowHold (reScale C ω) (C ^ 2 * s) = ENNReal.ofReal (C ^ 2) * flowHold ω s :=
  holdLen_of_dilate (simLabel_injective _ _ _ _) (pow_pos hC 2) (reScale_label hC ω) s

theorem measurable_labelEval : Measurable fun p : FlowSpace × ℝ => (p.1.2.1, p.2) :=
  measurable_fst.snd.fst.prodMk measurable_snd

theorem measurable_flowExit : Measurable fun p : FlowSpace × ℝ => flowExit p.1 p.2 := by
  have h := measurable_exitLen.comp measurable_labelEval
  show Measurable fun p : FlowSpace × ℝ => exitLen p.1.2.1 p.2
  simpa only [Function.comp_def] using h

theorem measurable_flowEntry : Measurable fun p : FlowSpace × ℝ => flowEntry p.1 p.2 := by
  have h := measurable_entryLen.comp measurable_labelEval
  show Measurable fun p : FlowSpace × ℝ => entryLen p.1.2.1 p.2
  simpa only [Function.comp_def] using h

theorem measurable_flowHold : Measurable fun p : FlowSpace × ℝ => flowHold p.1 p.2 := by
  have h := measurable_holdLen.comp measurable_labelEval
  show Measurable fun p : FlowSpace × ℝ => holdLen p.1.2.1 p.2
  simpa only [Function.comp_def] using h

theorem flowHold_eq_zero_iff (ω : FlowSpace) (s : ℝ) :
    flowHold ω s = 0 ↔ ω.2.1.toFun s = ⊤ :=
  holdLen_eq_zero_iff _ _

/-! ## 2. The kernel of Lemma 17.1 -/

/-- The closed `K|I_s|`-neighbourhood `[a - K|I_s|, b + K|I_s|]` of the holding interval
`I_s = [a, b)`, read off through the age and the residual lifetime at `s`. -/
noncomputable def enlargedHold (K : ℝ) (ω : FlowSpace) (s : ℝ) : Set ℝ :=
  Set.Icc (s - (flowEntry ω s).toReal - K * (flowHold ω s).toReal)
    (s + (flowExit ω s).toReal + K * (flowHold ω s).toReal)

open Classical in
/-- **The kernel of Lemma 17.1**: `V(Ω, s, t) = |I_s|⁻¹ 1{dist(t, I_s) ≤ K|I_s|}`, zero at a nonvertex
source time (`|I_s| = 0`) and at an unbounded holding interval. -/
noncomputable def subKernel (K : ℝ) (ω : FlowSpace) (s t : ℝ) : ℝ≥0∞ :=
  if flowHold ω s = 0 ∨ flowHold ω s = ∞ then 0
  else (flowHold ω s)⁻¹ * (enlargedHold K ω s).indicator (fun _ => (1 : ℝ≥0∞)) t

theorem subKernel_of_cond (K : ℝ) {ω : FlowSpace} {s : ℝ}
    (h : flowHold ω s = 0 ∨ flowHold ω s = ∞) (t : ℝ) : subKernel K ω s t = 0 := by
  rw [subKernel, if_pos h]

theorem subKernel_of_not_cond (K : ℝ) {ω : FlowSpace} {s : ℝ}
    (h : ¬ (flowHold ω s = 0 ∨ flowHold ω s = ∞)) (t : ℝ) :
    subKernel K ω s t
      = (flowHold ω s)⁻¹ * (enlargedHold K ω s).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  rw [subKernel, if_neg h]

/-! ### Measurability -/

theorem measurable_flowHold₃ :
    Measurable fun p : FlowSpace × ℝ × ℝ => flowHold p.1 p.2.1 :=
  measurable_flowHold.comp (measurable_fst.prodMk measurable_snd.fst)

theorem measurable_flowEntry₃ :
    Measurable fun p : FlowSpace × ℝ × ℝ => flowEntry p.1 p.2.1 :=
  measurable_flowEntry.comp (measurable_fst.prodMk measurable_snd.fst)

theorem measurable_flowExit₃ :
    Measurable fun p : FlowSpace × ℝ × ℝ => flowExit p.1 p.2.1 :=
  measurable_flowExit.comp (measurable_fst.prodMk measurable_snd.fst)

theorem measurableSet_mem_enlargedHold (K : ℝ) :
    MeasurableSet {p : FlowSpace × ℝ × ℝ | p.2.2 ∈ enlargedHold K p.1 p.2.1} := by
  have hlo : Measurable fun p : FlowSpace × ℝ × ℝ =>
      p.2.1 - (flowEntry p.1 p.2.1).toReal - K * (flowHold p.1 p.2.1).toReal :=
    (measurable_snd.fst.sub measurable_flowEntry₃.ennreal_toReal).sub
      (measurable_flowHold₃.ennreal_toReal.const_mul K)
  have hhi : Measurable fun p : FlowSpace × ℝ × ℝ =>
      p.2.1 + (flowExit p.1 p.2.1).toReal + K * (flowHold p.1 p.2.1).toReal :=
    (measurable_snd.fst.add measurable_flowExit₃.ennreal_toReal).add
      (measurable_flowHold₃.ennreal_toReal.const_mul K)
  exact (measurableSet_le hlo measurable_snd.snd).inter (measurableSet_le measurable_snd.snd hhi)

theorem measurable_indicator_enlargedHold (K : ℝ) :
    Measurable fun p : FlowSpace × ℝ × ℝ =>
      (enlargedHold K p.1 p.2.1).indicator (fun _ => (1 : ℝ≥0∞)) p.2.2 := by
  have hgen : Measurable (Set.indicator {p : FlowSpace × ℝ × ℝ | p.2.2 ∈ enlargedHold K p.1 p.2.1}
      (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_mem_enlargedHold K)
  have hEq : (fun p : FlowSpace × ℝ × ℝ =>
      (enlargedHold K p.1 p.2.1).indicator (fun _ => (1 : ℝ≥0∞)) p.2.2)
      = Set.indicator {p : FlowSpace × ℝ × ℝ | p.2.2 ∈ enlargedHold K p.1 p.2.1}
        (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    by_cases hp : p.2.2 ∈ enlargedHold K p.1 p.2.1
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem
        (show p ∈ {p : FlowSpace × ℝ × ℝ | p.2.2 ∈ enlargedHold K p.1 p.2.1} from hp)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem
        (show p ∉ {p : FlowSpace × ℝ × ℝ | p.2.2 ∈ enlargedHold K p.1 p.2.1} from hp)]
  rw [hEq]
  exact hgen

open Classical in
theorem measurable_subKernel (K : ℝ) :
    Measurable fun p : FlowSpace × ℝ × ℝ => subKernel K p.1 p.2.1 p.2.2 := by
  have hcond : MeasurableSet {p : FlowSpace × ℝ × ℝ |
      flowHold p.1 p.2.1 = 0 ∨ flowHold p.1 p.2.1 = ∞} :=
    (measurable_flowHold₃ (measurableSet_singleton 0)).union
      (measurable_flowHold₃ (measurableSet_singleton ∞))
  have hEq : (fun p : FlowSpace × ℝ × ℝ => subKernel K p.1 p.2.1 p.2.2)
      = fun p : FlowSpace × ℝ × ℝ =>
        if flowHold p.1 p.2.1 = 0 ∨ flowHold p.1 p.2.1 = ∞ then 0
        else (flowHold p.1 p.2.1)⁻¹ *
          (enlargedHold K p.1 p.2.1).indicator (fun _ => (1 : ℝ≥0∞)) p.2.2 := rfl
  rw [hEq]
  exact Measurable.ite hcond measurable_const
    (measurable_flowHold₃.inv.mul (measurable_indicator_enlargedHold K))

/-! ### Covariance -/

theorem indicator_Icc_congr_shift {A B A' B' r t : ℝ} (hA : A' + r = A) (hB : B' + r = B) :
    (Set.Icc A' B').indicator (fun _ => (1 : ℝ≥0∞)) (t - r)
      = (Set.Icc A B).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  have hiff : t - r ∈ Set.Icc A' B' ↔ t ∈ Set.Icc A B := by
    simp only [Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  by_cases h : t ∈ Set.Icc A B
  · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]

theorem indicator_Icc_congr_scale {A B A' B' t a : ℝ} (ha : 0 < a) (hA : A' = a * A)
    (hB : B' = a * B) :
    (Set.Icc A' B').indicator (fun _ => (1 : ℝ≥0∞)) (a * t)
      = (Set.Icc A B).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  have hiff : a * t ∈ Set.Icc A' B' ↔ t ∈ Set.Icc A B := by
    rw [hA, hB]
    simp only [Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨le_of_mul_le_mul_left h1 ha, le_of_mul_le_mul_left h2 ha⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_le_mul_of_nonneg_left h1 ha.le, mul_le_mul_of_nonneg_left h2 ha.le⟩
  by_cases h : t ∈ Set.Icc A B
  · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]

/-- **Time-shift covariance of the kernel** under the re-rooting flow. -/
theorem timeShiftCovariant_subKernel (K : ℝ) : TimeShiftCovariant reRootFlow (subKernel K) := by
  intro r s t ω
  have hH : flowHold (reRootFlow r ω) (s - r) = flowHold ω s := by
    rw [flowHold_shift, sub_add_cancel]
  have hE : flowEntry (reRootFlow r ω) (s - r) = flowEntry ω s := by
    rw [flowEntry_shift, sub_add_cancel]
  have hX : flowExit (reRootFlow r ω) (s - r) = flowExit ω s := by
    rw [flowExit_shift, sub_add_cancel]
  by_cases h : flowHold ω s = 0 ∨ flowHold ω s = ∞
  · rw [subKernel_of_cond K h, subKernel_of_cond K (by rwa [hH])]
  · rw [subKernel_of_not_cond K h, subKernel_of_not_cond K (by rwa [hH]), hH]
    congr 1
    simp only [enlargedHold, hE, hX, hH]
    exact indicator_Icc_congr_shift (by ring) (by ring)

/-- **Parabolic covariance of degree `-2` of the kernel** under the scaling. -/
theorem parabolicCovariant_subKernel (K : ℝ) : ParabolicCovariant reScale (subKernel K) := by
  intro C hC ω s t
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  have hc0 : ENNReal.ofReal (C ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hC2).ne'
  have hcT : ENNReal.ofReal (C ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hH := flowHold_scale hC ω s
  have hE := flowEntry_scale hC ω s
  have hX := flowExit_scale hC ω s
  have hcond : (flowHold (reScale C ω) (C ^ 2 * s) = 0 ∨ flowHold (reScale C ω) (C ^ 2 * s) = ∞)
      ↔ (flowHold ω s = 0 ∨ flowHold ω s = ∞) := by
    rw [hH, mul_eq_zero, ENNReal.mul_eq_top]
    constructor
    · rintro ((h | h) | (⟨-, h⟩ | ⟨h, -⟩))
      · exact absurd h hc0
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hcT
    · rintro (h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl ⟨hc0, h⟩)
  by_cases h : flowHold ω s = 0 ∨ flowHold ω s = ∞
  · rw [subKernel_of_cond K h, subKernel_of_cond K (hcond.2 h), mul_zero]
  · rw [subKernel_of_not_cond K h, subKernel_of_not_cond K (fun h' => h (hcond.1 h')), hH,
      ENNReal.mul_inv (Or.inl hc0) (Or.inl hcT), ← ENNReal.ofReal_inv_of_pos hC2, mul_assoc]
    congr 2
    simp only [enlargedHold, hE, hX, hH, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC2.le]
    exact indicator_Icc_congr_scale hC2 (by ring) (by ring)

/-! ## 3. The outgoing integral -/

/-- **The outgoing integral is `1 + 2K`** when the origin lies in a bounded holding interval, and
`0` otherwise. -/
theorem lintegral_subKernel_outgoing (K : ℝ) (hK : 0 ≤ K) (ω : FlowSpace) :
    ∫⁻ t, subKernel K ω 0 t
      = if flowHold ω 0 = 0 ∨ flowHold ω 0 = ∞ then 0 else ENNReal.ofReal (1 + 2 * K) := by
  by_cases h : flowHold ω 0 = 0 ∨ flowHold ω 0 = ∞
  · rw [if_pos h]
    simp only [subKernel_of_cond K h, lintegral_zero]
  · rw [if_neg h]
    have h1 : flowHold ω 0 ≠ 0 := fun c => h (Or.inl c)
    have h2 : flowHold ω 0 ≠ ∞ := fun c => h (Or.inr c)
    have h0 : ω.2.1.toFun 0 ≠ ⊤ := fun c => h1 ((flowHold_eq_zero_iff ω 0).2 c)
    have hℓ : (flowHold ω 0).toReal = (flowEntry ω 0).toReal + (flowExit ω 0).toReal := by
      have hsum : flowHold ω 0 = flowEntry ω 0 + flowExit ω 0 := holdLen_of_ne_top _ h0
      rw [hsum] at h2 ⊢
      exact ENNReal.toReal_add (ENNReal.add_ne_top.1 h2).1 (ENNReal.add_ne_top.1 h2).2
    simp only [subKernel_of_not_cond K h]
    have hmeasI : Measurable fun t : ℝ => (enlargedHold K ω 0).indicator (fun _ => (1 : ℝ≥0∞)) t :=
      measurable_const.indicator measurableSet_Icc
    rw [lintegral_const_mul _ hmeasI,
      lintegral_indicator_const (s := enlargedHold K ω 0) measurableSet_Icc, one_mul]
    unfold enlargedHold
    rw [Real.volume_Icc]
    have harith : 0 + (flowExit ω 0).toReal + K * (flowHold ω 0).toReal
        - (0 - (flowEntry ω 0).toReal - K * (flowHold ω 0).toReal)
        = (1 + 2 * K) * (flowHold ω 0).toReal := by
      rw [hℓ]
      ring
    rw [harith, ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_toReal h2, mul_comm, mul_assoc,
      ENNReal.mul_inv_cancel h1 h2, mul_one]

/-! ## 4. The incoming integral counts the holding intervals -/

/-- **The family of holding intervals** of the label path (each is the holding interval through
one of its rational times). -/
def holdFamily (ω : FlowSpace) : Set (Set ℝ) :=
  {I | ∃ q : ℚ, ω.2.1.toFun q ≠ ⊤ ∧ I = holdSet ω.2.1 q}

theorem mem_holdFamily_iff (ω : FlowSpace) (I : Set ℝ) :
    I ∈ holdFamily ω ↔ ∃ q : ℚ, ω.2.1.toFun q ≠ ⊤ ∧ I = holdSet ω.2.1 q := Iff.rfl

theorem countable_holdFamily (ω : FlowSpace) : (holdFamily ω).Countable :=
  (Set.countable_range fun q : ℚ => holdSet ω.2.1 q).mono fun _ ⟨q, _, hq⟩ =>
    Set.mem_range.2 ⟨q, hq.symm⟩

theorem measurableSet_of_mem_holdFamily {ω : FlowSpace} {I : Set ℝ} (hI : I ∈ holdFamily ω) :
    MeasurableSet I := by
  obtain ⟨q, -, rfl⟩ := hI
  exact measurableSet_holdSet _ _

/-- Distinct holding intervals are disjoint. -/
theorem pairwiseDisjoint_holdFamily (ω : FlowSpace) :
    (holdFamily ω).PairwiseDisjoint (fun I : Set ℝ => I) := by
  refine Set.pairwiseDisjoint_iff.2 fun I hI J hJ hne => ?_
  obtain ⟨q, -, rfl⟩ := hI
  obtain ⟨q', -, rfl⟩ := hJ
  obtain ⟨t, ht, ht'⟩ := hne
  show holdSet ω.2.1 q = holdSet ω.2.1 q'
  rw [← holdSet_eq_of_mem _ ht, ← holdSet_eq_of_mem _ ht']

/-- The holding interval through any vertex time belongs to the family. -/
theorem holdSet_mem_holdFamily (ω : FlowSpace) {t : ℝ} (ht : ω.2.1.toFun t ≠ ⊤) :
    holdSet ω.2.1 t ∈ holdFamily ω := by
  obtain ⟨q, hq⟩ := exists_rat_mem_holdSet ω.2.1 ht
  exact (mem_holdFamily_iff ω (holdSet ω.2.1 t)).2
    ⟨q, ne_top_of_mem_holdSet _ hq, (holdSet_eq_of_mem _ hq).symm⟩

/-- The `K`-enlargement of a set of times, `[inf I - K|I|, sup I + K|I|]`. -/
noncomputable def enlargeSet (K : ℝ) (I : Set ℝ) : Set ℝ :=
  Set.Icc (sInf I - K * (volume I).toReal) (sSup I + K * (volume I).toReal)

/-- **The intervals counted by Lemma 17.1**: the bounded holding intervals `I` whose
`K|I|`-neighbourhood contains the origin. -/
def countedSet (K : ℝ) (ω : FlowSpace) : Set (Set ℝ) :=
  {I | I ∈ holdFamily ω ∧ volume I ≠ ∞ ∧ (0 : ℝ) ∈ enlargeSet K I}

theorem mem_countedSet_iff (K : ℝ) (ω : FlowSpace) (I : Set ℝ) :
    I ∈ countedSet K ω ↔ I ∈ holdFamily ω ∧ volume I ≠ ∞ ∧ (0 : ℝ) ∈ enlargeSet K I := Iff.rfl

/-- **The count of Lemma 17.1**, as an `ℝ≥0∞`-valued cardinality. -/
noncomputable def subCount (K : ℝ) (ω : FlowSpace) : ℝ≥0∞ :=
  ∑' _ : countedSet K ω, (1 : ℝ≥0∞)

/-- On a bounded holding interval the kernel with target time `0` is constant. -/
theorem subKernel_eq_on_holdSet (K : ℝ) (ω : FlowSpace) {q : ℝ} (hq : ω.2.1.toFun q ≠ ⊤)
    (hfin : holdLen ω.2.1 q ≠ ∞) {t : ℝ} (ht : t ∈ holdSet ω.2.1 q) :
    subKernel K ω t 0 = (volume (holdSet ω.2.1 q))⁻¹ *
      (enlargeSet K (holdSet ω.2.1 q)).indicator (fun _ => (1 : ℝ≥0∞)) 0 := by
  have ht' : ω.2.1.toFun t ≠ ⊤ := ne_top_of_mem_holdSet _ ht
  obtain ⟨hlo, hhi, hlen⟩ := endpoints_eq_of_mem ω.2.1 ht hfin
  have he := entryLen_ne_top_of_holdLen ω.2.1 hq hfin
  have hx := exitLen_ne_top_of_holdLen ω.2.1 hq hfin
  have hvol : volume (holdSet ω.2.1 q) = holdLen ω.2.1 q := volume_holdSet_of_ne_top _ hq he hx
  have hIco := holdSet_eq_Ico ω.2.1 hq he hx
  have hab : q - (entryLen ω.2.1 q).toReal < q + (exitLen ω.2.1 q).toReal := by
    have := ENNReal.toReal_pos (exitLen_pos ω.2.1 hq).ne' hx
    linarith [(ENNReal.toReal_nonneg : 0 ≤ (entryLen ω.2.1 q).toReal)]
  have hinf : sInf (holdSet ω.2.1 q) = q - (entryLen ω.2.1 q).toReal := by
    rw [hIco]
    exact csInf_Ico hab
  have hsup : sSup (holdSet ω.2.1 q) = q + (exitLen ω.2.1 q).toReal := by
    rw [hIco]
    exact csSup_Ico hab
  have hcond : ¬ (flowHold ω t = 0 ∨ flowHold ω t = ∞) := by
    rintro (h | h)
    · exact ht' ((holdLen_eq_zero_iff _ _).1 h)
    · exact hfin (hlen ▸ h)
  rw [subKernel_of_not_cond K hcond]
  show (holdLen ω.2.1 t)⁻¹ * (enlargedHold K ω t).indicator (fun _ => (1 : ℝ≥0∞)) 0
    = (volume (holdSet ω.2.1 q))⁻¹ * (enlargeSet K (holdSet ω.2.1 q)).indicator (fun _ => 1) 0
  rw [hlen, hvol]
  congr 2
  simp only [enlargedHold, enlargeSet, hinf, hsup, hvol]
  show Set.Icc (t - (entryLen ω.2.1 t).toReal - K * (holdLen ω.2.1 t).toReal)
      (t + (exitLen ω.2.1 t).toReal + K * (holdLen ω.2.1 t).toReal)
    = Set.Icc (q - (entryLen ω.2.1 q).toReal - K * (holdLen ω.2.1 q).toReal)
      (q + (exitLen ω.2.1 q).toReal + K * (holdLen ω.2.1 q).toReal)
  rw [hlo, hhi, hlen]

/-- On an unbounded holding interval the kernel with target time `0` vanishes. -/
theorem subKernel_eq_zero_on_holdSet (K : ℝ) (ω : FlowSpace) {q : ℝ}
    (hfin : holdLen ω.2.1 q = ∞) {t : ℝ} (ht : t ∈ holdSet ω.2.1 q) : subKernel K ω t 0 = 0 :=
  subKernel_of_cond K (Or.inr (by
    show holdLen ω.2.1 t = ∞
    rw [holdLen_eq_of_mem _ ht, hfin])) 0

theorem support_subKernel_subset (K : ℝ) (ω : FlowSpace) :
    Function.support (fun t => subKernel K ω t 0) ⊆ ⋃ I ∈ holdFamily ω, I := by
  intro t ht
  have hne : subKernel K ω t 0 ≠ 0 := ht
  have ht' : ω.2.1.toFun t ≠ ⊤ := by
    intro htop
    exact hne (subKernel_of_cond K (Or.inl ((flowHold_eq_zero_iff ω t).2 htop)) 0)
  exact Set.mem_biUnion (holdSet_mem_holdFamily ω ht') (self_mem_holdSet _ ht')

open Classical in
/-- The set integral of the kernel over one holding interval of the family. -/
theorem setLIntegral_subKernel_holdSet (K : ℝ) (ω : FlowSpace) {I : Set ℝ}
    (hI : I ∈ holdFamily ω) :
    ∫⁻ t in I, subKernel K ω t 0
      = if volume I ≠ ∞ ∧ (0 : ℝ) ∈ enlargeSet K I then 1 else 0 := by
  obtain ⟨q, hq, rfl⟩ := hI
  by_cases hfin : holdLen ω.2.1 q = ∞
  · have hvol : volume (holdSet ω.2.1 q) = ∞ := by
      by_contra hv
      rw [holdLen_of_ne_top _ hq, ENNReal.add_eq_top] at hfin
      rcases hfin with he | hx
      · have hsub := Iic_subset_holdSet ω.2.1 hq he
        exact hv (top_le_iff.1 (le_trans (le_of_eq Real.volume_Iic.symm) (measure_mono hsub)))
      · have hsub := Ici_subset_holdSet ω.2.1 hq hx
        exact hv (top_le_iff.1 (le_trans (le_of_eq Real.volume_Ici.symm) (measure_mono hsub)))
    rw [if_neg (fun h : volume (holdSet ω.2.1 q) ≠ ∞ ∧ (0 : ℝ) ∈ enlargeSet K (holdSet ω.2.1 q) =>
      h.1 hvol)]
    rw [setLIntegral_congr_fun (measurableSet_holdSet _ _)
      (fun t ht => subKernel_eq_zero_on_holdSet K ω hfin ht)]
    simp
  · have he := entryLen_ne_top_of_holdLen ω.2.1 hq hfin
    have hx := exitLen_ne_top_of_holdLen ω.2.1 hq hfin
    have hvol : volume (holdSet ω.2.1 q) = holdLen ω.2.1 q := volume_holdSet_of_ne_top _ hq he hx
    have hv0 : volume (holdSet ω.2.1 q) ≠ 0 := by
      rw [hvol]
      exact (holdLen_pos _ hq).ne'
    have hvT : volume (holdSet ω.2.1 q) ≠ ∞ := by
      rw [hvol]
      exact hfin
    rw [setLIntegral_congr_fun (measurableSet_holdSet _ _)
      (fun t ht => subKernel_eq_on_holdSet K ω hq hfin ht), setLIntegral_const]
    by_cases h0 : (0 : ℝ) ∈ enlargeSet K (holdSet ω.2.1 q)
    · rw [if_pos (⟨hvT, h0⟩ : volume (holdSet ω.2.1 q) ≠ ∞ ∧
        (0 : ℝ) ∈ enlargeSet K (holdSet ω.2.1 q)), Set.indicator_of_mem h0, mul_one,
        ENNReal.inv_mul_cancel hv0 hvT]
    · rw [if_neg (fun h : volume (holdSet ω.2.1 q) ≠ ∞ ∧
        (0 : ℝ) ∈ enlargeSet K (holdSet ω.2.1 q) => h0 h.2), Set.indicator_of_notMem h0,
        mul_zero, zero_mul]

open Classical in
/-- **The incoming integral counts the bounded holding intervals whose `K`-enlargement contains
the origin.** -/
theorem lintegral_subKernel_incoming (K : ℝ) (ω : FlowSpace) :
    ∫⁻ t, subKernel K ω t 0 = subCount K ω := by
  rw [← setLIntegral_eq_of_support_subset (support_subKernel_subset K ω),
    lintegral_biUnion (countable_holdFamily ω) (fun I hI => measurableSet_of_mem_holdFamily hI)
      (pairwiseDisjoint_holdFamily ω)]
  have hEq : ∀ I : holdFamily ω, ∫⁻ t in (I : Set ℝ), subKernel K ω t 0
      = if volume (I : Set ℝ) ≠ ∞ ∧ (0 : ℝ) ∈ enlargeSet K I then 1 else 0 :=
    fun I => setLIntegral_subKernel_holdSet K ω I.2
  simp only [hEq]
  unfold subCount
  rw [tsum_subtype (countedSet K ω) (fun _ => (1 : ℝ≥0∞)),
    tsum_subtype (holdFamily ω) (fun I => if volume I ≠ ∞ ∧ (0 : ℝ) ∈ enlargeSet K I then 1 else 0)]
  refine tsum_congr fun I => ?_
  by_cases hI : I ∈ holdFamily ω
  · rw [Set.indicator_of_mem hI]
    by_cases hc : volume I ≠ ∞ ∧ (0 : ℝ) ∈ enlargeSet K I
    · rw [if_pos hc, Set.indicator_of_mem ((mem_countedSet_iff K ω I).2 ⟨hI, hc.1, hc.2⟩)]
    · rw [if_neg hc, Set.indicator_of_notMem (fun h => hc ⟨((mem_countedSet_iff K ω I).1 h).2.1,
        ((mem_countedSet_iff K ω I).1 h).2.2⟩)]
  · rw [Set.indicator_of_notMem hI,
      Set.indicator_of_notMem (fun h => hI ((mem_countedSet_iff K ω I).1 h).1)]

/-- A finite count means finitely many counted intervals. -/
theorem finite_countedSet_of_subCount_lt_top {K : ℝ} {ω : FlowSpace} (h : subCount K ω < ∞) :
    (countedSet K ω).Finite := by
  by_contra hinf
  have : Infinite (countedSet K ω) := Set.infinite_coe_iff.2 hinf
  exact absurd h (by
    unfold subCount
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
    exact lt_irrefl _)

/-! ## 5. Lemma 17.1 -/

/-- **Lemma 17.1 for one `K`**: under the temporal mass transport, the count is a.s. finite. -/
theorem ae_subCount_lt_top {Q : Measure FlowSpace} [IsFiniteMeasure Q]
    (htr : ParabolicTemporalTransport Q reRootFlow reScale) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂Q, subCount K ω < ∞ := by
  have hmeas := measurable_subKernel K
  have key := htr (subKernel K) hmeas (timeShiftCovariant_subKernel K)
    (parabolicCovariant_subKernel K)
  have hout : Measurable fun p : FlowSpace × ℝ => subKernel K p.1 0 p.2 :=
    measurable_outgoing _ hmeas
  have hin : Measurable fun p : FlowSpace × ℝ => subKernel K p.1 p.2 0 :=
    measurable_incoming _ hmeas
  have hL : ∫⁻ p : FlowSpace × ℝ, subKernel K p.1 0 p.2 ∂(Q.prod volume)
      = ∫⁻ ω, ∫⁻ t, subKernel K ω 0 t ∂volume ∂Q :=
    lintegral_prod _ hout.aemeasurable
  have hR : ∫⁻ p : FlowSpace × ℝ, subKernel K p.1 p.2 0 ∂(Q.prod volume)
      = ∫⁻ ω, ∫⁻ t, subKernel K ω t 0 ∂volume ∂Q :=
    lintegral_prod _ hin.aemeasurable
  have hbound : ∫⁻ ω, ∫⁻ t, subKernel K ω 0 t ∂volume ∂Q
      ≤ ENNReal.ofReal (1 + 2 * K) * Q Set.univ := by
    calc ∫⁻ ω, ∫⁻ t, subKernel K ω 0 t ∂volume ∂Q
        ≤ ∫⁻ _, ENNReal.ofReal (1 + 2 * K) ∂Q := by
          refine lintegral_mono fun ω => ?_
          rw [lintegral_subKernel_outgoing K hK ω]
          split_ifs
          · exact zero_le
          · exact le_rfl
      _ = ENNReal.ofReal (1 + 2 * K) * Q Set.univ := lintegral_const _
  have hfin : ∫⁻ ω, ∫⁻ t, subKernel K ω t 0 ∂volume ∂Q ≠ ∞ := by
    rw [← hR, ← key, hL]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top Q _))
      hbound
  have hae := ae_lt_top hin.lintegral_prod_right' hfin
  filter_upwards [hae] with ω hω
  rwa [lintegral_subKernel_incoming K ω] at hω

/-- **Lemma 17.1 (holding intervals are submacroscopic).**  Under the temporal mass transport
(16.2) for a finite law on the flow carrier, almost surely, for every `K : ℕ`, only finitely many
bounded holding intervals `I` of the label path satisfy `0 ∈ [inf I - K|I|, sup I + K|I|]`. -/
theorem ae_forall_finite_submacroscopic {Q : Measure FlowSpace} [IsFiniteMeasure Q]
    (htr : ParabolicTemporalTransport Q reRootFlow reScale) :
    ∀ᵐ ω ∂Q, ∀ K : ℕ, (countedSet K ω).Finite := by
  refine ae_all_iff.2 fun K => ?_
  filter_upwards [ae_subCount_lt_top htr K (Nat.cast_nonneg K)] with ω hω
  exact finite_countedSet_of_subCount_lt_top hω

/-! ## 6. Pathwise consequences: (17.2)

For the block construction of Section 17 the counting property is consumed through the
**window supremum** `windowSup ω T`, the supremal length of the holding intervals meeting the window
`[-T, T)` (read through their rational times, `exists_rat_mem_holdSet_inter_Ico`).  Given the
counting property for every natural `K` and finiteness of every holding interval, it is finite for
every `T` and is `o(T)`. -/

/-- The supremal length of the holding intervals meeting `[-T, T)`. -/
noncomputable def windowSup (ω : FlowSpace) (T : ℝ) : ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : (q : ℝ) ∈ Set.Ico (-T) T), flowHold ω q

theorem windowSup_mono (ω : FlowSpace) {T T' : ℝ} (h : T ≤ T') : windowSup ω T ≤ windowSup ω T' :=
  iSup₂_mono' fun q hq => ⟨q, ⟨by linarith [hq.1], by linarith [hq.2]⟩, le_rfl⟩

theorem le_windowSup (ω : FlowSpace) {T : ℝ} {q : ℚ} (hq : (q : ℝ) ∈ Set.Ico (-T) T) :
    flowHold ω q ≤ windowSup ω T :=
  le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Set.Ico (-T) T) => flowHold ω q) q hq

/-- A holding interval meeting the window at a rational time, of length at least `ε`, is counted
at every `K ≥ T / ε`. -/
theorem holdSet_mem_countedSet (ω : FlowSpace) {T ε : ℝ} (hε : 0 < ε) {K : ℝ} (hKT : T ≤ K * ε)
    {q : ℚ} (hq : (q : ℝ) ∈ Set.Ico (-T) T) (hqv : ω.2.1.toFun q ≠ ⊤)
    (hfin : holdLen ω.2.1 q ≠ ∞) (hlen : ENNReal.ofReal ε ≤ holdLen ω.2.1 q) :
    holdSet ω.2.1 q ∈ countedSet K ω := by
  have hK : 0 ≤ K := by
    by_contra hK
    push_neg at hK
    have : K * ε < 0 := mul_neg_of_neg_of_pos hK hε
    linarith [hq.1, hq.2]
  have he := entryLen_ne_top_of_holdLen ω.2.1 hqv hfin
  have hx := exitLen_ne_top_of_holdLen ω.2.1 hqv hfin
  have hvol : volume (holdSet ω.2.1 q) = holdLen ω.2.1 q := volume_holdSet_of_ne_top _ hqv he hx
  have hIco := holdSet_eq_Ico ω.2.1 hqv he hx
  have hab : q - (entryLen ω.2.1 q).toReal < q + (exitLen ω.2.1 q).toReal := by
    have := ENNReal.toReal_pos (exitLen_pos ω.2.1 hqv).ne' hx
    linarith [(ENNReal.toReal_nonneg : 0 ≤ (entryLen ω.2.1 q).toReal)]
  have hℓε : ε ≤ (holdLen ω.2.1 q).toReal := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hlen
  refine (mem_countedSet_iff K ω _).2 ⟨(mem_holdFamily_iff ω _).2 ⟨q, hqv, rfl⟩, by
    rw [hvol]
    exact hfin, ?_⟩
  simp only [enlargeSet, hvol, Set.mem_Icc]
  rw [hIco, csInf_Ico hab, csSup_Ico hab]
  have hKℓ : K * ε ≤ K * (holdLen ω.2.1 q).toReal := mul_le_mul_of_nonneg_left hℓε hK
  constructor
  · linarith [hq.2, (ENNReal.toReal_nonneg : 0 ≤ (entryLen ω.2.1 q).toReal)]
  · linarith [hq.1, (ENNReal.toReal_nonneg : 0 ≤ (exitLen ω.2.1 q).toReal)]

/-- The total length of the counted intervals is finite when the count is. -/
theorem tsum_volume_countedSet_ne_top {K : ℝ} {ω : FlowSpace} (hfin : (countedSet K ω).Finite) :
    ∑' I : countedSet K ω, volume (I : Set ℝ) ≠ ∞ := by
  haveI := hfin.fintype
  rw [tsum_fintype]
  exact (ENNReal.sum_lt_top.2 fun I _ => lt_top_iff_ne_top.2 I.2.2.1).ne

/-- **(17.2), the finiteness clause**: the window supremum is bounded by `ε` plus the total length
of the intervals counted at any `K ≥ T / ε`. -/
theorem windowSup_le (ω : FlowSpace) {T ε : ℝ} (hε : 0 < ε) {K : ℝ} (hKT : T ≤ K * ε)
    (hall : ∀ q : ℚ, ω.2.1.toFun q ≠ ⊤ → holdLen ω.2.1 q ≠ ∞) :
    windowSup ω T ≤ ENNReal.ofReal ε + ∑' I : countedSet K ω, volume (I : Set ℝ) := by
  refine iSup₂_le fun q hq => ?_
  by_cases hqv : ω.2.1.toFun q = ⊤
  · show holdLen ω.2.1 q ≤ _
    rw [holdLen_of_top _ hqv]
    exact zero_le
  · by_cases hlen : ENNReal.ofReal ε ≤ holdLen ω.2.1 q
    · have hmem := holdSet_mem_countedSet ω hε hKT hq hqv (hall q hqv) hlen
      have he := entryLen_ne_top_of_holdLen ω.2.1 hqv (hall q hqv)
      have hx := exitLen_ne_top_of_holdLen ω.2.1 hqv (hall q hqv)
      have hvol : volume (holdSet ω.2.1 q) = holdLen ω.2.1 q :=
        volume_holdSet_of_ne_top _ hqv he hx
      calc flowHold ω q = volume ((⟨holdSet ω.2.1 q, hmem⟩ : countedSet K ω) : Set ℝ) := hvol.symm
        _ ≤ ∑' I : countedSet K ω, volume (I : Set ℝ) :=
            ENNReal.le_tsum (f := fun I : countedSet K ω => volume (I : Set ℝ)) _
        _ ≤ ENNReal.ofReal ε + ∑' I : countedSet K ω, volume (I : Set ℝ) := le_add_self
    · push_neg at hlen
      exact le_trans hlen.le le_self_add

/-- **(17.2), the finiteness clause**: the window supremum is finite for every `T`. -/
theorem windowSup_lt_top_of_finite {ω : FlowSpace} (hcount : ∀ K : ℕ, (countedSet K ω).Finite)
    (hall : ∀ q : ℚ, ω.2.1.toFun q ≠ ⊤ → holdLen ω.2.1 q ≠ ∞) (T : ℝ) : windowSup ω T < ∞ := by
  obtain ⟨K, hK⟩ := exists_nat_ge T
  refine lt_of_le_of_lt (windowSup_le ω one_pos (K := K) (by linarith) hall) ?_
  exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
    lt_top_iff_ne_top.2 (tsum_volume_countedSet_ne_top (hcount K))⟩

/-- **(17.2), the `o(T)` clause**: for every `ε > 0` there is a constant `C` with
`windowSup ω T ≤ ε T + C` for all `T ≥ 0`. -/
theorem windowSup_le_of_finite {ω : FlowSpace} (hcount : ∀ K : ℕ, (countedSet K ω).Finite)
    (hall : ∀ q : ℚ, ω.2.1.toFun q ≠ ⊤ → holdLen ω.2.1 q ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ T : ℝ, 0 ≤ T → windowSup ω T ≤ ENNReal.ofReal (ε * T) + C := by
  obtain ⟨K, hK⟩ := exists_nat_ge (1 / ε)
  refine ⟨∑' I : countedSet K ω, volume (I : Set ℝ), tsum_volume_countedSet_ne_top (hcount K),
    fun T hT => ?_⟩
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · rw [← hT0]
    refine le_trans (iSup₂_le fun q hq => ?_) zero_le
    exact absurd (lt_of_le_of_lt hq.1 hq.2) (by norm_num)
  · have hKT : T ≤ (K : ℝ) * (ε * T) := by
      have h1 : 1 ≤ (K : ℝ) * ε := by
        have := mul_le_mul_of_nonneg_right hK hε.le
        rwa [one_div, inv_mul_cancel₀ hε.ne'] at this
      nlinarith
    exact windowSup_le ω (mul_pos hε hTpos) hKT hall

end ReflectedGMS.HoldingIntervalsSubmacroscopic

#print axioms ReflectedGMS.HoldingIntervalsSubmacroscopic.timeShiftCovariant_subKernel
#print axioms ReflectedGMS.HoldingIntervalsSubmacroscopic.parabolicCovariant_subKernel
#print axioms ReflectedGMS.HoldingIntervalsSubmacroscopic.measurable_subKernel
#print axioms ReflectedGMS.HoldingIntervalsSubmacroscopic.lintegral_subKernel_outgoing
#print axioms ReflectedGMS.HoldingIntervalsSubmacroscopic.lintegral_subKernel_incoming
#print axioms ReflectedGMS.HoldingIntervalsSubmacroscopic.ae_forall_finite_submacroscopic
#print axioms ReflectedGMS.HoldingIntervalsSubmacroscopic.windowSup_lt_top_of_finite
#print axioms ReflectedGMS.HoldingIntervalsSubmacroscopic.windowSup_le_of_finite
