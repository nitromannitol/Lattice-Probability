/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TwoSidedCycleReversal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedCycleSplice

/-!
# `hcyc` modulo clauses 2 and 3 (regeneration lane, milestone 2 reduced to two named inputs)

`Temporal/TwoSidedCycleSplice` proves `CycleErgodic (entranceLaw ν) rho` for the
entrance-rooted i.i.d.-cycle law of any cycle law `ν` (milestone 2(a)).  This module states the
two remaining clauses of the handoff (`outputs/fable-regenerative-invariance-handoff.md`,
"Milestones 2–3", items (b), (c)) as named hypotheses and proves that they give `hcyc`.

## The cycle reversal

`cycRev` keeps the holding at `v` in front and reverses the excursion (right-continuously):
for a cycle `c` = hold `h` at `v` ⊕ excursion `E` of total length `L`,

  `cycRev c u = v` (`u < h`),  `c((L + h − u)−)` (`h ≤ u < L`),  `∞` (`u ≥ L`).

It is a measurable self-map of the cycle space (`measurable_cycRev`); the holding time is read
off the path along a dense sequence (`holdE_eq`).

## The two hypotheses

* **(b) `CompleteCycleReversal ν`**: `ν.map cycRev = ν` — clause 2, reversal invariance of the
  complete stopped cycle.
* **(c) `RootedCycleDecomposition P ν`**: `P.map rho ≪ mixedLaw ν`, where `mixedLaw ν` is the
  splice of the independent sequence with law `ν` at the indices `k ≥ -1` and `ν.map cycRev` at
  `k ≤ -2` — clause 3 proper (cycle decomposition of the rooted law, the straddling holding
  `Gamma(2)` vs `Exp`), which does NOT presuppose clause 2: re-rooting the vertex-rooted law at
  the first return puts the forward excursion `E₁` (with the straddling holding) at index `-1`
  and, at `k ≤ -2`, the cycles `hold h'_k ⊕ rev E'_{k-1}` of the backward copy, i.e. reversed
  forward cycles.

The handoff's literal clause 3, `EntranceAbsCont P ν : P.map rho ≪ entranceLaw ν`, is (b)+(c)
(`entranceAbsCont_of_reversal`), and it alone gives `CycleErgodic P rho`
(`cycleErgodic_of_entranceAbsCont`).  `hcyc_of_reversal_and_decomposition` is the fibrewise form
consumed by `RegenerativeInvarianceFiberwise.fiberwiseConstant_of_cycleErgodic`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.TwoSidedCycleSplice

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.RegenerativeInvarianceFiberwise

/-! ### 1. The cycle reversal -/

/-- The constant path at `v`. -/
def constPath (v : ℕ) : Trajectory ℕ := fun _ => some v

theorem isRegLL_constPath (v : ℕ) : IsRegLL (constPath v) where
  regular := rightRegularAt_of (fun t _ h => ⟨t + 1, lt_add_one t, fun _ _ _ => h⟩)
    (fun _ h => by simp [constPath] at h)
  leftLimits := fun y _ ht => by
    by_cases hvy : v = y
    · exact ⟨0, ht, Or.inl fun _ _ => by simp [constPath, hvy]⟩
    · exact ⟨0, ht, Or.inr fun _ _ => by simp [constPath, hvy]⟩

/-- The reversed cycle path: hold `h` at `v`, then the right-continuous reversal of the
excursion `c|[h, L)`, killed at `L`. -/
noncomputable def cycRevPath (x : Trajectory ℕ) (v : ℕ) (h L : ℝ≥0) : Trajectory ℕ :=
  glue (constPath v) h (glue (revPiece x L) (L - h) cem)

/-- The holding time at `v`, read along the dense sequence. -/
noncomputable def holdE (v : ℕ) (x : Trajectory ℕ) : ℝ≥0∞ :=
  ⨅ n : ℕ, if x (TopologicalSpace.denseSeq ℝ≥0 n) ≠ some v then
    ((TopologicalSpace.denseSeq ℝ≥0 n : ℝ≥0) : ℝ≥0∞) else ⊤

theorem holdE_eq {v : ℕ} {x : Trajectory ℕ} {L h : ℝ≥0} (hL : h < L)
    (hbef : ∀ t, t < h → x t = some v) (haft : ∀ t, h ≤ t → t < L → x t ≠ some v) :
    holdE v x = h := by
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
    induction a using ENNReal.recTopCoe with
    | top => exact le_top
    | coe b =>
      have hb : h < b := ENNReal.coe_lt_coe.1 ha
      obtain ⟨q, ⟨n, rfl⟩, hq1, hq2⟩ :=
        Dense.exists_between (TopologicalSpace.denseRange_denseSeq ℝ≥0) (lt_min hb hL)
      refine (iInf_le _ n).trans ?_
      rw [if_pos (haft _ hq1.le (lt_of_lt_of_le hq2 (min_le_right _ _)))]
      exact ENNReal.coe_le_coe.2 (lt_of_lt_of_le hq2 (min_le_left _ _)).le
  · refine le_iInf fun n => ?_
    split_ifs with hne
    · exact ENNReal.coe_le_coe.2 (not_lt.1 fun hlt => hne (hbef _ hlt))
    · exact le_top

variable {v : ℕ}

/-- The holding time of a cycle. -/
noncomputable def holdTime (c : Cyc v) : ℝ≥0 := (holdE v c.1.1).toNNReal

theorem holdTime_eq (c : Cyc v) {h : ℝ≥0} (hL : h < c.1.2)
    (hbef : ∀ t, t < h → c.1.1 t = some v) (haft : ∀ t, h ≤ t → t < c.1.2 → c.1.1 t ≠ some v) :
    holdTime c = h := by
  rw [holdTime, holdE_eq hL hbef haft, ENNReal.toNNReal_coe]

theorem isCycle_cycRevPath (c : Cyc v) :
    IsCycle v (cycRevPath c.1.1 v (holdTime c) c.1.2) c.1.2 := by
  obtain ⟨h, h0, hL, hbef, haft⟩ := c.2.hold
  rw [holdTime_eq c hL hbef haft]
  refine ⟨?_, ?_, ?_, ⟨h, h0, hL, ?_, ?_⟩⟩
  · rw [cycRevPath, glue_of_lt h0]
    rfl
  · exact isRegLL_glue (isRegLL_constPath v)
      (isRegLL_glue (isRegLL_revPiece c.2.regLL _) isRegLL_cem _) _
  · intro t ht
    have hht : h ≤ t := hL.le.trans ht
    rw [cycRevPath, glue_of_le hht, glue_of_le (tsub_le_tsub_right ht h)]
    rfl
  · intro t ht
    rw [cycRevPath, glue_of_lt ht]
    rfl
  · intro t hht htL
    rw [cycRevPath, glue_of_le hht, glue_of_lt ((tsub_lt_tsub_iff_right hht).2 htL),
      revPiece_of_lt (lt_of_le_of_lt tsub_le_self htL)]
    have hlt : h < c.1.2 - (t - h) := by
      rw [lt_tsub_iff_left, tsub_add_cancel_of_le hht]
      exact htL
    exact leftLim_ne_some_of hlt fun s hs => haft s hs.1.le (lt_of_lt_of_le hs.2 tsub_le_self)

/-- **The complete-cycle reversal** on the cycle space: holding kept in front, excursion
reversed. -/
noncomputable def cycRev (c : Cyc v) : Cyc v :=
  ⟨(cycRevPath c.1.1 v (holdTime c) c.1.2, c.1.2), isCycle_cycRevPath c⟩

theorem measurable_holdTime : Measurable (holdTime (v := v)) := by
  refine ENNReal.measurable_toNNReal.comp (Measurable.iInf fun n => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have hx : Measurable fun c : Cyc v => c.1.1 := measurable_fst.comp measurable_subtype_coe
  have hq : Measurable fun c : Cyc v => c.1.1 (TopologicalSpace.denseSeq ℝ≥0 n) :=
    (measurable_pi_apply (TopologicalSpace.denseSeq ℝ≥0 n)).comp hx
  exact hq (measurableSet_option {s : Option ℕ | s ≠ some v})

theorem measurable_cycRev : Measurable (cycRev (v := v)) := by
  have hx : Measurable fun c : Cyc v => c.1.1 := measurable_fst.comp measurable_subtype_coe
  have hL : Measurable fun c : Cyc v => c.1.2 := measurable_snd.comp measurable_subtype_coe
  have hH := measurable_holdTime (v := v)
  have hpath : Measurable fun c : Cyc v => cycRevPath c.1.1 v (holdTime c) c.1.2 := by
    refine measurable_pi_iff.2 fun u => ?_
    show Measurable fun c : Cyc v => if u < holdTime c then some v else
      (if u - holdTime c < c.1.2 - holdTime c then
        (if u - holdTime c < c.1.2 then leftLim c.1.1 (c.1.2 - (u - holdTime c)) else none)
        else none)
    refine Measurable.ite (measurableSet_lt measurable_const hH) measurable_const ?_
    refine Measurable.ite (measurableSet_lt (measurable_nnreal_sub measurable_const hH)
      (measurable_nnreal_sub hL hH)) ?_ measurable_const
    refine Measurable.ite (measurableSet_lt (measurable_nnreal_sub measurable_const hH) hL) ?_
      measurable_const
    exact measurable_leftLim_at hx (fun c => c.2.regLL)
      (measurable_nnreal_sub hL (measurable_nnreal_sub measurable_const hH))
  exact (hpath.prodMk hL).subtype_mk

/-! ### 2. The two named hypotheses and the reduction -/

/-- The splice of the independent sequence with law `ν` at the indices `k ≥ -1` and the
reversed law `ν.map cycRev` at `k ≤ -2` — the law of the re-rooted vertex-rooted two-sided path
in cycle coordinates, before clause 2 is used. -/
noncomputable def mixedLaw (ν : Measure (Cyc v)) : Measure TwoSidedReg :=
  (Measure.infinitePi fun k : ℤ => if k ≤ -2 then ν.map cycRev else ν).map splice

/-- **(b) Clause 2: reversal invariance of the complete stopped cycle.** -/
def CompleteCycleReversal (ν : Measure (Cyc v)) : Prop := ν.map cycRev = ν

/-- **(c) Clause 3 proper: the cycle decomposition of the rooted law.**  After one re-rooting,
the rooted two-sided law is absolutely continuous w.r.t. the splice of independent cycles with
law `ν` at `k ≥ -1` and reversed cycles at `k ≤ -2` (straddling holding `Gamma(2)` vs `Exp`). -/
def RootedCycleDecomposition (P : Measure TwoSidedReg) (ν : Measure (Cyc v)) : Prop :=
  P.map rho ≪ mixedLaw ν

/-- The handoff's literal clause 3: `(κ e).map ρ ≪ Q_ent`. -/
def EntranceAbsCont (P : Measure TwoSidedReg) (ν : Measure (Cyc v)) : Prop :=
  P.map rho ≪ entranceLaw ν

/-- Under clause 2 the mixed law is the entrance-rooted i.i.d. law. -/
theorem mixedLaw_of_reversal {ν : Measure (Cyc v)} (hb : CompleteCycleReversal ν) :
    mixedLaw ν = entranceLaw ν := by
  unfold CompleteCycleReversal at hb
  unfold mixedLaw entranceLaw Temporal.iidCycleLaw
  simp only [hb, ite_self]

/-- **(b) + (c) ⟹ the literal clause 3.** -/
theorem entranceAbsCont_of_reversal {P : Measure TwoSidedReg} {ν : Measure (Cyc v)}
    (hb : CompleteCycleReversal ν) (hc : RootedCycleDecomposition P ν) : EntranceAbsCont P ν := by
  unfold EntranceAbsCont
  rw [← mixedLaw_of_reversal hb]
  exact hc

/-- **The literal clause 3 gives cycle ergodicity** (transfer along `P.map ρ ≪ Q_ent`). -/
theorem cycleErgodic_of_entranceAbsCont {P : Measure TwoSidedReg} {ν : Measure (Cyc v)}
    [IsProbabilityMeasure ν] (hc : EntranceAbsCont P ν) : CycleErgodic P rho :=
  cycleErgodic_of_map_absolutelyContinuous measurable_rho (cycleErgodic_entranceLaw ν) hc

/-- **Milestone 2 modulo clauses 2 and 3.** -/
theorem cycleErgodic_of_reversal_and_decomposition {P : Measure TwoSidedReg}
    {ν : Measure (Cyc v)} [IsProbabilityMeasure ν] (hb : CompleteCycleReversal ν)
    (hc : RootedCycleDecomposition P ν) : CycleErgodic P rho :=
  cycleErgodic_of_entranceAbsCont (entranceAbsCont_of_reversal hb hc)

end ReflectedGMS.TwoSidedCycleSplice
