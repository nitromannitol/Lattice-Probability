/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.FirstCycleLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedCycleSpliceKernel
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerationKernelMeasurability

/-!
# The first complete cycle of the actual walk and its law (regeneration milestone 2(b)/(c))

`Temporal/TwoSidedCycleSpliceKernel.hcyc_rootedRegKernel` asks, at each live environment, for a
probability law `ν` on the cycle space `Cyc (rootLabel e)` with clause (b)
`CompleteCycleReversal ν` and clause (c) `RootedCycleDecomposition (rootedRegKernel … e) ν`.
The intended `ν` is **the law of the first complete cycle of the actual area walk from the
root**: the holding at the root followed by the excursion, killed at the first complete return.

This module fixes that `ν` once and for all (both (b) and (c) are stated about it):

* `RegLL` — the one-sided regularity subtype (right-regular with left limits);
* `firstCycle v : RegLL → Cyc v` — the path killed at its first complete return to `v`, with
  that return time as length (`isCycle_killedAtReturn`); a fixed two-step default cycle when the
  path does not start at `v` or never returns (`defaultCycle`); **measurable**
  (`measurable_firstCycle`);
* `regSlotLaw G hwalk n e` — the forward label law `slotLaw G n e` lifted to `RegLL` through the
  sample space (`TwoSidedCycleSpliceKernel.exists_slotLaw_lift`); a law on the subtype is unique
  given its image (`regSlotLaw_eq_of_map_val_eq`);
* **`firstCycleLaw G hwalk n e : Measure (Cyc n)`** — `(regSlotLaw G hwalk n e).map (firstCycle n)`,
  a probability measure; at the root it is the `ν` of `hcyc_rootedRegKernel`;
* `firstCycleLaw_eq_map_of_map_val_eq` — any lift of the slot law computes it;
* `firstCycleLaw_eq_map_rootedRegKernel` — it is the law of the first cycle of the forward half
  under the rooted kernel on the regularity subtype (with `hmeas` discharged by
  `RegenerationKernelMeasurability.measurable_slotTransition`, or with any `hmeas`).

Nothing here is probabilistic: no reversal or decomposition statement is proved.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.FirstCycleLaw

open Code EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.RegenerationKernel
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.TwoSidedCycleSplice

/-! ### 1. The one-sided regularity subtype -/

/-- Right-regular trajectories with left limits (one half of `TwoSidedReg`). -/
abbrev RegLL : Type := {x : Trajectory ℕ // IsRegLL x}

/-- The diagonal embedding into the two-sided carrier (used only to reuse its measurability
lemmas, which read the forward half). -/
def diagReg (x : RegLL) : TwoSidedReg := ⟨(x.1, x.1), ⟨x.2, x.2⟩⟩

theorem measurable_diagReg : Measurable diagReg :=
  (measurable_subtype_coe.prodMk measurable_subtype_coe).subtype_mk

theorem measurable_fwdReturn_reg : Measurable fun x : RegLL => fwdReturn x.1 :=
  measurable_fwdReturn.comp measurable_diagReg

theorem measurable_retLen_reg : Measurable fun x : RegLL => retLen x.1 :=
  measurable_retLen.comp measurable_diagReg

/-- The forward half of a two-sided regular pair. -/
def fwdReg (p : TwoSidedReg) : RegLL := ⟨p.1.1, p.2.fwd⟩

theorem measurable_fwdReg : Measurable fwdReg :=
  (measurable_fst.comp measurable_subtype_coe).subtype_mk

/-! ### 2. The path killed at its first complete return is a complete cycle -/

/-- **Structure of the first complete return** of a right-regular path started at `v` that
returns: an exit time `a` with `0 < a < r`, the path at `v` on `[0,a)` and off `v` on `[a,r)`,
where `r = retLen x` is the first return. -/
theorem exists_hold_of_fwdReturn {v : ℕ} {x : Trajectory ℕ}
    (hx : RightRegularAt (coord (V := ℕ)) x) (h0 : x 0 = some v) (hr : fwdReturn x ≠ ⊤) :
    fwdReturn x = retLen x ∧ ∃ a : ℝ≥0, 0 < a ∧ a < retLen x ∧ (∀ t, t < a → x t = some v) ∧
      (∀ t, a ≤ t → t < retLen x → x t ≠ some v) ∧ x (retLen x) = some v := by
  have hfr : fwdReturn x = retTime v x := by
    unfold fwdReturn
    rw [h0]
    rfl
  obtain ⟨r, hr'⟩ := WithTop.ne_top_iff_exists.1 hr
  have hrl : retLen x = r := by
    rw [retLen, ← hr']
    rfl
  refine ⟨by rw [hrl, hr'], ?_⟩
  rw [hrl]
  have hret : retTime v x = r := by rw [← hfr, hr']
  -- the exit from `v`
  cases hex : exitAfter coord (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) x with
  | top =>
    exfalso
    have htop : retTime v x = ⊤ := by
      rw [retTime_eq]
      exact hitAfter_top hex
    rw [hret] at htop
    exact WithTop.coe_ne_top htop
  | coe a =>
    have ha : MeasureTheory.hittingAfter coord {s | s ≠ x 0} 0 x = a := by
      rw [← exitAfter_zero_eq]
      exact hex
    have hadm : AdmissibleTarget {s : Option ℕ | s ≠ x 0} := by
      rw [h0]
      exact admissibleTarget_ne v
    have hxa : x a ≠ some v := by
      have hm : coord a x ∈ {s : Option ℕ | s ≠ x 0} :=
        mem_of_hittingAfter_eq_of_rightRegular hx hadm ha
      have hm' : x a ≠ x 0 := hm
      rwa [h0] at hm'
    have hbef : ∀ t, t < a → x t = some v := by
      intro t hta
      have hlt : ((t : ℝ≥0) : WithTop ℝ≥0) < MeasureTheory.hittingAfter coord {s | s ≠ x 0} 0 x := by
        rw [ha]
        exact WithTop.coe_lt_coe.2 hta
      have hn := MeasureTheory.notMem_of_lt_hittingAfter hlt (bot_le : (0 : ℝ≥0) ≤ t)
      have hn' : ¬ (x t ≠ x 0) := hn
      rw [not_not, h0] at hn'
      exact hn'
    have ha0 : 0 < a := by
      rcases (bot_le : (0 : ℝ≥0) ≤ a).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hxa
        exact hxa h0
    have hr2 : MeasureTheory.hittingAfter coord (some '' (({v} : Finset ℕ) : Set ℕ)) a x = r := by
      have h1 := retTime_eq v x
      rw [hitAfter_coe hex] at h1
      rw [← h1]
      exact hret
    have hxr : x r = some v := by
      obtain ⟨w, hw, hxw⟩ :=
        mem_of_hittingAfter_eq_of_rightRegular hx (admissibleTarget_image {v}) hr2
      have hwv : w = v := by simpa using hw
      have hxw' : x r = some w := hxw.symm
      rw [hxw', hwv]
    have har : a ≤ r := WithTop.coe_le_coe.1 (hr2 ▸ MeasureTheory.le_hittingAfter x)
    have har' : a < r := by
      rcases har.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [h] at hxa
        exact hxa hxr
    refine ⟨a, ha0, har', hbef, fun t hat htr => ?_, hxr⟩
    have hlt : ((t : ℝ≥0) : WithTop ℝ≥0) <
        MeasureTheory.hittingAfter coord (some '' (({v} : Finset ℕ) : Set ℕ)) a x := by
      rw [hr2]
      exact WithTop.coe_lt_coe.2 htr
    have hn := MeasureTheory.notMem_of_lt_hittingAfter hlt hat
    intro hxt
    exact hn ⟨v, by simp, (show coord t x = some v from hxt).symm⟩

/-- **The path killed at its first complete return is a complete cycle.** -/
theorem isCycle_killedAtReturn {v : ℕ} {x : Trajectory ℕ} (hx : IsRegLL x) (h0 : x 0 = some v)
    (hr : fwdReturn x ≠ ⊤) : IsCycle v (glue x (retLen x) cem) (retLen x) := by
  obtain ⟨-, a, ha0, har, hbef, haft, -⟩ := exists_hold_of_fwdReturn hx.regular h0 hr
  refine ⟨?_, isRegLL_glue hx isRegLL_cem _, fun t ht => ?_, ⟨a, ha0, har, fun t ht => ?_,
    fun t hat htr => ?_⟩⟩
  · rw [glue_of_lt (ha0.trans har)]
    exact h0
  · rw [glue_of_le ht]
    rfl
  · rw [glue_of_lt (ht.trans har)]
    exact hbef t ht
  · rw [glue_of_lt htr]
    exact haft t hat htr

/-! ### 3. The first-cycle map -/

/-- A fixed default cycle (hold `1` at `v`, then `1` at `v + 1`). -/
noncomputable def defaultCycle (v : ℕ) : Cyc v := twoStepCycle (Nat.succ_ne_self v).symm

open Classical in
/-- The first cycle, as a raw pair. -/
noncomputable def firstCycleRaw (v : ℕ) (x : RegLL) : Trajectory ℕ × ℝ≥0 :=
  if x.1 0 = some v ∧ fwdReturn x.1 ≠ ⊤ then (glue x.1 (retLen x.1) cem, retLen x.1)
  else (defaultCycle v).1

theorem isCycle_firstCycleRaw (v : ℕ) (x : RegLL) :
    IsCycle v (firstCycleRaw v x).1 (firstCycleRaw v x).2 := by
  unfold firstCycleRaw
  split_ifs with h
  · exact isCycle_killedAtReturn x.2 h.1 h.2
  · exact (defaultCycle v).2

/-- **The first complete cycle** of a regular path from `v`: the path killed at its first complete
return, with that return time as length; the default cycle if the path does not start at `v` or
never returns. -/
noncomputable def firstCycle (v : ℕ) (x : RegLL) : Cyc v :=
  ⟨firstCycleRaw v x, isCycle_firstCycleRaw v x⟩

theorem firstCycle_of_good {v : ℕ} {x : RegLL} (h0 : x.1 0 = some v) (hr : fwdReturn x.1 ≠ ⊤) :
    (firstCycle v x).1 = (glue x.1 (retLen x.1) cem, retLen x.1) := by
  show firstCycleRaw v x = _
  unfold firstCycleRaw
  rw [if_pos ⟨h0, hr⟩]

theorem measurableSet_goodStart (v : ℕ) :
    MeasurableSet {x : RegLL | x.1 0 = some v ∧ fwdReturn x.1 ≠ ⊤} := by
  have h1 : MeasurableSet {x : RegLL | x.1 0 = some v} := by
    have hm : Measurable fun x : RegLL => x.1 0 :=
      (measurable_pi_apply 0).comp measurable_subtype_coe
    show MeasurableSet ((fun x : RegLL => x.1 0) ⁻¹' {some v})
    exact hm (measurableSet_option _)
  have h2 : MeasurableSet {x : RegLL | fwdReturn x.1 ≠ ⊤} :=
    (measurable_fwdReturn_reg (measurableSet_singleton ⊤)).compl
  exact h1.inter h2

theorem measurable_firstCycleRaw (v : ℕ) : Measurable (firstCycleRaw v) := by
  classical
  have hT := measurable_retLen_reg
  have hglue : Measurable fun x : RegLL => glue x.1 (retLen x.1) cem := by
    refine measurable_pi_iff.2 fun s => ?_
    show Measurable fun x : RegLL => if s < retLen x.1 then x.1 s else (none : Option ℕ)
    exact Measurable.ite (measurableSet_lt measurable_const hT)
      ((measurable_pi_apply s).comp measurable_subtype_coe) measurable_const
  have h : Measurable fun x : RegLL =>
      if x ∈ {x : RegLL | x.1 0 = some v ∧ fwdReturn x.1 ≠ ⊤} then
        (glue x.1 (retLen x.1) cem, retLen x.1) else (defaultCycle v).1 :=
    Measurable.ite (measurableSet_goodStart v) (hglue.prodMk hT) measurable_const
  have heq : firstCycleRaw v = fun x : RegLL =>
      if x ∈ {x : RegLL | x.1 0 = some v ∧ fwdReturn x.1 ≠ ⊤} then
        (glue x.1 (retLen x.1) cem, retLen x.1) else (defaultCycle v).1 := by
    funext x
    unfold firstCycleRaw
    by_cases hx : x.1 0 = some v ∧ fwdReturn x.1 ≠ ⊤
    · rw [if_pos hx, if_pos (show x ∈ {x : RegLL | x.1 0 = some v ∧ fwdReturn x.1 ≠ ⊤} from hx)]
    · rw [if_neg hx, if_neg (show x ∉ {x : RegLL | x.1 0 = some v ∧ fwdReturn x.1 ≠ ⊤} from hx)]
  rw [heq]
  exact h

/-- **The first-cycle map is measurable.** -/
theorem measurable_firstCycle (v : ℕ) : Measurable (firstCycle v) :=
  (measurable_firstCycleRaw v).subtype_mk

/-! ### 4. The first-cycle law -/

/-- The forward label law `slotLaw G n e`, lifted to the regularity subtype through the sample
space (unique: `regSlotLaw_eq_of_map_val_eq`). -/
noncomputable def regSlotLaw (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (n : ℕ) (e : Env) : Measure RegLL :=
  (exists_slotLaw_lift G hwalk n e).choose

instance regSlotLaw_isProbabilityMeasure (G : Set Env)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (n : ℕ) (e : Env) :
    IsProbabilityMeasure (regSlotLaw G hwalk n e) :=
  (exists_slotLaw_lift G hwalk n e).choose_spec.1

theorem regSlotLaw_map_val (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (n : ℕ) (e : Env) : (regSlotLaw G hwalk n e).map Subtype.val = slotLaw G n e :=
  (exists_slotLaw_lift G hwalk n e).choose_spec.2

/-- Every lift of the slot law to the regularity subtype is `regSlotLaw`. -/
theorem regSlotLaw_eq_of_map_val_eq (G : Set Env)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (n : ℕ) (e : Env) {μ : Measure RegLL}
    (hμ : μ.map Subtype.val = slotLaw G n e) : regSlotLaw G hwalk n e = μ :=
  subtype_measure_eq_of_map_val_eq ((regSlotLaw_map_val G hwalk n e).trans hμ.symm)

/-- **The first-cycle law**: the law of the first complete cycle (holding at the start slot `n`
followed by the excursion, killed at the first complete return) of the actual area walk of `e`
started at slot `n`, in the label coding.  At `n = rootLabel e` this is the cycle law `ν` of
`TwoSidedCycleSpliceKernel.hcyc_rootedRegKernel`.  Off the live set (`e ∉ G` or the slot absent)
it is the point mass at `defaultCycle n`. -/
noncomputable def firstCycleLaw (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (n : ℕ) (e : Env) : Measure (Cyc n) :=
  (regSlotLaw G hwalk n e).map (firstCycle n)

instance firstCycleLaw_isProbabilityMeasure (G : Set Env)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (n : ℕ) (e : Env) :
    IsProbabilityMeasure (firstCycleLaw G hwalk n e) :=
  by unfold firstCycleLaw; infer_instance

end ReflectedGMS.FirstCycleLaw
