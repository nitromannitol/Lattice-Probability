/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CycleDecompositionRegeneration at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CycleDecompositionLaw

/-!
# The forward regeneration input at the actual walk (milestone 2(c), part 3)

`CycleDecompositionActual.ForwardCycleInputs` has three fields.  This module **proves the first**,
`ForwardRegeneration n (regSlotLaw G hwalk n e)` (`forwardRegeneration_regSlotLaw`), at every
environment on the gate with slot `n` present, by transporting the checked sample-space
regeneration of the actual walk (`ActualExcursionErgodicIdentification`:
`ae_mem_stopEvent_firstReturnTime`, `map_futureAt_firstReturnTime`,
`indepFun_killedPathAt_futureAt`) to the label coding on the regularity subtype.

* `retTime_labelTraj`, `fwdReturn_labelTraj` — first returns are invariant under the label coding;
* `exists_lift_fun` — an a.e. lift of a sample-space map to a subtype, as a measurable function;
  `regSlotLaw` is its image law (uniqueness of lifts);
* `cycLen` — a measurable functional of a raw path returning the length of a killed path along the
  dense sequence (so the cycle is a measurable function of the killed path, a.s.);
* **`forwardRegeneration_regSlotLaw`**.

Consequently the only remaining inputs of clause (c) at the actual kernel are (R4)
`HoldExcIndep` and (R5) `StraddleAbsCont` of `firstCycleLaw` (`forwardCycleInputs_of`,
`rootedCycleDecomposition_rootedRegKernel_of`, `hcyc_rootedRegKernel_of_holdings`).
-/

-- Merged from `ReflectedGMS/Temporal/CycleDecompositionActual.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_CycleDecompositionActual

/-!
# (c) at the actual rooted kernel, and `hcyc` from (b) + the forward cycle inputs

The rooted kernel on the regularity subtype is, at every environment, the independent pair of the
lifted forward slot law (`rootedRegKernel_eq_pairReg`: a law on the subtype is determined by its
image).  Hence `CycleDecompositionLaw.rootedCycleDecomposition_of_regeneration` applies with
`μ = regSlotLaw G hwalk (rootLabel e) e` and `ν = firstCycleLaw G hwalk (rootLabel e) e`
(literally `μ.map (firstCycle _)`):

* **`rootedCycleDecomposition_rootedRegKernel`** — clause (c) at the actual kernel from the
  forward-cycle inputs `ForwardCycleInputs G hwalk e` (one-step regeneration of the lifted slot law
  at the first return, (R4) holding/excursion independence and (R5) straddle absolute continuity of
  its cycle law);
* **`hcyc_rootedRegKernel_of_inputs`** (and `…'` with `hmeas` discharged) — cycle ergodicity of the
  actual kernel from clause (b) `CompleteCycleReversal (firstCycleLaw …)` and those inputs, a.e.
  on the live set.

The inputs are properties of the ONE-SIDED walk from the root at a fixed environment; they hold for
the actual area walk (see the handoff): regeneration at returns is
`ActualExcursionErgodicIdentification.map_futureAt_firstReturnTime` /
`indepFun_killedPathAt_futureAt` (transported to the label coding), (R4) is property (iii) of
`IsReflectedWalk` (exit time ⊥ exit position) + the strong Markov property at the exit time, (R5)
is `Exp(q) ∗ Exp(q) = Γ(2, q) ≪ Exp(q)`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CycleDecomposition

open Code EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.RegenerationKernel
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.TwoSidedCycleSplice
open ReflectedGMS.FirstCycleLaw
open ReflectedGMS.RegenerativeInvarianceFiberwise

/-- **The rooted kernel on the regularity subtype is the independent pair of lifted slot laws.** -/
theorem rootedRegKernel_eq_pairReg (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) (e : Env) :
    rootedRegKernel G hG hwalk hmeas e =
      ((regSlotLaw G hwalk (rootLabel e) e).prod (regSlotLaw G hwalk (rootLabel e) e)).map
        pairReg := by
  apply subtype_measure_eq_of_map_val_eq
  rw [rootedRegKernel_map_val, Measure.map_map measurable_subtype_coe measurable_pairReg]
  have e1 : (Subtype.val ∘ pairReg : RegLL × RegLL → TwoSidedCoding) =
      Prod.map Subtype.val Subtype.val := rfl
  rw [e1, ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe,
    regSlotLaw_map_val]
  rfl

/-- **The forward-cycle inputs at an environment**: one-step regeneration of the lifted forward
slot law from the root at its first complete return, and (R4), (R5) for its cycle law. -/
structure ForwardCycleInputs (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (e : Env) : Prop where
  regen : ForwardRegeneration (rootLabel e) (regSlotLaw G hwalk (rootLabel e) e)
  holdExc : HoldExcIndep (firstCycleLaw G hwalk (rootLabel e) e)
  straddle : StraddleAbsCont (firstCycleLaw G hwalk (rootLabel e) e)

/-- **Clause (c) at the actual kernel.** -/
theorem rootedCycleDecomposition_rootedRegKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hmeas : ∀ (n : ℕ) (t : ℝ≥0) (m : ℕ), Measurable (slotTransition G n t m)) {e : Env}
    (h : ForwardCycleInputs G hwalk e) :
    RootedCycleDecomposition (rootedRegKernel G hG hwalk hmeas e)
      (firstCycleLaw G hwalk (rootLabel e) e) := by
  rw [rootedRegKernel_eq_pairReg]
  exact rootedCycleDecomposition_of_regeneration _ h.regen h.holdExc h.straddle

end ReflectedGMS.CycleDecomposition

end Merged_CycleDecompositionActual

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CycleDecomposition

open Code EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.RegenerationKernel
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.TwoSidedCycleSplice
open ReflectedGMS.FirstCycleLaw
open ReflectedGMS.RegenerativeInvarianceFiberwise
open ReflectedGMS.Temporal.ActualExcursionErgodicIdentification
open ReflectedGMS.TargetReturnRecursion

/-! ### 1. Label invariance of the first return -/

theorem hittingAfter_label {r : RawCode} {x : Trajectory (Vertex r)}
    {S : Set (Option (Vertex r))} {S' : Set (Option ℕ)} (h : ∀ t, x t ∈ S ↔ labelTraj x t ∈ S')
    (n : ℝ≥0) :
    MeasureTheory.hittingAfter coord S' n (labelTraj x) =
      MeasureTheory.hittingAfter coord S n x := by
  have hc : (∃ j, n ≤ j ∧ coord j (labelTraj x) ∈ S') ↔ ∃ j, n ≤ j ∧ coord j x ∈ S := by
    simp only [coord, h]
  have hs : {j | n ≤ j ∧ coord j (labelTraj x) ∈ S'} = {j | n ≤ j ∧ coord j x ∈ S} := by
    ext j
    simp only [Set.mem_setOf_eq, coord, h]
  rw [MeasureTheory.hittingAfter_def, MeasureTheory.hittingAfter_def]
  dsimp only
  rw [hs]
  by_cases hex : ∃ j, n ≤ j ∧ coord j x ∈ S
  · rw [if_pos hex, if_pos (hc.2 hex)]
  · rw [if_neg hex, if_neg (fun h' => hex (hc.1 h'))]

theorem retTime_labelTraj {r : RawCode} (x : Trajectory (Vertex r)) (w : Vertex r) :
    retTime w.val (labelTraj x) = retTime w x := by
  have hinj : Function.Injective (Option.map (Subtype.val : Vertex r → ℕ)) :=
    Option.map_injective Subtype.val_injective
  have hexit : exitAfter coord (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) (labelTraj x) =
      exitAfter coord (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) x := by
    rw [exitAfter_zero_eq, exitAfter_zero_eq]
    refine hittingAfter_label (fun t => ?_) 0
    simp only [Set.mem_setOf_eq, labelTraj_apply, ne_eq, hinj.eq_iff]
  have hmem : ∀ t, x t ∈ some '' ((({w} : Finset (Vertex r))) : Set (Vertex r)) ↔
      labelTraj x t ∈ some '' ((({w.val} : Finset ℕ)) : Set ℕ) := by
    intro t
    cases hxt : x t with
    | none => simp [labelTraj_apply, hxt]
    | some u => simp [labelTraj_apply, hxt, Subtype.ext_iff]
  rw [retTime_eq, retTime_eq]
  cases hx : exitAfter coord (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) x with
  | top => rw [hitAfter_top hx, hitAfter_top (hexit.trans hx)]
  | coe a =>
    rw [hitAfter_coe hx, hitAfter_coe (hexit.trans hx)]
    exact hittingAfter_label hmem a

theorem fwdReturn_labelTraj {r : RawCode} {x : Trajectory (Vertex r)} {w : Vertex r}
    (h0 : x 0 = some w) : fwdReturn (labelTraj x) = retTime w x := by
  unfold fwdReturn
  rw [labelTraj_apply, h0]
  exact retTime_labelTraj x w

/-! ### 2. Lifts and the length of a killed path -/

/-- **An a.e. lift to a subtype, as a measurable function.** -/
theorem exists_lift_fun {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω)
    {f : Ω → Y} (hf : Measurable f) {p : Y → Prop} (hp : ∀ᵐ ω ∂P, p (f ω)) {y₀ : Y}
    (hy₀ : p y₀) : ∃ g : Ω → {y // p y}, Measurable g ∧ ∀ᵐ ω ∂P, (g ω).1 = f ω := by
  classical
  set G₀ : Set Ω := (toMeasurable P {ω | ¬ p (f ω)})ᶜ with hG₀
  have hG₀m : MeasurableSet G₀ := (measurableSet_toMeasurable _ _).compl
  have hgood : ∀ ω ∈ G₀, p (f ω) := by
    intro ω hω
    by_contra hn
    exact hω (subset_toMeasurable _ _ hn)
  have hae : ∀ᵐ ω ∂P, ω ∈ G₀ := by
    rw [ae_iff]
    have hc : {ω | ¬ ω ∈ G₀} = toMeasurable P {ω | ¬ p (f ω)} := by
      ext ω
      simp [hG₀]
    rw [hc, measure_toMeasurable]
    exact ae_iff.1 hp
  set g₀ : Ω → Y := fun ω => if ω ∈ G₀ then f ω else y₀ with hg₀
  have hg : ∀ ω, p (g₀ ω) := by
    intro ω
    by_cases hω : ω ∈ G₀
    · simp only [hg₀, if_pos hω]
      exact hgood ω hω
    · simp only [hg₀, if_neg hω]
      exact hy₀
  refine ⟨fun ω => ⟨g₀ ω, hg ω⟩, (Measurable.ite hG₀m hf measurable_const).subtype_mk, ?_⟩
  filter_upwards [hae] with ω hω
  show g₀ ω = f ω
  simp only [hg₀, if_pos hω]

/-- The length of a killed path, read along the dense sequence: the supremum of the dense times
at which the path is not at `∞`. -/
noncomputable def cycLen (c : Trajectory ℕ) : ℝ≥0 :=
  (⨆ k : ℕ, if c (TopologicalSpace.denseSeq ℝ≥0 k) ≠ none then
    ((TopologicalSpace.denseSeq ℝ≥0 k : ℝ≥0) : ℝ≥0∞) else 0).toNNReal

theorem measurable_cycLen : Measurable cycLen := by
  refine ENNReal.measurable_toNNReal.comp (Measurable.iSup fun k => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have hm : Measurable fun c : Trajectory ℕ => c (TopologicalSpace.denseSeq ℝ≥0 k) :=
    measurable_pi_apply _
  show MeasurableSet ((fun c : Trajectory ℕ => c (TopologicalSpace.denseSeq ℝ≥0 k)) ⁻¹'
    {o : Option ℕ | o ≠ none})
  exact hm (measurableSet_option _)

theorem iSup_denseSeq_lt {r : ℝ≥0} (hr : 0 < r) :
    (⨆ k : ℕ, if TopologicalSpace.denseSeq ℝ≥0 k < r then
      ((TopologicalSpace.denseSeq ℝ≥0 k : ℝ≥0) : ℝ≥0∞) else 0) = (r : ℝ≥0∞) := by
  apply le_antisymm
  · refine iSup_le fun k => ?_
    split_ifs with hk
    · exact ENNReal.coe_le_coe.2 hk.le
    · exact zero_le
  · refine le_of_forall_lt fun c hc => ?_
    have hcr : c ≠ ⊤ := ne_top_of_lt hc
    obtain ⟨c', rfl⟩ := WithTop.ne_top_iff_exists.1 hcr
    have hc' : c' < r := ENNReal.coe_lt_coe.1 hc
    obtain ⟨q, ⟨k, rfl⟩, hq1, hq2⟩ :=
      Dense.exists_between (TopologicalSpace.denseRange_denseSeq ℝ≥0) hc'
    refine lt_iSup_iff.2 ⟨k, ?_⟩
    rw [if_pos hq2]
    exact ENNReal.coe_lt_coe.2 hq1

/-! ### 3. Transport to the regularity subtype -/

theorem indepFun_of_val {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] {p : α → Prop} {q : β → Prop} {μ : Measure Ω} {f : Ω → {a // p a}}
    {g : Ω → {b // q b}} (h : IndepFun (fun ω => (f ω).1) (fun ω => (g ω).1) μ) :
    IndepFun f g μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  obtain ⟨B, hB, rfl⟩ := hs
  obtain ⟨C, hC, rfl⟩ := ht
  exact h B C hB hC

theorem indepFun_map_of_comp {Ω γ β β' : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    [MeasurableSpace β] [MeasurableSpace β'] {P : Measure Ω} [IsFiniteMeasure P] {g : Ω → γ}
    (hg : Measurable g) {A : γ → β} {B : γ → β'} (hA : Measurable A) (hB : Measurable B)
    (h : IndepFun (A ∘ g) (B ∘ g) P) : IndepFun A B (P.map g) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (hA.comp hg).aemeasurable
    (hB.comp hg).aemeasurable] at h
  rw [indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable,
    Measure.map_map (hA.prodMk hB) hg, Measure.map_map hA hg, Measure.map_map hB hg]
  exact h

/-- **The lifted slot law, and the first-cycle law, as images of the sample law** (for clause (b):
cylinder probabilities of `firstCycleLaw` are sample-space probabilities of the actual walk). -/
theorem exists_sample_lift (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    {e : Env} (he : e ∈ G) {n : ℕ} (hn : (e.val.1 n).isSome) :
    ∃ g : (areaFamily e).Ω → RegLL, Measurable g ∧
      (∀ᵐ ω ∂(areaFamily e).P ⟨n, hn⟩, (g ω).1 = labelTraj ((areaFamily e).trajectory ω)) ∧
      regSlotLaw G hwalk n e = ((areaFamily e).P ⟨n, hn⟩).map g ∧
      firstCycleLaw G hwalk n e = ((areaFamily e).P ⟨n, hn⟩).map (firstCycle n ∘ g) := by
  obtain ⟨g, hgm, hg⟩ := exists_lift_fun ((areaFamily e).P ⟨n, hn⟩)
    (f := fun ω => labelTraj ((areaFamily e).trajectory ω))
    (measurable_labelTraj.comp (areaFamily e).measurable_trajectory)
    (ae_isRegLL_label e (hwalk e he) ⟨n, hn⟩) isRegLL_cem
  have hgval : (Subtype.val ∘ g) =ᵐ[(areaFamily e).P ⟨n, hn⟩]
      labelTraj ∘ (areaFamily e).trajectory := hg
  have hμ : regSlotLaw G hwalk n e = ((areaFamily e).P ⟨n, hn⟩).map g := by
    refine regSlotLaw_eq_of_map_val_eq G hwalk n e ?_
    rw [Measure.map_map measurable_subtype_coe hgm, Measure.map_congr hgval,
      slotLaw_of_mem he hn, ProcessFamily.law,
      Measure.map_map measurable_labelTraj (areaFamily e).measurable_trajectory]
  refine ⟨g, hgm, hg, hμ, ?_⟩
  rw [firstCycleLaw, hμ, Measure.map_map (measurable_firstCycle n) hgm]

/-- **Forward regeneration of the lifted slot law of the actual walk.** -/
theorem forwardRegeneration_regSlotLaw (G : Set Env)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) {e : Env} (he : e ∈ G) {n : ℕ}
    (hn : (e.val.1 n).isSome) : ForwardRegeneration n (regSlotLaw G hwalk n e) := by
  classical
  haveI := nontrivial_vertex e
  have hw := isReflectedWalk_areaFamily e (hwalk e he)
  have hconn := decode_connected e
  set z : Vertex e.val := ⟨n, hn⟩ with hz
  set PF := areaFamily e with hPF
  set τ := firstReturnTime PF.X z with hτ
  obtain ⟨g, hgm, hg⟩ := exists_lift_fun (PF.P z) (f := fun ω => labelTraj (PF.trajectory ω))
    (measurable_labelTraj.comp PF.measurable_trajectory) (ae_isRegLL_label e (hwalk e he) z)
    isRegLL_cem
  have hgval : (Subtype.val ∘ g) =ᵐ[PF.P z] labelTraj ∘ PF.trajectory := hg
  have hμ : regSlotLaw G hwalk n e = (PF.P z).map g := by
    refine regSlotLaw_eq_of_map_val_eq G hwalk n e ?_
    rw [Measure.map_map measurable_subtype_coe hgm, Measure.map_congr hgval,
      slotLaw_of_mem he hn, ProcessFamily.law,
      Measure.map_map measurable_labelTraj PF.measurable_trajectory]
  -- the good event on the sample space
  have hstart : ∀ᵐ ω ∂PF.P z, PF.X 0 ω = some z := (hw z).1
  have hret : ∀ᵐ ω ∂PF.P z, ω ∈ stopEvent PF.X τ z := ae_mem_stopEvent_firstReturnTime hw hconn z
  have hdef : ∀ᵐ ω ∂PF.P z, ∀ k : ℕ, PF.X (TopologicalSpace.denseSeq ℝ≥0 k) ω ≠ none := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [(hw z).2.1 (TopologicalSpace.denseSeq ℝ≥0 k)] with ω hω
    obtain ⟨u, hu⟩ := hω.1
    rw [hu]
    exact Option.some_ne_none u
  -- pathwise consequences
  have hgood : ∀ᵐ ω ∂PF.P z, Good n (g ω) ∧ ∃ r : ℝ≥0, τ ω = r ∧ retLen (g ω).1 = r := by
    filter_upwards [hg, hstart, hret] with ω h1 h2 h3
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 h3.1
    have h0 : PF.trajectory ω 0 = some z := h2
    have hfr : fwdReturn (g ω).1 = τ ω := by
      rw [h1, fwdReturn_labelTraj h0]
      rfl
    refine ⟨⟨?_, ?_⟩, r, hr.symm, ?_⟩
    · rw [h1, labelTraj_apply, h0]
      rfl
    · rw [hfr]
      exact h3.1
    · rw [retLen, hfr, ← hr]
      rfl
  refine ⟨?_, ?_, ?_⟩
  · -- R1
    rw [hμ]
    refine (ae_map_iff hgm.aemeasurable (measurableSet_good n)).2 ?_
    filter_upwards [hgood] with ω hω
    exact hω.1
  · -- R2
    rw [hμ]
    apply subtype_measure_eq_of_map_val_eq
    have hfm : AEMeasurable (futureAt PF.X τ) (PF.P z) :=
      aemeasurable_futureAt' PF.measurable_X (hw z).2.2.1 (hw z).2.2.2.1
        (aemeasurable_targetReturnTime hw hconn (Finset.singleton_nonempty z)
          (Finset.mem_singleton_self z) 1)
    have hshift : (fun ω => (nx (g ω)).1) =ᵐ[PF.P z] labelTraj ∘ futureAt PF.X τ := by
      filter_upwards [hg, hgood] with ω h1 h2
      obtain ⟨r, hr, hrl⟩ := h2.2
      funext s
      show (g ω).1 (s + retLen (g ω).1) = labelTraj (futureAt PF.X τ ω) s
      rw [hrl, h1, labelTraj_apply, labelTraj_apply]
      show (PF.X (s + r) ω).map Subtype.val = (PF.X (s + (τ ω).untopA) ω).map Subtype.val
      rw [hr]
      rfl
    rw [Measure.map_map measurable_subtype_coe measurable_nx, Measure.map_map
      (measurable_subtype_coe.comp measurable_nx) hgm, Measure.map_map measurable_subtype_coe hgm,
      Measure.map_congr hgval]
    have e1 : (Subtype.val ∘ nx) ∘ g = fun ω => (nx (g ω)).1 := rfl
    rw [e1, Measure.map_congr hshift, ← AEMeasurable.map_map_of_aemeasurable
      measurable_labelTraj.aemeasurable hfm, map_futureAt_firstReturnTime hw hconn z,
      ProcessFamily.law, Measure.map_map measurable_labelTraj PF.measurable_trajectory]
  · -- R3
    rw [hμ]
    refine indepFun_map_of_comp hgm (measurable_firstCycle n) measurable_nx ?_
    refine indepFun_of_val ?_
    have hK : Measurable fun c : Trajectory (Vertex e.val) => (labelTraj c, cycLen (labelTraj c)) :=
      measurable_labelTraj.prodMk (measurable_cycLen.comp measurable_labelTraj)
    have hind := (indepFun_killedPathAt_futureAt hw hconn z).comp hK measurable_labelTraj
    refine hind.congr ?_ ?_
    · filter_upwards [hg, hgood, hdef] with ω h1 h2 h3
      obtain ⟨r, hr, hrl⟩ := h2.2
      have hcyc := firstCycle_of_good h2.1.1 h2.1.2
      have hkill : labelTraj (killedPathAt PF.X τ ω) = glue (g ω).1 (retLen (g ω).1) cem := by
        funext s
        rw [hrl, h1, labelTraj_apply]
        show (if (s : WithTop ℝ≥0) < τ ω then PF.X s ω else none).map Subtype.val =
          glue (labelTraj (PF.trajectory ω)) r cem s
        rw [hr]
        by_cases hs : s < r
        · rw [if_pos (WithTop.coe_lt_coe.2 hs), glue_of_lt hs]
          rfl
        · rw [if_neg (fun h => hs (WithTop.coe_lt_coe.1 h)), glue_of_le (not_lt.1 hs)]
          rfl
      have hr0 : 0 < r := by
        have := Cyc.len_pos (firstCycle n (g ω))
        rw [hcyc] at this
        rwa [hrl] at this
      have hlen : cycLen (labelTraj (killedPathAt PF.X τ ω)) = r := by
        rw [hkill, hrl]
        unfold cycLen
        have hterm : ∀ k : ℕ, (if glue (g ω).1 r cem (TopologicalSpace.denseSeq ℝ≥0 k) ≠ none then
            ((TopologicalSpace.denseSeq ℝ≥0 k : ℝ≥0) : ℝ≥0∞) else 0) =
            if TopologicalSpace.denseSeq ℝ≥0 k < r then
              ((TopologicalSpace.denseSeq ℝ≥0 k : ℝ≥0) : ℝ≥0∞) else 0 := by
          intro k
          by_cases hk : TopologicalSpace.denseSeq ℝ≥0 k < r
          · rw [if_pos hk, if_pos]
            rw [glue_of_lt hk, h1, labelTraj_apply]
            intro hnone
            exact h3 k (Option.map_eq_none_iff.1 hnone)
          · rw [if_neg hk, if_neg]
            rw [glue_of_le (not_lt.1 hk)]
            exact fun h => h rfl
        simp only [hterm]
        rw [iSup_denseSeq_lt hr0, ENNReal.toNNReal_coe]
      show (labelTraj (killedPathAt PF.X τ ω), cycLen (labelTraj (killedPathAt PF.X τ ω))) =
        (firstCycle n (g ω)).1
      rw [hcyc, hlen, hkill, hrl]
    · filter_upwards [hg, hgood] with ω h1 h2
      obtain ⟨r, hr, hrl⟩ := h2.2
      funext s
      show labelTraj (futureAt PF.X τ ω) s = (g ω).1 (s + retLen (g ω).1)
      rw [hrl, h1, labelTraj_apply, labelTraj_apply]
      show (PF.X (s + (τ ω).untopA) ω).map Subtype.val = (PF.X (s + r) ω).map Subtype.val
      rw [hr]
      rfl

/-! ### 4. Clause (c) and `hcyc` at the actual kernel from (R4) + (R5) -/

theorem forwardCycleInputs_of (G : Set Env) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    {e : Env} (he : e ∈ G) (hslot : (e.val.1 (rootLabel e)).isSome)
    (h4 : HoldExcIndep (firstCycleLaw G hwalk (rootLabel e) e))
    (h5 : StraddleAbsCont (firstCycleLaw G hwalk (rootLabel e) e)) :
    ForwardCycleInputs G hwalk e :=
  ⟨forwardRegeneration_regSlotLaw G hwalk he hslot, h4, h5⟩

/-- **Clause (c) at the actual kernel from (R4) and (R5).** -/
theorem rootedCycleDecomposition_rootedRegKernel_of (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) {e : Env} (he : e ∈ G)
    (hslot : (e.val.1 (rootLabel e)).isSome)
    (h4 : HoldExcIndep (firstCycleLaw G hwalk (rootLabel e) e))
    (h5 : StraddleAbsCont (firstCycleLaw G hwalk (rootLabel e) e)) :
    RootedCycleDecomposition (rootedRegKernel G hG hwalk
      (RegenerationKernelMeasurability.measurable_slotTransition G hG hwalk) e)
      (firstCycleLaw G hwalk (rootLabel e) e) :=
  rootedCycleDecomposition_rootedRegKernel G hG hwalk _ (forwardCycleInputs_of G hwalk he hslot h4 h5)

end ReflectedGMS.CycleDecomposition
