/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.HoldingIntervalFiniteness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CadlagRegenerationActual
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedTemporalTransport
import LatticeProb.Bonanno.ReflectedGMS.Temporal.LabelHoldingIntervals

/-!
# Boundedness of the holding intervals of the bridge kernel

The third clause of `HoldingDataFlowSpace.HoldingLawInputs` asks that every holding interval of the
label path be bounded: `∀ q : ℚ, Y q ≠ ⊤ → holdLen Y q ≠ ∞`.  By `holdLen_of_ne_top` this is the
conjunction of "the walk has already left some earlier vertex" (`entryLen < ∞`) and "the walk will
leave the current vertex" (`exitLen < ∞`), so it is exactly the statement that the label path is
**not eventually constant in either time direction** — a property of the reflected walk, not of the
geometry.

The proof is in three layers.

* Pathwise (`exists_gt_leftLim_ne`, `holdLen_ne_top_of_exists`): in `ℕ∞` a finite label `n` has
  `{n}` both open and closed, so a càdlàg path that differs from `n` at `t` also has a *left limit*
  differing from `n` at some later time.  This is what carries the forward statement about the
  second sample onto the backward half of the glue, which is read through `Function.leftLim`.
* Walk level (`ae_forall_leaves`): started at any vertex `r`, the walk is a.s. off **every** vertex
  `v` at arbitrarily large times.  For `v = r` this is `CadlagRegeneration.ae_leaves` (property (iv)
  at the integer times plus a.s. finiteness of the exponential exit time); for `v ≠ r` it is
  property (v), recurrence at `r`, with no extra work.  No new probabilistic input is used.
* Kernel level (`ae_holdLen_ne_top_flowKernel`): the two halves of `build` are independent copies of
  the walk from the root vertex, so the glued label path is cofinally different from every finite
  label in both directions, and `holdLen` is finite at every rational vertex time.

Nothing here certifies `p:lem:regeninvariant`, `hsys` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.HoldingIntervalFiniteness

open Code EnvironmentFields EnvironmentLaws RootDensities
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.FlowCodingLine ReflectedGMS.FlowCodingKernel
open ReflectedGMS.CellRootedTemporalTransport
open ReflectedGMS.LabelHoldingIntervals

/-! ## 1. Two pathwise facts -/

/-- **A càdlàg `ℕ∞` path that avoids a finite label at `t` avoids it as a LEFT LIMIT later.**
For `n ≠ ⊤` the singleton `{n}` is both open (`ENat.isOpen_singleton`) and closed, so
right-continuity pushes `g ≠ n` onto an interval to the right of `t` and the closedness of `{n}ᶜ`
keeps the left limit at an interior point of that interval away from `n`. -/
theorem exists_gt_leftLim_ne {g : ℝ → ℕ∞} (hg : IsCadlag g) {n : ℕ∞} (hn : n ≠ ⊤) {t : ℝ}
    (ht : g t ≠ n) : ∃ s : ℝ, t < s ∧ Function.leftLim g s ≠ n := by
  have h1 : ∀ᶠ u in 𝓝[>] t, g u ≠ n :=
    (hg.isRightContinuous t).tendsto.eventually ((isOpen_ne (x := n)).eventually_mem ht)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
  have htu : t < u := hu
  refine ⟨(t + u) / 2, by linarith, ?_⟩
  have hclosed : IsClosed ({n}ᶜ : Set ℕ∞) := (ENat.isOpen_singleton hn).isClosed_compl
  have hlim := hg.tendsto_nhdsLT_leftLim ((t + u) / 2)
  have hev : ∀ᶠ x in 𝓝[<] ((t + u) / 2), g x ∈ ({n}ᶜ : Set ℕ∞) := by
    filter_upwards [Ioo_mem_nhdsLT (show t < (t + u) / 2 by linarith)] with x hx
    exact hsub ⟨hx.1, by linarith [hx.2]⟩
  have := hclosed.mem_of_tendsto hlim hev
  simpa using this

/-- **The holding interval through `s` is bounded** as soon as the path takes a different value at
some later and at some earlier time. -/
theorem holdLen_ne_top_of_exists {Y : CadlagPath ℕ∞} {s : ℝ}
    (hfwd : ∃ t, s < t ∧ Y.toFun t ≠ Y.toFun s)
    (hbwd : ∃ t, t < s ∧ Y.toFun t ≠ Y.toFun s) : holdLen Y s ≠ ∞ := by
  obtain ⟨t₁, ht₁, hy₁⟩ := hfwd
  obtain ⟨t₂, ht₂, hy₂⟩ := hbwd
  refine holdLen_ne_top_of Y ?_ ?_
  · exact ((entryLen_le Y ht₂ hy₂).trans_lt ENNReal.ofReal_lt_top).ne
  · exact ((exitLen_le Y ht₁ hy₁).trans_lt ENNReal.ofReal_lt_top).ne

/-! ## 2. The walk leaves every vertex at arbitrarily large times -/

section Walk

open ReflectedWalk ReflectedWalk.Theorem16 ReflectedGMS.CadlagRegeneration

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Nontrivial V]
variable {Gr : ConductanceGraph V} {w : V → ℝ} {hmin : Gr.EnergyMinimizer} {PF : ProcessFamily V}

/-- **Started anywhere, the walk is off every vertex at arbitrarily large times.**  At the starting
vertex this is `CadlagRegeneration.ae_leaves`; at any other vertex it is property (v), recurrence at
the start, which already forces the walk away from `v` at arbitrarily large times. -/
theorem ae_forall_leaves (h : IsReflectedWalk Gr w hmin PF) (r : V) :
    ∀ᵐ ω ∂PF.P r, ∀ (v : V) (T : ℝ≥0), ∃ t : ℝ≥0, T ≤ t ∧ PF.X t ω ≠ some v := by
  filter_upwards [ae_leaves h r, (h r).2.2.2.2.2.2.1] with ω hleave hrec v T
  by_cases hv : v = r
  · subst hv
    exact hleave T
  · obtain ⟨t, hT, ht⟩ := hrec T
    refine ⟨t, hT, ?_⟩
    rw [ht]
    simp only [ne_eq, Option.some.injEq]
    exact fun hh => hv hh.symm

end Walk

/-! ## 3. The label path of one half -/

section Half

variable {e : Env}

theorem labelPath_eq (ω : (areaFamily e).Ω) (t : ℝ≥0) :
    labelPath e ω t = toENatLabel (((areaFamily e).X t ω).map Subtype.val) := rfl

/-- The label path takes only the cemetery value and the labels of actual vertices. -/
theorem labelPath_eq_top_or_vertex (ω : (areaFamily e).Ω) (t : ℝ≥0) :
    labelPath e ω t = ⊤ ∨ ∃ v : Vertex e.val, labelPath e ω t = (v.val : ℕ∞) := by
  cases hX : (areaFamily e).X t ω with
  | none => exact Or.inl (by rw [labelPath_eq, hX]; rfl)
  | some a => exact Or.inr ⟨a, by rw [labelPath_eq, hX]; rfl⟩

theorem labelPath_ne_of_X_ne {ω : (areaFamily e).Ω} {t : ℝ≥0} {v : Vertex e.val}
    (h : (areaFamily e).X t ω ≠ some v) : labelPath e ω t ≠ (v.val : ℕ∞) := by
  cases hX : (areaFamily e).X t ω with
  | none =>
      have hv : labelPath e ω t = ⊤ := by rw [labelPath_eq, hX]; rfl
      rw [hv]
      exact fun hc => (ENat.natCast_ne_top v.val) hc.symm
  | some a =>
      have hne : a ≠ v := fun hav => h (by rw [hX, hav])
      have hv : labelPath e ω t = (a.val : ℕ∞) := by rw [labelPath_eq, hX]; rfl
      rw [hv]
      intro hc
      exact hne (Subtype.ext (Nat.cast_inj.1 hc))

/-- **Cofinal avoidance of every finite label** by the label path of a half that leaves every
vertex at arbitrarily large times. -/
theorem exists_gt_labelPath_ne {ω : (areaFamily e).Ω}
    (hleave : ∀ (v : Vertex e.val) (S : ℝ≥0), ∃ t : ℝ≥0, S ≤ t ∧ (areaFamily e).X t ω ≠ some v)
    {n : ℕ∞} (hn : n ≠ ⊤) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ labelPath e ω t.toNNReal ≠ n := by
  have hTle : T ≤ max T 0 := le_max_left _ _
  have hpos : (0 : ℝ) ≤ max T 0 + 1 := by
    have : (0 : ℝ) ≤ max T 0 := le_max_right _ _
    linarith
  by_cases hex : ∃ v : Vertex e.val, (v.val : ℕ∞) = n
  · obtain ⟨v, rfl⟩ := hex
    obtain ⟨t, hSt, ht⟩ := hleave v (Real.toNNReal (max T 0 + 1))
    have hle : (max T 0 + 1 : ℝ) ≤ (t : ℝ) := by
      have h1 : ((Real.toNNReal (max T 0 + 1) : ℝ≥0) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hSt
      rwa [Real.coe_toNNReal _ hpos] at h1
    refine ⟨(t : ℝ), by linarith, ?_⟩
    rw [Real.toNNReal_coe]
    exact labelPath_ne_of_X_ne ht
  · push_neg at hex
    refine ⟨max T 0 + 1, by linarith, ?_⟩
    intro hc
    rcases labelPath_eq_top_or_vertex ω (max T 0 + 1 : ℝ).toNNReal with h1 | ⟨v, h1⟩
    · rw [h1] at hc
      exact hn hc.symm
    · rw [h1] at hc
      exact hex v hc

end Half

/-! ## 4. The glued label path of a built configuration -/

section Build

variable {z : CellField} {e : Env} {r : Vertex e.val}
variable {ω : (areaFamily e).Ω × (areaFamily e).Ω}

/-- Cofinal avoidance of a finite label at LARGE times, from the forward half. -/
theorem exists_gt_build_ne (hω : ω ∈ goodSet z e r)
    (hleave : ∀ (v : Vertex e.val) (S : ℝ≥0), ∃ t : ℝ≥0, S ≤ t ∧ (areaFamily e).X t ω.1 ≠ some v)
    {n : ℕ∞} (hn : n ≠ ⊤) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ (build z e r ω).1.toFun t ≠ n := by
  obtain ⟨t, hTt, ht⟩ := exists_gt_labelPath_ne hleave hn (max T 0)
  have hT : T < t := lt_of_le_of_lt (le_max_left T 0) hTt
  have h0 : (0 : ℝ) ≤ t := le_of_lt (lt_of_le_of_lt (le_max_right T 0) hTt)
  refine ⟨t, hT, ?_⟩
  rw [build_of_mem z e r hω]
  show glue (fun s : ℝ => labelPath e ω.1 s.toNNReal)
    (fun s : ℝ => labelPath e ω.2 s.toNNReal) t ≠ n
  rw [glue_of_nonneg _ _ h0]
  exact ht

/-- Cofinal avoidance of a finite label at LARGE NEGATIVE times, from the backward half.  The
backward half of the glue is read through a left limit, which is why `exists_gt_leftLim_ne` is
needed on top of the forward statement for the second sample. -/
theorem exists_lt_build_ne (hω : ω ∈ goodSet z e r)
    (hleave : ∀ (v : Vertex e.val) (S : ℝ≥0), ∃ t : ℝ≥0, S ≤ t ∧ (areaFamily e).X t ω.2 ≠ some v)
    {n : ℕ∞} (hn : n ≠ ⊤) (T : ℝ) :
    ∃ t : ℝ, t < T ∧ (build z e r ω).1.toFun t ≠ n := by
  have hg := halfGood_of_mem_goodSet z e r hω
  obtain ⟨s, hSs, hs⟩ := exists_gt_labelPath_ne hleave hn (max (-T) 0)
  have hs0 : (0 : ℝ) < s := lt_of_le_of_lt (le_max_right (-T) 0) hSs
  have hsT : -T < s := lt_of_le_of_lt (le_max_left (-T) 0) hSs
  have hcad : IsCadlag fun x : ℝ => labelPath e ω.2 x.toNNReal :=
    isCadlag_comp_toNNReal (isCadlag_labelPath hg.2)
  obtain ⟨s', hss', hs'⟩ := exists_gt_leftLim_ne hcad hn hs
  refine ⟨-s', by linarith, ?_⟩
  rw [build_of_mem z e r hω]
  show glue (fun x : ℝ => labelPath e ω.1 x.toNNReal)
    (fun x : ℝ => labelPath e ω.2 x.toNNReal) (-s') ≠ n
  rw [glue_of_neg _ _ (show -s' < 0 by linarith), neg_neg]
  exact hs'

end Build

/-- **The holding intervals of a built configuration are bounded at every rational vertex time**,
almost surely. -/
theorem ae_build_holdLen_ne_top {z : CellField} {e : Env}
    (hadm : EnvironmentAreaClockAdmissible e) (r : Vertex e.val)
    (hgood : ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)), ω ∈ goodSet z e r) :
    ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)),
      ∀ q : ℚ, (build z e r ω).1.toFun q ≠ ⊤ → holdLen (build z e r ω).1 q ≠ ∞ := by
  haveI := nontrivial_vertex e
  have hw := isReflectedWalk_areaFamily e hadm
  have hleave := ae_forall_leaves hw r
  filter_upwards [hgood, Measure.quasiMeasurePreserving_fst.ae hleave,
    Measure.quasiMeasurePreserving_snd.ae hleave] with ω hω h1 h2 q hq
  exact holdLen_ne_top_of_exists (exists_gt_build_ne hω h1 hq (q : ℝ))
    (exists_lt_build_ne hω h2 hq (q : ℝ))

/-! ## 5. The clause at the bridge kernel -/

/-- The bounded-holding-interval event on the flow carrier. -/
def HoldBounded : Set FlowSpace :=
  {ω : FlowSpace | ∀ q : ℚ, ω.2.1.toFun q ≠ ⊤ → holdLen ω.2.1 q ≠ ∞}

theorem measurableSet_holdBounded : MeasurableSet HoldBounded := by
  have hlab : ∀ q : ℚ, Measurable fun ω : FlowSpace => ω.2.1.toFun (q : ℝ) := fun q =>
    (CadlagPath.measurable_eval (q : ℝ)).comp (measurable_fst.comp measurable_snd)
  have hhold : ∀ q : ℚ, Measurable fun ω : FlowSpace => holdLen ω.2.1 (q : ℝ) := fun q =>
    measurable_holdLen.comp ((measurable_fst.comp measurable_snd).prodMk measurable_const)
  have hset : HoldBounded =
      ⋂ q : ℚ, ({ω : FlowSpace | ω.2.1.toFun (q : ℝ) = ⊤} ∪
        {ω : FlowSpace | holdLen ω.2.1 (q : ℝ) ≠ ∞}) := by
    ext ω
    simp only [HoldBounded, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
    constructor
    · intro h q
      by_cases hq : ω.2.1.toFun (q : ℝ) = ⊤
      · exact Or.inl hq
      · exact Or.inr (h q hq)
    · intro h q hq
      rcases h q with h' | h'
      · exact absurd h' hq
      · exact h'
  rw [hset]
  refine MeasurableSet.iInter fun q => MeasurableSet.union ?_ ?_
  · exact (hlab q) (measurableSet_singleton ⊤)
  · exact (hhold q) (measurableSet_singleton ∞).compl

section Kernel

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

/-- **The holding intervals of `ν ⊗ₘ κF` are bounded almost surely.** -/
theorem ae_holdLen_ne_top_flowKernel (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hGc : ν Gᶜ = 0) :
    ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext),
      ∀ q : ℚ, ω.2.1.toFun q ≠ ⊤ → holdLen ω.2.1 q ≠ ∞ := by
  refine Measure.ae_compProd_of_ae_ae measurableSet_holdBounded ?_
  have hGae : ∀ᵐ e ∂ν, e ∈ G := ae_iff.2 hGc
  filter_upwards [hGae, Spatial.ae_notMem_boundaryMask_of_massTransport ν hmt] with e he hm
  obtain ⟨root, hroot, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode e)
    (decode_geometry e) hm
  have hlive : Live G e := ⟨he, by rw [rootLabel_of_some hroot]; exact root.property⟩
  have hSe : MeasurableSet {y : FlowCoding | ((e, y) : FlowSpace) ∈ HoldBounded} :=
    measurable_prodMk_left measurableSet_holdBounded
  rw [flowKernel_apply, flowFibre_of_live hlive]
  refine (ae_map_iff (measurable_build z e _).aemeasurable hSe).2 ?_
  exact ae_build_holdLen_ne_top (hwalk e he) _ (ae_mem_goodSet hwalk hext hlive)

end Kernel

end ReflectedGMS.HoldingIntervalFiniteness
