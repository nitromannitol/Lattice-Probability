/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.FlowCodingLine at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedCycleSplice
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationFlow

/-!
# The two-sided line coding: gluing a forward path and a left-limit-reversed backward path

Requirement (B2) of the carrier bridge (`outputs/regeneration-flow-handoff.2026-09-18.md` §4): the
label path of the flow carrier is `Y s = x₊(s)` for `s ≥ 0` and `Y (-s) = x₋(s-)` (the LEFT limit
of the backward half) for `s > 0`; this makes the line path càdlàg.  The same gluing is needed for
the position path.  This module proves it once, for any regular Hausdorff state space:

* `tendsto_leftLim_nhdsLT` / `tendsto_leftLim_nhdsGT`: the left-limit function of a càdlàg path
  on `ℝ` is left-continuous and has right limits equal to the path;
* `isCadlag_leftLim_neg`: hence `s ↦ leftLim G (-s)` is càdlàg;
* `glue F G s = F s` (`s ≥ 0`), `leftLim G (-s)` (`s < 0`), and `isCadlag_glue`;
* `isCadlag_comp_toNNReal`: a càdlàg path on `ℝ≥0`, read through `Real.toNNReal`, is càdlàg on `ℝ`;
* `isCadlag_label`: the `ℕ∞`-label path (`⊤` = cemetery) of a right-regular label trajectory with
  left limits (`TwoSidedCycleSplice.IsRegLL`: properties (ii)+(R) and
  `Forms/VertexIndicatorLeftLimits`) is càdlàg in the one-point compactification;
* `leftLim_eq_of_eventuallyEq_const`: at a point where the path is locally constant, the left
  limit is that constant (the reading at fixed rational times).

Nothing here is probabilistic.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.FlowCodingLine

open ReflectedGMS.TwoSidedCycleSplice ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedWalk ReflectedWalk.Theorem16

/-! ### 1. The left-limit function of a càdlàg path on `ℝ` -/

section Generic

variable {S : Type*} [TopologicalSpace S]

/-- **The left-limit function is left-continuous.** -/
theorem tendsto_leftLim_nhdsLT [RegularSpace S] [T2Space S] {G : ℝ → S} (hG : IsCadlag G)
    (r : ℝ) : Tendsto (Function.leftLim G) (𝓝[<] r) (𝓝 (Function.leftLim G r)) := by
  have hL := hG.tendsto_nhdsLT_leftLim r
  rw [(closed_nhds_basis (Function.leftLim G r)).tendsto_right_iff]
  rintro V ⟨hVn, hVc⟩
  have hev : ∀ᶠ x in 𝓝[<] r, G x ∈ V := hL hVn
  obtain ⟨a, har, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' (sub_one_lt r)).1 hev
  filter_upwards [Ioo_mem_nhdsLT har] with r' hr'
  have h1 := hG.tendsto_nhdsLT_leftLim r'
  have h2 : ∀ᶠ x in 𝓝[<] r', G x ∈ V := by
    filter_upwards [Ioo_mem_nhdsLT hr'.1] with x hx
    exact hsub ⟨hx.1, hx.2.trans hr'.2⟩
  exact hVc.mem_of_tendsto h1 h2

/-- **The left-limit function has right limits, equal to the path** (right-continuity). -/
theorem tendsto_leftLim_nhdsGT [RegularSpace S] [T2Space S] {G : ℝ → S} (hG : IsCadlag G)
    (r : ℝ) : Tendsto (Function.leftLim G) (𝓝[>] r) (𝓝 (G r)) := by
  rw [(closed_nhds_basis (G r)).tendsto_right_iff]
  rintro V ⟨hVn, hVc⟩
  have hev : ∀ᶠ x in 𝓝[>] r, G x ∈ V := hG.isRightContinuous r hVn
  obtain ⟨b, hrb, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (lt_add_one r)).1 hev
  filter_upwards [Ioo_mem_nhdsGT hrb] with r' hr'
  have h1 := hG.tendsto_nhdsLT_leftLim r'
  have h2 : ∀ᶠ x in 𝓝[<] r', G x ∈ V := by
    filter_upwards [Ioo_mem_nhdsLT hr'.1] with x hx
    exact hsub ⟨hx.1, hx.2.trans hr'.2⟩
  exact hVc.mem_of_tendsto h1 h2

theorem tendsto_neg_nhdsGT (s : ℝ) : Tendsto Neg.neg (𝓝[>] s) (𝓝[<] (-s)) := by
  simpa using (tendsto_neg_nhdsGT_neg (a := -s))

theorem tendsto_neg_nhdsLT (s : ℝ) : Tendsto Neg.neg (𝓝[<] s) (𝓝[>] (-s)) := by
  simpa using (tendsto_neg_nhdsLT_neg (a := -s))

/-- **The reflected left-limit path `s ↦ G(-s -)` is càdlàg.** -/
theorem isCadlag_leftLim_neg [RegularSpace S] [T2Space S] {G : ℝ → S} (hG : IsCadlag G) :
    IsCadlag fun s : ℝ => Function.leftLim G (-s) where
  isRightContinuous s := (tendsto_leftLim_nhdsLT hG (-s)).comp (tendsto_neg_nhdsGT s)
  tendsto_nhdsLT s := ⟨G (-s), (tendsto_leftLim_nhdsGT hG (-s)).comp (tendsto_neg_nhdsLT s)⟩

/-- **The two-sided glue**: the forward path on `[0,∞)`, the left-limit reversal of the backward
path on `(-∞,0)`. -/
noncomputable def glue (F G : ℝ → S) (s : ℝ) : S :=
  if 0 ≤ s then F s else Function.leftLim G (-s)

theorem glue_of_nonneg (F G : ℝ → S) {s : ℝ} (hs : 0 ≤ s) : glue F G s = F s := if_pos hs

theorem glue_of_neg (F G : ℝ → S) {s : ℝ} (hs : s < 0) :
    glue F G s = Function.leftLim G (-s) := if_neg (not_le.2 hs)

/-- **The glue of two càdlàg paths is càdlàg.** -/
theorem isCadlag_glue [RegularSpace S] [T2Space S] {F G : ℝ → S} (hF : IsCadlag F)
    (hG : IsCadlag G) : IsCadlag (glue F G) where
  isRightContinuous s := by
    rcases le_or_gt 0 s with hs | hs
    · have hev : glue F G =ᶠ[𝓝[>] s] F := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact glue_of_nonneg F G (hs.trans (le_of_lt hx))
      exact (hF.isRightContinuous s).congr_of_eventuallyEq hev (glue_of_nonneg F G hs)
    · have hev : glue F G =ᶠ[𝓝[>] s] fun x => Function.leftLim G (-x) := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hs)] with x hx
        exact glue_of_neg F G hx
      exact ((isCadlag_leftLim_neg hG).isRightContinuous s).congr_of_eventuallyEq hev
        (glue_of_neg F G hs)
  tendsto_nhdsLT s := by
    rcases lt_or_ge 0 s with hs | hs
    · obtain ⟨l, hl⟩ := hF.tendsto_nhdsLT s
      refine ⟨l, hl.congr' ?_⟩
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hs)] with x hx
      exact (glue_of_nonneg F G (le_of_lt hx)).symm
    · obtain ⟨l, hl⟩ := (isCadlag_leftLim_neg hG).tendsto_nhdsLT s
      refine ⟨l, hl.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (glue_of_neg F G (lt_of_lt_of_le hx hs)).symm

/-- **The left limit at a point of local constancy** is the constant. -/
theorem leftLim_eq_of_eventuallyEq_const [T2Space S] {G : ℝ → S} {r : ℝ} {c : S}
    (h : ∀ᶠ x in 𝓝[<] r, G x = c) : Function.leftLim G r = c :=
  leftLim_eq_of_tendsto (tendsto_const_nhds.congr' (h.mono fun _ hx => hx.symm))

/-- **A càdlàg path on `ℝ≥0` read through `Real.toNNReal` is càdlàg on `ℝ`.** -/
theorem isCadlag_comp_toNNReal {f : ℝ≥0 → S} (hf : IsCadlag f) :
    IsCadlag fun s : ℝ => f s.toNNReal where
  isRightContinuous s := by
    rcases le_or_gt 0 s with hs | hs
    · have hmap : Tendsto Real.toNNReal (𝓝[>] s) (𝓝[>] s.toNNReal) := by
        refine tendsto_nhdsWithin_iff.2 ⟨continuous_real_toNNReal.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact Real.toNNReal_lt_toNNReal_iff'.2 ⟨hx, lt_of_le_of_lt hs hx⟩
      exact (hf.isRightContinuous s.toNNReal).tendsto.comp hmap
    · have hev : (fun x : ℝ => f x.toNNReal) =ᶠ[𝓝[>] s] fun _ => f s.toNNReal := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hs)] with x hx
        rw [Real.toNNReal_of_nonpos (le_of_lt hx), Real.toNNReal_of_nonpos (le_of_lt hs)]
      exact continuousWithinAt_const.congr_of_eventuallyEq hev rfl
  tendsto_nhdsLT s := by
    rcases lt_or_ge 0 s with hs | hs
    · obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT s.toNNReal
      refine ⟨l, hl.comp ?_⟩
      refine tendsto_nhdsWithin_iff.2 ⟨continuous_real_toNNReal.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.toNNReal_lt_toNNReal_iff'.2 ⟨hx, hs⟩
    · refine ⟨f 0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Real.toNNReal_of_nonpos (le_of_lt (lt_of_lt_of_le hx hs))]

end Generic

/-! ### 2. The label path in the one-point compactification `ℕ∞` -/

/-- A label state in `ℕ∞`: the cemetery `none` is `⊤`. -/
def toENatLabel (o : Option ℕ) : ℕ∞ := o.elim ⊤ fun n => (n : ℕ∞)

@[simp] theorem toENatLabel_none : toENatLabel none = ⊤ := rfl

@[simp] theorem toENatLabel_some (n : ℕ) : toENatLabel (some n) = (n : ℕ∞) := rfl

theorem toENatLabel_eq_natCast_iff {o : Option ℕ} {n : ℕ} :
    toENatLabel o = (n : ℕ∞) ↔ o = some n := by
  cases o with
  | none =>
    simp only [toENatLabel_none, reduceCtorEq, iff_false]
    exact (ENat.natCast_ne_top n).symm
  | some m =>
    simp only [toENatLabel_some, Nat.cast_inj, Option.some.injEq]

theorem toOptLabel_toENatLabel (o : Option ℕ) : toOptLabel (toENatLabel o) = o := by
  cases o with
  | none => exact ENat.recTopCoe_top _ _
  | some n => exact ENat.recTopCoe_natCast _ _ n

/-- A path into `ℕ∞` that eventually avoids every finite label tends to the cemetery. -/
theorem tendsto_top_of_eventually_ne {α : Type*} {l : Filter α} {L : α → ℕ∞}
    (h : ∀ n : ℕ, ∀ᶠ a in l, L a ≠ n) : Tendsto L l (𝓝 ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro N
  have hall : ∀ᶠ a in l, ∀ k ∈ Finset.range (N + 1), L a ≠ k :=
    (Filter.eventually_all_finset _).2 fun k _ => h k
  filter_upwards [hall] with a ha
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨k, hk, hkN⟩ := ENat.le_natCast_iff.1 hlt
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_of_le hkN)) hk

/-- **The `ℕ∞`-label path of a right-regular label trajectory with left limits is càdlàg.** -/
theorem isCadlag_label {x : Trajectory ℕ} (hx : IsRegLL x) :
    IsCadlag fun t : ℝ≥0 => toENatLabel (x t) where
  isRightContinuous t := by
    show Tendsto (fun t : ℝ≥0 => toENatLabel (x t)) (𝓝[>] t) (𝓝 (toENatLabel (x t)))
    cases hxt : x t with
    | some w =>
      obtain ⟨b, htb, hb⟩ := rr_some hx.regular hxt
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT htb] with s hs
      rw [hb s hs.1.le hs.2]
    | none =>
      refine tendsto_top_of_eventually_ne fun n => ?_
      obtain ⟨b, htb, hb⟩ := rr_none hx.regular hxt n
      filter_upwards [Ioo_mem_nhdsGT htb] with s hs hsn
      exact hb s hs.1 hs.2 (toENatLabel_eq_natCast_iff.1 hsn)
  tendsto_nhdsLT t := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | ht
    · subst h0
      have hI : Set.Iio (0 : ℝ≥0) = ∅ := Set.eq_empty_of_forall_notMem fun x hx =>
        not_lt_of_ge (zero_le : (0 : ℝ≥0) ≤ x) hx
      refine ⟨⊤, ?_⟩
      rw [hI, nhdsWithin_empty]
      exact tendsto_bot
    · by_cases hex : ∃ y : ℕ, ∃ a < t, ∀ s ∈ Ioo a t, x s = some y
      · obtain ⟨y, a, hat, ha⟩ := hex
        refine ⟨(y : ℕ∞), tendsto_const_nhds.congr' ?_⟩
        filter_upwards [Ioo_mem_nhdsLT hat] with s hs
        rw [ha s hs]
        rfl
      · refine ⟨⊤, tendsto_top_of_eventually_ne fun n => ?_⟩
        obtain ⟨a, hat, hor⟩ := hx.leftLimits n t ht
        rcases hor with h1 | h1
        · exact absurd ⟨n, a, hat, h1⟩ hex
        · filter_upwards [Ioo_mem_nhdsLT hat] with s hs hsn
          exact h1 s hs (toENatLabel_eq_natCast_iff.1 hsn)

end ReflectedGMS.FlowCodingLine
