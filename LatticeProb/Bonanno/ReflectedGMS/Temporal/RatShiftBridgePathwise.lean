/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.RatShiftBridgePathwise at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RatShiftBridgeCadlag
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedRegenerativeInvariance

/-!
# The rational-shift bridge, pathwise

`CellRootedRegenerativeInvariance.RatShiftBridge R μ` asks, for `μ`-a.e. `w` and every `n`, for a
configuration `x` and a time `t` with `ratRead x = R (ρⁿ w)` and
`ratRead (flowShift t x) = R (ρⁿ⁺¹ w)`.  This module reduces it to a MEASURABLE almost-sure event
on the regularity subtype:

* `GoodAt x t` — the label trajectory is locally constant at a vertex around `t`; its countable
  form `GoodAtQ` (read along `denseSeq`) is jointly measurable (`measurable_goodAtQ`) and equivalent
  on right-regular paths (`goodAt_of_goodAtQ`);
* `Lab p` — the forward half is `GoodAtQ` at every rational `q ≥ 0`, the backward half at every
  rational `q > 0` (measurable, `measurable_lab`);
* **`bridge_step`**: if the rational position readings of `p` satisfy the càdlàg criterion
  `RatShiftBridgeCadlag.RatCadlag`, and `Lab p`, `Lab (ρ p)` hold, then `x` = (the glued label
  path of `p`, the càdlàg extension of its position readings) and `t` = the first return time
  witness the bridge at `p`.  The four cases `q ≥ 0`, `-T < q < 0`, `q = -T`, `q < -T` are read
  off the local constancy of the halves of `ρ p` at `|q|` (the backward half of `ρ p` is the
  left-limit reversal of the first cycle, glued to the old backward half);
* **`ratShiftBridge_of_ae`**: `RatShiftBridge` from `∀ᵐ w, RatCadlag (R w).2 ∧ ∀ n, Lab (ρⁿ w)`;
  the càdlàg criterion propagates along the orbit because every `ratRead` of a configuration
  satisfies it (`ratCadlag_ratRead`).
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.RatShiftBridgePathwise

open Code EnvironmentFields
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.FlowCodingKernel ReflectedGMS.FlowCodingLine
open ReflectedGMS.TwoSidedCycleSplice ReflectedGMS.CellRootedRegenerativeInvariance
open ReflectedGMS.RatShiftBridgeCadlag ReflectedGMS.CadlagRegeneration

/-! ### 1. Local constancy at a vertex -/

/-- **Local constancy at a vertex** on a neighbourhood of `t` in `ℝ≥0` (one-sided at `0`). -/
def GoodAt (x : Trajectory ℕ) (t : ℝ≥0) : Prop :=
  ∃ v : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ≥0, dist s t < ε → x s = some v

/-- The countable form of `GoodAt`, read along the dense sequence of `ℝ≥0`. -/
def GoodAtQ (x : Trajectory ℕ) (t : ℝ≥0) : Prop :=
  ∃ v : ℕ, ∃ m : ℕ, ∀ k : ℕ, dist (TopologicalSpace.denseSeq ℝ≥0 k) t < 1 / ((m : ℝ) + 1) →
    x (TopologicalSpace.denseSeq ℝ≥0 k) = some v

theorem goodAtQ_of_goodAt {x : Trajectory ℕ} {t : ℝ≥0} (h : GoodAt x t) : GoodAtQ x t := by
  obtain ⟨v, ε, hε, hx⟩ := h
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  exact ⟨v, m, fun k hk => hx _ (lt_trans hk hm)⟩

theorem measurable_goodAtQ : Measurable fun p : Trajectory ℕ × ℝ≥0 => GoodAtQ p.1 p.2 := by
  refine Measurable.exists fun v => Measurable.exists fun m => Measurable.forall fun k => ?_
  refine Measurable.imp ?_ ?_
  · exact measurableSet_setOfPred.1
      (measurableSet_lt (measurable_const.dist measurable_snd) measurable_const)
  · exact ((measurable_pi_apply _).comp measurable_fst).eq_const _

theorem exists_denseSeq_between {U : Set ℝ≥0} (hU : IsOpen U) {s b : ℝ≥0} (hs : s ∈ U)
    (hsb : s < b) : ∃ k, TopologicalSpace.denseSeq ℝ≥0 k ∈ U ∩ Ioo s b := by
  have hcl : s ∈ closure (Ioo s b) := by
    rw [closure_Ioo hsb.ne]
    exact left_mem_Icc.2 hsb.le
  have hne := mem_closure_iff_nhds.1 hcl U (hU.mem_nhds hs)
  exact (TopologicalSpace.denseRange_denseSeq ℝ≥0).exists_mem_open (hU.inter isOpen_Ioo) hne

/-- On a right-regular path the countable form gives local constancy. -/
theorem goodAt_of_goodAtQ {x : Trajectory ℕ} (hx : IsRegLL x) {t : ℝ≥0} (h : GoodAtQ x t) :
    GoodAt x t := by
  obtain ⟨v, m, hv⟩ := h
  refine ⟨v, 1 / ((m : ℝ) + 1), by positivity, fun s hs => ?_⟩
  have hU : IsOpen (Metric.ball t (1 / ((m : ℝ) + 1))) := Metric.isOpen_ball
  cases hxs : x s with
  | some u =>
    obtain ⟨b, hsb, hb⟩ := rr_some hx.regular hxs
    obtain ⟨k, hkU, hk⟩ := exists_denseSeq_between hU hs hsb
    have h1 := hb _ hk.1.le hk.2
    rw [hv k hkU] at h1
    rw [h1]
  | none =>
    exfalso
    obtain ⟨b, hsb, hb⟩ := rr_none hx.regular hxs v
    obtain ⟨k, hkU, hk⟩ := exists_denseSeq_between hU hs hsb
    exact hb _ hk.1 hk.2 (hv k hkU)

/-- **Left limits constant on a right neighbourhood force the value** (right regularity). -/
theorem eq_of_leftLim_eq {x : Trajectory ℕ} (hx : IsRegLL x) {r c : ℝ≥0} (hrc : r < c) {w : ℕ}
    (h : ∀ r' : ℝ≥0, r < r' → r' < c → leftLim x r' = some w) : x r = some w := by
  cases hxr : x r with
  | some u =>
    obtain ⟨b, hrb, hb⟩ := rr_some hx.regular hxr
    obtain ⟨r', h1, h2⟩ := exists_between (lt_min hrb hrc)
    have hl : leftLim x r' = some u := leftLim_eq_some_iff.2
      ⟨r, h1, fun s hs => hb s hs.1.le (lt_trans hs.2 (lt_of_lt_of_le h2 (min_le_left _ _)))⟩
    have := h r' h1 (lt_of_lt_of_le h2 (min_le_right _ _))
    rw [hl] at this
    exact this
  | none =>
    exfalso
    obtain ⟨b, hrb, hb⟩ := rr_none hx.regular hxr w
    obtain ⟨r', h1, h2⟩ := exists_between (lt_min hrb hrc)
    obtain ⟨a, har, ha⟩ := leftLim_eq_some_iff.1 (h r' h1 (lt_of_lt_of_le h2 (min_le_right _ _)))
    obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt har h1)
    exact hb s (lt_of_le_of_lt (le_max_right _ _) hs1)
      (lt_trans hs2 (lt_of_lt_of_le h2 (min_le_left _ _)))
      (ha s ⟨lt_of_le_of_lt (le_max_left _ _) hs1, hs2⟩)

/-! ### 2. The label event -/

/-- **The label event** of a two-sided coding: the forward half is locally constant at a vertex
at every rational time `q ≥ 0`, the backward half at every rational time `q > 0`. -/
def Lab (p : Trajectory ℕ × Trajectory ℕ) : Prop :=
  (∀ q : ℚ, 0 ≤ q → GoodAtQ p.1 (q : ℝ).toNNReal) ∧ ∀ q : ℚ, 0 < q → GoodAtQ p.2 (q : ℝ).toNNReal

theorem measurable_lab : Measurable Lab := by
  refine Measurable.and (Measurable.forall fun q => Measurable.imp measurable_const ?_)
    (Measurable.forall fun q => Measurable.imp measurable_const ?_)
  · exact measurable_goodAtQ.comp (measurable_fst.prodMk measurable_const)
  · exact measurable_goodAtQ.comp (measurable_snd.prodMk measurable_const)

/-! ### 3. The glued label path of a regular pair -/

/-- The `ℕ∞`-label path on the line: the forward half on `[0,∞)`, the left-limit reversal of the
backward half on `(-∞,0)` (as in `FlowCodingKernel.goodPath`). -/
noncomputable def lineLabel (p : TwoSidedReg) : ℝ → ℕ∞ :=
  FlowCodingLine.glue (fun s : ℝ => toENatLabel (p.1.1 s.toNNReal))
    (fun s : ℝ => toENatLabel (p.1.2 s.toNNReal))

theorem isCadlag_lineLabel (p : TwoSidedReg) : IsCadlag (lineLabel p) :=
  isCadlag_glue (isCadlag_comp_toNNReal (isCadlag_label p.2.fwd))
    (isCadlag_comp_toNNReal (isCadlag_label p.2.bwd))

theorem lineLabel_of_nonneg (p : TwoSidedReg) {y : ℝ} (hy : 0 ≤ y) :
    lineLabel p y = toENatLabel (p.1.1 y.toNNReal) :=
  FlowCodingLine.glue_of_nonneg _ _ hy

/-- Constancy of the forward half on `[α, β)` is constancy of the line path there. -/
theorem lineLabel_pos_of_const (p : TwoSidedReg) {α β : ℝ} (hα : 0 ≤ α) {w : ℕ}
    (hf : ∀ s : ℝ≥0, α ≤ (s : ℝ) → (s : ℝ) < β → p.1.1 s = some w) {y : ℝ} (h1 : α ≤ y)
    (h2 : y < β) : lineLabel p y = (w : ℕ∞) := by
  have hy : 0 ≤ y := hα.trans h1
  rw [lineLabel_of_nonneg p hy, hf y.toNNReal (by rw [Real.coe_toNNReal _ hy]; exact h1)
    (by rw [Real.coe_toNNReal _ hy]; exact h2)]
  rfl

/-- Constancy of the backward half on `(α, β)` is constancy of the line path on `[-β, -α)`. -/
theorem lineLabel_neg_of_const (p : TwoSidedReg) {α β : ℝ} (hα : 0 ≤ α) {w : ℕ}
    (hb : ∀ s : ℝ≥0, α < (s : ℝ) → (s : ℝ) < β → p.1.2 s = some w) {y : ℝ} (h1 : α < -y)
    (h2 : -y ≤ β) : lineLabel p y = (w : ℕ∞) := by
  have hy : y < 0 := by linarith
  show FlowCodingLine.glue _ _ y = _
  rw [FlowCodingLine.glue_of_neg _ _ hy]
  apply leftLim_eq_of_eventuallyEq_const
  filter_upwards [Ioo_mem_nhdsLT h1] with x hx
  have hx0 : 0 ≤ x := by linarith [hx.1]
  rw [hb x.toNNReal (by rw [Real.coe_toNNReal _ hx0]; exact hx.1)
    (by rw [Real.coe_toNNReal _ hx0]; linarith [hx.2])]
  rfl

theorem dist_toNNReal_lt {s : ℝ≥0} {a ε : ℝ} (ha : 0 ≤ a) (h1 : a - ε < s) (h2 : (s : ℝ) < a + ε) :
    dist s a.toNNReal < ε := by
  rw [NNReal.dist_eq, Real.coe_toNNReal _ ha, abs_lt]
  constructor <;> linarith

/-- On `Lab`, the rational code of `p` is the line path at the rationals. -/
theorem rawLabel_eq_lineLabel (p : TwoSidedReg) (hL : Lab p.1) (q : ℚ) :
    rawLabel p.1 q = lineLabel p q := by
  by_cases hq : 0 ≤ q
  · unfold rawLabel
    rw [if_pos hq, lineLabel_of_nonneg p (by exact_mod_cast hq)]
  · have hq' : q < 0 := not_le.1 hq
    have hqr : (q : ℝ) < 0 := by exact_mod_cast hq'
    obtain ⟨w, ε, hε, hb⟩ := goodAt_of_goodAtQ p.2.bwd (hL.2 (-q) (neg_pos.2 hq'))
    have hcast : (((-q : ℚ) : ℝ)) = -(q : ℝ) := by push_cast; ring
    rw [hcast] at hb
    have hval : p.1.2 (-(q : ℝ)).toNNReal = some w := hb _ (by rw [dist_self]; exact hε)
    unfold rawLabel
    rw [if_neg hq, hval]
    symm
    refine lineLabel_neg_of_const p (α := -(q : ℝ) - min ε (-(q : ℝ))) (β := -(q : ℝ) + ε)
      (by linarith [min_le_right ε (-(q : ℝ))]) (fun s h1 h2 => hb s ?_) ?_ ?_
    · exact dist_toNNReal_lt (by linarith) (by linarith [min_le_left ε (-(q : ℝ))]) h2
    · linarith [lt_min hε (neg_pos.2 hqr)]
    · linarith

/-! ### 4. The configuration of a pair and its positions -/

/-- **The configuration of a regular pair with càdlàg-extendable position readings.** -/
theorem exists_line (z : CellField) (e : Env) (p : TwoSidedReg)
    (hC : RatCadlag (ratCode z (e, p.1)).2) (hL : Lab p.1) :
    ∃ x : FlowCoding, x.1.toFun = lineLabel p ∧ ratRead x = ratCode z (e, p.1) := by
  obtain ⟨Z, hZ, hZq⟩ := exists_cadlag_of_ratCadlag hC
  refine ⟨(⟨lineLabel p, isCadlag_lineLabel p⟩, ⟨Z, hZ⟩), rfl, ?_⟩
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
  · exact (rawLabel_eq_lineLabel p hL q).symm
  · exact hZq q

/-- **The position at a point of right constancy of the line path** is the representative. -/
theorem pos_eq_of_right_const {z : CellField} {e : Env} {p : TwoSidedReg} {x : FlowCoding}
    (hx1 : x.1.toFun = lineLabel p) (hx : ratRead x = ratCode z (e, p.1)) (hL : Lab p.1)
    {s : ℝ} {c : ℕ∞} {ε : ℝ} (hε : 0 < ε) (hc : ∀ y, s < y → y < s + ε → lineLabel p y = c) :
    x.2.toFun s = repAt z e c := by
  have := comap_nhdsGT_neBot s
  have hZ : Tendsto (fun r : ℚ => x.2.toFun r) (rightF s) (𝓝 (x.2.toFun s)) :=
    (x.2.isCadlag'.isRightContinuous s).tendsto.comp tendsto_comap
  refine tendsto_nhds_unique hZ (tendsto_const_nhds.congr' ?_)
  have hmem : (fun q : ℚ => (q : ℝ)) ⁻¹' Ioo s (s + ε) ∈ rightF s :=
    preimage_mem_comap (Ioo_mem_nhdsGT (by linarith))
  filter_upwards [hmem] with r hr
  have h1 : x.2.toFun r = repAt z e (rawLabel p.1 r) := congrFun (congrArg Prod.snd hx) r
  rw [h1, rawLabel_eq_lineLabel p hL r, hc r hr.1 hr.2]

/-! ### 5. One step of the bridge -/

theorem toNNReal_sub_add {y : ℝ} {T : ℝ≥0} (h : (T : ℝ) ≤ y) :
    (y - T).toNNReal + T = y.toNNReal := by
  apply NNReal.eq
  rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by linarith [NNReal.coe_nonneg T])]
  ring

/-- The forward case `q ≥ 0` of the bridge step. -/
theorem key_fwd (p : TwoSidedReg) {T : ℝ≥0} {F : Trajectory ℕ} (hF : F = shiftBy T p.1.1)
    (hFreg : IsRegLL F) {q : ℚ} (hq : 0 ≤ q) (hg : GoodAtQ F (q : ℝ).toNNReal) :
    ∃ w : ℕ, F (q : ℝ).toNNReal = some w ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ y : ℝ, (q : ℝ) + T ≤ y → y < (q : ℝ) + T + ε → lineLabel p y = (w : ℕ∞) := by
  obtain ⟨w, ε, hε, hw⟩ := goodAt_of_goodAtQ hFreg hg
  refine ⟨w, hw _ (by rw [dist_self]; exact hε), ε, hε, fun y hy1 hy2 => ?_⟩
  have hqr : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hT0 := NNReal.coe_nonneg T
  refine lineLabel_pos_of_const p (α := (q : ℝ) + T) (β := (q : ℝ) + T + ε)
    (by linarith) (fun s hs1 hs2 => ?_) hy1 hy2
  have hTs : (T : ℝ) ≤ s := by linarith
  have hsT : (0 : ℝ) ≤ (s : ℝ) - T := by linarith
  have h := hw ((s : ℝ) - T).toNNReal
    (dist_toNNReal_lt hqr (by rw [Real.coe_toNNReal _ hsT]; linarith)
      (by rw [Real.coe_toNNReal _ hsT]; linarith))
  rw [hF] at h
  have hs' : ((s : ℝ) - T).toNNReal + T = s := by
    rw [toNNReal_sub_add hTs, Real.toNNReal_coe]
  have e1 : shiftBy T p.1.1 ((s : ℝ) - T).toNNReal = p.1.1 s := by
    show p.1.1 (((s : ℝ) - T).toNNReal + T) = p.1.1 s
    rw [hs']
  rw [e1] at h
  exact h

/-- The backward case `q < 0` of the bridge step. -/
theorem key_bwd (p : TwoSidedReg) {T : ℝ≥0} {B : Trajectory ℕ}
    (hB : B = TwoSidedCycleSplice.glue (revPiece p.1.1 T) T p.1.2) (hBreg : IsRegLL B) {q : ℚ}
    (hq : q < 0) (hg : GoodAtQ B (-(q : ℝ)).toNNReal) :
    ∃ w : ℕ, B (-(q : ℝ)).toNNReal = some w ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ y : ℝ, (q : ℝ) + T ≤ y → y < (q : ℝ) + T + ε → lineLabel p y = (w : ℕ∞) := by
  have hqr : (q : ℝ) < 0 := by exact_mod_cast hq
  have hu0 : (0 : ℝ) ≤ -(q : ℝ) := by linarith
  obtain ⟨w, ε, hε, hw⟩ := goodAt_of_goodAtQ hBreg hg
  refine ⟨w, hw _ (by rw [dist_self]; exact hε), ?_⟩
  rw [hB] at hw
  rcases lt_trichotomy (-(q : ℝ)) (T : ℝ) with hlt | heq | hgt
  · -- `0 < -q < T`: the reversed first cycle
    have hm1 := min_le_left ε (-(q : ℝ))
    have hm2 := min_le_right ε (-(q : ℝ))
    have hmpos : 0 < min ε (-(q : ℝ)) := lt_min hε (by linarith)
    refine ⟨min ε (-(q : ℝ)), hmpos, fun y hy1 hy2 => ?_⟩
    have hy0 : 0 ≤ y := by linarith
    rw [lineLabel_of_nonneg p hy0]
    have hpos : (0 : ℝ) < (q : ℝ) + T + min ε (-(q : ℝ)) := by linarith
    have hc : y.toNNReal < ((q : ℝ) + T + min ε (-(q : ℝ))).toNNReal :=
      (Real.toNNReal_lt_toNNReal_iff hpos).2 hy2
    rw [eq_of_leftLim_eq p.2.fwd hc fun r' hr1 hr2 => ?_]
    · rfl
    have hr1' : y < r' := (Real.toNNReal_lt_iff_lt_coe hy0).1 hr1
    have hr2' : (r' : ℝ) < (q : ℝ) + T + min ε (-(q : ℝ)) := Real.lt_toNNReal_iff_coe_lt.1 hr2
    have hr0 : (0 : ℝ) < r' := by linarith
    have hr'T : r' ≤ T := by
      have : (r' : ℝ) ≤ T := by linarith
      exact_mod_cast this
    have hT0 : (0 : ℝ) < T := by linarith
    have hsT : T - r' < T := tsub_lt_self (by exact_mod_cast hT0) (by exact_mod_cast hr0)
    have hcoe : ((T - r' : ℝ≥0) : ℝ) = T - r' := NNReal.coe_sub hr'T
    have h := hw (T - r') (dist_toNNReal_lt hu0 (by rw [hcoe]; linarith)
      (by rw [hcoe]; linarith))
    rw [TwoSidedCycleSplice.glue_of_lt hsT, revPiece_of_lt hsT, tsub_tsub_cancel_of_le hr'T] at h
    exact h
  · -- `-q = T`: the junction at time `0`
    have hT0 : (0 : ℝ) < T := by linarith
    have hm1 := min_le_left ε (T : ℝ)
    have hm2 := min_le_right ε (T : ℝ)
    refine ⟨min ε T, lt_min hε hT0, fun y hy1 hy2 => ?_⟩
    have hy0 : 0 ≤ y := by linarith
    rw [lineLabel_of_nonneg p hy0]
    have hc : y.toNNReal < (min ε (T : ℝ)).toNNReal :=
      (Real.toNNReal_lt_toNNReal_iff (lt_min hε hT0)).2 (by linarith)
    rw [eq_of_leftLim_eq p.2.fwd hc fun r' hr1 hr2 => ?_]
    · rfl
    have hr1' : y < r' := (Real.toNNReal_lt_iff_lt_coe hy0).1 hr1
    have hr2' : (r' : ℝ) < min ε (T : ℝ) := Real.lt_toNNReal_iff_coe_lt.1 hr2
    have hr0 : (0 : ℝ) < r' := by linarith
    have hr'T : r' ≤ T := by
      have : (r' : ℝ) ≤ T := by linarith
      exact_mod_cast this
    have hsT : T - r' < T := tsub_lt_self (by exact_mod_cast hT0) (by exact_mod_cast hr0)
    have hcoe : ((T - r' : ℝ≥0) : ℝ) = T - r' := NNReal.coe_sub hr'T
    have h := hw (T - r') (dist_toNNReal_lt hu0 (by rw [hcoe]; linarith)
      (by rw [hcoe]; linarith))
    rw [TwoSidedCycleSplice.glue_of_lt hsT, revPiece_of_lt hsT, tsub_tsub_cancel_of_le hr'T] at h
    exact h
  · -- `-q > T`: the old backward half
    have hm1 := min_le_left ε (-(q : ℝ) - T)
    have hm2 := min_le_right ε (-(q : ℝ) - T)
    refine ⟨min ε (-(q : ℝ) - T), lt_min hε (by linarith), fun y hy1 hy2 => ?_⟩
    refine lineLabel_neg_of_const p (α := -(q : ℝ) - T - min ε (-(q : ℝ) - T))
      (β := -(q : ℝ) - T + min ε (-(q : ℝ) - T)) (by linarith)
      (fun s hs1 hs2 => ?_) (by linarith) (by linarith)
    have h := hw (s + T) (dist_toNNReal_lt hu0 (by push_cast; linarith)
      (by push_cast; linarith))
    rwa [TwoSidedCycleSplice.glue_of_le le_add_self, add_tsub_cancel_right] at h

/-- **The bridge at one pair.** -/
theorem bridge_step (z : CellField) (e : Env) (p : TwoSidedReg)
    (hC : RatCadlag (ratCode z (e, p.1)).2) (h0 : Lab p.1) (h1 : Lab (rho p).1) :
    ∃ (x : FlowCoding) (t : ℝ), ratRead x = ratCode z (e, p.1) ∧
      ratRead (flowShift t x) = ratCode z (e, (rho p).1) := by
  obtain ⟨x, hx1, hx⟩ := exists_line z e p hC h0
  by_cases hret : fwdReturn p.1.1 = ⊤
  · have hrho : rho p = p := Subtype.ext (by
      show rhoRaw p.1 = p.1
      unfold rhoRaw
      rw [if_pos hret])
    refine ⟨x, 0, hx, ?_⟩
    have h0x : flowShift 0 x = x :=
      Prod.ext (CadlagPath.timeShift_zero _) (CadlagPath.timeShift_zero _)
    rw [hrho, h0x]
    exact hx
  have hrho1 : (rho p).1.1 = shiftBy (retLen p.1.1) p.1.1 := by
    show (rhoRaw p.1).1 = _
    unfold rhoRaw
    rw [if_neg hret]
  have hrho2 : (rho p).1.2 =
      TwoSidedCycleSplice.glue (revPiece p.1.1 (retLen p.1.1)) (retLen p.1.1) p.1.2 := by
    show (rhoRaw p.1).2 = _
    unfold rhoRaw
    rw [if_neg hret]
  have key : ∀ q : ℚ, ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, (q : ℝ) + retLen p.1.1 ≤ y →
      y < (q : ℝ) + retLen p.1.1 + ε → lineLabel p y = rawLabel (rho p).1 q := by
    intro q
    by_cases hq : 0 ≤ q
    · obtain ⟨w, hw, ε, hε, hk⟩ := key_fwd p hrho1 (rho p).2.fwd hq (h1.1 q hq)
      refine ⟨ε, hε, fun y hy1 hy2 => ?_⟩
      rw [hk y hy1 hy2]
      unfold rawLabel
      rw [if_pos hq, hw]
      rfl
    · have hq' : q < 0 := not_le.1 hq
      have hcast : (((-q : ℚ) : ℝ)) = -(q : ℝ) := by push_cast; ring
      have hg := h1.2 (-q) (neg_pos.2 hq')
      rw [hcast] at hg
      obtain ⟨w, hw, ε, hε, hk⟩ := key_bwd p hrho2 (rho p).2.bwd hq' hg
      refine ⟨ε, hε, fun y hy1 hy2 => ?_⟩
      rw [hk y hy1 hy2]
      unfold rawLabel
      rw [if_neg hq, hw]
      rfl
  refine ⟨x, retLen p.1.1, hx, Prod.ext (funext fun q => ?_) (funext fun q => ?_)⟩
  · obtain ⟨ε, hε, hk⟩ := key q
    show x.1.toFun ((q : ℝ) + retLen p.1.1) = rawLabel (rho p).1 q
    rw [hx1]
    exact hk _ le_rfl (by linarith)
  · obtain ⟨ε, hε, hk⟩ := key q
    show x.2.toFun ((q : ℝ) + retLen p.1.1) = repAt z e (rawLabel (rho p).1 q)
    exact pos_eq_of_right_const hx1 hx h0 hε fun y hy1 hy2 => hk y hy1.le hy2

/-! ### 6. The bridge along the orbit -/

/-- Every configuration's position readings satisfy the càdlàg criterion. -/
theorem ratCadlag_ratRead (x : FlowCoding) : RatCadlag (ratRead x).2 :=
  ratCadlag_of_isCadlag x.2.isCadlag'

/-- **`RatShiftBridge` from a measurable almost-sure event.** -/
theorem ratShiftBridge_of_ae (z : CellField) (e : Env) {μ : Measure TwoSidedReg}
    (h : ∀ᵐ w ∂μ, RatCadlag (ratCode z (e, w.1)).2 ∧ ∀ n : ℕ, Lab (rho^[n] w).1) :
    RatShiftBridge (fun w => ratCode z (e, w.val)) μ := by
  filter_upwards [h] with w hw
  obtain ⟨hC, hL⟩ := hw
  have hL' : ∀ n : ℕ, Lab (rho (rho^[n] w)).1 := fun n => by
    rw [← Function.iterate_succ_apply' rho n w]
    exact hL (n + 1)
  have hCn : ∀ n : ℕ, RatCadlag (ratCode z (e, (rho^[n] w).1)).2 := by
    intro n
    induction n with
    | zero => exact hC
    | succ n ih =>
      obtain ⟨x, t, -, hx⟩ := bridge_step z e (rho^[n] w) ih (hL n) (hL' n)
      rw [Function.iterate_succ_apply', ← hx]
      exact ratCadlag_ratRead _
  intro n
  obtain ⟨x, t, h0, h1⟩ := bridge_step z e (rho^[n] w) (hCn n) (hL n) (hL' n)
  refine ⟨x, t, h0, ?_⟩
  rw [Function.iterate_succ_apply']
  exact h1

end ReflectedGMS.RatShiftBridgePathwise
