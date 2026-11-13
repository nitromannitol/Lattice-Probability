/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ContinuousInterpolation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionCore

/-!
# The continuous interpolation of the representative path (`p:sec:interpolation`)

This is the first producer of `SpatialEnds.IsContinuousInterpolation` in the tree.  Everything
here is **deterministic and pathwise**; the probabilistic inputs enter only through the
structure `PathInputs`, which lists pathwise properties of one collapsed vertex path.

## Contents

* **Complete holding intervals** (`hasCompleteCollapsedHoldingIntervals_of_inputs`): right
  regularity, edge jumps, finite-cut avoidance at nonvertex times and the fact that no sojourn is
  infinite (`LeavesEveryVertex`) put every vertex time inside a complete maximal holding
  interval.  The exit time is a supremum; the left end is the infimum of
  `SpatialExtensionCore.exists_collapsedHoldingInterval_of_leftVertexConstant`.  Two complete
  holding intervals through one time coincide (`IsCollapsedHoldingInterval.unique`).
* **The interpolation** (`interpolation`): the affine map from `z v` to `z w` over the holding
  interval through `r`, and the spatial extension `Z` at end-valued times.
* **Continuity** (`continuous_interpolation`), exactly the argument of the manuscript
  (`tex:1340`): affine inside holding intervals; at the start of a sojourn, either `Z` jumps
  there — and then the jump is the end of a preceding holding interval, on which the
  interpolation is again affine — or `Z` is left-continuous there, and every holding interval
  meeting a left neighbourhood ends inside it, so the interpolation is squeezed between two values
  of `Z`; at an end-valued time, `Z` is continuous and every ordinary jump issued near that time
  is small (`smallJumps_of_largeCellsFinite`: the visited cells leave every finite set, stay in a
  bounded region, and only finitely many cells meeting a bounded region have diameter above a
  scale — manuscript `s:lem:largecells`, stated here as `LargeCellsFinite`).  The interpolation
  error `|z_H - z_{H'}| ≤ d_H + d_{H'}` is the manuscript's.
* **Assembly** (`PathInputs.isContinuousInterpolation`, `PathInputs.regularSpatialExtension`):
  from `PathInputs`, the canonical càdlàg extension `pathExtension z X` is a
  `RegularSpatialExtension` and `interpolation F z X (pathExtension z X)` is an
  `IsContinuousInterpolation`, for every lift with collapse `X`.
* **Time change** (`PathInputs.of_timeChange`): `PathInputs` transports along a homeomorphic
  time change of `[0,∞)`; this is how the exact clock inherits everything from the exponential
  one.

Nothing here is probabilistic and nothing here certifies any main theorem.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped NNReal

namespace ReflectedGMS.ContinuousInterpolation

open AreaClocks SpatialEnds InvarianceMainStatement StatementIngredients
open ReflectedGMS.PathwiseClockClauseLift ReflectedGMS.SpatialExtensionConstruction

variable {V : Type*}

/-! ## Complete holding intervals -/

/-- No sojourn of the path at a vertex is infinite. -/
def LeavesEveryVertex (X : ℝ≥0 → Option V) : Prop :=
  ∀ (r : ℝ≥0) (v : V), X r = some v → ∃ q, r < q ∧ X q ≠ some v

/-- `SpatialEnds.HasCompleteHoldingIntervals`, on the collapsed path. -/
def HasCompleteCollapsedHoldingIntervals (F : IndexedCells V) (X : ℝ≥0 → Option V) : Prop :=
  ∀ (r : ℝ≥0) (v : V), X r = some v →
    ∃ s t w, IsCollapsedHoldingInterval F X v w s t ∧ r ∈ Ico s t

/-- **The exit time of a sojourn.**  From a vertex time `r` at `v`, the path stays at `v` up to
a time `t > r` at which it sits at a different vertex `w`: the supremum of the sojourn is finite
because the path leaves `v`, it is not a nonvertex time because the path is left-constant there,
and it is not a time at `v` by right regularity. -/
theorem exists_exit_of_rightRegular {X : ℝ≥0 → Option V} (hreg : RightRegular X)
    (hcut : AvoidsFiniteCutsAtNonvertexTimes X) (hleave : LeavesEveryVertex X)
    {r : ℝ≥0} {v : V} (hr : X r = some v) :
    ∃ t w, r < t ∧ (∀ q ∈ Ico r t, X q = some v) ∧ X t = some w ∧ w ≠ v := by
  let S : Set ℝ≥0 := {q | r < q ∧ ∀ p ∈ Ico r q, X p = some v}
  obtain ⟨ε, hε, hεX⟩ := hreg.1 r ⟨v, hr⟩
  have hεS : r + ε ∈ S :=
    ⟨lt_add_of_pos_right r hε, fun p hp => (hεX p hp).trans hr⟩
  obtain ⟨q₀, hrq₀, hq₀⟩ := hleave r v hr
  have hbdd : BddAbove S := by
    refine ⟨q₀, fun q hq => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hq₀ (hq.2 q₀ ⟨hrq₀.le, hlt⟩)
  have hrt : r < sSup S := lt_of_lt_of_le hεS.1 (le_csSup hbdd hεS)
  have hcon : ∀ p ∈ Ico r (sSup S), X p = some v := by
    intro p hp
    obtain ⟨q, hqS, hpq⟩ := exists_lt_of_lt_csSup ⟨_, hεS⟩ hp.2
    exact hqS.2 p ⟨hp.1, hpq⟩
  have htpos : 0 < sSup S := lt_of_le_of_lt zero_le hrt
  obtain ⟨w, hw⟩ : ∃ w, X (sSup S) = some w := by
    rcases hXt : X (sSup S) with _ | w
    · exact absurd ⟨v, r, hrt, hcon⟩ (not_leftVertexConstant_of_none hcut hXt htpos)
    · exact ⟨w, rfl⟩
  refine ⟨sSup S, w, hrt, hcon, hw, ?_⟩
  intro hwv
  have hw' : X (sSup S) = some v := hwv ▸ hw
  obtain ⟨ε', hε', hε'X⟩ := hreg.1 (sSup S) ⟨v, hw'⟩
  have hmem : sSup S + ε' ∈ S := by
    refine ⟨hrt.trans (lt_add_of_pos_right _ hε'), fun p hp => ?_⟩
    rcases lt_or_ge p (sSup S) with hpt | hpt
    · exact hcon p ⟨hp.1, hpt⟩
    · exact (hε'X p ⟨hpt, hp.2⟩).trans hw'
  exact absurd (le_csSup hbdd hmem) (not_le.2 (lt_add_of_pos_right _ hε'))

/-- **Every vertex time lies in a complete holding interval.** -/
theorem hasCompleteCollapsedHoldingIntervals_of_inputs (F : IndexedCells V)
    {X : ℝ≥0 → Option V} (hreg : RightRegular X) (hedge : EdgeJumps F X)
    (hcut : AvoidsFiniteCutsAtNonvertexTimes X) (hleave : LeavesEveryVertex X) :
    HasCompleteCollapsedHoldingIntervals F X := by
  intro r v hr
  obtain ⟨t, w, hrt, hcon, hw, hwv⟩ := exists_exit_of_rightRegular hreg hcut hleave hr
  obtain ⟨s, hs⟩ := exists_collapsedHoldingInterval_of_leftVertexConstant F hreg hedge
    ⟨r, hrt, hcon⟩ hw (Ne.symm hwv)
  refine ⟨s, t, w, hs, ?_, hrt⟩
  by_contra hsr
  push_neg at hsr
  rcases hs.2.2.2.2 with h0 | hmax
  · rw [h0] at hsr
    exact (not_lt.2 zero_le) hsr
  · obtain ⟨q, hq, hqv⟩ := hmax r hsr
    exact hqv (hcon q ⟨hq.1.le, hq.2.trans hs.1⟩)

/-- The collapsed form lifts to `SpatialEnds.HasCompleteHoldingIntervals` for every lift. -/
theorem hasCompleteHoldingIntervals_of_collapsed {F : IndexedCells V} {Y : ℝ≥0 → State F}
    {X : ℝ≥0 → Option V} (hc : ∀ t, collapse (Y t) = X t)
    (h : HasCompleteCollapsedHoldingIntervals F X) : HasCompleteHoldingIntervals F Y := by
  intro r v hr
  have hX : X r = some v := by rw [← hc r, hr]; rfl
  obtain ⟨s, t, w, hs, hmem⟩ := h r v hX
  exact ⟨s, t, w, (isHoldingInterval_iff_isCollapsedHoldingInterval hc v w s t).2 hs, hmem⟩

/-- **Two complete holding intervals through one time coincide**: the vertex is the value at
that time, the right ends agree because the following vertex is adjacent (hence different), and
the left ends agree by maximality. -/
theorem IsCollapsedHoldingInterval.unique {F : IndexedCells V} {X : ℝ≥0 → Option V}
    {v w v' w' : V} {s t s' t' r : ℝ≥0}
    (h : IsCollapsedHoldingInterval F X v w s t) (h' : IsCollapsedHoldingInterval F X v' w' s' t')
    (hr : r ∈ Ico s t) (hr' : r ∈ Ico s' t') : v = v' ∧ w = w' ∧ s = s' ∧ t = t' := by
  have hvv : v = v' := by
    have h1 := h.2.1 r hr
    rw [h'.2.1 r hr'] at h1
    exact (Option.some_injective _ h1).symm
  subst hvv
  have htt : t = t' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hX := h'.2.1 t ⟨hr'.1.trans hr.2.le, hlt⟩
      rw [h.2.2.1] at hX
      exact h.2.2.2.1.ne (Option.some_injective _ hX).symm
    · have hX := h.2.1 t' ⟨hr.1.trans hr'.2.le, hlt⟩
      rw [h'.2.2.1] at hX
      exact h'.2.2.2.1.ne (Option.some_injective _ hX).symm
  subst htt
  have hww : w = w' := Option.some_injective _ (h.2.2.1.symm.trans h'.2.2.1)
  subst hww
  refine ⟨rfl, rfl, ?_, rfl⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rcases h'.2.2.2.2 with h0 | hmax
    · rw [h0] at hlt
      exact (not_lt.2 zero_le) hlt
    · obtain ⟨q, hq, hqv⟩ := hmax s hlt
      exact hqv (h.2.1 q ⟨hq.1.le, hq.2.trans_le (hr'.1.trans hr.2.le)⟩)
  · rcases h.2.2.2.2 with h0 | hmax
    · rw [h0] at hlt
      exact (not_lt.2 zero_le) hlt
    · obtain ⟨q, hq, hqv⟩ := hmax s' hlt
      exact hqv (h'.2.1 q ⟨hq.1.le, hq.2.trans_le (hr.1.trans hr'.2.le)⟩)

/-! ## The interpolation -/

/-- The affine map from `a` to `b` over the time interval `[s, t]`. -/
noncomputable def affinePiece (a b : Plane) (s t r : ℝ≥0) : Plane :=
  AffineMap.lineMap a b (((r : ℝ) - s) / ((t : ℝ) - s))

theorem continuous_affinePiece (a b : Plane) (s t : ℝ≥0) :
    Continuous (fun r => affinePiece a b s t r) := by
  have h1 : Continuous fun r : ℝ≥0 => ((r : ℝ) - s) / ((t : ℝ) - s) :=
    (NNReal.continuous_coe.sub continuous_const).div_const _
  exact (AffineMap.lineMap_continuous (R := ℝ) (p := a) (q := b)).comp h1

theorem affinePiece_left (a b : Plane) (s t : ℝ≥0) : affinePiece a b s t s = a := by
  simp [affinePiece]

theorem affinePiece_right (a b : Plane) {s t : ℝ≥0} (hst : s < t) :
    affinePiece a b s t t = b := by
  have hne : (t : ℝ) - s ≠ 0 := sub_ne_zero.2 (NNReal.coe_lt_coe.2 hst).ne'
  simp [affinePiece, div_self hne]

/-- The interpolation parameter of a time in `[s, t]` lies in `[0, 1]`. -/
theorem affineParam_mem {s t r : ℝ≥0} (hr : r ∈ Icc s t) (hst : s < t) :
    0 ≤ ((r : ℝ) - s) / ((t : ℝ) - s) ∧ ((r : ℝ) - s) / ((t : ℝ) - s) ≤ 1 := by
  have h1 : (s : ℝ) ≤ r := NNReal.coe_le_coe.2 hr.1
  have h2 : (r : ℝ) ≤ t := NNReal.coe_le_coe.2 hr.2
  have h3 : (s : ℝ) < t := NNReal.coe_lt_coe.2 hst
  refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
  rw [div_le_one (by linarith)]
  linarith

/-- The affine piece stays within `‖b - a‖` of its initial value. -/
theorem norm_affinePiece_sub_left_le (a b : Plane) {s t r : ℝ≥0} (hr : r ∈ Icc s t)
    (hst : s < t) : ‖affinePiece a b s t r - a‖ ≤ ‖b - a‖ := by
  obtain ⟨h0, h1⟩ := affineParam_mem hr hst
  rw [affinePiece, AffineMap.lineMap_apply_module', add_sub_cancel_right, norm_smul,
    Real.norm_of_nonneg h0]
  exact mul_le_of_le_one_left (norm_nonneg _) h1

/-- The affine piece stays in every ball containing both of its end values. -/
theorem norm_affinePiece_sub_lt {a b c : Plane} {s t r : ℝ≥0} (hr : r ∈ Icc s t)
    (hst : s < t) {ε : ℝ} (ha : ‖a - c‖ < ε) (hb : ‖b - c‖ < ε) :
    ‖affinePiece a b s t r - c‖ < ε := by
  obtain ⟨h0, h1⟩ := affineParam_mem hr hst
  set θ : ℝ := ((r : ℝ) - s) / ((t : ℝ) - s) with hθ
  have hsplit : affinePiece a b s t r - c = (1 - θ) • (a - c) + θ • (b - c) := by
    rw [affinePiece, ← hθ, AffineMap.lineMap_apply_module]
    simp only [smul_sub, sub_smul, one_smul]
    abel
  have hle : ‖affinePiece a b s t r - c‖ ≤ (1 - θ) * ‖a - c‖ + θ * ‖b - c‖ := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 h1), Real.norm_of_nonneg h0]
  have hm : max ‖a - c‖ ‖b - c‖ < ε := max_lt ha hb
  nlinarith [mul_le_mul_of_nonneg_left (le_max_left ‖a - c‖ ‖b - c‖) (sub_nonneg.2 h1),
    mul_le_mul_of_nonneg_left (le_max_right ‖a - c‖ ‖b - c‖) h0]

open Classical in
/-- **The continuous interpolation of the representative path.**  On the complete holding
interval `[s, t)` through `r`, at `v` and followed by `w`, it is the affine map from `z v` to
`z w`; at every other time (in particular at every end-valued time) it is the spatial
extension `Z`. -/
noncomputable def interpolation (F : IndexedCells V) (z : V → Plane) (X : ℝ≥0 → Option V)
    (Z : ℝ≥0 → Plane) (r : ℝ≥0) : Plane :=
  if h : ∃ p : V × V × ℝ≥0 × ℝ≥0,
      IsCollapsedHoldingInterval F X p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ r ∈ Ico p.2.2.1 p.2.2.2 then
    affinePiece (z h.choose.1) (z h.choose.2.1) h.choose.2.2.1 h.choose.2.2.2 r
  else Z r

theorem interpolation_eq_of_mem (F : IndexedCells V) (z : V → Plane) (X : ℝ≥0 → Option V)
    (Z : ℝ≥0 → Plane) {v w : V} {s t r : ℝ≥0} (h : IsCollapsedHoldingInterval F X v w s t)
    (hr : r ∈ Ico s t) : interpolation F z X Z r = affinePiece (z v) (z w) s t r := by
  have hex : ∃ p : V × V × ℝ≥0 × ℝ≥0,
      IsCollapsedHoldingInterval F X p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ r ∈ Ico p.2.2.1 p.2.2.2 :=
    ⟨(v, w, s, t), h, hr⟩
  have hp : hex.choose = (v, w, s, t) := by
    obtain ⟨h1, h2, h3, h4⟩ :=
      IsCollapsedHoldingInterval.unique hex.choose_spec.1 h hex.choose_spec.2 hr
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
  rw [interpolation, dif_pos hex, hp]

theorem interpolation_eq_of_none (F : IndexedCells V) (z : V → Plane) (X : ℝ≥0 → Option V)
    (Z : ℝ≥0 → Plane) {r : ℝ≥0} (hr : X r = none) : interpolation F z X Z r = Z r := by
  rw [interpolation, dif_neg]
  rintro ⟨p, hp, hpr⟩
  have h1 := hp.2.1 r hpr
  rw [hr] at h1
  simp at h1

/-- On the whole closed holding interval, including its right end, the interpolation is the
affine piece. -/
theorem interpolation_eq_on_Icc (F : IndexedCells V) (z : V → Plane) (X : ℝ≥0 → Option V)
    (Z : ℝ≥0 → Plane) (hhold : HasCompleteCollapsedHoldingIntervals F X) {v w : V}
    {s t r : ℝ≥0} (h : IsCollapsedHoldingInterval F X v w s t) (hr : r ∈ Icc s t) :
    interpolation F z X Z r = affinePiece (z v) (z w) s t r := by
  rcases eq_or_lt_of_le hr.2 with hrt | hrt
  · rw [hrt, affinePiece_right _ _ h.1]
    obtain ⟨s'', t'', w'', h'', hmem''⟩ := hhold t w h.2.2.1
    have hs'' : s'' = t := by
      refine le_antisymm hmem''.1 ?_
      by_contra hlt
      push_neg at hlt
      have hq1 : max s s'' < t := max_lt h.1 hlt
      have hXv := h.2.1 (max s s'') ⟨le_max_left _ _, hq1⟩
      have hXw := h''.2.1 (max s s'') ⟨le_max_right _ _, hq1.trans hmem''.2⟩
      rw [hXv] at hXw
      exact h.2.2.2.1.ne (Option.some_injective _ hXw)
    rw [interpolation_eq_of_mem F z X Z h'' hmem'', hs'', affinePiece_left]
  · exact interpolation_eq_of_mem F z X Z h ⟨hr.1, hrt⟩

/-! ## Continuity -/

/-- **Continuity of the interpolation** (manuscript `tex:1340`).

Inputs: complete holding intervals; a càdlàg `Z` through the representatives at vertex times,
continuous at end-valued times, whose jumps are ends of complete holding intervals; and small
ordinary jumps near every end-valued time. -/
theorem continuous_interpolation (F : IndexedCells V) (z : V → Plane) {X : ℝ≥0 → Option V}
    {Z : ℝ≥0 → Plane} (hhold : HasCompleteCollapsedHoldingIntervals F X)
    (hZ : IsCadlag Z) (hvert : ∀ t v, X t = some v → Z t = z v)
    (hend : ∀ t, X t = none → ContinuousAt Z t)
    (hjump : ∀ t : ℝ≥0, 0 < t → Function.leftLim Z t ≠ Z t →
      ∃ s v w, IsCollapsedHoldingInterval F X v w s t)
    (hsmall : ∀ t, X t = none → ∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝 t, ∀ v w, X r = some v →
      F.graph.toSimpleGraph.Adj v w → ‖z w - z v‖ ≤ δ) :
    Continuous (interpolation F z X Z) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rcases hXp : X p with _ | v
  · -- an end-valued time: `Z` is continuous and the nearby ordinary jumps are small
    have hval : interpolation F z X Z p = Z p := interpolation_eq_of_none F z X Z hXp
    show Tendsto (interpolation F z X Z) (𝓝 p) (𝓝 (interpolation F z X Z p))
    rw [hval, Metric.tendsto_nhds]
    intro ε hε
    have hZp := Metric.tendsto_nhds.1 (hend p hXp) (ε / 2) (half_pos hε)
    filter_upwards [hZp, hsmall p hXp (ε / 2) (half_pos hε)] with r hr hsm
    rcases hXr : X r with _ | u
    · rw [interpolation_eq_of_none F z X Z hXr]
      linarith
    · obtain ⟨s', t', w', hI', hmem'⟩ := hhold r u hXr
      rw [interpolation_eq_of_mem F z X Z hI' hmem', dist_eq_norm]
      have hA : ‖affinePiece (z u) (z w') s' t' r - z u‖ ≤ ε / 2 :=
        (norm_affinePiece_sub_left_le (z u) (z w') ⟨hmem'.1, hmem'.2.le⟩ hI'.1).trans
          (hsm u w' hXr hI'.2.2.2.1)
      have hB : ‖z u - Z p‖ < ε / 2 := by
        rw [← hvert r u hXr, ← dist_eq_norm]
        exact hr
      have hC := norm_sub_le_norm_sub_add_norm_sub (affinePiece (z u) (z w') s' t' r) (z u) (Z p)
      linarith
  · obtain ⟨s, t, w, hI, hmem⟩ := hhold p v hXp
    have hEqOn : ∀ r ∈ Icc s t, interpolation F z X Z r = affinePiece (z v) (z w) s t r :=
      fun r hr => interpolation_eq_on_Icc F z X Z hhold hI hr
    have hg := continuous_affinePiece (z v) (z w) s t
    rcases eq_or_lt_of_le hmem.1 with hsp | hsp
    · -- `p` is the start of its sojourn
      have hIp : IsCollapsedHoldingInterval F X v w p t := hsp ▸ hI
      have hEqOnp : ∀ r ∈ Icc p t, interpolation F z X Z r = affinePiece (z v) (z w) p t r :=
        fun r hr => interpolation_eq_on_Icc F z X Z hhold hIp hr
      have hgp := continuous_affinePiece (z v) (z w) p t
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · rcases eq_or_ne p 0 with h0 | h0
        · rw [← continuousWithinAt_Iio_iff_Iic]
          have hIio : Iio p = ∅ := by
            rw [h0]
            exact Set.Iio_eq_empty_iff.2 (isMin_iff_forall_not_lt.2 fun _ => not_lt.2 zero_le)
          rw [hIio, ContinuousWithinAt, nhdsWithin_empty]
          exact tendsto_bot
        · have hppos : 0 < p := pos_iff_ne_zero.2 h0
          by_cases hj : Function.leftLim Z p = Z p
          · -- no jump of `Z` at `p`: squeeze between two values of `Z`
            rw [← continuousWithinAt_Iio_iff_Iic]
            have hval : interpolation F z X Z p = Z p := by
              rw [hEqOnp p ⟨le_rfl, hIp.1.le⟩, affinePiece_left]
              exact (hvert p v hXp).symm
            show Tendsto (interpolation F z X Z) (𝓝[<] p) (𝓝 (interpolation F z X Z p))
            rw [hval, Metric.tendsto_nhds]
            intro ε hε
            have hZl : Tendsto Z (𝓝[<] p) (𝓝 (Z p)) := by
              have h1 := hZ.tendsto_nhdsLT_leftLim p
              rwa [hj] at h1
            have hev := Metric.tendsto_nhds.1 hZl ε hε
            obtain ⟨a, hap, hab⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hppos).1 hev
            filter_upwards [Ioo_mem_nhdsLT hap] with r hr
            rcases hXr : X r with _ | u
            · rw [interpolation_eq_of_none F z X Z hXr]
              exact hab hr
            · obtain ⟨s', t', w', hI', hmem'⟩ := hhold r u hXr
              have ht'p : t' ≤ p := by
                by_contra hlt
                push_neg at hlt
                have hXs : X p = some u := hI'.2.1 p ⟨hmem'.1.trans hr.2.le, hlt⟩
                rw [hXp] at hXs
                have huv : v = u := Option.some_injective _ hXs
                rcases hIp.2.2.2.2 with h0' | hmax
                · exact h0 h0'
                · obtain ⟨q, hq, hqv⟩ := hmax r hr.2
                  apply hqv
                  rw [huv]
                  exact hI'.2.1 q ⟨hmem'.1.trans hq.1.le, hq.2.trans hlt⟩
              rw [interpolation_eq_of_mem F z X Z hI' hmem', dist_eq_norm]
              have hu : ‖z u - Z p‖ < ε := by
                rw [← hvert r u hXr, ← dist_eq_norm]
                exact hab hr
              have hw : ‖z w' - Z p‖ < ε := by
                rcases eq_or_lt_of_le ht'p with heq | hlt
                · rw [← hvert t' w' hI'.2.2.1, heq, sub_self, norm_zero]
                  exact hε
                · rw [← hvert t' w' hI'.2.2.1, ← dist_eq_norm]
                  exact hab ⟨hr.1.trans hmem'.2, hlt⟩
              exact norm_affinePiece_sub_lt ⟨hmem'.1, hmem'.2.le⟩ hI'.1 hu hw
          · -- `Z` jumps at `p`: the jump ends a complete holding interval
            obtain ⟨s'', u, w'', hI''⟩ := hjump p hppos hj
            have hw'' : w'' = v := Option.some_injective _ (hI''.2.2.1.symm.trans hXp)
            rw [hw''] at hI''
            have hEq'' : ∀ r ∈ Icc s'' p,
                interpolation F z X Z r = affinePiece (z u) (z v) s'' p r :=
              fun r hr => interpolation_eq_on_Icc F z X Z hhold hI'' hr
            refine (continuous_affinePiece (z u) (z v) s'' p).continuousWithinAt.congr_of_eventuallyEq
              ?_ (hEq'' p ⟨hI''.1.le, le_rfl⟩)
            filter_upwards [Ioc_mem_nhdsLE hI''.1] with r hr
            exact hEq'' r ⟨hr.1.le, hr.2⟩
      · refine hgp.continuousWithinAt.congr_of_eventuallyEq ?_ (hEqOnp p ⟨le_rfl, hIp.1.le⟩)
        filter_upwards [Ico_mem_nhdsGE hIp.1] with r hr
        exact hEqOnp r ⟨hr.1, hr.2.le⟩
    · -- `p` is interior to its holding interval
      refine hg.continuousAt.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hsp hmem.2] with r hr
      exact hEqOn r ⟨hr.1.le, hr.2.le⟩

/-- **`IsContinuousInterpolation`** for every lift of the collapsed path, from the inputs of
`continuous_interpolation`. -/
theorem isContinuousInterpolation_interpolation (F : IndexedCells V) (z : V → Plane)
    {Y : ℝ≥0 → State F} {X : ℝ≥0 → Option V} (hc : ∀ t, collapse (Y t) = X t)
    {Z : ℝ≥0 → Plane} (hhold : HasCompleteCollapsedHoldingIntervals F X)
    (hZ : IsCadlag Z) (hvert : ∀ t v, X t = some v → Z t = z v)
    (hend : ∀ t, X t = none → ContinuousAt Z t)
    (hjump : ∀ t : ℝ≥0, 0 < t → Function.leftLim Z t ≠ Z t →
      ∃ s v w, IsCollapsedHoldingInterval F X v w s t)
    (hsmall : ∀ t, X t = none → ∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝 t, ∀ v w, X r = some v →
      F.graph.toSimpleGraph.Adj v w → ‖z w - z v‖ ≤ δ) :
    IsContinuousInterpolation F z Y Z (interpolation F z X Z) := by
  refine ⟨continuous_interpolation F z hhold hZ hvert hend hjump hsmall,
    hasCompleteHoldingIntervals_of_collapsed hc hhold, ?_, ?_⟩
  · intro v w s t hI r hr
    exact interpolation_eq_on_Icc F z X Z hhold
      ((isHoldingInterval_iff_isCollapsedHoldingInterval hc v w s t).1 hI) hr
  · intro t e ht
    exact interpolation_eq_of_none F z X Z (by rw [← hc t, ht]; rfl)

/-! ## Small ordinary jumps near end-valued times (`s:lem:largecells`) -/

/-- Manuscript `s:lem:largecells`, consequence: only finitely many cells meeting a bounded
region have diameter above a positive scale. -/
def LargeCellsFinite (F : IndexedCells V) : Prop :=
  ∀ R δ : ℝ, 0 < δ → {v : V | Hits F (Metric.closedBall (0 : Plane) R) v ∧
    δ < Metric.diam (F.cell v : Set Plane)}.Finite

/-- **Near an end-valued time every ordinary jump is small.**  The visited cells stay in a
bounded region (continuity of `Z` there), they leave every finite set of cells (finite-cut
avoidance), so eventually neither the current cell nor any neighbour is one of the finitely many
large cells of that region; and `|z_H - z_{H'}| ≤ d_H + d_{H'}` across an ordinary edge. -/
theorem smallJumps_of_largeCellsFinite [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (hL : LargeCellsFinite F) (z : V → Plane) (hz : CellRepresentatives F z)
    {X : ℝ≥0 → Option V} (hcut : AvoidsFiniteCutsAtNonvertexTimes X) {Z : ℝ≥0 → Plane}
    (hvert : ∀ t v, X t = some v → Z t = z v) {t : ℝ≥0} (ht : X t = none)
    (hZt : ContinuousAt Z t) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝 t, ∀ v w, X r = some v → F.graph.toSimpleGraph.Adj v w → ‖z w - z v‖ ≤ δ := by
  classical
  set R : ℝ := ‖Z t‖ + 1 with hRdef
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hK₁ := hL R (δ / 2) hδ2
  have hK₂ := hL (R + δ / 2) (δ / 2) hδ2
  have hK₃ : (⋃ u ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) (R + δ / 2)) v ∧
      δ / 2 < Metric.diam (F.cell v : Set Plane)}, F.graph.toSimpleGraph.neighborSet u).Finite :=
    hK₂.biUnion fun u _ => hF.2.2.2.2.2.2.1 u
  set K : Finset V := (hK₁.union hK₃).toFinset with hK
  have hZev := Metric.tendsto_nhds.1 hZt 1 one_pos
  filter_upwards [hcut t ht K, hZev] with r hr hZr v w hv hvw
  have hZv : Z r = z v := hvert r v hv
  have hvK : v ∉ (K : Set V) := fun hmem => hr ⟨v, hmem, hv.symm⟩
  rw [hK, Set.Finite.coe_toFinset] at hvK
  have hnorm : ‖z v‖ ≤ R := by
    rw [← hZv, hRdef]
    have h1 : ‖Z r‖ ≤ ‖Z t‖ + dist (Z r) (Z t) := by
      rw [dist_eq_norm]
      exact norm_le_insert' (Z r) (Z t)
    linarith
  have hvhit : Hits F (Metric.closedBall (0 : Plane) R) v :=
    ⟨z v, hz v, by simpa using hnorm⟩
  have hdv : Metric.diam (F.cell v : Set Plane) ≤ δ / 2 := by
    by_contra hlt
    push_neg at hlt
    exact hvK (Or.inl ⟨hvhit, hlt⟩)
  obtain ⟨q, hqv, hqw⟩ := hF.2.2.2.2.2.2.2 hvw
  have hqz : dist q (z v) ≤ Metric.diam (F.cell v : Set Plane) :=
    Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded hqv (hz v)
  have hwhit : Hits F (Metric.closedBall (0 : Plane) (R + δ / 2)) w := by
    refine ⟨q, hqw, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖q‖ ≤ ‖z v‖ + dist q (z v) := by
      rw [dist_eq_norm]
      exact norm_le_insert' q (z v)
    linarith
  have hdw : Metric.diam (F.cell w : Set Plane) ≤ δ / 2 := by
    by_contra hlt
    push_neg at hlt
    refine hvK (Or.inr ?_)
    rw [Set.mem_iUnion₂]
    exact ⟨w, ⟨hwhit, hlt⟩, hvw.symm⟩
  have hgap : ‖z w - z v‖ ≤ Metric.diam (F.cell v : Set Plane) +
      Metric.diam (F.cell w : Set Plane) := by
    rw [← dist_eq_norm]
    calc dist (z w) (z v) ≤ dist (z w) q + dist q (z v) := dist_triangle _ _ _
      _ ≤ Metric.diam (F.cell w : Set Plane) + Metric.diam (F.cell v : Set Plane) :=
          add_le_add (Metric.dist_le_diam_of_mem (F.cell w).isCompact.isBounded (hz w) hqw) hqz
      _ = _ := add_comm _ _
  linarith

/-! ## The pathwise inputs, and the assembly -/

/-- **The pathwise inputs of the construction**, for one collapsed vertex path `X` and the
representatives `z`: the right regularity, edge-jump, finite-cut avoidance and no-infinite-sojourn
properties of the walk, density of the vertex times, the no-boundary-jump property of
`p:prop:purejump` for `z`, and existence of a càdlàg path through `z` at the vertex times. -/
structure PathInputs (F : IndexedCells V) (z : V → Plane) (X : ℝ≥0 → Option V) : Prop where
  rightRegular : RightRegular X
  edgeJumps : EdgeJumps F X
  avoidsCuts : AvoidsFiniteCutsAtNonvertexTimes X
  leaves : LeavesEveryVertex X
  dense : Dense {t | ∃ v, X t = some v}
  noBoundaryJumps : NoBoundaryJumps X z
  existsCadlag : ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧ ∀ t v, X t = some v → Z t = z v

/-- The canonical càdlàg path through `z` along `X` (unique when it exists, by density of the
vertex times). -/
noncomputable def pathExtension (z : V → Plane) (X : ℝ≥0 → Option V) : ℝ≥0 → Plane :=
  Classical.epsilon fun Z : ℝ≥0 → Plane => IsCadlag Z ∧ ∀ t v, X t = some v → Z t = z v

theorem PathInputs.pathExtension_spec {F : IndexedCells V} {z : V → Plane}
    {X : ℝ≥0 → Option V} (h : PathInputs F z X) :
    IsCadlag (pathExtension z X) ∧ ∀ t v, X t = some v → pathExtension z X t = z v :=
  Classical.epsilon_spec h.existsCadlag

theorem PathInputs.hasCompleteCollapsedHoldingIntervals {F : IndexedCells V} {z : V → Plane}
    {X : ℝ≥0 → Option V} (h : PathInputs F z X) : HasCompleteCollapsedHoldingIntervals F X :=
  hasCompleteCollapsedHoldingIntervals_of_inputs F h.rightRegular h.edgeJumps h.avoidsCuts
    h.leaves

/-- The extension is continuous at every nonvertex time. -/
theorem PathInputs.continuousAt_of_none {F : IndexedCells V} {z : V → Plane}
    {X : ℝ≥0 → Option V} (h : PathInputs F z X) {t : ℝ≥0} (ht : X t = none) :
    ContinuousAt (pathExtension z X) t :=
  SpatialExtensionConstruction.continuousAt_of_none h.pathExtension_spec.1
    h.pathExtension_spec.2 h.noBoundaryJumps h.avoidsCuts ht

/-- Every jump of the extension ends a complete holding interval. -/
theorem PathInputs.jump {F : IndexedCells V} {z : V → Plane} {X : ℝ≥0 → Option V}
    (h : PathInputs F z X) (t : ℝ≥0) (ht : 0 < t)
    (hne : Function.leftLim (pathExtension z X) t ≠ pathExtension z X t) :
    ∃ s v w, IsCollapsedHoldingInterval F X v w s t := by
  have hZ := h.pathExtension_spec
  obtain ⟨v, s₀, hs₀, hv₀⟩ := h.noBoundaryJumps _ hZ.1 hZ.2 t ht hne
  have hleft : Function.leftLim (pathExtension z X) t = z v := by
    have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    refine leftLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ico_mem_nhdsLT hs₀] with r hr
    exact (hZ.2 r v (hv₀ r hr)).symm
  obtain ⟨w, hw⟩ : ∃ w, X t = some w := by
    rcases hXt : X t with _ | w
    · exact absurd ⟨v, s₀, hs₀, hv₀⟩ (not_leftVertexConstant_of_none h.avoidsCuts hXt ht)
    · exact ⟨w, rfl⟩
  have hvw : v ≠ w := by
    intro hvw
    rw [← hvw] at hw
    exact hne (hleft.trans (hZ.2 t v hw).symm)
  obtain ⟨s, hs⟩ := exists_collapsedHoldingInterval_of_leftVertexConstant F h.rightRegular
    h.edgeJumps ⟨s₀, hs₀, hv₀⟩ hw hvw
  exact ⟨s, v, w, hs⟩

/-- **Continuity of the interpolation** from the pathwise inputs. -/
theorem PathInputs.continuous_interpolation [Countable V] {F : IndexedCells V}
    (hF : Geometry F) (hL : LargeCellsFinite F) {z : V → Plane} (hz : CellRepresentatives F z)
    {X : ℝ≥0 → Option V} (h : PathInputs F z X) :
    Continuous (interpolation F z X (pathExtension z X)) :=
  ContinuousInterpolation.continuous_interpolation F z h.hasCompleteCollapsedHoldingIntervals
    h.pathExtension_spec.1 h.pathExtension_spec.2 (fun _ ht => h.continuousAt_of_none ht) h.jump
    (fun _ ht _ hδ => smallJumps_of_largeCellsFinite F hF hL z hz h.avoidsCuts
      h.pathExtension_spec.2 ht (h.continuousAt_of_none ht) hδ)

/-- **The regular spatial extension**, for every lift with collapse `X`. -/
theorem PathInputs.regularSpatialExtension {F : IndexedCells V} {z : V → Plane}
    {X : ℝ≥0 → Option V} (h : PathInputs F z X) {Y : ℝ≥0 → State F}
    (hc : ∀ t, collapse (Y t) = X t) :
    RegularSpatialExtension F z Y (pathExtension z X) := by
  have hsub : {t | ∃ v, X t = some v} ⊆ {t | ∃ v, Y t = Sum.inl v} := by
    rintro t ⟨v, hv⟩
    exact ⟨v, EndLabelConstruction.collapse_eq_some_iff.1 (by rw [hc t]; exact hv)⟩
  exact regularSpatialExtension_of_inputs F hc h.pathExtension_spec.1 h.pathExtension_spec.2
    h.noBoundaryJumps h.edgeJumps h.rightRegular h.avoidsCuts (Dense.mono hsub h.dense)

/-- **The continuous interpolation**, for every lift with collapse `X`. -/
theorem PathInputs.isContinuousInterpolation [Countable V] {F : IndexedCells V}
    (hF : Geometry F) (hL : LargeCellsFinite F) {z : V → Plane} (hz : CellRepresentatives F z)
    {X : ℝ≥0 → Option V} (h : PathInputs F z X) {Y : ℝ≥0 → State F}
    (hc : ∀ t, collapse (Y t) = X t) :
    IsContinuousInterpolation F z Y (pathExtension z X)
      (interpolation F z X (pathExtension z X)) :=
  isContinuousInterpolation_interpolation F z hc h.hasCompleteCollapsedHoldingIntervals
    h.pathExtension_spec.1 h.pathExtension_spec.2 (fun _ ht => h.continuousAt_of_none ht) h.jump
    (fun _ ht _ hδ => smallJumps_of_largeCellsFinite F hF hL z hz h.avoidsCuts
      h.pathExtension_spec.2 ht (h.continuousAt_of_none ht) hδ)

/-! ## Transport along a homeomorphic time change -/

/-- A strictly monotone homeomorphism of `[0,∞)` maps a short enough right neighbourhood of
`t` into any prescribed right neighbourhood of `h t`. -/
theorem exists_pos_image_lt (h : ℝ≥0 ≃ₜ ℝ≥0) (hmono : StrictMono h) (t : ℝ≥0) {ε₀ : ℝ≥0}
    (hε₀ : 0 < ε₀) : ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s, s < t + ε → h s < h t + ε₀ := by
  have hsymm : StrictMono h.symm := fun a b hab =>
    hmono.lt_iff_lt.1 (by rw [h.apply_symm_apply, h.apply_symm_apply]; exact hab)
  have htu : t < h.symm (h t + ε₀) := by
    have h1 := hsymm (lt_add_of_pos_right (h t) hε₀)
    rwa [h.symm_apply_apply] at h1
  refine ⟨h.symm (h t + ε₀) - t, tsub_pos_of_lt htu, fun s hs => ?_⟩
  rw [add_tsub_cancel_of_le htu.le] at hs
  have h1 := hmono hs
  rwa [h.apply_symm_apply] at h1

theorem rightRegular_of_timeChange {X Y : ℝ≥0 → Option V} (htc : IsHomeomorphicTimeChange X Y)
    (hY : RightRegular Y) : RightRegular X := by
  obtain ⟨h, hmono, -, hXY⟩ := htc
  refine ⟨fun t ht => ?_, fun t ht y => ?_⟩
  · obtain ⟨x, hx⟩ := ht
    obtain ⟨ε₀, hε₀, hε₀Y⟩ := hY.1 (h t) ⟨x, by rw [← hXY t]; exact hx⟩
    obtain ⟨ε, hε, himg⟩ := exists_pos_image_lt h hmono t hε₀
    refine ⟨ε, hε, fun s hs => ?_⟩
    rw [hXY s, hXY t]
    exact hε₀Y (h s) ⟨hmono.monotone hs.1, himg s hs.2⟩
  · obtain ⟨ε₀, hε₀, hε₀Y⟩ := hY.2 (h t) (by rw [← hXY t]; exact ht) y
    obtain ⟨ε, hε, himg⟩ := exists_pos_image_lt h hmono t hε₀
    refine ⟨ε, hε, fun s hs => ?_⟩
    rw [hXY s]
    exact hε₀Y (h s) ⟨hmono hs.1, himg s hs.2⟩

theorem avoidsFiniteCuts_of_timeChange {X Y : ℝ≥0 → Option V}
    (htc : IsHomeomorphicTimeChange X Y) (hY : AvoidsFiniteCutsAtNonvertexTimes Y) :
    AvoidsFiniteCutsAtNonvertexTimes X := by
  obtain ⟨h, -, -, hXY⟩ := htc
  intro t ht K
  have h1 := hY (h t) (by rw [← hXY t]; exact ht) K
  refine ((h.continuous.tendsto t).eventually h1).mono fun s hs => ?_
  rw [hXY s]
  exact hs

theorem leavesEveryVertex_of_timeChange {X Y : ℝ≥0 → Option V}
    (htc : IsHomeomorphicTimeChange X Y) (hY : LeavesEveryVertex Y) : LeavesEveryVertex X := by
  obtain ⟨h, hmono, -, hXY⟩ := htc
  have hsymm : StrictMono h.symm := fun a b hab =>
    hmono.lt_iff_lt.1 (by rw [h.apply_symm_apply, h.apply_symm_apply]; exact hab)
  intro r v hr
  obtain ⟨q, hq, hqv⟩ := hY (h r) v (by rw [← hXY r]; exact hr)
  refine ⟨h.symm q, ?_, ?_⟩
  · have h1 := hsymm hq
    rwa [h.symm_apply_apply] at h1
  · rw [hXY, h.apply_symm_apply]
    exact hqv

theorem dense_vertexTimes_of_timeChange {X Y : ℝ≥0 → Option V}
    (htc : IsHomeomorphicTimeChange X Y) (hY : Dense {t | ∃ v, Y t = some v}) :
    Dense {t | ∃ v, X t = some v} := by
  obtain ⟨h, -, -, hXY⟩ := htc
  have hpre : {t | ∃ v, X t = some v} = h ⁻¹' {t | ∃ v, Y t = some v} := by
    ext t
    simp only [mem_setOf_eq, mem_preimage, hXY t]
  rw [hpre]
  exact hY.preimage h.isOpenMap

/-- **`PathInputs` transports along a homeomorphic time change.** -/
theorem PathInputs.of_timeChange {F : IndexedCells V} {z : V → Plane} {X Y : ℝ≥0 → Option V}
    (htc : IsHomeomorphicTimeChange X Y) (hY : PathInputs F z Y) : PathInputs F z X where
  rightRegular := rightRegular_of_timeChange htc hY.rightRegular
  edgeJumps := edgeJumps_of_timeChange F htc hY.edgeJumps
  avoidsCuts := avoidsFiniteCuts_of_timeChange htc hY.avoidsCuts
  leaves := leavesEveryVertex_of_timeChange htc hY.leaves
  dense := dense_vertexTimes_of_timeChange htc hY.dense
  noBoundaryJumps := noBoundaryJumps_of_timeChange htc hY.noBoundaryJumps
  existsCadlag := exists_cadlag_extension_of_timeChange htc hY.existsCadlag

end ReflectedGMS.ContinuousInterpolation
