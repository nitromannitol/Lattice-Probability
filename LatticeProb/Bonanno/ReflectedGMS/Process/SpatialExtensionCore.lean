/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.SpatialExtensionCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.PathwiseClockClauseLift

/-!
# The deterministic core of the spatial extension `M` (`p:prop:pathsextend`)

Split out of `Process/SpatialExtensionConstruction.lean` so that it can be checked with
minimal imports.  Everything here is pathwise and deterministic.

* **Collapse reduction.** Every clause of `RegularSpatialExtension F Φ Xexp M` depends on the
  end-labelled lift `Xexp` only through its collapse to the `Option V`-valued path.
* **From a càdlàg vertex-agreeing path to `RegularSpatialExtension`.**  Given
  `NoBoundaryJumps` (the pathwise consequence of `p:prop:purejump`), `EdgeJumps`, right
  regularity (properties (ii)/(ii at ∞) of `IsReflectedWalk`), two-sided finite-cut avoidance at
  nonvertex times and density of vertex times, all four clauses follow: continuity at end
  times, uniqueness (`eq_of_isRightContinuous_of_dense`), local boundedness (from càdlàg), and
  `HasOnlyOrdinaryJumps`, whose maximal holding interval is constructed as an infimum
  (`exists_collapsedHoldingInterval_of_leftVertexConstant`).
* **Time change.** Càdlàg vertex agreement, `NoBoundaryJumps` and `EdgeJumps` transport along
  a homeomorphic time change of `[0,∞)`.

Nothing here is probabilistic, and nothing certifies `hreg`.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.SpatialExtensionConstruction

open AreaClocks SpatialEnds InvarianceMainStatement PathwiseClockClauseLift

/-! ## Pathwise predicates on the collapsed path -/

section Pathwise

variable {V : Type*}

/-- The collapsed path sits at a single vertex on a left neighbourhood of `t`: its left limit
in the one-point compactification of the (discrete) vertex set is that vertex. -/
def LeftVertexConstant (X : ℝ≥0 → Option V) (t : ℝ≥0) : Prop :=
  ∃ v : V, ∃ s : ℝ≥0, s < t ∧ ∀ r ∈ Ico s t, X r = some v

/-- **Manuscript `p:prop:purejump`, pathwise consequence for the coordinate `Φ`.**  A càdlàg
plane-valued path which equals `Φ` at every vertex time of `X` can jump only at times at
which the path arrives from a vertex: no jump involves a nonvertex state.  It is stated for
every such càdlàg path; this loses nothing, since that path is unique once the vertex times
are dense (`eq_of_isRightContinuous_of_dense`), and it asserts no existence. -/
def NoBoundaryJumps (X : ℝ≥0 → Option V) (Φ : V → Plane) : Prop :=
  ∀ Z : ℝ≥0 → Plane, IsCadlag Z → (∀ t x, X t = some x → Z t = Φ x) →
    ∀ t : ℝ≥0, 0 < t → Function.leftLim Z t ≠ Z t → LeftVertexConstant X t

/-- Every jump of the vertex path out of a vertex sojourn traverses an ordinary edge. -/
def EdgeJumps (F : IndexedCells V) (X : ℝ≥0 → Option V) : Prop :=
  ∀ (t : ℝ≥0) (v w : V), (∃ s, s < t ∧ ∀ r ∈ Ico s t, X r = some v) → X t = some w →
    v ≠ w → F.graph.toSimpleGraph.Adj v w

/-- Properties (ii) and (ii at `∞`) of `ReflectedWalk.IsReflectedWalk`, read along one
sample path. -/
def RightRegular (X : ℝ≥0 → Option V) : Prop :=
  (∀ t, (∃ x, X t = some x) → ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Ico t (t + ε), X s = X t) ∧
  (∀ t, X t = none → ∀ y : V, ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Ioo t (t + ε), X s ≠ some y)

/-- Two-sided avoidance of every finite vertex cut at every nonvertex time
(`FiniteCutPathEndExtension.reflected_ae_eventually_notMem_finiteCut`, read pathwise). -/
def AvoidsFiniteCutsAtNonvertexTimes (X : ℝ≥0 → Option V) : Prop :=
  ∀ t, X t = none → ∀ K : Finset V, ∀ᶠ s in 𝓝 t, X s ∉ some '' (K : Set V)

/-- At a positive nonvertex time the path is not left-constant at any vertex. -/
theorem not_leftVertexConstant_of_none {X : ℝ≥0 → Option V}
    (hcut : AvoidsFiniteCutsAtNonvertexTimes X) {t : ℝ≥0} (ht : X t = none)
    (htpos : 0 < t) : ¬ LeftVertexConstant X t := by
  rintro ⟨v, s, hst, hv⟩
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  have h1 : ∀ᶠ r in 𝓝[<] t, X r ∉ some '' (({v} : Finset V) : Set V) :=
    (hcut t ht {v}).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ r in 𝓝[<] t, r ∈ Ico s t := Ico_mem_nhdsLT hst
  obtain ⟨r, hr1, hr2⟩ := (h1.and h2).exists
  exact hr1 ⟨v, by simp, (hv r hr2).symm⟩

/-- **Continuity at every nonvertex time**, from the absence of boundary jumps: a càdlàg
path is continuous at `t` iff its left limit is its value, and at a positive nonvertex time
a jump would force left-constancy at a vertex, which finite-cut avoidance forbids. -/
theorem continuousAt_of_none {X : ℝ≥0 → Option V} {Φ : V → Plane} {Z : ℝ≥0 → Plane}
    (hZ : IsCadlag Z) (hvert : ∀ t x, X t = some x → Z t = Φ x)
    (hnbj : NoBoundaryJumps X Φ) (hcut : AvoidsFiniteCutsAtNonvertexTimes X)
    {t : ℝ≥0} (ht : X t = none) : ContinuousAt Z t := by
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, hZ.isRightContinuous t⟩
  rcases eq_or_ne t 0 with rfl | htne
  · have h0 : Iio (0 : ℝ≥0) = ∅ :=
      Set.Iio_eq_empty_iff.2 (isMin_iff_forall_not_lt.2 fun _ => not_lt.2 zero_le)
    show Tendsto Z (𝓝[Iio (0 : ℝ≥0)] 0) (𝓝 (Z 0))
    rw [h0, nhdsWithin_empty]
    exact tendsto_bot
  · have htpos : 0 < t := pos_iff_ne_zero.2 htne
    have hlim : Function.leftLim Z t = Z t := by
      by_contra hne
      exact not_leftVertexConstant_of_none hcut ht htpos (hnbj Z hZ hvert t htpos hne)
    have hten := hZ.tendsto_nhdsLT_leftLim t
    rw [hlim] at hten
    exact hten

/-- **The maximal holding interval preceding a jump**, constructed as an infimum.  Given a
left-constancy interval at `v` ending at `t`, its maximal enlargement `[sInf S, t)` is a
complete holding interval in the sense of `SpatialEnds.IsHoldingInterval` (collapsed form):
right regularity puts the infimum itself inside the sojourn, and the edge-jump input supplies
adjacency of the two vertices. -/
theorem exists_collapsedHoldingInterval_of_leftVertexConstant (F : IndexedCells V)
    {X : ℝ≥0 → Option V} (hreg : RightRegular X) (hedge : EdgeJumps F X)
    {t : ℝ≥0} {v w : V} (hleft : ∃ s, s < t ∧ ∀ r ∈ Ico s t, X r = some v)
    (hw : X t = some w) (hvw : v ≠ w) :
    ∃ s, IsCollapsedHoldingInterval F X v w s t := by
  obtain ⟨s₀, hs₀, hv₀⟩ := hleft
  let S : Set ℝ≥0 := {r | r < t ∧ ∀ q ∈ Ico r t, X q = some v}
  have hS₀ : s₀ ∈ S := ⟨hs₀, hv₀⟩
  have hSne : S.Nonempty := ⟨s₀, hS₀⟩
  have hSbdd : BddBelow S := ⟨0, fun _ _ => zero_le⟩
  have hst : sInf S < t := lt_of_le_of_lt (csInf_le hSbdd hS₀) hs₀
  have hgt : ∀ q, sInf S < q → q < t → X q = some v := by
    intro q hsq hqt
    obtain ⟨r, hrS, hrq⟩ := exists_lt_of_csInf_lt hSne hsq
    exact hrS.2 q ⟨hrq.le, hqt⟩
  have hXs : X (sInf S) = some v := by
    by_contra hne
    obtain ⟨ε, hε, hεs⟩ : ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ q ∈ Ioo (sInf S) (sInf S + ε), X q ≠ some v := by
      by_cases hnone : X (sInf S) = none
      · exact hreg.2 (sInf S) hnone v
      · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hnone
        obtain ⟨ε, hε, h⟩ := hreg.1 (sInf S) ⟨u, hu⟩
        refine ⟨ε, hε, fun q hq hqv => hne ?_⟩
        rw [← h q ⟨hq.1.le, hq.2⟩]
        exact hqv
    obtain ⟨q, hq1, hq2⟩ :=
      exists_between (lt_min (lt_add_of_pos_right (sInf S) hε) hst)
    exact hεs q ⟨hq1, lt_of_lt_of_le hq2 (min_le_left _ _)⟩
      (hgt q hq1 (lt_of_lt_of_le hq2 (min_le_right _ _)))
  refine ⟨sInf S, hst, ?_, hw, hedge t v w ⟨s₀, hs₀, hv₀⟩ hw hvw, Or.inr ?_⟩
  · intro q hq
    rcases eq_or_lt_of_le hq.1 with h | h
    · rw [← h]
      exact hXs
    · exact hgt q h hq.2
  · intro r hr
    by_contra hcon
    push_neg at hcon
    obtain ⟨r', hr'1, hr'2⟩ := exists_between hr
    have hr'S : r' ∈ S := by
      refine ⟨hr'2.trans hst, fun q hq => ?_⟩
      rcases lt_or_ge q (sInf S) with hqs | hqs
      · exact hcon q ⟨lt_of_lt_of_le hr'1 hq.1, hqs⟩
      · rcases eq_or_lt_of_le hqs with h | h
        · rw [← h]
          exact hXs
        · exact hgt q h hq.2
    exact absurd (csInf_le hSbdd hr'S) (not_le.2 hr'2)

/-- **`HasOnlyOrdinaryJumps` from the two pathwise inputs.**  A jump of `Z` at `t > 0` comes
from a vertex `v` on the left (no boundary jumps) and lands at a vertex `w` (a nonvertex time
is not left-constant), the two are distinct (else there is no jump) and adjacent (edge
jumps), and the maximal sojourn at `v` is a complete holding interval. -/
theorem hasOnlyOrdinaryJumps_of_inputs (F : IndexedCells V) {Xexp : ℝ≥0 → State F}
    {X : ℝ≥0 → Option V} (hc : ∀ t, collapse (Xexp t) = X t) {Φ : V → Plane}
    {Z : ℝ≥0 → Plane} (hZ : IsCadlag Z) (hvert : ∀ t x, X t = some x → Z t = Φ x)
    (hnbj : NoBoundaryJumps X Φ) (hedge : EdgeJumps F X) (hreg : RightRegular X)
    (hcut : AvoidsFiniteCutsAtNonvertexTimes X) :
    HasOnlyOrdinaryJumps F Φ Xexp Z := by
  intro t ht hne
  obtain ⟨v, s₀, hs₀, hv₀⟩ := hnbj Z hZ hvert t ht hne
  have hleft : Function.leftLim Z t = Φ v := by
    haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    refine leftLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ico_mem_nhdsLT hs₀] with r hr
    exact (hvert r v (hv₀ r hr)).symm
  obtain ⟨w, hw⟩ : ∃ w, X t = some w := by
    by_cases hXt : X t = none
    · exact absurd ⟨v, s₀, hs₀, hv₀⟩ (not_leftVertexConstant_of_none hcut hXt ht)
    · exact Option.ne_none_iff_exists'.1 hXt
  have hvw : v ≠ w := by
    rintro rfl
    exact hne (hleft.trans (hvert t v hw).symm)
  obtain ⟨s, hs⟩ := exists_collapsedHoldingInterval_of_leftVertexConstant F hreg hedge
    ⟨s₀, hs₀, hv₀⟩ hw hvw
  exact ⟨s, v, w, (isHoldingInterval_iff_isCollapsedHoldingInterval hc v w s t).2 hs, hleft,
    hvert t w hw⟩

/-- Two right-continuous functions on `[0,∞)` that agree on a dense set are equal: a dense
set clusters at every point from the right. -/
theorem eq_of_isRightContinuous_of_dense {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {S : Set ℝ≥0} (hS : Dense S) {Z W : ℝ≥0 → Y}
    (hZ : IsRightContinuous Z) (hW : IsRightContinuous W)
    (hagree : ∀ s ∈ S, Z s = W s) : Z = W := by
  funext t
  have hmem : t ∈ closure (Ioi t ∩ S) := by
    have h1 : Ioi t ⊆ closure (Ioi t ∩ S) := hS.open_subset_closure_inter isOpen_Ioi
    have h2 : closure (Ioi t) ⊆ closure (Ioi t ∩ S) := closure_minimal h1 isClosed_closure
    rw [closure_Ioi] at h2
    exact h2 (Set.mem_Ici.2 le_rfl)
  have hne : (𝓝[Ioi t ∩ S] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hmem
  have hle : 𝓝[Ioi t ∩ S] t ≤ 𝓝[Ioi t] t := nhdsWithin_mono t inter_subset_left
  have hZt : Tendsto Z (𝓝[Ioi t ∩ S] t) (𝓝 (Z t)) := (hZ t).tendsto.mono_left hle
  have hWt : Tendsto W (𝓝[Ioi t ∩ S] t) (𝓝 (W t)) := (hW t).tendsto.mono_left hle
  have hcongr : Tendsto Z (𝓝[Ioi t ∩ S] t) (𝓝 (W t)) := by
    refine hWt.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hagree s hs.2).symm
  exact tendsto_nhds_unique hZt hcongr

/-- **`RegularSpatialExtension` from a càdlàg vertex-agreeing path and the pathwise inputs.**
Every clause is determined by the collapse `X` of the lift `Xexp`; the end labels play no
role.  Continuity at end times and the ordinary-jump clause come from `NoBoundaryJumps` and
`EdgeJumps`, uniqueness from density of the vertex times, and local boundedness from the
càdlàg property alone. -/
theorem regularSpatialExtension_of_inputs (F : IndexedCells V) {Xexp : ℝ≥0 → State F}
    {X : ℝ≥0 → Option V} (hc : ∀ t, collapse (Xexp t) = X t) {Φ : V → Plane}
    {Z : ℝ≥0 → Plane} (hZ : IsCadlag Z) (hvert : ∀ t x, X t = some x → Z t = Φ x)
    (hnbj : NoBoundaryJumps X Φ) (hedge : EdgeJumps F X) (hreg : RightRegular X)
    (hcut : AvoidsFiniteCutsAtNonvertexTimes X)
    (hdense : Dense {t : ℝ≥0 | ∃ v, Xexp t = Sum.inl v}) :
    RegularSpatialExtension F Φ Xexp Z := by
  have hext : IsSpatialExtension F Φ Xexp Z := by
    refine ⟨hZ, fun t v hv => hvert t v ?_,
      fun t ε hε => continuousAt_of_none hZ hvert hnbj hcut ?_⟩
    · have h1 : collapse (Xexp t) = some v := by simp [hv, collapse]
      rwa [hc t] at h1
    · have h1 : collapse (Xexp t) = none := by simp [hε, collapse]
      rwa [hc t] at h1
  refine ⟨hext, fun W hW => ?_, fun T => ?_,
    hasOnlyOrdinaryJumps_of_inputs F hc hZ hvert hnbj hedge hreg hcut⟩
  · refine eq_of_isRightContinuous_of_dense hdense hW.1.isRightContinuous
      hZ.isRightContinuous ?_
    rintro s ⟨v, hv⟩
    rw [hW.2.1 s v hv, hext.2.1 s v hv]
  · exact isBounded_image_of_isCadlag_of_isCompact hZ isCompact_Icc

end Pathwise

/-! ## Transport along a homeomorphic time change of `[0,∞)` -/

section TimeChange

variable {V : Type*}

/-- Precomposition with a strictly increasing homeomorphism of `[0,∞)` preserves the càdlàg
property: it maps right neighbourhoods to right neighbourhoods and `𝓝[<] t` to
`𝓝[<] (h t)`. -/
theorem isCadlag_comp_of_strictMono {Y : Type*} [TopologicalSpace Y] (h : ℝ≥0 ≃ₜ ℝ≥0)
    (hmono : StrictMono h) {W : ℝ≥0 → Y} (hW : IsCadlag W) :
    IsCadlag (fun t => W (h t)) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · exact (hW.isRightContinuous (h t)).comp h.continuous.continuousWithinAt
      (fun s hs => hmono hs)
  · obtain ⟨l, hl⟩ := hW.tendsto_nhdsLT (h t)
    refine ⟨l, hl.comp ?_⟩
    exact tendsto_nhdsWithin_iff.2
      ⟨h.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun s hs => hmono hs⟩

/-- A càdlàg vertex-agreeing extension transports along a homeomorphic time change. -/
theorem exists_cadlag_extension_of_timeChange {X Y : ℝ≥0 → Option V} {Φ : V → Plane}
    (htc : IsHomeomorphicTimeChange X Y)
    (hY : ∃ W : ℝ≥0 → Plane, IsCadlag W ∧ ∀ t x, Y t = some x → W t = Φ x) :
    ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧ ∀ t x, X t = some x → Z t = Φ x := by
  obtain ⟨h, hmono, -, hXY⟩ := htc
  obtain ⟨W, hW, hvert⟩ := hY
  refine ⟨fun t => W (h t), isCadlag_comp_of_strictMono h hmono hW, fun t x hx => ?_⟩
  exact hvert (h t) x (by rw [← hXY t]; exact hx)

/-- The edge-jump property transports along a homeomorphic time change. -/
theorem edgeJumps_of_timeChange (F : IndexedCells V) {X Y : ℝ≥0 → Option V}
    (htc : IsHomeomorphicTimeChange X Y) (hY : EdgeJumps F Y) : EdgeJumps F X := by
  obtain ⟨h, hmono, -, hXY⟩ := htc
  intro t v w hleft hw hvw
  obtain ⟨s, hst, hv⟩ := hleft
  refine hY (h t) v w ⟨h s, hmono hst, fun r hr => ?_⟩ (by rw [← hXY t]; exact hw) hvw
  have hr' : h.symm r ∈ Ico s t := by
    constructor
    · exact hmono.le_iff_le.1 (by rw [h.apply_symm_apply]; exact hr.1)
    · exact hmono.lt_iff_lt.1 (by rw [h.apply_symm_apply]; exact hr.2)
  have hv' := hv (h.symm r) hr'
  rwa [hXY, h.apply_symm_apply] at hv'

/-- The no-boundary-jump property transports along a homeomorphic time change: the
transported path `Z ∘ h.symm` is càdlàg and vertex-agreeing for `Y`, its left limits are those
of `Z` at the corresponding times, and left-constancy intervals are mapped back. -/
theorem noBoundaryJumps_of_timeChange {X Y : ℝ≥0 → Option V} {Φ : V → Plane}
    (htc : IsHomeomorphicTimeChange X Y) (hY : NoBoundaryJumps Y Φ) :
    NoBoundaryJumps X Φ := by
  obtain ⟨h, hmono, -, hXY⟩ := htc
  have hsymm : StrictMono h.symm := fun a b hab =>
    hmono.lt_iff_lt.1 (by rw [h.apply_symm_apply, h.apply_symm_apply]; exact hab)
  intro Z hZ hvert t ht hne
  have hWcad : IsCadlag (fun u => Z (h.symm u)) := isCadlag_comp_of_strictMono h.symm hsymm hZ
  have hWvert : ∀ u x, Y u = some x → Z (h.symm u) = Φ x := by
    intro u x hu
    exact hvert (h.symm u) x (by rw [hXY, h.apply_symm_apply]; exact hu)
  have htpos : 0 < h t := lt_of_le_of_lt zero_le (hmono ht)
  have hneW : Function.leftLim (fun u => Z (h.symm u)) (h t) ≠
      (fun u => Z (h.symm u)) (h t) := by
    haveI : (𝓝[<] (h t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    have hlim : Function.leftLim (fun u => Z (h.symm u)) (h t) = Function.leftLim Z t := by
      refine leftLim_eq_of_tendsto ((hZ.tendsto_nhdsLT_leftLim t).comp ?_)
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun u hu => ?_⟩
      · have h1 : Tendsto h.symm (𝓝 (h t)) (𝓝 t) := by
          have h2 := h.symm.continuous.tendsto (h t)
          rwa [h.symm_apply_apply] at h2
        exact h1.mono_left nhdsWithin_le_nhds
      · exact (hsymm hu).trans_eq (h.symm_apply_apply t)
    rw [hlim]
    show Function.leftLim Z t ≠ Z (h.symm (h t))
    rw [h.symm_apply_apply]
    exact hne
  obtain ⟨v, s', hs', hv'⟩ := hY _ hWcad hWvert (h t) htpos hneW
  refine ⟨v, h.symm s', (hsymm hs').trans_eq (h.symm_apply_apply t), fun r hr => ?_⟩
  rw [hXY]
  exact hv' (h r) ⟨(h.apply_symm_apply s').symm.trans_le (hmono.monotone hr.1), hmono hr.2⟩

end TimeChange


end ReflectedGMS.SpatialExtensionConstruction
