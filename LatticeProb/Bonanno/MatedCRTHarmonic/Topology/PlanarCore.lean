/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Topology.PlanarCore at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Topology.Connected.LocallyPathConnected
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski

set_option autoImplicit false

/-!
# Generic planar separation lemmas

This module collects the curve-level facts used by the §4 proof. It reuses the loop degree,
Eilenberg criterion, and Janiszewski theorem from QuantumZipper, and the path-based `Disconnects`
definition from LQGMetric.
-/

namespace MatedCRTHarmonic.Topology

open Set
open QuantumZipper.CA.Topo

/-- A set separates `a` from `b` when every path between them meets the set. -/
def Separates (S : Set ℂ) (a b : ℂ) : Prop :=
  ∀ γ : Path a b, ∃ t, γ t ∈ S

/-- The local path-separation predicate is the singleton-endpoint instance of the host API. -/
theorem separates_iff_disconnects {S : Set ℂ} {a b : ℂ} :
    Separates S a b ↔ LQGMetric.Disconnects S {a} {b} := by
  constructor
  · intro h x y γ hx hy
    simp only [mem_singleton_iff] at hx hy
    subst x
    subst y
    obtain ⟨t, ht⟩ := h γ
    exact ⟨γ t, ⟨t, rfl⟩, ht⟩
  · intro h γ
    obtain ⟨z, hz, hzS⟩ := h a b γ (by simp) (by simp)
    obtain ⟨t, rfl⟩ := hz
    exact ⟨t, hzS⟩

/-- For a closed planar set, component separation in its complement is equivalent to having a
path in the complement. -/
theorem mem_connectedComponentIn_compl_iff_exists_path_avoiding
    {S : Set ℂ} (hS : IsClosed S) {a b : ℂ} :
    b ∈ connectedComponentIn Sᶜ a ↔ ∃ γ : Path a b, ∀ t, γ t ∉ S := by
  constructor
  · intro hb
    have ha : a ∈ Sᶜ := connectedComponentIn_nonempty_iff.mp ⟨b, hb⟩
    let C := connectedComponentIn Sᶜ a
    have hCopen : IsOpen C := hS.isOpen_compl.connectedComponentIn
    have hCconnected : IsConnected C := isConnected_connectedComponentIn_iff.mpr ha
    have hCpath : IsPathConnected C := hCopen.isConnected_iff_isPathConnected.mp hCconnected
    obtain ⟨γ, hγ⟩ := hCpath.joinedIn a (mem_connectedComponentIn ha) b hb
    exact ⟨γ, fun t ht => connectedComponentIn_subset Sᶜ a (hγ t) ht⟩
  · rintro ⟨γ, hγ⟩
    have hrange : range γ ⊆ Sᶜ := by
      rintro z ⟨t, rfl⟩
      exact hγ t
    have hpre : IsPreconnected (range γ) := isPreconnected_range γ.continuous
    have hsubset := hpre.subset_connectedComponentIn (x := a) ⟨0, γ.source⟩ hrange
    exact hsubset ⟨1, γ.target⟩

/-- In an open planar set, belonging to the same connected component is equivalent to being joined
by a path that stays in the set. -/
theorem mem_connectedComponentIn_open_iff_exists_path {U : Set ℂ} (hU : IsOpen U)
    {a b : ℂ} :
    b ∈ connectedComponentIn U a ↔ ∃ γ : Path a b, ∀ t, γ t ∈ U := by
  simpa [compl_compl] using
    (mem_connectedComponentIn_compl_iff_exists_path_avoiding (S := Uᶜ) hU.isClosed_compl
      (a := a) (b := b))

/-- A closed set separates `a` from `b` exactly when the points lie in distinct components of its
complement. -/
theorem separates_iff_not_mem_connectedComponentIn_compl
    {S : Set ℂ} (hS : IsClosed S) {a b : ℂ} :
    Separates S a b ↔ b ∉ connectedComponentIn Sᶜ a := by
  constructor
  · intro hsep hb
    obtain ⟨γ, hγ⟩ := mem_connectedComponentIn_compl_iff_exists_path_avoiding hS |>.mp hb
    obtain ⟨t, ht⟩ := hsep γ
    exact hγ t ht
  · intro hnotsep γ
    by_contra hmiss
    apply hnotsep
    apply (mem_connectedComponentIn_compl_iff_exists_path_avoiding hS).mpr
    refine ⟨γ, ?_⟩
    intro t ht
    exact hmiss ⟨t, ht⟩

/-- An arc does not separate two points outside it. -/
theorem not_separates_of_isArcSet {A : Set ℂ} (hA : IsArcSet A) {a b : ℂ}
    (ha : a ∉ A) (hb : b ∉ A) : ¬ Separates A a b := by
  rcases hA with ⟨g, hgc, hgi, rfl⟩
  have hAcompact : IsCompact (g '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hgc
  have hden : ∀ z ∈ g '' Icc (0 : ℝ) 1, z - b ≠ 0 := by
    intro z hz hz0
    apply hb
    rw [← sub_eq_zero.mp hz0]
    exact hz
  have hfun : ContinuousOn (fun z : ℂ => (z - a) / (z - b))
      (g '' Icc (0 : ℝ) 1) := by
    exact (continuousOn_id.sub continuousOn_const).div
      (continuousOn_id.sub continuousOn_const) hden
  have hnonzero : ∀ z ∈ g '' Icc (0 : ℝ) 1, (z - a) / (z - b) ≠ 0 := by
    intro z hz hz0
    have hnum : z - a ≠ 0 := sub_ne_zero.mpr (fun heq => ha (heq ▸ hz))
    have hden : z - b ≠ 0 := sub_ne_zero.mpr (fun heq => hb (heq ▸ hz))
    exact (div_ne_zero hnum hden) hz0
  obtain ⟨L, hLc, hLe⟩ := hasLogOn_of_arc hgc hgi hfun hnonzero
  have hcomp := not_separates_of_hasLogOn hAcompact ha hb ⟨L, hLc, hLe⟩
  intro hsep
  exact ((separates_iff_not_mem_connectedComponentIn_compl hAcompact.isClosed).mp hsep) hcomp

/-- Two points outside an arc lie in the same component of its complement. -/
theorem mem_connectedComponentIn_compl_of_isArcSet {A : Set ℂ} (hA : IsArcSet A)
    {a b : ℂ} (ha : a ∉ A) (hb : b ∉ A) : b ∈ connectedComponentIn Aᶜ a := by
  by_contra hcomp
  exact not_separates_of_isArcSet hA ha hb
    ((separates_iff_not_mem_connectedComponentIn_compl hA.isCompact.isClosed).mpr hcomp)

/-- If the degrees of a closed curve about two points differ, every path between those points
meets the curve. -/
theorem separates_of_loopDeg_ne {γ : C(unitInterval, ℂ)} (hclosed : γ 0 = γ 1)
    {a b : ℂ} (ha : ∀ t, γ t - a ≠ 0) (hb : ∀ t, γ t - b ≠ 0)
    (hdeg : loopDeg (γ - ContinuousMap.const unitInterval a) ha ≠
      loopDeg (γ - ContinuousMap.const unitInterval b) hb) :
    Separates (range γ) a b := by
  intro β
  by_contra hmiss
  have havoid : ∀ s, β s ∉ range γ := by
    intro s hs
    apply hmiss
    exact ⟨s, hs⟩
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => γ p.1 - β p.2,
      (γ.continuous.comp continuous_fst).sub (β.continuous.comp continuous_snd)⟩
  have hHnz : ∀ p, H p ≠ 0 := by
    rintro ⟨t, s⟩
    apply sub_ne_zero.mpr
    intro hEq
    exact havoid s ⟨t, hEq⟩
  have hHclosed : ∀ s, H (0, s) = H (1, s) := by
    intro s
    simp [H, hclosed]
  have hdegEq :
      loopDeg (slice H 0) (fun _ => hHnz _) = loopDeg (slice H 1) (fun _ => hHnz _) :=
    loopDeg_homotopy H hHnz hHclosed
  have hleft : slice H 0 = γ - ContinuousMap.const unitInterval a := by
    ext t
    simp only [slice, H, ContinuousMap.coe_mk, ContinuousMap.sub_apply,
      ContinuousMap.const_apply]
    rw [β.source]
  have hright : slice H 1 = γ - ContinuousMap.const unitInterval b := by
    ext t
    simp only [slice, H, ContinuousMap.coe_mk, ContinuousMap.sub_apply,
      ContinuousMap.const_apply]
    rw [β.target]
  apply hdeg
  simpa only [hleft, hright] using hdegEq

/-- Janiszewski transfer for a curve whose trace is the union of an arc and a compact set. This
is the topological core used when a junction subarc is removed from a closed walk. -/
theorem separates_of_union_with_arc {A K : Set ℂ} (hA : IsArcSet A) (hK : IsCompact K)
    {a b : ℂ} (ha : a ∉ A ∪ K) (hb : b ∉ A ∪ K)
    (hAK : IsPreconnected (A ∩ K)) (hsep : Separates (A ∪ K) a b) :
    Separates K a b := by
  by_contra hKsep
  have hAclosed : IsClosed A := hA.isCompact.isClosed
  have hUclosed : IsClosed (A ∪ K) := hAclosed.union hK.isClosed
  have hAcomp : b ∈ connectedComponentIn Aᶜ a := by
    by_contra hnotcomp
    exact not_separates_of_isArcSet hA (fun hz => ha (Or.inl hz)) (fun hz => hb (Or.inl hz))
      ((separates_iff_not_mem_connectedComponentIn_compl hAclosed).mpr hnotcomp)
  have hKcomp : b ∈ connectedComponentIn Kᶜ a := by
    by_contra hnotcomp
    exact hKsep ((separates_iff_not_mem_connectedComponentIn_compl hK.isClosed).mpr hnotcomp)
  have hUnionComp := janiszewski hA.isCompact hK hAK ha hb hAcomp hKcomp
  have hUnionNotSep : ¬ Separates (A ∪ K) a b := by
    intro hUnionSep
    exact ((separates_iff_not_mem_connectedComponentIn_compl hUclosed).mp hUnionSep) hUnionComp
  exact hUnionNotSep hsep

/-- Curve-level form of the Janiszewski transfer: if the trace of a closed curve is an arc joined
to a compact subtrace along a preconnected intersection, separation transfers to that subtrace. -/
theorem separates_of_curve_trace_eq_union_with_arc {γ : C(unitInterval, ℂ)} {A K : Set ℂ}
    (htrace : range γ = A ∪ K) (hA : IsArcSet A) (hK : IsCompact K) {a b : ℂ}
    (ha : a ∉ range γ) (hb : b ∉ range γ) (hAK : IsPreconnected (A ∩ K))
    (hsep : Separates (range γ) a b) : Separates K a b := by
  have ha' : a ∉ A ∪ K := by simpa [← htrace] using ha
  have hb' : b ∉ A ∪ K := by simpa [← htrace] using hb
  apply separates_of_union_with_arc hA hK ha' hb' hAK
  simpa [htrace] using hsep

end MatedCRTHarmonic.Topology
