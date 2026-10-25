module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/Harmonic.lean and BouRabeeGwynne/HarmonicCutoff.lean.
-/
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-!
# Harmonic functions on open sets and harmonic cutoffs

Classical `C²` harmonicity on subsets of a finite-dimensional real inner product space, together
with its bridge to Mathlib's `InnerProductSpace.HarmonicOnNhd`. It also gives compactly supported
`C²` extensions of a harmonic function near a compact set, which agree with it on a neighborhood
of that set.
-/

open Set Function Filter
open scoped Topology
open Laplacian

namespace LatticeProb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Classical `C²` harmonicity on a set `U`: `h` is twice continuously differentiable on `U` and
its Laplacian vanishes at every point of `U`. For an open set `U` this is the notion of
`InnerProductSpace.HarmonicOnNhd`, see `isHarmonicOn_iff_harmonicOnNhd`. -/
def IsHarmonicOn (h : E → ℝ) (U : Set E) : Prop :=
  ContDiffOn ℝ 2 h U ∧ ∀ x ∈ U, Δ h x = 0

/-- A function harmonic on `U` is `C²` on `U`. -/
lemma IsHarmonicOn.contDiffOn {h : E → ℝ} {U : Set E} (hh : IsHarmonicOn h U) :
    ContDiffOn ℝ 2 h U := hh.1

/-- The Laplacian of a function harmonic on `U` vanishes at every point of `U`. -/
lemma IsHarmonicOn.laplacian_eq_zero {h : E → ℝ} {U : Set E} (hh : IsHarmonicOn h U)
    {x : E} (hx : x ∈ U) : Δ h x = 0 :=
  hh.2 x hx

/-- `h` is harmonic on an open set containing `closure U`. -/
def HarmonicNearClosure (h : E → ℝ) (U : Set E) : Prop :=
  ∃ W : Set E, IsOpen W ∧ closure U ⊆ W ∧ IsHarmonicOn h W

/-- If `h` is harmonic near `closure U`, then it is harmonic on `U`. -/
lemma HarmonicNearClosure.harmonicOn {h : E → ℝ} {U : Set E}
    (hh : HarmonicNearClosure h U) : IsHarmonicOn h U := by
  rcases hh with ⟨W, hWopen, hUW, hhW⟩
  constructor
  · exact hhW.1.mono (subset_closure.trans hUW)
  · intro x hx
    exact hhW.2 x (hUW (subset_closure hx))

/-- On an open set, `IsHarmonicOn` is Mathlib's notion of harmonicity in a neighborhood. -/
theorem isHarmonicOn_iff_harmonicOnNhd {h : E → ℝ} {U : Set E} (hU : IsOpen U) :
    IsHarmonicOn h U ↔ InnerProductSpace.HarmonicOnNhd h U := by
  constructor
  · rintro ⟨hc, hl⟩ x hx
    refine ⟨hc.contDiffAt (hU.mem_nhds hx), ?_⟩
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hl y hy
  · intro hh
    exact ⟨fun x hx => (hh x hx).1.contDiffWithinAt, fun x hx => (hh x hx).2.eq_of_nhds⟩

/-- Harmonicity near `closure U` is Mathlib's notion of harmonicity in a neighborhood of
`closure U`. -/
theorem harmonicNearClosure_iff {h : E → ℝ} {U : Set E} :
    HarmonicNearClosure h U ↔ InnerProductSpace.HarmonicOnNhd h (closure U) := by
  constructor
  · rintro ⟨W, hW, hUW, hhW⟩ x hx
    exact (isHarmonicOn_iff_harmonicOnNhd hW).mp hhW x (hUW hx)
  · intro hh
    exact ⟨{x | InnerProductSpace.HarmonicAt h x}, InnerProductSpace.isOpen_setOf_harmonicAt h,
      fun x hx => hh x hx, (isHarmonicOn_iff_harmonicOnNhd
        (InnerProductSpace.isOpen_setOf_harmonicAt h)).mpr (fun x hx => hx)⟩

/-- Extend a `C²` function near a compact set by multiplying it by a smooth cutoff. The resulting
function is `C²` with compact support, and it agrees with `h` on an open neighborhood of the
compact set, so its derivatives there agree as well. -/
theorem exists_contDiff_compactSupport_eq_near_compact
    {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    {h : E → ℝ} (hh : ContDiffOn ℝ 2 h W) :
    ∃ (g : E → ℝ) (V : Set E),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ ContDiff ℝ 2 g ∧
      HasCompactSupport g ∧ tsupport g ⊆ W ∧ EqOn g h V := by
  obtain ⟨L, hL, hKL, hLW⟩ := exists_compact_between hK hW hKW
  obtain ⟨O, hO, hLO, hOW, hOc⟩ :=
    exists_open_between_and_isCompact_closure hL hW hLW
  obtain ⟨χ, hχ, _, hχsupp, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := modelWithCornersSelf ℝ E) (n := 2)
      hO hL.isClosed hLO
  have hχ2 : ContDiff ℝ 2 χ := contMDiff_iff_contDiff.mp hχ
  let g : E → ℝ := fun x => χ x * h x
  have hχcompact : HasCompactSupport χ := by
    simpa only [HasCompactSupport, tsupport, hχsupp] using hOc
  have hgsupport : tsupport g ⊆ W :=
    tsupport_mul_subset_left.trans (by simpa only [tsupport, hχsupp] using hOW)
  have hg : ContDiff ℝ 2 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ W
    · exact hχ2.contDiffAt.mul (hh.contDiffAt (hW.mem_nhds hx))
    · have hxO : x ∈ (closure O)ᶜ := fun hmem => hx (hOW hmem)
      have heq : g =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxO] with y hy
        have hyO : y ∉ O := fun hy' => hy (subset_closure hy')
        have hχzero : χ y = 0 := by
          apply notMem_support.mp
          simpa only [hχsupp] using hyO
        exact mul_eq_zero_of_left hχzero _
      exact contDiffAt_const.congr_of_eventuallyEq heq
  refine ⟨g, interior L, isOpen_interior, hKL, interior_subset.trans hLW,
    hg, hχcompact.mul_right, hgsupport, ?_⟩
  intro x hx
  change χ x * h x = h x
  rw [(hχone x).mp (interior_subset hx), one_mul]

/-- A function harmonic on `W` has, near any compact `K ⊆ W`, a compactly supported `C²`
extension that is harmonic on an open neighborhood of `K`. The Laplacian is local, so the
extension inherits harmonicity from `h` on the neighborhood where they agree. -/
theorem IsHarmonicOn.exists_compactSupport_eq_near_compact
    {h : E → ℝ} {K W : Set E} (hh : IsHarmonicOn h W)
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ (g : E → ℝ) (V : Set E),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ W ∧ ContDiff ℝ 2 g ∧
      HasCompactSupport g ∧ tsupport g ⊆ W ∧ EqOn g h V ∧ IsHarmonicOn g V := by
  obtain ⟨g, V, hV, hKV, hVW, hg, hgc, hgs, heq⟩ :=
    exists_contDiff_compactSupport_eq_near_compact hK hW hKW hh.contDiffOn
  refine ⟨g, V, hV, hKV, hVW, hg, hgc, hgs, heq, hg.contDiffOn, ?_⟩
  intro x hx
  have hlocal : g =ᶠ[𝓝 x] h := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact heq hy
  rw [(InnerProductSpace.laplacian_congr_nhds hlocal).eq_of_nhds]
  exact hh.laplacian_eq_zero (hVW hx)

namespace HarmonicBridgeExample

/-- The constant function `1` is harmonic on the open unit ball of `EuclideanSpace ℝ (Fin 2)`,
checked through `isHarmonicOn_iff_harmonicOnNhd`. -/
theorem const_isHarmonicOn_ball :
    IsHarmonicOn (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) (Metric.ball 0 1) :=
  (isHarmonicOn_iff_harmonicOnNhd Metric.isOpen_ball).mpr
    (InnerProductSpace.harmonicOnNhd_const _)

/-- The constant function `1` is harmonic near the closure of the open unit ball of
`EuclideanSpace ℝ (Fin 2)`, checked through `harmonicNearClosure_iff`. -/
theorem const_harmonicNearClosure_ball :
    HarmonicNearClosure (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) (Metric.ball 0 1) :=
  harmonicNearClosure_iff.mpr (InnerProductSpace.harmonicOnNhd_const _)

end HarmonicBridgeExample

end LatticeProb
