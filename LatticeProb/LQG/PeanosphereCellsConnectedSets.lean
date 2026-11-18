import LatticeProb.LQG.ShiftedSidedContact
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry

/-!
# Cells of the mated-CRT map meeting a connected set

Gwynne–Miller–Sheffield, *The Tutte embedding of the mated-CRT map converges to Liouville quantum
gravity* (arXiv 1705.11161), Proposition 3.1, verify the hypothesis "connectivity along lines" of
their abstract invariance principle for the space-filling SLE cells: for every horizontal or
vertical segment, the cells meeting it, with the edges of the mated-CRT map joining them, form a
connected graph. Their argument has two steps: the cells meeting a connected set are chained by
cells sharing a point of that set, and the cells through a common point are chained by cells
sharing a non-trivial boundary arc.

The second step is Theorem B of the Peanosphere route (`RouteM.thmB_induce_connected`). This file
proves the first step for an arbitrary locally finite closed cover by cells, and combines the two.

## Main statements

* `LatticeProb.connected_induce_verticesMeeting_of_pointConnected`: for a locally finite family of
  closed sets covering the plane, if the cells through each point induce a connected subgraph of a
  graph `G`, then so do the cells meeting any connected set.
* `MatedCRTHarmonic.RouteM.Peanosphere.connected_induce_verticesMeeting`: for a Peanosphere and a
  positive mesh, the cells `η([ε(x-1), εx])` meeting a connected set induce a connected subgraph of
  the mated-CRT map.
* `MatedCRTHarmonic.MoTInput.ae_connected_induce_verticesMeeting_time_translate`: under the
  mating-of-trees coupling, almost surely, for every phase `c`, every positive mesh and every
  connected set, the same holds for the cells of the time-translated curve.
-/

open Set

namespace LatticeProb

open MatedCRTHarmonic

/-- **Cells meeting a connected set.** Let `J` be a locally finite family of closed subsets of the
plane covering it, and suppose that, for every point `q`, the indices `x` with `q ∈ J x` induce a
connected subgraph of `G`. Then for every connected set `S`, the indices of the cells meeting `S`
induce a connected subgraph of `G`. -/
theorem connected_induce_verticesMeeting_of_pointConnected {V : Type*} (G : SimpleGraph V)
    (J : V → Set ℂ) (hcover : ∀ q : ℂ, ∃ x, q ∈ J x) (hclosed : ∀ x, IsClosed (J x))
    (hlf : LocallyFinite J) (hpt : ∀ q : ℂ, (G.induce {x | q ∈ J x}).Connected)
    {S : Set ℂ} (hS : IsConnected S) :
    (G.induce (verticesMeeting J S)).Connected := by
  classical
  set W := verticesMeeting J S with hW
  obtain ⟨q₀, hq₀⟩ := hS.nonempty
  obtain ⟨x₀, hx₀⟩ := hcover q₀
  have hx₀W : x₀ ∈ W := ⟨q₀, hx₀, hq₀⟩
  -- the union of the cells with indices in `C` is closed
  have hcl : ∀ C : Set V, IsClosed (⋃ x : C, J x) := fun C =>
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion fun x => hclosed x
  have key : ∀ (y : V) (hy : y ∈ W), (G.induce W).Reachable ⟨x₀, hx₀W⟩ ⟨y, hy⟩ := by
    by_contra hcon
    simp only [not_forall] at hcon
    obtain ⟨y₁, hy₁W, hy₁⟩ := hcon
    let A : Set V := {x | ∃ hx : x ∈ W, (G.induce W).Reachable ⟨x₀, hx₀W⟩ ⟨x, hx⟩}
    let B : Set V := {x | ∃ hx : x ∈ W, ¬ (G.induce W).Reachable ⟨x₀, hx₀W⟩ ⟨x, hx⟩}
    have hcover' : S ⊆ (⋃ x : A, J x) ∪ (⋃ x : B, J x) := by
      intro q hq
      obtain ⟨x, hx⟩ := hcover q
      have hxW : x ∈ W := ⟨q, hx, hq⟩
      by_cases hr : (G.induce W).Reachable ⟨x₀, hx₀W⟩ ⟨x, hxW⟩
      · exact Or.inl (mem_iUnion.2 ⟨⟨x, hxW, hr⟩, hx⟩)
      · exact Or.inr (mem_iUnion.2 ⟨⟨x, hxW, hr⟩, hx⟩)
    have hSA : (S ∩ ⋃ x : A, J x).Nonempty :=
      ⟨q₀, hq₀, mem_iUnion.2 ⟨⟨x₀, hx₀W, SimpleGraph.Reachable.refl _⟩, hx₀⟩⟩
    have hSB : (S ∩ ⋃ x : B, J x).Nonempty := by
      obtain ⟨q₁, hq₁J, hq₁S⟩ := id hy₁W
      exact ⟨q₁, hq₁S, mem_iUnion.2 ⟨⟨y₁, hy₁W, hy₁⟩, hq₁J⟩⟩
    obtain ⟨q, hqS, hqA, hqB⟩ :=
      isPreconnected_closed_iff.1 hS.isPreconnected _ _ (hcl A) (hcl B) hcover' hSA hSB
    obtain ⟨⟨a, haW, hra⟩, hqa⟩ := mem_iUnion.1 hqA
    obtain ⟨⟨b, hbW, hrb⟩, hqb⟩ := mem_iUnion.1 hqB
    have hsub : {x | q ∈ J x} ≤ W := fun x hx => ⟨q, hx, hqS⟩
    have hab : (G.induce W).Reachable ⟨a, haW⟩ ⟨b, hbW⟩ :=
      ((hpt q).preconnected ⟨a, hqa⟩ ⟨b, hqb⟩).map (SimpleGraph.induceHomOfLE G hsub).toHom
    exact hrb (hra.trans hab)
  have : Nonempty W := ⟨⟨x₀, hx₀W⟩⟩
  exact ⟨fun u v => (key u.1 u.2).symm.trans (key v.1 v.2)⟩

end LatticeProb

namespace MatedCRTHarmonic.RouteM

open MatedCRTHarmonic

variable {ε : ℝ} {ω : MatedCRT.Path2} {η : ℝ → ℂ}

/-- **Connectivity of the cells meeting a connected set** (Gwynne–Miller–Sheffield, arXiv
1705.11161, proof of Proposition 3.1, "connectivity along lines"): for a Peanosphere and a positive
mesh `ε`, for every connected `S ⊆ ℂ` the vertices `x` whose cells `η([ε(x-1), εx])` meet `S`
induce a connected subgraph of the mated-CRT map. In particular this holds for every horizontal or
vertical segment. -/
theorem Peanosphere.connected_induce_verticesMeeting (P : Peanosphere ω η) (hε : 0 < ε)
    (h : MatedCRT.IsLocallyFinite ε ω) {S : Set ℂ} (hS : IsConnected S) :
    ((MatedCRT.graph ε ω h).adj.induce
      (verticesMeeting (fun x : ℤ => η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) S)).Connected := by
  refine LatticeProb.connected_induce_verticesMeeting_of_pointConnected _ _ (fun q => ?_)
    (fun x => (isCompact_Icc.image P.cont).isClosed) ?_ (fun q => thmB_induce_connected P hε h q) hS
  · obtain ⟨t, ht⟩ := P.surj q
    obtain ⟨x, hx⟩ := thmB_exists_mem_Icc hε t
    exact ⟨x, t, hx, ht⟩
  · exact MoTInput.locallyFinite_curve_cellsAt (η := ⟨η, P.cont⟩) hε P.transient

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.RouteM MeasureTheory
open scoped NNReal

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Under the mating-of-trees coupling, almost surely, simultaneously for every phase `c`, every
positive mesh `ε` and every connected set `S`, the cells `η([ε(x-1) + c, εx + c])` meeting `S`
induce a connected subgraph of the mated-CRT map of the time-translated boundary path. -/
theorem ae_connected_induce_verticesMeeting_time_translate
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (c ε : ℝ), 0 < ε → ∀ (h : IsLocallyFinite ε (timeTranslate (bm ω) c))
      (S : Set ℂ), IsConnected S →
      ((MatedCRT.graph ε (timeTranslate (bm ω) c) h).adj.induce
        (verticesMeeting (fun x : ℤ => (fun t => η ω (t + c)) ''
          Icc (ε * ((x : ℝ) - 1)) (ε * x)) S)).Connected := by
  filter_upwards [ae_time_translate_sided_hypotheses D] with ω hω
  intro c ε hε h S hS
  exact (hω c).1.connected_induce_verticesMeeting hε h hS

end MatedCRTHarmonic.MoTInput
