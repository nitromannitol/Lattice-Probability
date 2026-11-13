/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4F.Prop210Degree47 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4F.Prop210DegreeGeometry
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellAdjacency
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Graph
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry

/-!
# [18] Equation (4.7) for the mated-CRT cell graph

The two Brownian sides account for the factor two. Peanosphere merge and
The strict-side event make each neighbour cell meet the root window.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal

namespace MatedCRTHarmonic.GMS4F

/-- The concrete graph-degree comparison (4.7), on the side-strict and
positive-window-diameter event. -/
theorem matedCRT_degree_le_two_local_degrees
    {ε : ℝ} {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (hε : 0 < ε) (P : RouteM.Peanosphere ω η)
    (hG : RouteM.SideStrict ε ω) (hlf : MatedCRT.IsLocallyFinite ε ω)
    (hη : Continuous η) (t₀ : ℝ)
    (hD : 0 < diam (GMS4b.locWindow ε η t₀)) :
    ((MatedCRT.graph ε ω hlf).deg ⌈t₀ / ε⌉ : ℕ∞) ≤
      2 * (GMS4b.locDegIn ε η t₀ + GMS4b.locDegOut ε η t₀) := by
  classical
  let G := MatedCRT.graph ε ω hlf
  let x : ℤ := ⌈t₀ / ε⌉
  let N := (G.outDarts x).image G.dtgt
  have hcontact : ∀ y ∈ N,
      (GMS4b.cellOf ε η y ∩ GMS4b.locWindow ε η t₀).Nonempty := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    have hsrc : G.dsrc d = x := (Harmonic.mem_outDarts G).mp hd
    have hne : G.src d.1 ≠ G.tgt d.1 := by
      rcases d.1 with ⟨⟨a, b, side⟩, he⟩
      exact ne_of_lt he.1
    have hadj : G.adj.Adj x (G.dtgt d) := by
      rcases d with ⟨e, rev⟩
      cases rev
      · change G.src e = x at hsrc
        simpa [hsrc, LFMultigraph.dtgt] using (Harmonic.adj_of_edge G hne)
      · change G.tgt e = x at hsrc
        simpa [hsrc, LFMultigraph.dtgt] using (Harmonic.adj_of_edge G hne).symm
    have hinter := MoTInput.cell_intersects_of_matedCRT_adj hε P hG hadj.symm
    have hroot : GMS4b.cellOf ε η x ⊆ GMS4b.locWindow ε η t₀ :=
      root_cell_subset_window hε η t₀
    obtain ⟨w, hwy, hwx⟩ := hinter
    exact ⟨w, hwy, hroot hwx⟩
  have hcount := window_contact_cells_le_local_degrees hε η hη t₀ hD N hcontact
  have hdeg := matedCRT_degree_le_two_neighborCount hlf x
  calc
    (G.deg x : ℕ∞) ≤ 2 * (N.card : ℕ∞) := by exact_mod_cast hdeg
    _ ≤ 2 * (GMS4b.locDegIn ε η t₀ + GMS4b.locDegOut ε η t₀) :=
      by simpa only [mul_comm] using (mul_le_mul_left hcount 2)

/-- Equation (4.7) simultaneously at every dyadic scale and every root
time, almost surely under the concrete mating-of-trees bundle. -/
theorem ae_matedCRT_degree_le_two_local_degrees
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (t₀ : ℝ),
      ∃ hlf : MatedCRT.IsLocallyFinite (CellFamily.mesh k) (bm ω),
        (((MatedCRT.graph (CellFamily.mesh k) (bm ω) hlf).deg
          ⌈t₀ / CellFamily.mesh k⌉ : ℕ∞) ≤
        2 * (GMS4b.locDegIn (CellFamily.mesh k) (η ω) t₀ +
          GMS4b.locDegOut (CellFamily.mesh k) (η ω) t₀)) := by
  filter_upwards [MoTInput.ae_peanosphere D,
    MoTInput.ae_sideStrict_allMeshes D,
    MoTInput.ae_curve_intervals_have_interior D,
    MoTInput.ae_meshCellularEmbeddings D] with ω hP hside hInt hmesh
  intro k t₀
  have hε : 0 < CellFamily.mesh k := by dsimp [CellFamily.mesh]; positivity
  obtain ⟨hlf, H, hcell⟩ := hmesh k
  have hWinInt : (interior (GMS4b.locWindow (CellFamily.mesh k) (η ω) t₀)).Nonempty := by
    simpa only [GMS4b.locWindow] using
      hInt (t₀ - CellFamily.mesh k) (t₀ + CellFamily.mesh k) (by linarith)
  have hD := diam_locWindow_pos_of_interior_nonempty (η ω).continuous hWinInt
  exact ⟨hlf, matedCRT_degree_le_two_local_degrees hε hP (hside k)
    hlf (η ω).continuous t₀ hD⟩

end MatedCRTHarmonic.GMS4F

