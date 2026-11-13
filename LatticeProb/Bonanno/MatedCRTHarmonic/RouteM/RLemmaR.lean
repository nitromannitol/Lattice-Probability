/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.RLemmaR at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RAuxLoop
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.JTransfer

/-!
# Route M, Lemma R: a template walk revisits a vertex between its radial and final blocks

Let `D` be a monotone drawing of a
cellular embedding with property (LC) (`CellularEmbedding.PointConnected`), let every cell meeting `B̄(z, 2r)` have
diameter `≤ r/1000`, and let `v 0, …, v n` be a walk whose cells follow the moved polar template within `r/60` on
template intervals `[α j, β j]` (the hypotheses of `CellularEmbedding.TemplateSeparation`, bundled as
`IsTemplateWalk`).

**Lemma R** (`exists_radial_eq_final`): some vertex lies in both the radial block and the final block:
`v j = v k` with `[α j, β j] ⊆ [1/4, 1/2]`, `α k ≥ 3/4`, and hence `j < k`.

Proof (TF3 §8 steps 4–6). The auxiliary loop `C_aux` (`exists_auxLoop`) has degree one about `z` and lies in the
annulus `19r/20 < |· - z| < 21r/20`. The radial block, as a walk from `v j₀` (inside `|· - z| < 19r/20`) to `v j₁`
(outside `|· - z| > 21r/20`), therefore meets a vertex of `C_aux` (TFJ's Corollary J′ for closed walks,
`disconnects_of_closedWalk`). That vertex is not on the spiral walk `Q` (whose cells avoid the radial region), so it
is a vertex `v k` of the final block.
-/

set_option autoImplicit false

noncomputable section

open Set Metric SimpleGraph SimpleGraph.Walk

namespace MatedCRTHarmonic.RouteM

variable {V E : Type*} {G : LFMultigraph V E} {o : V} {H : CellularEmbedding G o}

/-- **Lemma R** (TF3 §8), bundled form: a template walk revisits a vertex of its radial block in its final block. -/
theorem exists_radial_eq_final (D : H.MonotoneDrawing) (hLC : H.PointConnected) {z : ℂ} {r ϑ : ℝ}
    (hr : 0 < r) (hsmall : ∀ x, (H.cell x ∩ closedBall z (2 * r)).Nonempty → diam (H.cell x) ≤ r / 1000)
    {n : ℕ} {v : ℕ → V} {α β : ℕ → ℝ} (hW : IsTemplateWalk H z r ϑ n v α β) :
    ∃ j k, j < k ∧ k ≤ n ∧ 1 / 4 ≤ α j ∧ β j ≤ 1 / 2 ∧ 3 / 4 ≤ α k ∧ v j = v k := by
  obtain ⟨j₀, j₁, hj₀j₁, hj₁n, hj₀1, hj₀2, hj₁1, hj₁2⟩ := hW.exists_radial_block
  obtain ⟨k₀, hk₀n, hk₀1, hk₀2⟩ := hW.exists_final_start
  obtain ⟨Waux, hann, ⟨hne, hdeg⟩, hsupp⟩ := exists_auxLoop D hLC hr hsmall hW hk₀n hk₀1 hk₀2
  -- the radial block as a walk from `v j₀` to `v j₁`
  have hRlen : j₀ + (j₁ - j₀) ≤ n := by omega
  set Rw : G.adj.Walk (v j₀) (v j₁) :=
    (walkAlongSeq v hW.adj (j₁ - j₀) j₀ hRlen).copy rfl (congrArg v (by omega)) with hRw
  have ha : ‖D.Ψ (D.pt (v j₀)) - z‖ < 19 * r / 20 := by
    have h := hW.norm_coord_radial_start hr (by omega) hj₀1 hj₀2 (D.Ψ_pt (v j₀))
    rw [norm_tmplCoord hr, div_lt_iff₀ hr] at h
    linarith
  have hb : 21 * r / 20 < ‖D.Ψ (D.pt (v j₁)) - z‖ := by
    have h := hW.norm_coord_radial_end hr hj₁n hj₁2 hj₁1 (D.Ψ_pt (v j₁))
    rw [norm_tmplCoord hr, lt_div_iff₀ hr] at h
    linarith
  -- Corollary J′ for the closed walk `C_aux`
  obtain ⟨y, hyR, hyW⟩ := disconnects_of_closedWalk D Waux hann hne hdeg ha hb Rw
  rw [hRw, support_copy] at hyR
  obtain ⟨t, ht, rfl⟩ := mem_support_walkAlongSeq v hW.adj (j₁ - j₀) j₀ hRlen hyR
  have hj1 : 1 / 4 ≤ α (j₀ + t) := hj₀1.trans (hW.monotone_α (by omega))
  have hj2 : β (j₀ + t) ≤ 1 / 2 := (hW.monotone_β (by omega)).trans hj₁1
  rcases hsupp _ hyW with ⟨k, hk₀k, hkn, hk⟩ | hnot
  · have hk1 : 3 / 4 ≤ α k := hk₀1.trans (hW.monotone_α hk₀k)
    refine ⟨j₀ + t, k, ?_, hkn, hj1, hj2, hk1, hk⟩
    by_contra hcon
    have h1 := hW.monotone_α (not_lt.1 hcon)
    have h2 := (hW.bounds (j₀ + t) (by omega)).2.1
    linarith
  · exact absurd rfl (hnot (j₀ + t) (by omega) hj1 hj2)

end MatedCRTHarmonic.RouteM
