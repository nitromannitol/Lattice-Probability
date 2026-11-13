/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.RSeparation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RLemmaR
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RTemplateLoop

/-!
# Route M, Lemma D″: template separation from a monotone drawing

(the separation argument, Details (a)).

**Lemma D″** (`templateSeparation_of_monotoneDrawing`): let `D` be a monotone drawing (Core interface
`CellularEmbedding.MonotoneDrawing`) of a cellular embedding `H` with property (LC) (`CellularEmbedding.PointConnected`,
TF2's Theorem B), and let every cell meeting `B̄(z, 2r)` have diameter `≤ r/1000`. Then `H` has the template
separation property `CellularEmbedding.TemplateSeparation z r`: for every walk `v 0, …, v n` whose cells follow the
moved polar template within `r/60` (an `r/60`-itinerary, TF3 §2), the visited set `{v 0, …, v n}` graph-disconnects
`V(∂B_{3r/4}(z))` from `V(∂B_{5r/4}(z))` in the frozen `LFMultigraph.Disconnects` sense.

Proof (TF3 §9).
1. Lemma R (`exists_radial_eq_final`) gives `v j = v k` with `j` in the radial block and `k` in the final block.
2. The closed sub-walk `v j → ⋯ → v k` (`exists_templateLoop`) has drawn loop in the annulus `22r/25 < |· - z| <
   28r/25` with degree one about `z`.
3. A vertex `a` whose cell meets `∂B_{3r/4}(z)` has `|Ψ(pt a) - z| ≤ 3r/4 + r/1000 < 22r/25`; a vertex `b` whose cell
   meets `∂B_{5r/4}(z)` has `|Ψ(pt b) - z| ≥ 5r/4 - r/1000 > 28r/25`.
4. TFJ's Corollary J′ for closed walks (`disconnects_of_closedWalk`): every walk from `a` to `b` meets a vertex of the
   sub-walk, which is a visited vertex.
-/

set_option autoImplicit false

noncomputable section

open Set Metric SimpleGraph SimpleGraph.Walk

namespace MatedCRTHarmonic.RouteM

variable {V E : Type*} {G : LFMultigraph V E} {o : V} {H : CellularEmbedding G o}

/-- **Lemma D″** (TF3 §9; TF3 Details (a), `templateSeparation_of_monotoneDrawing`): a monotone drawing, property
(LC) and cells of diameter `≤ r/1000` near `B̄(z, 2r)` give the template separation property at `(z, r)`. -/
theorem templateSeparation_of_monotoneDrawing (D : H.MonotoneDrawing) (hLC : H.PointConnected) {z : ℂ}
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x, (H.cell x ∩ closedBall z (2 * r)).Nonempty → diam (H.cell x) ≤ r / 1000) :
    H.TemplateSeparation z r := by
  intro ϑ n v α β hadj hα0 hβn hα hβ hov hbd hnear
  have hW : IsTemplateWalk H z r ϑ n v α β := ⟨hadj, hα0, hβn, hα, hβ, hov, hbd, hnear⟩
  obtain ⟨j, k, hjk, hkn, -, hj2, hk, hv⟩ := exists_radial_eq_final D hLC hr hsmall hW
  obtain ⟨W, hann, ⟨hne, hdeg⟩, hsupp⟩ := exists_templateLoop D hr hW hjk hkn hj2 hk hv
  intro a ha b hb w
  have ha' : ‖D.Ψ (D.pt a) - z‖ < 22 * r / 25 := by
    obtain ⟨q, hqa, hqS⟩ := ha
    have hqz : ‖q - z‖ = 3 * r / 4 := by rwa [mem_sphere, dist_eq_norm] at hqS
    have hd := norm_sub_le_of_smallCells hsmall hqa (by rw [hqz]; linarith) (D.Ψ_pt a)
    have htri := norm_sub_le_norm_sub_add_norm_sub (D.Ψ (D.pt a)) q z
    linarith
  have hb' : 28 * r / 25 < ‖D.Ψ (D.pt b) - z‖ := by
    obtain ⟨q, hqb, hqS⟩ := hb
    have hqz : ‖q - z‖ = 5 * r / 4 := by rwa [mem_sphere, dist_eq_norm] at hqS
    have hd := norm_sub_le_of_smallCells hsmall hqb (by rw [hqz]; linarith) (D.Ψ_pt b)
    have htri := norm_sub_le_norm_sub_add_norm_sub q (D.Ψ (D.pt b)) z
    rw [norm_sub_rev q (D.Ψ (D.pt b))] at htri
    linarith
  obtain ⟨y, hyw, hyW⟩ := disconnects_of_closedWalk D W hann hne hdeg ha' hb' w
  obtain ⟨i, -, hik, rfl⟩ := hsupp y hyW
  exact ⟨v i, hyw, i, hik.trans hkn, rfl⟩

end MatedCRTHarmonic.RouteM
