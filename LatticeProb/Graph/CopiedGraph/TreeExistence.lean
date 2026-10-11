/- Minimal-cardinality construction of a tree on the full original carrier.
Adapted from finite-avalanches, CopiedGraphConnectivity.reaches_erase_of_alternative
and Electrical/Trees/CopiedTreeExistence; original notices/source pins accompany this extraction. -/
import LatticeProb.Graph.CopiedGraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type*}

/-- Replace only a specified original occurrence by a path avoiding that occurrence. -/
theorem reaches_erase_of_alternative (J : CopiedGraph V E) {F : Finset E} (marked : E)
    (halt : J.reaches (F.erase marked) (J.left marked) (J.right marked))
    {x y : V} (h : J.reaches F x y) : J.reaches (F.erase marked) x y := by
  induction h with
  | refl => exact .refl
  | @tail u v _ hadj ih =>
    obtain ⟨e, he, hends⟩ := hadj
    by_cases hem : e = marked
    · subst e
      have hstep : J.reaches (F.erase marked) u v := by
        rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
        · simpa only [hl, hr] using halt
        · simpa only [hl, hr] using J.reaches_symm halt
      exact ih.trans hstep
    · exact ih.tail ⟨e, Finset.mem_erase.mpr ⟨hem, he⟩, hends⟩

/-- A connected nonempty copied graph with finitely many copies has a full-carrier tree. -/
theorem nonempty_spanningTree_of_reaches [Fintype E] [Nonempty V] (J : CopiedGraph V E)
    (hconn : ∀ x y : V, J.reaches Finset.univ x y) : Nonempty J.SpanningTree := by
  let candidates : Finset (Finset E) :=
    Finset.univ.filter (fun F => ∀ x y : V, J.reaches F x y)
  have inhabited : candidates.Nonempty :=
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconn⟩⟩
  obtain ⟨F, hF, hminimal⟩ := candidates.exists_min_image Finset.card inhabited
  have connected : ∀ x y : V, J.reaches F x y := (Finset.mem_filter.mp hF).2
  refine ⟨⟨F, Set.univ_nonempty, connected, ?_⟩⟩
  intro e he hcycle
  have smaller : F.erase e ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x y =>
      J.reaches_erase_of_alternative e hcycle (connected x y)⟩
  exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem he))
    (hminimal (F.erase e) smaller)

/-- The original tree-count denominator is positive on a connected nonempty carrier. -/
theorem card_spanningTree_pos [Fintype E] [Nonempty V] (J : CopiedGraph V E)
    (hconn : ∀ x y : V, J.reaches Finset.univ x y) :
    0 < Fintype.card J.SpanningTree :=
  Fintype.card_pos_iff.mpr (J.nonempty_spanningTree_of_reaches hconn)

end
end LatticeProb.Graph.CopiedGraph
