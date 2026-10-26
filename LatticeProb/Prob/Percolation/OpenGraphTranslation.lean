import LatticeProb.Prob.Percolation.LatticeBondTranslation

/-!
# Isomorphism of translated open graphs

Literal vertex addition intertwines the open graphs of a configuration and its inverse bond
pullback. The inverse subtracts the displacement, and reachability has the same covariance.
-/

namespace LatticeProb.Percolation

variable {d : ℕ}

/-- The open graph isomorphism adds the displacement to every lattice vertex. -/
def openGraphTranslation (z : Vertex d) (ω : Configuration d) :
    openGraph ω ≃g openGraph (configurationTranslation z ω) where
  toFun x := x + z
  invFun x := x - z
  left_inv x := add_sub_cancel_right x z
  right_inv x := sub_add_cancel x z
  map_rel_iff' := openGraph_adj_translation_iff z ω _ _

/-- The entire forward vertex map is literal addition. -/
theorem openGraphTranslation_apply (z : Vertex d) (ω : Configuration d) (x : Vertex d) :
    openGraphTranslation z ω x = x + z := rfl

/-- The entire inverse vertex map is literal subtraction. -/
theorem openGraphTranslation_symm_apply (z : Vertex d) (ω : Configuration d)
    (x : Vertex d) : (openGraphTranslation z ω).symm x = x - z := rfl

/-- Reachability is preserved and reflected when both endpoints move by the displacement. -/
theorem openGraph_reachable_translation_iff (z : Vertex d) (ω : Configuration d)
    (x y : Vertex d) :
    (openGraph (configurationTranslation z ω)).Reachable (x + z) (y + z) ↔
      (openGraph ω).Reachable x y :=
  (openGraphTranslation z ω).reachable_iff

/-- Arbitrary translated endpoints are reachable exactly when their inverse images are. -/
theorem openGraph_reachable_sub_translation_iff (z : Vertex d) (ω : Configuration d)
    (x y : Vertex d) :
    (openGraph (configurationTranslation z ω)).Reachable x y ↔
      (openGraph ω).Reachable (x - z) (y - z) := by
  simpa only [sub_add_cancel] using
    openGraph_reachable_translation_iff z ω (x - z) (y - z)

end LatticeProb.Percolation
