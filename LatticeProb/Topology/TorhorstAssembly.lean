import LatticeProb.Topology.CircleCharacterization
import LatticeProb.Topology.ComplementComponents

/-!
# Torhorst's theorem from its plane-topological and continuum-theoretic ingredients

Torhorst's theorem (`TorhorstSimpleLoop`; Torhorst (1921), Whyburn, *Analytic Topology*, Chapter VI, §2) says that
for a locally connected continuum `K ⊆ ℂ` with two points and without cut points, the frontier of every connected
component of `ℂ \ K` is a simple loop. The classical proof splits into three independent ingredients:

1. *unicoherence of the plane*: the frontier of a complementary component of a plane continuum is connected
   (Kuratowski, *Topology* II, §61);
2. *separation by pairs*: under the hypotheses of Torhorst's theorem, every two distinct points of the frontier of
   a complementary component separate it (crosscuts and the Jordan curve theorem; Whyburn VI.2);
3. *R. L. Moore's characterisation of the circle*: a nondegenerate metric continuum separated by every pair of its
   points is homeomorphic to the circle (Kuratowski, *Topology* II, §47-49).

`torhorstSimpleLoop_of_ingredients` assembles them: given the three statements, Torhorst's theorem holds. The
remaining facts of the assembly (the frontier is compact and has two points) are proved in
`LatticeProb.Topology.ComplementComponents`. Ingredient 3 is
`nonempty_homeomorph_circle_of_forall_not_isPreconnected_diff_pair` (`LatticeProb.Topology.CircleCharacterization`),
so `torhorstSimpleLoop_of_unicoherent_of_pairSeparates` needs only ingredients 1 and 2.
-/

namespace LatticeProb.Topology

open Set

/-- **Torhorst's theorem from its three ingredients.** If the frontier of every complementary component of a
plane continuum is connected (unicoherence), if under the hypotheses of Torhorst's theorem every two distinct
points of the frontier of a complementary component separate it, and if a nondegenerate plane continuum separated
by every pair of its points is homeomorphic to the circle (R. L. Moore), then `TorhorstSimpleLoop` holds. -/
theorem torhorstSimpleLoop_of_ingredients
    (hUnicoherent : ∀ K : Set ℂ, IsCompact K → IsConnected K → ∀ C ∈ connectedComponentsIn Kᶜ,
      IsConnected (frontier C))
    (hPairSeparates : ∀ K : Set ℂ, IsCompact K → IsConnected K → K.Nontrivial → IsLocallyConnectedSet K →
      (∀ a : ℂ, ¬ IsCutPoint K a) → ∀ C ∈ connectedComponentsIn Kᶜ,
        ∀ a ∈ frontier C, ∀ b ∈ frontier C, a ≠ b → ¬ IsPreconnected (frontier C \ {a, b}))
    (hMoore : ∀ Γ : Set ℂ, IsCompact Γ → IsConnected Γ → Γ.Nontrivial →
      (∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ¬ IsPreconnected (Γ \ {a, b})) → Nonempty (Circle ≃ₜ Γ)) :
    TorhorstSimpleLoop := by
  intro K hK hKc hKn hKlc hKcut C hC
  rw [isSimpleLoop_iff_nonempty_homeomorph]
  exact hMoore _ (isCompact_frontier_of_mem_connectedComponentsIn_compl hK hC) (hUnicoherent K hK hKc C hC)
    (frontier_nontrivial_of_mem_connectedComponentsIn_compl hK.isClosed hKn hC)
    (hPairSeparates K hK hKc hKn hKlc hKcut C hC)


/-- **Torhorst's theorem from unicoherence and separation by pairs.** R. L. Moore's characterisation of the circle
is proved (`nonempty_homeomorph_circle_of_forall_not_isPreconnected_diff_pair`), so `TorhorstSimpleLoop` follows
from the first two ingredients alone. -/
theorem torhorstSimpleLoop_of_unicoherent_of_pairSeparates
    (hUnicoherent : ∀ K : Set ℂ, IsCompact K → IsConnected K → ∀ C ∈ connectedComponentsIn Kᶜ,
      IsConnected (frontier C))
    (hPairSeparates : ∀ K : Set ℂ, IsCompact K → IsConnected K → K.Nontrivial → IsLocallyConnectedSet K →
      (∀ a : ℂ, ¬ IsCutPoint K a) → ∀ C ∈ connectedComponentsIn Kᶜ,
        ∀ a ∈ frontier C, ∀ b ∈ frontier C, a ≠ b → ¬ IsPreconnected (frontier C \ {a, b})) :
    TorhorstSimpleLoop :=
  torhorstSimpleLoop_of_ingredients hUnicoherent hPairSeparates fun _ hΓ hΓc hΓn hpair =>
    nonempty_homeomorph_circle_of_forall_not_isPreconnected_diff_pair hΓ hΓc hΓn hpair

end LatticeProb.Topology
