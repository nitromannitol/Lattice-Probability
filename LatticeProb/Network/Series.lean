/-
The series law, as a chain of nested cutsets.

`LatticeProb/Network/NashWilliams.lean` bounds the effective resistance from
below by the reciprocal conductances of any family of PAIRWISE DISJOINT cutsets
across which the equilibrium current carries a unit.  The family the series law
uses is the boundary cuts of a nested chain of sets around the source, and the
two things to check are exactly the two hypotheses: the cuts are disjoint as
soon as every edge leaving one set lands inside the next, and each carries a
unit because Kirchhoff's node law holds across any set that contains the source
and only vertices where the voltage is harmonic.

The conclusion is that `L` such cuts, each of at most `N` edges, force the
effective resistance to be at least `L / (2N)`: a chain of `L` bottlenecks in
series.  Resistances add.  The factor two is the ordered-pair convention of
`LatticeProb/Network/Basic.lean`, under which every energy sum counts each edge
twice.
-/
import LatticeProb.Network.NashWilliams

open Finset
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [DecidableEq V]

/-- The boundary cut of a set: the ordered pairs that leave it. -/
noncomputable def cutPairs (G : SimpleGraph V) [G.LocallyFinite] (U : Finset V) :
    Finset (V × V) :=
  U.biUnion fun x => ((G.neighborFinset x).filter fun y => y ∉ U).image fun y => (x, y)

theorem mem_cutPairs {U : Finset V} {p : V × V} :
    p ∈ cutPairs G U ↔ p.1 ∈ U ∧ p.2 ∉ U ∧ G.Adj p.1 p.2 := by
  classical
  constructor
  · intro hp
    rw [cutPairs, Finset.mem_biUnion] at hp
    obtain ⟨x, hx, hpx⟩ := hp
    rw [Finset.mem_image] at hpx
    obtain ⟨y, hy, hxy⟩ := hpx
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
    subst hxy
    exact ⟨hx, hy.2, hy.1⟩
  · rintro ⟨h1, h2, h3⟩
    rw [cutPairs, Finset.mem_biUnion]
    refine ⟨p.1, h1, ?_⟩
    rw [Finset.mem_image]
    exact ⟨p.2, Finset.mem_filter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr h3, h2⟩, rfl⟩

/-- A sum over the boundary cut is the double sum defining the flux. -/
theorem sum_cutPairs (U : Finset V) (F : V → V → ℝ) :
    ∑ p ∈ cutPairs G U, F p.1 p.2
      = ∑ x ∈ U, ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∉ U), F x y := by
  classical
  rw [cutPairs, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_image (fun y _ z _ h => congrArg Prod.snd h)]
  · intro a _ b _ hab
    simp only [Function.onFun]
    refine Finset.disjoint_left.mpr fun p hp hq => ?_
    rw [Finset.mem_image] at hp hq
    obtain ⟨y, _, hy⟩ := hp
    obtain ⟨z, _, hz⟩ := hq
    exact hab ((congrArg Prod.fst hy).trans (congrArg Prod.fst hz).symm)

/-- The flux out of a set is the current summed over its boundary cut. -/
theorem flux_eq_sum_cutPairs (c : V → V → ℝ) (f : V → ℝ) (U : Finset V) :
    flux G c f U = ∑ p ∈ cutPairs G U, current G c f p.1 p.2 := by
  rw [flux, sum_cutPairs]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr ?_ fun y _ => rfl
  congr 1

/-- Every boundary cut of a subset of `C` is a set of pairs of the neighbourhood
of `C`, which is where the energy sums live. -/
theorem cutPairs_subset_pairs {C U : Finset V} (h : U ⊆ C) :
    cutPairs G U ⊆ pairs G (nbhd G C) := by
  classical
  intro p hp
  obtain ⟨h1, _, h3⟩ := mem_cutPairs.mp hp
  rw [pairs, Finset.mem_biUnion]
  refine ⟨p.1, subset_nbhd C (h h1), ?_⟩
  rw [Finset.mem_image]
  exact ⟨p.2, (SimpleGraph.mem_neighborFinset _ _ _).mpr h3, rfl⟩

/-- Under the unit conductance the total conductance of a cut is the number of
its edges. -/
theorem sum_unitCond_cutPairs (U : Finset V) :
    ∑ p ∈ cutPairs G U, unitCond G p.1 p.2 = ((cutPairs G U).card : ℝ) := by
  classical
  rw [Finset.sum_congr rfl fun p hp => ?_, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [unitCond, if_pos (mem_cutPairs.mp hp).2.2]

/-- **The series law.**  The boundary cuts of a nested chain of sets around the
source are pairwise disjoint as soon as every edge leaving one set lands inside
the next, and each carries a unit of current, so their reciprocal conductances
add up inside the effective resistance. -/
theorem nashWilliams_nested (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) (L : ℕ) (U : ℕ → Finset V) (hoU : ∀ k, o ∈ U k) (hUC : ∀ k, U k ⊆ C)
    (hgrow : ∀ (k : ℕ) (x : V), x ∈ U k → G.neighborFinset x ⊆ U (k + 1))
    (hmono : Monotone U) :
    ∑ k ∈ Finset.range L, 1 / ((cutPairs G (U k)).card : ℝ) ≤ 2 * effRes G C o := by
  classical
  have hdisj : ((Finset.range L : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun k => cutPairs G (U k) := by
    intro k _ l _ hkl
    have key : ∀ a b : ℕ, a < b → Disjoint (cutPairs G (U a)) (cutPairs G (U b)) := by
      intro a b hab
      refine Finset.disjoint_left.mpr fun p hpa hpb => ?_
      obtain ⟨ha1, ha2, ha3⟩ := mem_cutPairs.mp hpa
      obtain ⟨-, hb2, -⟩ := mem_cutPairs.mp hpb
      refine hb2 (hmono (by omega : a + 1 ≤ b) ?_)
      exact hgrow a p.1 ha1 ((SimpleGraph.mem_neighborFinset _ _ _).mpr ha3)
    simp only [Function.onFun]
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l h
    · exact (key l k h).symm
  have hcut : ∀ k ∈ Finset.range L,
      1 ≤ ∑ p ∈ cutPairs G (U k),
        current G (unitCond G) (killedGreenReal G (C : Set V) o) p.1 p.2 := by
    intro k _
    rw [← flux_eq_sum_cutPairs]
    refine le_of_eq (flux_eq_one isCond_unitCond _ (U k) (hoU k) ?_).symm
    intro x hx
    rw [netLaplacian_unitCond]
    by_cases hxo : x = o
    · subst hxo
      rw [if_pos rfl]
      exact laplacian_killedGreenReal_source hG C ho hq
    · rw [if_neg hxo, neg_zero]
      exact harmonic_killedGreenReal hG C ho hq (by exact_mod_cast hUC k hx) hxo
  have hmain := nashWilliams_le_effRes hG C ho hq (Finset.range L) (fun k => cutPairs G (U k))
    (fun k _ => cutPairs_subset_pairs (hUC k)) hdisj
    (fun k _ p hp => by
      rw [unitCond, if_pos (mem_cutPairs.mp hp).2.2]
      norm_num) hcut
  refine le_trans (le_of_eq ?_) hmain
  exact Finset.sum_congr rfl fun k _ => by rw [sum_unitCond_cutPairs]

/-- **The series law with a uniform bound on the cuts.**  If each of `L` nested
cuts has at most `N` edges, the effective resistance is at least `L / (2N)`. -/
theorem card_div_le_effRes (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) (L N : ℕ) (U : ℕ → Finset V) (hoU : ∀ k, o ∈ U k)
    (hUC : ∀ k, U k ⊆ C) (hgrow : ∀ (k : ℕ) (x : V), x ∈ U k → G.neighborFinset x ⊆ U (k + 1))
    (hmono : Monotone U) (hcard : ∀ k < L, (cutPairs G (U k)).card ≤ N) :
    (L : ℝ) / N ≤ 2 * effRes G C o := by
  classical
  have hpos : ∀ k < L, 0 < (cutPairs G (U k)).card := by
    intro k hk
    by_contra hc
    have hempty : cutPairs G (U k) = ∅ := Finset.card_eq_zero.mp (by omega)
    have hflux : (1 : ℝ) ≤ ∑ p ∈ cutPairs G (U k),
        current G (unitCond G) (killedGreenReal G (C : Set V) o) p.1 p.2 := by
      rw [← flux_eq_sum_cutPairs]
      refine le_of_eq (flux_eq_one isCond_unitCond _ (U k) (hoU k) ?_).symm
      intro x hx
      rw [netLaplacian_unitCond]
      by_cases hxo : x = o
      · subst hxo
        rw [if_pos rfl]
        exact laplacian_killedGreenReal_source hG C ho hq
      · rw [if_neg hxo, neg_zero]
        exact harmonic_killedGreenReal hG C ho hq (by exact_mod_cast hUC k hx) hxo
    rw [hempty, Finset.sum_empty] at hflux
    linarith
  have hterm : ∀ k ∈ Finset.range L,
      1 / (N : ℝ) ≤ 1 / ((cutPairs G (U k)).card : ℝ) := by
    intro k hk
    have hk' : k < L := Finset.mem_range.mp hk
    have h1 : (0 : ℝ) < ((cutPairs G (U k)).card : ℝ) := by exact_mod_cast hpos k hk'
    have h2 : ((cutPairs G (U k)).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard k hk'
    exact one_div_le_one_div_of_le h1 h2
  have hsum : (L : ℝ) / N = ∑ k ∈ Finset.range L, 1 / (N : ℝ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hsum]
  exact le_trans (Finset.sum_le_sum hterm)
    (nashWilliams_nested hG C ho hq L U hoU hUC hgrow hmono)

/-- **The series law with the chain asked for only up to a horizon.**  On an
infinite graph the natural chain is unbounded, so no single finite `C` contains
every `U k`, and truncating the chain breaks the growth hypothesis at the last
index.  The proof uses the three hypotheses only below the horizon, so this is
the form an exhausting chain supplies. -/
theorem nashWilliams_upto (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) (L : ℕ) (U : ℕ → Finset V) (hoU : ∀ k < L, o ∈ U k)
    (hUC : ∀ k < L, U k ⊆ C)
    (hgrow : ∀ k < L, ∀ x ∈ U k, G.neighborFinset x ⊆ U (k + 1))
    (hmono : ∀ a b, a ≤ b → b < L → U a ⊆ U b) :
    ∑ k ∈ Finset.range L, 1 / ((cutPairs G (U k)).card : ℝ) ≤ 2 * effRes G C o := by
  classical
  have hdisj : ((Finset.range L : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun k => cutPairs G (U k) := by
    intro k hk l hl hkl
    have key : ∀ a b : ℕ, a < b → b < L → Disjoint (cutPairs G (U a)) (cutPairs G (U b)) := by
      intro a b hab hbL
      refine Finset.disjoint_left.mpr fun p hpa hpb => ?_
      obtain ⟨ha1, ha2, ha3⟩ := mem_cutPairs.mp hpa
      obtain ⟨-, hb2, -⟩ := mem_cutPairs.mp hpb
      refine hb2 (hmono (a + 1) b (by omega) hbL ?_)
      exact hgrow a (by omega) p.1 ha1 ((SimpleGraph.mem_neighborFinset _ _ _).mpr ha3)
    simp only [Finset.coe_range, Set.mem_Iio] at hk hl
    simp only [Function.onFun]
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l h hl
    · exact (key l k h hk).symm
  have hcut : ∀ k ∈ Finset.range L,
      1 ≤ ∑ p ∈ cutPairs G (U k),
        current G (unitCond G) (LatticeProb.Graph.killedGreenReal G (C : Set V) o) p.1 p.2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← flux_eq_sum_cutPairs]
    refine le_of_eq (flux_eq_one isCond_unitCond _ (U k) (hoU k hk) ?_).symm
    intro x hx
    rw [netLaplacian_unitCond]
    by_cases hxo : x = o
    · subst hxo
      rw [if_pos rfl]
      exact laplacian_killedGreenReal_source hG C ho hq
    · rw [if_neg hxo, neg_zero]
      exact harmonic_killedGreenReal hG C ho hq (by exact_mod_cast hUC k hk hx) hxo
  have hmain := nashWilliams_le_effRes hG C ho hq (Finset.range L) (fun k => cutPairs G (U k))
    (fun k hk => cutPairs_subset_pairs (hUC k (Finset.mem_range.1 hk))) hdisj
    (fun k _ p hp => by
      rw [unitCond, if_pos (mem_cutPairs.mp hp).2.2]
      norm_num) hcut
  refine le_trans (le_of_eq ?_) hmain
  exact Finset.sum_congr rfl fun k _ => by rw [sum_unitCond_cutPairs]

end LatticeProb.Network
