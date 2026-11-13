import LatticeProb.Prob.Percolation.LSS.Defs

/-!
# The general domination statement from the bounded-degree form

The general Liggett-Schonmann-Stacey domination for `k`-dependent fields of bits on
`ℤ^d`, `LiggettSchonmannStacey`, follows from its bounded-degree form
`LiggettSchonmannStaceyBoundedDegree`.

A `k`-dependent field of bits on `ℤ^d` has the dependence graph that joins two
distinct sites at `ℓ^∞`-distance at most `k`. Every vertex of this graph has at most
`(2k+1)^d - 1` neighbours, all lying in the cube of radius `k` around it, so the graph
has degree at most `Δ = (2k+1)^d` and every vertex has degree strictly below `Δ`; the
condition on finite components is therefore automatic. The two statements are otherwise
word for word the same: the product law is `Measure.infinitePi` of the same Bernoulli
law, and increasing events and independence of restrictions to finite sets of sites
coincide.

Ported from the Exploding-Sandpiles formalization, `Support/ExtLSSG.lean`.
-/

namespace LatticeProb.Percolation.LSS

open LatticeProb MeasureTheory

/-- The dependence graph of a `k`-dependent field on `ℤ^d`: two distinct sites are
adjacent when they are at `ℓ^∞`-distance at most `k`. -/
noncomputable def xlssg_graph (d k : ℕ) : SimpleGraph (Site d) where
  Adj a b := a ≠ b ∧ ∀ l, |a l - b l| ≤ (k : ℤ)
  symm := ⟨fun a b ⟨hne, hd⟩ => ⟨hne.symm, fun l => by rw [abs_sub_comm]; exact hd l⟩⟩
  loopless := ⟨fun a ha => ha.1 rfl⟩

/-- The cube of radius `k` around a site. -/
noncomputable def xlssg_box (d k : ℕ) (a : Site d) : Finset (Site d) :=
  Finset.Icc (a - fun _ => (k : ℤ)) (a + fun _ => (k : ℤ))

theorem xlssg_mem_box {d k : ℕ} {a b : Site d} :
    b ∈ xlssg_box d k a ↔ ∀ l, |a l - b l| ≤ (k : ℤ) := by
  simp only [xlssg_box, Finset.mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply]
  constructor
  · rintro ⟨h1, h2⟩ l
    rw [abs_le]
    have := h1 l
    have := h2 l
    constructor <;> linarith
  · intro h
    refine ⟨fun l => ?_, fun l => ?_⟩
    · have := (abs_le.mp (h l)).2
      linarith
    · have := (abs_le.mp (h l)).1
      linarith

theorem xlssg_card_box (d k : ℕ) (a : Site d) : (xlssg_box d k a).card = (2 * k + 1) ^ d := by
  simp only [xlssg_box, Pi.card_Icc, Int.card_Icc, Pi.sub_apply, Pi.add_apply]
  have : ∀ l : Fin d, ((a l + (k : ℤ) + 1 - (a l - (k : ℤ))).toNat) = 2 * k + 1 := by
    intro l
    omega
  simp [this]

theorem xlssg_neighborSet_subset (d k : ℕ) (a : Site d) :
    (xlssg_graph d k).neighborSet a ⊆ ((xlssg_box d k a).erase a : Finset (Site d)) := by
  intro b hb
  obtain ⟨hne, hd⟩ := hb
  simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
  exact ⟨xlssg_mem_box.mpr hd, hne.symm⟩

/-- Every vertex of the dependence graph has finitely many neighbours, strictly fewer
than `(2k+1)^d`. -/
theorem xlssg_degree (d k : ℕ) (a : Site d) :
    ((xlssg_graph d k).neighborSet a).Finite ∧
      ((xlssg_graph d k).neighborSet a).ncard < (2 * k + 1) ^ d := by
  have hfin : ((xlssg_graph d k).neighborSet a).Finite :=
    (Finset.finite_toSet _).subset (xlssg_neighborSet_subset d k a)
  refine ⟨hfin, ?_⟩
  have hmem : a ∈ xlssg_box d k a := xlssg_mem_box.mpr (fun l => by simp)
  calc ((xlssg_graph d k).neighborSet a).ncard
      ≤ (((xlssg_box d k a).erase a : Finset (Site d)) : Set (Site d)).ncard :=
        Set.ncard_le_ncard (xlssg_neighborSet_subset d k a) (Finset.finite_toSet _)
    _ = ((xlssg_box d k a).erase a).card := Set.ncard_coe_finset _
    _ < (xlssg_box d k a).card := Finset.card_erase_lt_of_mem hmem
    _ = (2 * k + 1) ^ d := xlssg_card_box d k a

/-- A `k`-dependent field of bits on `ℤ^d` has the dependence graph `xlssg_graph d k`. -/
theorem xlssg_dependenceGraph {d k : ℕ} {μ : Measure (Site d → Bool)}
    (hμ : KDependent k μ) : HasDependenceGraph (xlssg_graph d k) μ := by
  intro I J hIJ hadj
  apply hμ I J
  intro a ha b hb
  by_contra hcon
  push Not at hcon
  have hne : a ≠ b := by
    intro hab
    exact Finset.disjoint_left.mp hIJ ha (hab ▸ hb)
  exact hadj a ha b hb ⟨hne, fun l => by simpa [abs_sub_comm] using hcon l⟩

/-- The general Liggett-Schonmann-Stacey domination follows from the bounded-degree
form. -/
theorem xlssg_of_bd (h : LiggettSchonmannStaceyBoundedDegree) :
    LiggettSchonmannStacey := by
  intro d k _ ρ hρ0 hρ1
  obtain ⟨p, hp1, hp⟩ := h (Site d) (xlssg_graph d k) ((2 * k + 1) ^ d)
    (Nat.one_le_pow _ _ (by omega))
    (fun s => ⟨(xlssg_degree d k s).1, (xlssg_degree d k s).2.le⟩)
    (fun s _ => ⟨s, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, (xlssg_degree d k s).2⟩)
    ρ hρ0 hρ1
  refine ⟨p, hp1, fun μ hμ hk hpμ A hA hinc => ?_⟩
  exact hp μ hμ (xlssg_dependenceGraph hk) hpμ A hA hinc

end LatticeProb.Percolation.LSS
