import LatticeProb.Graph.Boundary
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Network.Dirichlet

/-!
# Maximum principle from a coercive harmonic barrier

On a connected locally finite network, a nonnegative harmonic barrier with finite sublevel
sets reduces the maximum principle on a proper domain to the finite maximum principle.
Only an upper bound on the function is needed; no boundary condition at infinity is assumed.
-/

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- A harmonic function on a finite proper set is bounded by its outer graph boundary data.
Values beyond the set and its outer boundary play no role. -/
theorem le_on_finset_of_outerBoundary (hG : G.Connected) {c : V → V → ℝ}
    (hc : IsCond G c) (C : Finset V) {q : V} (hq : q ∉ C) (f : V → ℝ) (M : ℝ)
    (hharm : HarmonicOn G c f (C : Set V))
    (hboundary : ∀ x ∈ outerBoundary G (C : Set V), f x ≤ M) :
    ∀ x ∈ C, f x ≤ M := by
  classical
  let g : V → ℝ := fun x => if x ∈ closureN G (C : Set V) then f x else M
  have hinside (x : V) (hx : x ∈ C) : g x = f x :=
    if_pos (Or.inl hx)
  have hneighbor (x : V) (hx : x ∈ C) (y : V) (hxy : G.Adj x y) : g y = f y := by
    apply if_pos
    by_cases hy : y ∈ C
    · exact Or.inl hy
    · exact Or.inr ⟨hy, x, hx, hxy.symm⟩
  have hgharm : ∀ x ∈ C, x ∉ (∅ : Set V) → netLaplacian G c g x = 0 := by
    intro x hx _
    calc
      netLaplacian G c g x = netLaplacian G c f x := by
        unfold netLaplacian
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hinside x hx, hneighbor x hx y ((SimpleGraph.mem_neighborFinset G x y).mp hy)]
      _ = 0 := hharm x hx
  have hgout : ∀ x, x ∉ C → g x ≤ M := by
    intro x hx
    dsimp only [g]
    split_ifs with h
    · exact hboundary x ⟨hx, h.resolve_left hx |>.2⟩
    · exact le_rfl
  have hbound := le_of_harmonicOn hG hc C ∅ g M hq hgharm hgout
    (fun x hx => False.elim hx)
  intro x hx
  rw [← hinside x hx]
  exact hbound x

/-- For each positive parameter, subtracting a coercive harmonic barrier makes a bounded-above
harmonic function nonpositive relative to its outer boundary bound. Coercivity means precisely
that every sublevel set of the barrier within the domain is finite. -/
theorem sub_barrier_nonpos (hG : G.Connected) {c : V → V → ℝ} (hc : IsCond G c)
    (Ω : Set V) (hproper : ∃ q, q ∉ Ω) (f v : V → ℝ) (M B : ℝ)
    (hf : HarmonicOn G c f Ω) (hv : HarmonicOn G c v Ω)
    (hbounded : ∀ x ∈ Ω, f x ≤ B) (hnonneg : ∀ x, 0 ≤ v x)
    (hfinite : ∀ r : ℝ, {x | x ∈ Ω ∧ v x ≤ r}.Finite)
    (hboundary : ∀ x ∈ outerBoundary G Ω, f x ≤ M)
    {t : ℝ} (ht : 0 < t) : ∀ x ∈ Ω, f x - M - t * v x ≤ 0 := by
  classical
  let w : V → ℝ := fun x => f x - M - t * v x
  have hw : HarmonicOn G c w Ω := by
    intro x hx
    change netLaplacian G c (fun y => (f y - M) - t * v y) x = 0
    rw [netLaplacian_sub, netLaplacian_sub, netLaplacian_const,
      netLaplacian_smul, hf x hx, hv x hx]
    ring
  have hposfinite : {x | x ∈ Ω ∧ 0 < w x}.Finite := by
    refine (hfinite ((B - M) / t)).subset ?_
    intro x hx
    refine ⟨hx.1, (le_div_iff₀ ht).mpr ?_⟩
    have hfx := hbounded x hx.1
    have hwx : 0 < f x - M - t * v x := hx.2
    nlinarith
  let C := hposfinite.toFinset
  have hC (x : V) : x ∈ C ↔ x ∈ Ω ∧ 0 < w x := hposfinite.mem_toFinset
  obtain ⟨q, hq⟩ := hproper
  have hqC : q ∉ C := fun h => hq ((hC q).mp h).1
  have hCboundary : ∀ x ∈ outerBoundary G (C : Set V), w x ≤ 0 := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · exact le_of_not_gt (fun h => hx.1 ((hC x).mpr ⟨hxΩ, h⟩))
    · obtain ⟨y, hy, hxy⟩ := hx.2
      have hfx := hboundary x ⟨hxΩ, y, ((hC y).mp hy).1, hxy⟩
      have htv := mul_nonneg ht.le (hnonneg x)
      dsimp only [w]
      linarith
  have hCbound := le_on_finset_of_outerBoundary hG hc C hqC w 0
    (fun x hx => hw x ((hC x).mp hx).1) hCboundary
  intro x hx
  change w x ≤ 0
  by_contra h
  have hxC := (hC x).mpr ⟨hx, lt_of_not_ge h⟩
  exact h (hCbound x hxC)

/-- A bounded-above harmonic function on a proper domain is bounded by its outer boundary
values whenever a nonnegative harmonic barrier has finite sublevel sets on that domain. -/
theorem le_of_coercive_barrier (hG : G.Connected) {c : V → V → ℝ} (hc : IsCond G c)
    (Ω : Set V) (hproper : ∃ q, q ∉ Ω) (f v : V → ℝ) (M B : ℝ)
    (hf : HarmonicOn G c f Ω) (hv : HarmonicOn G c v Ω)
    (hbounded : ∀ x ∈ Ω, f x ≤ B) (hnonneg : ∀ x, 0 ≤ v x)
    (hfinite : ∀ r : ℝ, {x | x ∈ Ω ∧ v x ≤ r}.Finite)
    (hboundary : ∀ x ∈ outerBoundary G Ω, f x ≤ M) : ∀ x ∈ Ω, f x ≤ M := by
  intro x hx
  by_contra h
  have hgap : 0 < f x - M := sub_pos.mpr (lt_of_not_ge h)
  let t := (f x - M) / (2 * (v x + 1))
  have hvx := hnonneg x
  have hden : 0 < 2 * (v x + 1) := by linarith
  have ht : 0 < t := div_pos hgap hden
  have hestimate := sub_barrier_nonpos hG hc Ω hproper f v M B hf hv hbounded hnonneg
    hfinite hboundary ht x hx
  have hidentity : t * (2 * (v x + 1)) = f x - M := div_mul_cancel₀ _ hden.ne'
  nlinarith

end LatticeProb.Network
