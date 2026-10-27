import LatticeProb.Network.Caccioppoli

/-! # Local Caccioppoli inequality

A supported test function gives a local estimate on a conductance graph.
-/

open scoped BigOperators Classical

namespace LatticeProb.Network

/-- A discrete Caccioppoli inequality on a conductance network: if `f` is harmonic on `B`
and the test function `f * η²` vanishes outside `B`, the `η`-weighted Dirichlet energy of `f`
is controlled by the `f²`-weighted gradient energy of `η`. -/

theorem caccioppoli_of_support {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : IsCond G c)
    (S B : Finset V) (f η : V → ℝ)
    (hf : ∀ x ∈ B, netLaplacian G c f x = 0)
    (htest : ∀ x, x ∉ B → f x * η x ^ 2 = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x - f y) ^ 2 * η x ^ 2 ≤
      4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
  have hform := formOn_eq_neg_two_mul hc S B f
    (fun x => f x * η x ^ 2) htest hBS hnb
  have hharm : ∑ x ∈ B, f x * η x ^ 2 * netLaplacian G c f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hf x hx]
    ring
  rw [hharm, mul_zero] at hform
  have hpt : ∀ x ∈ S, ∀ y ∈ G.neighborFinset x,
      c x y * (f x - f y) ^ 2 * η x ^ 2 ≤
        2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
          4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) := by
    intro x _ y _
    have hc0 := hc.nonneg x y
    nlinarith [caccioppoli_pointwise (f x) (f y) (η x) (η y),
      mul_nonneg hc0 (sq_nonneg (f x - f y)), mul_nonneg hc0 (sq_nonneg (η x - η y))]
  calc ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x - f y) ^ 2 * η x ^ 2
      ≤ ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
            4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpt x hx y hy
    _ = 2 * formOn G c S f (fun x => f x * η x ^ 2) +
          4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
      have h1 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))) =
          2 * formOn G c S f (fun x => f x * η x ^ 2) := by
        simp only [formOn, Finset.mul_sum]
      have h2 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) =
          4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        simp only [Finset.mul_sum]
      rw [show (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2))) =
          (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))) +
            ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib]
      rw [h1, h2]
    _ = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
      rw [hform]
      ring

end LatticeProb.Network
