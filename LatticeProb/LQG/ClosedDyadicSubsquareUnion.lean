import LatticeProb.LQG.InternalMetricDyadicChaining
import LatticeProb.LQG.InternalMetricFiniteUnionOfTriangle
import LatticeProb.Topology.CornerSquareShells

/-!
# Grid rectangles of closed dyadic subsquares

Let `S = [a, a + s] × [b, b + s]` and `h = 2⁻ᵐ s`. The closed rectangle
`[a + i₀ h, a + (i₀ + K + 1) h] × [b + j₀ h, b + (j₀ + L + 1) h]` is the union of the `(K + 1)(L + 1)` closed dyadic
subsquares `S_{m, i₀ + k, j₀ + l}` (`k ≤ K`, `l ≤ L`) of level `m` of `S`. Since the rectangle is convex, hence
preconnected, its internal diameter for a function with the triangle inequality is at most the sum of the internal
diameters of these subsquares (`internalMetric_biUnion_le_sum_of_ofReal_triangle`).

## Main statements

* `LatticeProb.LQG.closedDyadicSubsquare_biUnion_eq`: the rectangle is the union of the subsquares.
* `LatticeProb.LQG.internalMetric_closedDyadicSubsquare_grid_le`: the internal diameter of the rectangle is at most
  `(K + 1)(L + 1) A` when every subsquare has internal diameter at most `A`.
-/

open Set
open scoped ENNReal

namespace LatticeProb.LQG

/-- Consecutive closed intervals of length `h ≥ 0` on the grid `a + h ℤ` fill a closed interval:
`⋃_{k ≤ K} [a + (i₀ + k) h, a + (i₀ + k + 1) h] = [a + i₀ h, a + (i₀ + K + 1) h]`. -/
theorem biUnion_range_Icc_add_mul (a h : ℝ) (hh : 0 ≤ h) (i₀ K : ℕ) :
    ⋃ k ∈ Finset.range (K + 1), Icc (a + ((i₀ + k : ℕ) : ℝ) * h) (a + (((i₀ + k : ℕ) : ℝ) + 1) * h) =
      Icc (a + (i₀ : ℝ) * h) (a + ((i₀ : ℝ) + K + 1) * h) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, ih, Set.union_comm]
    have e : ((i₀ + (K + 1) : ℕ) : ℝ) = (i₀ : ℝ) + K + 1 := by push_cast; ring
    have hK : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
    rw [e, Set.Icc_union_Icc_eq_Icc (by nlinarith [mul_nonneg hK hh]) (by nlinarith)]
    congr 2
    push_cast
    ring

/-- The union over a product of finite index sets of the products `X i ×ℂ Y j` is the product of the unions. -/
theorem biUnion_product_reProdIm {ι κ : Type*} (A : Finset ι) (B : Finset κ) (X : ι → Set ℝ) (Y : κ → Set ℝ) :
    ⋃ ij ∈ A ×ˢ B, X ij.1 ×ℂ Y ij.2 = (⋃ i ∈ A, X i) ×ℂ (⋃ j ∈ B, Y j) := by
  ext z
  simp only [mem_iUnion, Finset.mem_product, Complex.mem_reProdIm, exists_prop, Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨hi, hj⟩, hx, hy⟩
    exact ⟨⟨i, hi, hx⟩, ⟨j, hj, hy⟩⟩
  · rintro ⟨⟨i, hi, hx⟩, ⟨j, hj, hy⟩⟩
    exact ⟨i, j, ⟨hi, hj⟩, hx, hy⟩

/-- **A grid rectangle is the union of its closed dyadic subsquares.** For `s ≥ 0` and `h = 2⁻ᵐ s`, the closed
rectangle `[a + i₀ h, a + (i₀ + K + 1) h] × [b + j₀ h, b + (j₀ + L + 1) h]` is the union of the closed dyadic subsquares
`S_{m, i₀ + k, j₀ + l}` of level `m` of `[a, a + s] × [b, b + s]`, `k ≤ K`, `l ≤ L`. -/
theorem closedDyadicSubsquare_biUnion_eq (a b s : ℝ) (hs : 0 ≤ s) (m i₀ j₀ K L : ℕ) :
    ⋃ kl ∈ Finset.range (K + 1) ×ˢ Finset.range (L + 1),
        closedDyadicSubsquare a b s m (i₀ + kl.1) (j₀ + kl.2) =
      Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
        Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m)) := by
  have hh : 0 ≤ s / 2 ^ m := by positivity
  have h := biUnion_product_reProdIm (Finset.range (K + 1)) (Finset.range (L + 1))
    (fun k => Icc (a + ((i₀ + k : ℕ) : ℝ) * (s / 2 ^ m)) (a + (((i₀ + k : ℕ) : ℝ) + 1) * (s / 2 ^ m)))
    (fun l => Icc (b + ((j₀ + l : ℕ) : ℝ) * (s / 2 ^ m)) (b + (((j₀ + l : ℕ) : ℝ) + 1) * (s / 2 ^ m)))
  rw [biUnion_range_Icc_add_mul a _ hh i₀ K, biUnion_range_Icc_add_mul b _ hh j₀ L] at h
  exact h

/-- **Internal diameter of a grid rectangle of closed dyadic subsquares.** Let `E` satisfy the triangle inequality
`ofReal (E x z) ≤ ofReal (E x y) + ofReal (E y z)`, `s ≥ 0` and `h = 2⁻ᵐ s`. If each closed dyadic subsquare
`S_{m, i₀ + k, j₀ + l}` (`k ≤ K`, `l ≤ L`) of `[a, a + s] × [b, b + s]` has `E`-internal diameter at most `A`, then the
rectangle `R = [a + i₀ h, a + (i₀ + K + 1) h] × [b + j₀ h, b + (j₀ + L + 1) h]` has `E`-internal diameter at most
`(K + 1)(L + 1) A`. -/
theorem internalMetric_closedDyadicSubsquare_grid_le {E : ℂ → ℂ → ℝ}
    (htri : ∀ x y z, ENNReal.ofReal (E x z) ≤ ENNReal.ofReal (E x y) + ENNReal.ofReal (E y z))
    {a b s : ℝ} (hs : 0 ≤ s) {m i₀ j₀ K L : ℕ} {A : ℝ≥0∞}
    (hA : ∀ k ≤ K, ∀ l ≤ L, ∀ u ∈ closedDyadicSubsquare a b s m (i₀ + k) (j₀ + l),
      ∀ v ∈ closedDyadicSubsquare a b s m (i₀ + k) (j₀ + l),
        internalMetric E (closedDyadicSubsquare a b s m (i₀ + k) (j₀ + l)) u v ≤ A) :
    ∀ u ∈ Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
        Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m)),
      ∀ v ∈ Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
        Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m)),
      internalMetric E (Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
        Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m))) u v ≤
        ((K : ℝ≥0∞) + 1) * ((L : ℝ≥0∞) + 1) * A := by
  rw [← closedDyadicSubsquare_biUnion_eq a b s hs m i₀ j₀ K L]
  have hK : IsPreconnected (⋃ kl ∈ Finset.range (K + 1) ×ˢ Finset.range (L + 1),
      closedDyadicSubsquare a b s m (i₀ + kl.1) (j₀ + kl.2)) := by
    rw [closedDyadicSubsquare_biUnion_eq a b s hs m i₀ j₀ K L]
    exact (LatticeProb.Topology.convex_reProdIm (convex_Icc _ _) (convex_Icc _ _)).isPreconnected
  have h := internalMetric_biUnion_le_sum_of_ofReal_triangle htri hK
    (fun _ _ => isClosed_Icc.reProdIm isClosed_Icc) (A := fun _ => A) (fun kl hkl => by
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hkl
      exact hA kl.1 (Nat.lt_succ_iff.1 hkl.1) kl.2 (Nat.lt_succ_iff.1 hkl.2))
  intro u hu v hv
  refine (h u hu v hv).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end LatticeProb.LQG
