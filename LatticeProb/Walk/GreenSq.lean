/-
The square of the truncated Green function, and the correlation of two
truncated Green functions, as double sums of the return probability.

`∑_y g_m(y) g_n(y) = ∑_{a<m} ∑_{b<n} p_{a+b}(0)`.  The proof is Chapman-Kolmogorov
(`srwHeat_add`) together with the symmetry of the kernel (`srwHeat_neg`), which
turn `∑_y p_a(y) p_b(y)` into `p_{a+b}(0)`; the rest is exchanging a `tsum` over
the sites with two finite sums, which is free because each `p_a(·)` is finitely
supported.

Grouping the double sum by `s = a + b` reduces it to a one-dimensional sum, with
the number of pairs at level `s` as the weight.  That weight is exactly
`min (s+1) m` when `n = m` and `s < m`, and at most `min (s+1) m` always, which
is what makes the double sum comparable with `∑_s min(s, t) s^{-d/2}` once the
on-diagonal bounds of `LatticeProb/Walk/SRWDiag.lean` are put in.
-/
import LatticeProb.Walk.SRWDiag

noncomputable section

namespace LatticeProb

variable {d : ℕ}

/-! ### The pairing of two kernels -/

/-- **The `ℓ²` pairing of two kernels is the return probability at the sum of
the times.**  `∑_y p_a(0,y) p_b(0,y) = p_{a+b}(0,0)`. -/
theorem tsum_srwHeat_mul (a b : ℕ) :
    ∑' y : Site d, srwHeat d a y * srwHeat d b y = srwHeat d (a + b) 0 := by
  rw [srwHeat_add a b 0]
  refine tsum_congr fun y => ?_
  rw [show (0 : Site d) - y = -y by ring, srwHeat_neg]

/-- **The correlation of two truncated Green functions.**
`∑_y g_m(y) g_n(y) = ∑_{a<m} ∑_{b<n} p_{a+b}(0,0)`. -/
theorem tsum_srwGreen_mul (m n : ℕ) :
    ∑' y : Site d, srwGreen d m y * srwGreen d n y
      = ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, srwHeat d (a + b) 0 := by
  have h1 : ∀ y : Site d, srwGreen d m y * srwGreen d n y
      = ∑ a ∈ Finset.range m, srwHeat d a y * srwGreen d n y := by
    intro y
    rw [srwGreen, Finset.sum_mul]
  rw [tsum_congr h1,
    Summable.tsum_finsetSum (fun a _ => summable_srwHeat_mul a (fun y => srwGreen d n y))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∀ y : Site d, srwHeat d a y * srwGreen d n y
      = ∑ b ∈ Finset.range n, srwHeat d a y * srwHeat d b y := by
    intro y
    rw [srwGreen, Finset.mul_sum]
  rw [tsum_congr h2,
    Summable.tsum_finsetSum (fun b _ => summable_srwHeat_mul a (fun y => srwHeat d b y))]
  exact Finset.sum_congr rfl fun b _ => tsum_srwHeat_mul a b

/-- **The variance scale as a double sum.**
`∑_y g_t(y)^2 = ∑_{a<t} ∑_{b<t} p_{a+b}(0,0)`. -/
theorem tsum_srwGreen_sq (t : ℕ) :
    ∑' y : Site d, srwGreen d t y ^ 2
      = ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, srwHeat d (a + b) 0 := by
  rw [← tsum_srwGreen_mul t t]
  exact tsum_congr fun y => sq _

/-! ### Grouping the double sum by the total time -/

/-- The number of pairs `(a,b)` with `a < m`, `b < n` and `a + b = s`. -/
def pairCount (m n s : ℕ) : ℕ :=
  (((Finset.range m) ×ˢ (Finset.range n)).filter fun p => p.1 + p.2 = s).card

/-- **A double sum over a product of intervals, grouped by the sum of the
indices.** -/
theorem sum_sum_add_eq (m n : ℕ) (f : ℕ → ℝ) :
    ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, f (a + b)
      = ∑ s ∈ Finset.range (m + n), (pairCount m n s : ℝ) * f s := by
  classical
  have hmaps : ∀ p ∈ (Finset.range m) ×ˢ (Finset.range n),
      p.1 + p.2 ∈ Finset.range (m + n) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact Finset.mem_range.mpr (by omega)
  have hfib := Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2)
    (f := fun p : ℕ × ℕ => f (p.1 + p.2)) hmaps
  rw [← Finset.sum_product', ← hfib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pairCount]
  have hcongr : ∀ p ∈ (((Finset.range m) ×ˢ (Finset.range n)).filter
      fun p : ℕ × ℕ => p.1 + p.2 = s), f (p.1 + p.2) = f s := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]

/-- The number of pairs at level `s` is at most `min (s+1) m`. -/
theorem pairCount_le (m n s : ℕ) : pairCount m n s ≤ min (s + 1) m := by
  classical
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1)
      (((Finset.range m) ×ˢ (Finset.range n)).filter fun p : ℕ × ℕ => p.1 + p.2 = s) := by
    intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_range] at hp hq
    have h1 : p.1 = q.1 := hpq
    exact Prod.ext h1 (by omega)
  refine le_min ?_ ?_
  · calc pairCount m n s ≤ (Finset.range (s + 1)).card := by
          refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1) ?_ hinj
          intro p hp
          obtain ⟨hmem, hsum⟩ := Finset.mem_filter.mp hp
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
          rw [Finset.mem_range] at h1 h2
          have hs : p.1 + p.2 = s := hsum
          refine Finset.mem_range.mpr ?_
          show p.1 < s + 1
          omega
      _ = s + 1 := Finset.card_range _
  · calc pairCount m n s ≤ (Finset.range m).card := by
          refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1) ?_ hinj
          intro p hp
          exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      _ = m := Finset.card_range _

/-- Below the horizon every pair at level `s` is present. -/
theorem pairCount_of_lt {m n s : ℕ} (hm : s < m) (hn : s < n) : pairCount m n s = s + 1 := by
  classical
  rw [pairCount]
  have himg : (((Finset.range m) ×ˢ (Finset.range n)).filter fun p : ℕ × ℕ => p.1 + p.2 = s)
      = (Finset.range (s + 1)).image fun a => (a, s - a) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨p.1, by omega, Prod.ext rfl ?_⟩
      simp only
      omega
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by simp; omega⟩
  rw [himg, Finset.card_image_of_injOn (fun a _ b _ h => (Prod.mk.injEq _ _ _ _ ▸ h).1),
    Finset.card_range]

/-! ### The variance scale between two one-dimensional sums -/

/-- **The variance scale is at most the one-dimensional sum with the weight
`min (s+1) t`.** -/
theorem tsum_srwGreen_sq_le (t : ℕ) :
    ∑' y : Site d, srwGreen d t y ^ 2
      ≤ ∑ s ∈ Finset.range (2 * t), (min (s + 1) t : ℝ) * srwHeat d s 0 := by
  rw [tsum_srwGreen_sq t, sum_sum_add_eq t t (fun s => srwHeat d s 0),
    show t + t = 2 * t by ring]
  refine Finset.sum_le_sum fun s _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (srwHeat_nonneg s 0)
  exact_mod_cast pairCount_le t t s

/-- **The variance scale is at least the one-dimensional sum over the times
below the horizon, with the weight `s+1`.** -/
theorem le_tsum_srwGreen_sq (t : ℕ) :
    ∑ s ∈ Finset.range t, ((s : ℝ) + 1) * srwHeat d s 0
      ≤ ∑' y : Site d, srwGreen d t y ^ 2 := by
  rw [tsum_srwGreen_sq t, sum_sum_add_eq t t (fun s => srwHeat d s 0),
    show t + t = 2 * t by ring]
  calc ∑ s ∈ Finset.range t, ((s : ℝ) + 1) * srwHeat d s 0
      = ∑ s ∈ Finset.range t, (pairCount t t s : ℝ) * srwHeat d s 0 := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [Finset.mem_range] at hs
        rw [pairCount_of_lt hs hs]
        push_cast
        ring
    _ ≤ ∑ s ∈ Finset.range (2 * t), (pairCount t t s : ℝ) * srwHeat d s 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by intro s hs; rw [Finset.mem_range] at hs ⊢; omega)
          (fun s _ _ => mul_nonneg (Nat.cast_nonneg _) (srwHeat_nonneg s 0))

end LatticeProb
