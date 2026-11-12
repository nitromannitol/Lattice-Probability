import LatticeProb.LQG.WeylScalingLogShellCriterion
import LatticeProb.LQG.InternalMetricFiniteUnion
import LatticeProb.LQG.LengthMetricDerived
import LatticeProb.Topology.CornerSquareShells

/-!
# Covering an exponential shell by mesh squares

The exponential shell `A_k = {e^{-(k+1)} ≤ |x| ≤ e^{-k}}` is preconnected, and it is covered by the closed squares
`[t m, t m + t] × [t n, t n + t]` of the grid of mesh `t = e^{-k} / 32` which meet it, with `|m|, |n| ≤ 33`. Each such
square lies in the `e^{-(k+2)}`-neighbourhood of `A_k` (its diameter is at most `2 t = e^{-k} / 16 < e^{-(k+2)}`), and
their union is preconnected. Hence, for a Euclidean length metric `D`, the internal diameter of `A_k` in its
`e^{-(k+2)}`-neighbourhood is at most the sum, over a fixed finite set of grid indices, of the internal diameters of
the squares.

This reduces bounds on the internal diameter of exponential shells (multiscale chaining towards a point) to bounds on
the internal diameters of closed squares, the form in which tail estimates for LQG metrics are available.
-/

open Set Metric
open scoped ENNReal

namespace LatticeProb.LQG

/-- The closed square `[t m, t m + t] × [t n, t n + t]` of the grid of mesh `t`, for `p = (m, n)`. -/
def meshSquare (t : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  Icc (t * p.1) (t * p.1 + t) ×ℂ Icc (t * p.2) (t * p.2 + t)

/-- The grid indices `(m, n)` with `-33 ≤ m, n ≤ 32`. -/
irreducible_def expShellSquareIndex : Finset (ℤ × ℤ) :=
  Finset.Icc (-33) 32 ×ˢ Finset.Icc (-33) 32

theorem mem_expShellSquareIndex {p : ℤ × ℤ} :
    p ∈ expShellSquareIndex ↔ p.1 ∈ Finset.Icc (-33 : ℤ) 32 ∧ p.2 ∈ Finset.Icc (-33 : ℤ) 32 := by
  rw [expShellSquareIndex_def, Finset.mem_product]

/-- The mesh of the squares covering the `k`-th exponential shell. -/
noncomputable def expShellMesh (k : ℕ) : ℝ :=
  Real.exp (-(k : ℝ)) / 32

theorem expShellMesh_pos (k : ℕ) : 0 < expShellMesh k :=
  div_pos (Real.exp_pos _) (by norm_num)

open Classical in
/-- The grid indices of the squares of mesh `e^{-k} / 32` which meet the `k`-th exponential shell. -/
noncomputable irreducible_def expShellSquares (k : ℕ) : Finset (ℤ × ℤ) :=
  expShellSquareIndex.filter fun p => (meshSquare (expShellMesh k) p ∩ expShell k).Nonempty

theorem mem_expShellSquares {k : ℕ} {p : ℤ × ℤ} :
    p ∈ expShellSquares k ↔
      p ∈ expShellSquareIndex ∧ (meshSquare (expShellMesh k) p ∩ expShell k).Nonempty := by
  classical
  rw [expShellSquares_def, Finset.mem_filter]

theorem expShellSquares_subset (k : ℕ) : expShellSquares k ⊆ expShellSquareIndex :=
  fun _ hp => (mem_expShellSquares.1 hp).1

theorem isClosed_meshSquare (t : ℝ) (p : ℤ × ℤ) : IsClosed (meshSquare t p) :=
  isClosed_Icc.reProdIm isClosed_Icc

theorem isPreconnected_meshSquare (t : ℝ) (p : ℤ × ℤ) : IsPreconnected (meshSquare t p) :=
  (LatticeProb.Topology.convex_reProdIm (convex_Icc _ _) (convex_Icc _ _)).isPreconnected

/-- The exponential shell is the image of `[e^{-(k+1)}, e^{-k}] × ℝ` under polar coordinates; hence it is
preconnected. -/
theorem isPreconnected_expShell (k : ℕ) : IsPreconnected (expShell k) := by
  have himage : expShell k = (fun q : ℝ × ℝ => (q.1 : ℂ) * Complex.exp (q.2 * Complex.I)) ''
      (Icc (Real.exp (-((k : ℝ) + 1))) (Real.exp (-(k : ℝ))) ×ˢ univ) := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(‖x‖, Complex.arg x), ⟨⟨h1, h2⟩, mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I x⟩
    · rintro ⟨q, ⟨⟨h1, h2⟩, -⟩, rfl⟩
      have hq : 0 ≤ q.1 := (Real.exp_pos _).le.trans h1
      have hn : ‖(q.1 : ℂ) * Complex.exp (q.2 * Complex.I)‖ = q.1 := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hq]
      exact ⟨hn ▸ h1, hn ▸ h2⟩
  rw [himage]
  exact (isPreconnected_Icc.prod isPreconnected_univ).image _ (by fun_prop : Continuous _).continuousOn

/-- Every point of the `k`-th exponential shell lies in a square of mesh `e^{-k} / 32` meeting the shell. -/
theorem expShell_subset_biUnion_meshSquare (k : ℕ) :
    expShell k ⊆ ⋃ p ∈ expShellSquares k, meshSquare (expShellMesh k) p := by
  intro x hx
  have ht := expShellMesh_pos k
  have hxr : ‖x‖ ≤ 32 * expShellMesh k := by
    rw [expShellMesh, mul_div_cancel₀ _ (by norm_num : (32 : ℝ) ≠ 0)]
    exact hx.2
  -- the floor coordinates
  set m : ℤ := ⌊x.re / expShellMesh k⌋ with hm
  set n : ℤ := ⌊x.im / expShellMesh k⌋ with hn
  have hmem : x ∈ meshSquare (expShellMesh k) (m, n) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have := Int.floor_le (x.re / expShellMesh k)
      calc expShellMesh k * (m : ℝ) ≤ expShellMesh k * (x.re / expShellMesh k) :=
            mul_le_mul_of_nonneg_left this ht.le
        _ = x.re := by field_simp
    · have := Int.lt_floor_add_one (x.re / expShellMesh k)
      calc x.re = expShellMesh k * (x.re / expShellMesh k) := by field_simp
        _ ≤ expShellMesh k * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_left this.le ht.le
        _ = expShellMesh k * m + expShellMesh k := by ring
    · have := Int.floor_le (x.im / expShellMesh k)
      calc expShellMesh k * (n : ℝ) ≤ expShellMesh k * (x.im / expShellMesh k) :=
            mul_le_mul_of_nonneg_left this ht.le
        _ = x.im := by field_simp
    · have := Int.lt_floor_add_one (x.im / expShellMesh k)
      calc x.im = expShellMesh k * (x.im / expShellMesh k) := by field_simp
        _ ≤ expShellMesh k * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left this.le ht.le
        _ = expShellMesh k * n + expShellMesh k := by ring
  -- the floor coordinates lie in `[-33, 32]`
  have hcoord : ∀ a : ℝ, |a| ≤ ‖x‖ → (⌊a / expShellMesh k⌋ : ℤ) ∈ Finset.Icc (-33 : ℤ) 32 := by
    intro a ha
    have hb : |a / expShellMesh k| ≤ 32 := by
      rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
      linarith
    obtain ⟨hb1, hb2⟩ := abs_le.1 hb
    rw [Finset.mem_Icc]
    constructor
    · have h1 : ((-33 : ℤ) : ℝ) ≤ a / expShellMesh k := by push_cast; linarith
      have h2 := Int.le_floor.2 h1
      exact h2
    · exact Int.lt_add_one_iff.1 (Int.floor_lt.2 (by push_cast; linarith))
  have hidx : (m, n) ∈ expShellSquares k :=
    mem_expShellSquares.2 ⟨mem_expShellSquareIndex.2 ⟨hcoord _ (Complex.abs_re_le_norm x),
      hcoord _ (Complex.abs_im_le_norm x)⟩, ⟨x, hmem, hx⟩⟩
  exact mem_biUnion hidx hmem

/-- `e^{-k} / 16 < e^{-(k+2)}`. -/
theorem two_mul_expShellMesh_lt (k : ℕ) : 2 * expShellMesh k < Real.exp (-((k : ℝ) + 2)) := by
  have he : Real.exp 2 < 16 := by
    have h1 : Real.exp 1 < 4 := Real.exp_one_lt_d9.trans (by norm_num)
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]
    nlinarith [Real.exp_pos 1]
  have hk : Real.exp (-((k : ℝ) + 2)) = Real.exp (-(k : ℝ)) / Real.exp 2 := by
    rw [neg_add, Real.exp_add, Real.exp_neg 2, div_eq_mul_inv]
  rw [hk, expShellMesh, lt_div_iff₀ (Real.exp_pos 2)]
  have := Real.exp_pos (-(k : ℝ))
  nlinarith

/-- A square of mesh `t` has Euclidean diameter at most `2 t`. -/
theorem dist_le_two_mul_of_mem_meshSquare {t : ℝ} {p : ℤ × ℤ} {x y : ℂ} (hx : x ∈ meshSquare t p)
    (hy : y ∈ meshSquare t p) : dist x y ≤ 2 * t := by
  obtain ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, ⟨hy3, hy4⟩⟩ := hy
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  have h1 : |x.re - y.re| ≤ t := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have h2 : |x.im - y.im| ≤ t := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  linarith

/-- The squares meeting the `k`-th exponential shell lie in its `e^{-(k+2)}`-neighbourhood. -/
theorem biUnion_meshSquare_subset_thickening (k : ℕ) :
    (⋃ p ∈ expShellSquares k, meshSquare (expShellMesh k) p) ⊆
      thickening (Real.exp (-((k : ℝ) + 2))) (expShell k) := by
  intro y hy
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 hy
  obtain ⟨x, hxp, hx⟩ := (mem_expShellSquares.1 hp).2
  exact mem_thickening_iff.2 ⟨x, hx,
    (dist_le_two_mul_of_mem_meshSquare hyp hxp).trans_lt (two_mul_expShellMesh_lt k)⟩

/-- The union of the squares meeting the `k`-th exponential shell is preconnected. -/
theorem isPreconnected_biUnion_meshSquare (k : ℕ) :
    IsPreconnected (⋃ p ∈ expShellSquares k, meshSquare (expShellMesh k) p) := by
  set K := ⋃ p ∈ expShellSquares k, meshSquare (expShellMesh k) p with hK
  have hAK : expShell k ⊆ K := expShell_subset_biUnion_meshSquare k
  obtain ⟨x₀, hx₀⟩ : (expShell k).Nonempty := ⟨Real.exp (-(k : ℝ)), by
    have h0 : (0 : ℝ) ≤ Real.exp (-(k : ℝ)) := (Real.exp_pos _).le
    have hn : ‖((Real.exp (-(k : ℝ)) : ℝ) : ℂ)‖ = Real.exp (-(k : ℝ)) := Complex.norm_of_nonneg h0
    refine ⟨?_, ?_⟩
    · rw [hn]; exact Real.exp_le_exp.2 (by linarith)
    · rw [hn]⟩
  refine isPreconnected_of_forall x₀ fun y hy => ?_
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 hy
  obtain ⟨z, hzp, hz⟩ := (mem_expShellSquares.1 hp).2
  refine ⟨expShell k ∪ meshSquare (expShellMesh k) p, union_subset hAK
    (subset_biUnion_of_mem (u := fun p => meshSquare (expShellMesh k) p) hp), Or.inl hx₀, Or.inr hyp, ?_⟩
  exact (isPreconnected_expShell k).union z hz hzp (isPreconnected_meshSquare _ p)

/-- **Internal diameter of an exponential shell through mesh squares.** For a Euclidean length metric `D`, if every
square of mesh `e^{-k} / 32` with index in `[-33, 32]²` has `D`-internal diameter at most `A p`, then the internal
diameter of the `k`-th exponential shell in its `e^{-(k+2)}`-neighbourhood is at most `∑ₚ A p`. -/
theorem IsEuclideanLengthMetric.internalDiam_expShell_le_sum {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (k : ℕ) {A : ℤ × ℤ → ℝ≥0∞}
    (hA : ∀ p ∈ expShellSquareIndex, ∀ u ∈ meshSquare (expShellMesh k) p, ∀ v ∈ meshSquare (expShellMesh k) p,
      internalMetric D (meshSquare (expShellMesh k) p) u v ≤ A p) :
    internalDiam D (Real.exp (-((k : ℝ) + 2))) (expShell k) ≤ ∑ p ∈ expShellSquareIndex, A p := by
  have hsum := hD.internalMetric_biUnion_le_sum (isPreconnected_biUnion_meshSquare k)
    (fun p _ => isClosed_meshSquare _ p) (fun p hp => hA p (expShellSquares_subset k hp))
  refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
  calc internalMetric D (thickening (Real.exp (-((k : ℝ) + 2))) (expShell k)) u v
      ≤ internalMetric D (⋃ p ∈ expShellSquares k, meshSquare (expShellMesh k) p) u v :=
        internalMetric_anti_set (biUnion_meshSquare_subset_thickening k) u v
    _ ≤ ∑ p ∈ expShellSquares k, A p :=
        hsum u (expShell_subset_biUnion_meshSquare k hu) v (expShell_subset_biUnion_meshSquare k hv)
    _ ≤ ∑ p ∈ expShellSquareIndex, A p :=
        Finset.sum_le_sum_of_subset (expShellSquares_subset k)

end LatticeProb.LQG
