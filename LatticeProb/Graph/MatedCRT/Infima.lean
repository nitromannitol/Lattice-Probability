import LatticeProb.Graph.MatedCRT.FromPaths

/-!
# Attained coordinate infima for the mated-CRT path graph

For lattice vertices `a < b` of mesh `ε`, the three closed intervals `[a - ε, a]`,
`[b - ε, b]` and `[a, b - ε]` in Definition 1.1 of
[Internal DLA on mated-CRT maps](https://arxiv.org/abs/2211.04891v2) are nonempty and
compact, so each real infimum in `coordinateCondition` is the attained minimum of a continuous
path.  The middle interval is nonempty because distinct lattice points differ by at least `ε`.
-/

namespace LatticeProb.MatedCRT

/-- Distinct lattice vertices in increasing order differ by at least the mesh `ε`. -/
theorem orderedPair_add_le (ε : Set.Ioi (0 : ℝ)) (p : OrderedPair ε) :
    p.val.1.val + ε.val ≤ p.val.2.val := by
  obtain ⟨i, hi⟩ := p.val.1.property
  obtain ⟨j, hj⟩ := p.val.2.property
  have hε : 0 < ε.val := ε.property
  have hlt : p.val.1.val < p.val.2.val := p.property
  have hij : i < j := by
    have h : ε.val * (i : ℝ) < ε.val * (j : ℝ) := by
      rw [← hi, ← hj]
      exact hlt
    exact_mod_cast lt_of_mul_lt_mul_left h hε.le
  have hij1 : i + 1 ≤ j := by omega
  have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij1
  calc p.val.1.val + ε.val = ε.val * ((i : ℝ) + 1) := by rw [hi]; ring
    _ ≤ ε.val * (j : ℝ) := mul_le_mul_of_nonneg_left hcast hε.le
    _ = p.val.2.val := hj.symm

/-- The infimum of a continuous path over a nonempty closed interval is attained. -/
theorem isLeast_sInf_image_Icc (X : RootedPath) {l u : ℝ} (h : l ≤ u) :
    IsLeast ((X.val : ℝ → ℝ) '' Set.Icc l u) (sInf ((X.val : ℝ → ℝ) '' Set.Icc l u)) :=
  (isCompact_Icc.image X.val.continuous).isLeast_sInf ((Set.nonempty_Icc.2 h).image _)

/-- All three real infima in the coordinate condition are attained minima of the path. -/
theorem coordinateInfima_spec : ∀ (ε : Set.Ioi (0 : ℝ)) (X : RootedPath) (p : OrderedPair ε),
  let a : ℝ := p.val.1.val
  let b : ℝ := p.val.2.val
  IsLeast ((X.val : ℝ → ℝ) '' Set.Icc (a - ε.val) a)
    (sInf ((X.val : ℝ → ℝ) '' Set.Icc (a - ε.val) a)) ∧
  IsLeast ((X.val : ℝ → ℝ) '' Set.Icc (b - ε.val) b)
    (sInf ((X.val : ℝ → ℝ) '' Set.Icc (b - ε.val) b)) ∧
  IsLeast ((X.val : ℝ → ℝ) '' Set.Icc a (b - ε.val))
    (sInf ((X.val : ℝ → ℝ) '' Set.Icc a (b - ε.val))) := by
  intro ε X p
  dsimp only
  have hε : 0 < ε.val := ε.property
  have hgap := orderedPair_add_le ε p
  exact ⟨isLeast_sInf_image_Icc X (by linarith), isLeast_sInf_image_Icc X (by linarith),
    isLeast_sInf_image_Icc X (by linarith)⟩

end LatticeProb.MatedCRT
