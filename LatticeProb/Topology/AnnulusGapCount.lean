/-
# Counting the gaps between crossing continua of a round annulus

Let `K ⊆ ℂ` be closed, `x ∈ ℂ` and `0 ≤ s < t`. Suppose `N ≥ 2` crossing continua `P 0, …, P (N - 1)` of the
closed annulus `closedBall x t \ ball x s` avoid `K` and meet the outer circle only at the points
`circleMap x t (θ i)`, with `θ 0 < θ 1 < ⋯ < θ (N - 1) < θ 0 + 2π`, and that no two of these points are joined by a
preconnected subset of `closedBall x t \ K`. Then at least `N` components of `K ∩ {z | s ≤ dist z x ≤ t}` cross the
annulus. Each gap `(θ i, θ (i + 1))` (with `θ N = θ 0 + 2π`) carries a crossing component by
`exists_crossing_component_meets_gap`, and two different gaps carry different components by the alternation lemma
`false_of_alternating_annulus_crossings`.
-/
import LatticeProb.Topology.AnnulusGaps

open Set Metric Complex

namespace LatticeProb.Topology

/-- A component of `K ∩ (dist · x) ⁻¹' [s, t]`, for a closed set `K`, is a continuum of the closed annulus
`closedBall x t \ ball x s` contained in `K`. -/
theorem isCompact_isConnected_of_mem_connectedComponentsIn_annulus {K : Set ℂ} (hK : IsClosed K)
    {x : ℂ} {s t : ℝ} {C : Set ℂ}
    (hC : C ∈ connectedComponentsIn (K ∩ (fun z => dist z x) ⁻¹' Icc s t)) :
    IsCompact C ∧ IsConnected C ∧ C ⊆ K ∧ C ⊆ closedBall x t \ ball x s := by
  unfold connectedComponentsIn at hC
  obtain ⟨y, hy, rfl⟩ := hC
  have hScl : IsClosed (K ∩ (fun z => dist z x) ⁻¹' Icc s t) :=
    hK.inter (isClosed_Icc.preimage (continuous_id.dist continuous_const))
  have hCcl : IsClosed (connectedComponentIn (K ∩ (fun z => dist z x) ⁻¹' Icc s t) y) :=
    closure_subset_iff_isClosed.1
      (isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hy))
        (closure_minimal (connectedComponentIn_subset _ _) hScl))
  have hCA : connectedComponentIn (K ∩ (fun z => dist z x) ⁻¹' Icc s t) y ⊆
      closedBall x t \ ball x s :=
    (connectedComponentIn_subset _ _).trans (inter_preimage_dist_Icc K x s t ▸ inter_subset_right)
  exact ⟨(isCompact_closedBall x t).of_isClosed_subset hCcl (hCA.trans sdiff_subset),
    isConnected_connectedComponentIn_iff.2 hy, (connectedComponentIn_subset _ _).trans inter_subset_left,
    hCA⟩

/-- **Counting gaps between crossing continua.** Let `K ⊆ ℂ` be closed, `0 ≤ s < t`, `N ≥ 2`, and let
`θ : ℕ → ℝ` be strictly increasing on `[0, N]` with `θ N = θ 0 + 2π` and gaps `θ (i + 1) - θ i ≥ 2ε` (`i < N`).
For `i ≤ N` let `P i` be a continuum of the closed annulus `closedBall x t \ ball x s` disjoint from `K`, meeting
`sphere x s` at `a i` and meeting `sphere x t` only at `circleMap x t (θ i)`. Assume that the arcs of angular radius
`ε` about the `θ i` miss `K` and that no preconnected subset of `closedBall x t \ K` contains two of the points
`circleMap x t (θ i)`, `i < N`. If the set of components of `K ∩ (dist · x) ⁻¹' [s, t]` meeting both
`{dist · x = s}` and `{dist · x = t}` is finite, it has at least `N` elements. -/
theorem le_ncard_annulus_crossings_of_sorted_gaps {x : ℂ} {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {K : Set ℂ} (hK : IsClosed K)
    (hT : {U ∈ connectedComponentsIn (K ∩ (fun z => dist z x) ⁻¹' Icc s t) |
      (∃ p ∈ U, dist p x = s) ∧ ∃ p ∈ U, dist p x = t}.Finite)
    {N : ℕ} (hN : 2 ≤ N) {θ : ℕ → ℝ} (hθ : StrictMonoOn θ (Iic N))
    (hθN : θ N = θ 0 + 2 * Real.pi) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ i < N, θ i + 2 * ε ≤ θ (i + 1))
    (hεK : ∀ i < N, ∀ γ ∈ Ioo (θ i - ε) (θ i + ε), circleMap x t γ ∉ K)
    {P : ℕ → Set ℂ} {a : ℕ → ℂ}
    (hP : ∀ i ≤ N, IsCompact (P i)) (hPc : ∀ i ≤ N, IsConnected (P i))
    (hPA : ∀ i ≤ N, P i ⊆ closedBall x t \ ball x s)
    (haP : ∀ i ≤ N, a i ∈ P i) (ha : ∀ i ≤ N, dist (a i) x = s)
    (hbP : ∀ i ≤ N, circleMap x t (θ i) ∈ P i)
    (hPt : ∀ i ≤ N, ∀ z ∈ P i, dist z x = t → z = circleMap x t (θ i))
    (hPK : ∀ i ≤ N, Disjoint (P i) K)
    (hjoin : ∀ i < N, ∀ j < N, i ≠ j → ∀ Z ⊆ closedBall x t \ K, IsPreconnected Z →
      circleMap x t (θ i) ∈ Z → circleMap x t (θ j) ∉ Z) :
    N ≤ {U ∈ connectedComponentsIn (K ∩ (fun z => dist z x) ⁻¹' Icc s t) |
      (∃ p ∈ U, dist p x = s) ∧ ∃ p ∈ U, dist p x = t}.ncard := by
  set T := {U ∈ connectedComponentsIn (K ∩ (fun z => dist z x) ⁻¹' Icc s t) |
      (∃ p ∈ U, dist p x = s) ∧ ∃ p ∈ U, dist p x = t} with hTdef
  have hpi := Real.pi_pos
  have hmono : ∀ {i j : ℕ}, i < j → j ≤ N → θ i < θ j := fun {i j} hij hj =>
    hθ (mem_Iic.2 (hij.le.trans hj)) (mem_Iic.2 hj) hij
  have hmono' : ∀ {i j : ℕ}, i ≤ j → j ≤ N → θ i ≤ θ j := fun {i j} hij hj =>
    hθ.monotoneOn (mem_Iic.2 (hij.trans hj)) (mem_Iic.2 hj) hij
  have heN : circleMap x t (θ N) = circleMap x t (θ 0) := by
    rw [hθN, periodic_circleMap x t (θ 0)]
  -- each gap carries a crossing component
  have hpair : ∀ i < N, ∃ C : Set ℂ, ∃ α : ℝ, C ∈ T ∧ α ∈ Icc (θ i + ε) (θ (i + 1) - ε) ∧
      circleMap x t α ∈ C := by
    intro i hi
    have hi1 : i + 1 ≤ N := hi
    have hlt : θ (i + 1) < θ i + 2 * Real.pi := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [← hθN]
        exact hmono (by omega) le_rfl
      · have h1 := hmono' hi1 le_rfl
        have h2 := hmono hi0 hi.le
        linarith
    have hεK' : ∀ γ ∈ Ioo (θ (i + 1) - ε) (θ (i + 1) + ε), circleMap x t γ ∉ K := by
      rcases Nat.lt_or_ge (i + 1) N with h | h
      · exact hεK (i + 1) h
      · have hiN : i + 1 = N := le_antisymm hi1 h
        intro γ hγ
        rw [← (periodic_circleMap x t).sub_eq γ]
        apply hεK 0 (by omega)
        rw [hiN, hθN] at hγ
        constructor <;> linarith [hγ.1, hγ.2]
    have hjoin' : ∀ Z ⊆ closedBall x t \ K, IsPreconnected Z → circleMap x t (θ i) ∈ Z →
        circleMap x t (θ (i + 1)) ∉ Z := by
      rcases Nat.lt_or_ge (i + 1) N with h | h
      · exact hjoin i hi (i + 1) h (by omega)
      · have hiN : i + 1 = N := le_antisymm hi1 h
        intro Z hZ hZc hbZ hb'Z
        rw [hiN, heN] at hb'Z
        exact hjoin 0 (by omega) i hi (by omega) Z hZ hZc hb'Z hbZ
    obtain ⟨C, hCmem, ⟨hCs, hCt⟩, α, hα, hαC⟩ := exists_crossing_component_meets_gap hs hst hK
      (hP i hi.le) (hPc i hi.le) (hP (i + 1) hi1) (hPc (i + 1) hi1) (hPA i hi.le) (hPA (i + 1) hi1)
      (haP i hi.le) (ha i hi.le) (haP (i + 1) hi1) (ha (i + 1) hi1) (hbP i hi.le) (hbP (i + 1) hi1)
      (hPt i hi.le) (hPt (i + 1) hi1) (hPK i hi.le) (hPK (i + 1) hi1) hε (hgap i hi) hlt
      (hεK i hi) hεK' hjoin'
    exact ⟨C, α, ⟨hCmem, hCs, hCt⟩, hα, hαC⟩
  choose! C α hCT hα hαC using hpair
  -- different gaps carry different components
  have hne : ∀ i j, i < j → j < N → C i ≠ C j := by
    intro i j hij hj hCij
    have hiN : i < N := hij.trans hj
    obtain ⟨hCc, hCconn, hCK, hCA⟩ :=
      isCompact_isConnected_of_mem_connectedComponentsIn_annulus hK (mem_sep_iff.1 (hCT i hiN)).1
    have hi1 : i + 1 ≤ N := hiN
    have hj1 : j + 1 ≤ N := hj
    have hαi := hα i hiN
    have hαj := hα j hj
    have h1 := hmono' (show i + 1 ≤ j by omega) hj.le
    have h2 := hmono' hj1 le_rfl
    have h3 := hmono' (Nat.zero_le i) hiN.le
    have hαjC : circleMap x t (α j) ∈ C i := by
      rw [hCij]
      exact hαC j hj
    exact false_of_alternating_annulus_crossings hs hst (θ₁ := α i) (θ₂ := θ (i + 1)) (θ₃ := α j)
      (θ₄ := θ (j + 1)) (by linarith [hαi.2]) (by linarith [hαj.1]) (by linarith [hαj.2])
      (by linarith [hαi.1]) (hP (i + 1) hi1) (hPc (i + 1) hi1) (hP (j + 1) hj1) (hPc (j + 1) hj1)
      (hPA (i + 1) hi1) (hPA (j + 1) hj1) (haP (i + 1) hi1) (mem_sphere.2 (ha (i + 1) hi1))
      (haP (j + 1) hj1) (mem_sphere.2 (ha (j + 1) hj1)) hCc hCconn hCA
      (disjoint_union_right.2
        ⟨(hPK (i + 1) hi1).symm.mono_left hCK, (hPK (j + 1) hj1).symm.mono_left hCK⟩)
      (hαC i hiN) hαjC (hbP (i + 1) hi1) (hbP (j + 1) hj1)
  have hinj : InjOn C (Finset.range N : Set ℕ) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (hne i j h hj)
    · exact h
    · exact absurd hij.symm (hne j i h hi)
  have hmaps : MapsTo C (Finset.range N : Set ℕ) (hT.toFinset : Set (Set ℂ)) := by
    intro i hi
    rw [Finset.mem_coe, Finset.mem_range] at hi
    rw [Finset.mem_coe, Finite.mem_toFinset]
    exact hCT i hi
  have hcard := Finset.card_le_card_of_injOn C hmaps hinj
  rw [Finset.card_range, ← ncard_eq_toFinset_card T hT] at hcard
  exact hcard

end LatticeProb.Topology
