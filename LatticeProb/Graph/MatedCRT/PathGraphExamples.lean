import LatticeProb.Graph.MatedCRT.PathGraphLemmas

/-!
# Deterministic consumption checks for the mated-CRT path-graph lemmas

These are explicit deterministic input paths, not Brownian samples.  At mesh `ε = 1`, the identity
path in both coordinates has no edge between the lattice points `0` and `2` and exactly one edge
between `0` and `1`.  The rooted parabola `t ↦ t - t ^ 2` in both coordinates has exactly two
parallel edges between `0` and `2`.  The finite-boundary lemma is applied to the vertex set `{0}`.
Every check consumes the actual lemmas of `PathGraphLemmas` and `Infima`.
-/

namespace LatticeProb.MatedCRT.Examples

/-- The mesh `ε = 1`. -/
def unitMesh : Set.Ioi (0 : ℝ) :=
  ⟨1, Set.mem_Ioi.mpr one_pos⟩

/-- The identity path `t ↦ t`, rooted at zero. -/
def identityPath : RootedPath :=
  ⟨ContinuousMap.id ℝ, rfl⟩

/-- The rooted parabola `t ↦ t - t ^ 2`. -/
def parabolaPath : RootedPath :=
  ⟨⟨fun t => t - t ^ 2, by fun_prop⟩, by simp⟩

/-- The integer `n` as a vertex of the unit-mesh lattice. -/
def unitVertex (n : ℤ) : Vertex unitMesh :=
  ⟨(n : ℝ), n, (one_mul (n : ℝ)).symm⟩

/-- The ordered pair of the lattice points `0 < 2`. -/
def zeroTwo : OrderedPair unitMesh :=
  ⟨(unitVertex 0, unitVertex 2), by norm_num [unitVertex]⟩

/-- The mesh `unitMesh` has value `1`. -/
theorem unitMesh_val : unitMesh.val = 1 := rfl

/-- The left endpoint of `zeroTwo` is the real number `0`. -/
theorem zeroTwo_fst_val : zeroTwo.val.1.val = 0 := by simp [zeroTwo, unitVertex]

/-- The right endpoint of `zeroTwo` is the real number `2`. -/
theorem zeroTwo_snd_val : zeroTwo.val.2.val = 2 := by simp [zeroTwo, unitVertex]

/-- The successor of the lattice point `n` is the lattice point `n + 1`. -/
theorem successor_unitVertex (n : ℤ) :
    successor unitMesh (unitVertex n) = unitVertex (n + 1) := by
  apply Subtype.ext
  show (n : ℝ) + 1 = ((n + 1 : ℤ) : ℝ)
  simp

/-- The identity path is the identity function. -/
theorem identityPath_apply (t : ℝ) : (identityPath.val : ℝ → ℝ) t = t := rfl

/-- The parabola path is `t ↦ t - t ^ 2`. -/
theorem parabolaPath_apply (t : ℝ) : (parabolaPath.val : ℝ → ℝ) t = t - t ^ 2 := rfl

/-- The identity path attains its infimum over `[l, u]` at the left endpoint. -/
theorem identity_sInf_Icc {l u : ℝ} (h : l ≤ u) :
    sInf ((identityPath.val : ℝ → ℝ) '' Set.Icc l u) = l := by
  have hle := isLeast_sInf_image_Icc identityPath h
  obtain ⟨t, ht, hts⟩ := hle.1
  have hid := identityPath_apply t
  exact le_antisymm (hle.2 ⟨l, ⟨le_rfl, h⟩, rfl⟩) (by linarith [ht.1])

/-- The coordinate condition fails for the identity path on the pair `(0, 2)` at mesh `1`. -/
theorem identity_not_coordinateCondition_zeroTwo :
    ¬ coordinateCondition unitMesh identityPath zeroTwo := by
  unfold coordinateCondition
  dsimp only
  rw [zeroTwo_fst_val, zeroTwo_snd_val, unitMesh_val,
    identity_sInf_Icc (by norm_num : (2 : ℝ) - 1 ≤ 2),
    identity_sInf_Icc (by norm_num : (0 : ℝ) ≤ 2 - 1)]
  intro h
  have h1 := le_trans (le_max_right _ _) h
  norm_num at h1

/-- The coordinate condition holds for the parabola on the pair `(0, 2)` at mesh `1`. -/
theorem parabola_coordinateCondition_zeroTwo :
    coordinateCondition unitMesh parabolaPath zeroTwo := by
  unfold coordinateCondition
  dsimp only
  rw [zeroTwo_fst_val, zeroTwo_snd_val, unitMesh_val]
  have hA : sInf ((parabolaPath.val : ℝ → ℝ) '' Set.Icc (0 - 1) 0) ≤ -2 :=
    (isLeast_sInf_image_Icc parabolaPath (by norm_num)).2
      ⟨-1, ⟨by norm_num, by norm_num⟩, by rw [parabolaPath_apply]; norm_num⟩
  have hB : sInf ((parabolaPath.val : ℝ → ℝ) '' Set.Icc (2 - 1) 2) ≤ -2 :=
    (isLeast_sInf_image_Icc parabolaPath (by norm_num)).2
      ⟨2, ⟨by norm_num, by norm_num⟩, by rw [parabolaPath_apply]; norm_num⟩
  refine le_csInf ⟨(parabolaPath.val : ℝ → ℝ) 0, 0, ⟨le_rfl, by norm_num⟩, rfl⟩ ?_
  rintro _ ⟨t, ⟨h1, h2⟩, rfl⟩
  rw [parabolaPath_apply]
  refine max_le (hA.trans ?_) (hB.trans ?_) <;> nlinarith

/-- With identity paths at mesh `1` there is no edge between `0` and `2`. -/
theorem identity_no_edge_zero_two :
    ¬ ∃ e : PotentialEdge unitMesh,
      (fromPaths unitMesh identityPath identityPath).IsLink e (unitVertex 0) (unitVertex 2) := by
  obtain ⟨hex, -, -, -⟩ := fromPaths_multiplicity_spec unitMesh identityPath identityPath zeroTwo
  intro h
  rcases hex.mp h with h | h <;> exact identity_not_coordinateCondition_zeroTwo h

/-- With identity paths at mesh `1` there is exactly one edge between `0` and `1`. -/
theorem identity_unique_edge_zero_one :
    ∃! e : PotentialEdge unitMesh,
      (fromPaths unitMesh identityPath identityPath).IsLink e (unitVertex 0) (unitVertex 1) := by
  have h := consecutive_edge_unique unitMesh identityPath identityPath (unitVertex 0)
  simpa [successor_unitVertex] using h

/-- The single edge between `0` and `1` for identity paths is the first potential edge. -/
theorem identity_edge_zero_one_first_slot (e : PotentialEdge unitMesh)
    (h : (fromPaths unitMesh identityPath identityPath).IsLink e (unitVertex 0) (unitVertex 1)) :
    e.2 = 0 := by
  obtain ⟨hen | hen, hab⟩ :=
    (fromPaths_isLink_iff unitMesh identityPath identityPath e _ _).mp h
  · exact hen.1
  · exfalso
    have hlt : e.1.val.1.val < e.1.val.2.val := e.1.property
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have v1 : e.1.val.1.val = 0 := by rw [← h1]; simp [unitVertex]
      have v2 : e.1.val.2.val = 1 := by rw [← h2]; simp [unitVertex]
      have hgap := hen.2.1
      linarith [unitMesh_val]
    · have v1 : e.1.val.2.val = 0 := by rw [← h1]; simp [unitVertex]
      have v2 : e.1.val.1.val = 1 := by rw [← h2]; simp [unitVertex]
      linarith

/-- With parabola paths at mesh `1` there are exactly two physical edges between `0` and `2`. -/
theorem parabola_exactly_two_edges_zero_two :
    ∃ e₁ e₂ : PotentialEdge unitMesh, e₁ ≠ e₂ ∧ ∀ e : PotentialEdge unitMesh,
      (fromPaths unitMesh parabolaPath parabolaPath).IsLink e (unitVertex 0) (unitVertex 2) ↔
        e = e₁ ∨ e = e₂ := by
  obtain ⟨-, htwo, hthree, -⟩ :=
    fromPaths_multiplicity_spec unitMesh parabolaPath parabolaPath zeroTwo
  have hgap : unitMesh.val < zeroTwo.val.2.val - zeroTwo.val.1.val := by
    rw [zeroTwo_fst_val, zeroTwo_snd_val, unitMesh_val]
    norm_num
  obtain ⟨e₁, e₂, hne, h₁, h₂⟩ :=
    htwo.mpr ⟨hgap, parabola_coordinateCondition_zeroTwo, parabola_coordinateCondition_zeroTwo⟩
  refine ⟨e₁, e₂, hne, fun e => ⟨fun he => ?_, ?_⟩⟩
  · rcases hthree e₁ e₂ e h₁ h₂ he with h | h | h
    · exact absurd h hne
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact h₁
    · exact h₂

/-- The middle infimum for the pair `(0, 2)`, read off from `coordinateInfima_spec`: the parabola
has infimum `0` over `[0, 1]`. -/
theorem parabola_middle_infimum_zero :
    sInf ((parabolaPath.val : ℝ → ℝ) '' Set.Icc 0 1) = 0 := by
  obtain ⟨-, -, hmid⟩ := coordinateInfima_spec unitMesh parabolaPath zeroTwo
  rw [zeroTwo_fst_val, zeroTwo_snd_val, unitMesh_val, show (2 : ℝ) - 1 = 1 by norm_num] at hmid
  refine hmid.unique ⟨⟨0, ⟨le_rfl, zero_le_one⟩, by rw [parabolaPath_apply]; norm_num⟩, ?_⟩
  rintro _ ⟨t, ⟨h1, h2⟩, rfl⟩
  rw [parabolaPath_apply]
  nlinarith

/-- The finite-boundary lemma applied to the vertex set `{0}` for the identity paths. -/
theorem identity_boundary_zero :
    ∃ a ∈ ({unitVertex 0} : Finset (Vertex unitMesh)), ∃ b : Vertex unitMesh,
      b ∉ ({unitVertex 0} : Finset (Vertex unitMesh)) ∧
        (fromPaths unitMesh identityPath identityPath).Adj a b :=
  finite_set_has_outer_neighbor unitMesh identityPath identityPath {unitVertex 0}
    (Finset.singleton_nonempty _)

/-- The outer neighbour of `{0}` is adjacent to `0` and differs from it. -/
theorem identity_outer_neighbor_zero :
    ∃ b : Vertex unitMesh, b ≠ unitVertex 0 ∧
      (fromPaths unitMesh identityPath identityPath).Adj (unitVertex 0) b := by
  obtain ⟨a, ha, b, hb, hab⟩ := identity_boundary_zero
  rw [Finset.mem_singleton] at ha hb
  subst ha
  exact ⟨b, hb, hab⟩

end LatticeProb.MatedCRT.Examples
