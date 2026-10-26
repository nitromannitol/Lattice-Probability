import LatticeProb.Graph.MatedCRT.Infima

/-!
# Edges of the mated-CRT graph of two continuous paths

The deterministic multigraph `fromPaths ε L R` of Definition 1.1 of
[Internal DLA on mated-CRT maps](https://arxiv.org/abs/2211.04891v2) has, between the endpoints
`a < b` of an ordered pair `p`, only the two potential edges `(p, 0)` and `(p, 1)`.  The first is
present when one coordinate condition holds, the second when both hold and `b - a > ε`.  Hence
there are never three pairwise distinct parallel edges and never a loop.  The edge from `a` to its
successor `a + ε` is always present and unique, which gives an outer neighbour of every nonempty
finite vertex set.  No local finiteness is assumed or claimed: constant paths give vertices of
infinite degree.
-/

namespace LatticeProb.MatedCRT

/-- A link between vertices `a < b` has exactly the ordered endpoints `(a, b)`. -/
theorem isLink_iff_of_lt (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath) (e : PotentialEdge ε)
    (a b : Vertex ε) (h : a.val < b.val) :
    (fromPaths ε L R).IsLink e a b ↔
      edgeEnabled ε L R e ∧ e.1.val.1 = a ∧ e.1.val.2 = b := by
  constructor
  · rintro ⟨hen, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩
    · exact ⟨hen, ha.symm, hb.symm⟩
    · exfalso
      have h1 : a.val = e.1.val.2.val := by rw [ha]
      have h2 : b.val = e.1.val.1.val := by rw [hb]
      have h3 : e.1.val.1.val < e.1.val.2.val := e.1.property
      linarith
  · rintro ⟨hen, ha, hb⟩
    exact ⟨hen, Or.inl ⟨ha.symm, hb.symm⟩⟩

/-- A link between the endpoints of an ordered pair `p` is an enabled edge lying over `p`. -/
theorem isLink_orderedPair_iff (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath) (p : OrderedPair ε)
    (e : PotentialEdge ε) :
    (fromPaths ε L R).IsLink e p.val.1 p.val.2 ↔ edgeEnabled ε L R e ∧ e.1 = p := by
  rw [isLink_iff_of_lt ε L R e _ _ p.property]
  constructor
  · rintro ⟨hen, h1, h2⟩
    exact ⟨hen, Subtype.ext (Prod.ext h1 h2)⟩
  · rintro ⟨hen, rfl⟩
    exact ⟨hen, rfl, rfl⟩

/-- The first potential edge over `p` is enabled exactly when one coordinate condition holds. -/
theorem edgeEnabled_zero_iff (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath) (p : OrderedPair ε) :
    edgeEnabled ε L R (p, 0) ↔ coordinateCondition ε L p ∨ coordinateCondition ε R p := by
  unfold edgeEnabled
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd h (show (0 : Fin 2) ≠ 1 by decide)
  · exact fun h => Or.inl ⟨rfl, h⟩

/-- The second potential edge over `p` is enabled exactly when both conditions hold and the
endpoints are more than `ε` apart. -/
theorem edgeEnabled_one_iff (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath) (p : OrderedPair ε) :
    edgeEnabled ε L R (p, 1) ↔
      ε.val < p.val.2.val - p.val.1.val ∧
        coordinateCondition ε L p ∧ coordinateCondition ε R p := by
  unfold edgeEnabled
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact absurd h (show (1 : Fin 2) ≠ 0 by decide)
    · exact h
  · exact fun h => Or.inr ⟨rfl, h⟩

/-- An enabled edge of either slot carries at least one coordinate condition. -/
theorem coordinateCondition_or_of_edgeEnabled {ε : Set.Ioi (0 : ℝ)} {L R : RootedPath}
    {e : PotentialEdge ε} (h : edgeEnabled ε L R e) :
    coordinateCondition ε L e.1 ∨ coordinateCondition ε R e.1 := by
  rcases h with ⟨-, h⟩ | ⟨-, -, hL, -⟩
  · exact h
  · exact Or.inl hL

/-- An enabled edge in the second slot satisfies the strict gap and both coordinate conditions. -/
theorem gap_and_conditions_of_edgeEnabled_one {ε : Set.Ioi (0 : ℝ)} {L R : RootedPath}
    {e : PotentialEdge ε} (h : edgeEnabled ε L R e) (h1 : e.2 = 1) :
    ε.val < e.1.val.2.val - e.1.val.1.val ∧
      coordinateCondition ε L e.1 ∧ coordinateCondition ε R e.1 := by
  rcases h with ⟨h0, -⟩ | ⟨-, h⟩
  · exact absurd (h0.symm.trans h1) (by decide)
  · exact h

/-- Incidence in `fromPaths` is the displayed enabled-edge rule, with no extra conditions. -/
theorem fromPaths_isLink_iff : ∀ (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath)
    (e : PotentialEdge ε) (a b : Vertex ε),
  (fromPaths ε L R).IsLink e a b ↔
    (((e.2 = 0 ∧
        (coordinateCondition ε L e.1 ∨ coordinateCondition ε R e.1)) ∨
      (e.2 = 1 ∧
        ε.val < e.1.val.2.val - e.1.val.1.val ∧
        coordinateCondition ε L e.1 ∧ coordinateCondition ε R e.1)) ∧
     ((a = e.1.val.1 ∧ b = e.1.val.2) ∨
      (a = e.1.val.2 ∧ b = e.1.val.1))) := by
  intro ε L R e a b
  exact Iff.rfl

/-- A mated-CRT graph has no loops. -/
theorem not_isLink_self (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath) (v : Vertex ε)
    (e : PotentialEdge ε) : ¬ (fromPaths ε L R).IsLink e v v := by
  intro he
  have h4 : e.1.val.1.val < e.1.val.2.val := e.1.property
  obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := he
  · exact (ne_of_lt h4) (congrArg Subtype.val (h1.symm.trans h2))
  · exact (ne_of_lt h4) (congrArg Subtype.val (h2.symm.trans h1))

/-- Between the endpoints of an ordered pair there are zero, one or two physical edges, with the
displayed existence and multiplicity rules, and there are no loops. -/
theorem fromPaths_multiplicity_spec :
  ∀ (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath) (p : OrderedPair ε),
  let G := fromPaths ε L R
  let a := p.val.1
  let b := p.val.2
  ((∃ e : PotentialEdge ε, G.IsLink e a b) ↔
    (coordinateCondition ε L p ∨ coordinateCondition ε R p)) ∧
  ((∃ e₁ e₂ : PotentialEdge ε,
      e₁ ≠ e₂ ∧ G.IsLink e₁ a b ∧ G.IsLink e₂ a b) ↔
    (ε.val < b.val - a.val ∧
      coordinateCondition ε L p ∧ coordinateCondition ε R p)) ∧
  (∀ e₁ e₂ e₃ : PotentialEdge ε,
    G.IsLink e₁ a b → G.IsLink e₂ a b → G.IsLink e₃ a b →
      e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃) ∧
  (∀ (v : Vertex ε) (e : PotentialEdge ε), ¬ G.IsLink e v v) := by
  intro ε L R p
  dsimp only
  have key := isLink_orderedPair_iff ε L R p
  refine ⟨?_, ?_, ?_, fun v e => not_isLink_self ε L R v e⟩
  · constructor
    · rintro ⟨e, he⟩
      obtain ⟨hen, hp⟩ := (key e).1 he
      have h := coordinateCondition_or_of_edgeEnabled hen
      rwa [hp] at h
    · rintro (h | h)
      · exact ⟨(p, 0), (key _).2 ⟨(edgeEnabled_zero_iff ε L R p).2 (Or.inl h), rfl⟩⟩
      · exact ⟨(p, 0), (key _).2 ⟨(edgeEnabled_zero_iff ε L R p).2 (Or.inr h), rfl⟩⟩
  · constructor
    · rintro ⟨e₁, e₂, hne, h₁, h₂⟩
      obtain ⟨hen₁, hp₁⟩ := (key e₁).1 h₁
      obtain ⟨hen₂, hp₂⟩ := (key e₂).1 h₂
      have hsnd : e₁.2 ≠ e₂.2 := fun h => hne (Prod.ext (hp₁.trans hp₂.symm) h)
      have hk : ∀ k₁ k₂ : Fin 2, k₁ ≠ k₂ → k₁ = 1 ∨ k₂ = 1 := by decide
      rcases hk _ _ hsnd with h | h
      · have h' := gap_and_conditions_of_edgeEnabled_one hen₁ h
        rwa [hp₁] at h'
      · have h' := gap_and_conditions_of_edgeEnabled_one hen₂ h
        rwa [hp₂] at h'
    · intro hcond
      exact ⟨(p, 0), (p, 1), fun h => (show (0 : Fin 2) ≠ 1 by decide) (congrArg Prod.snd h),
        (key _).2 ⟨(edgeEnabled_zero_iff ε L R p).2 (Or.inl hcond.2.1), rfl⟩,
        (key _).2 ⟨(edgeEnabled_one_iff ε L R p).2 hcond, rfl⟩⟩
  · intro e₁ e₂ e₃ h₁ h₂ h₃
    have hp₁ := ((key e₁).1 h₁).2
    have hp₂ := ((key e₂).1 h₂).2
    have hp₃ := ((key e₃).1 h₃).2
    have hk : ∀ k₁ k₂ k₃ : Fin 2, k₁ = k₂ ∨ k₁ = k₃ ∨ k₂ = k₃ := by decide
    rcases hk e₁.2 e₂.2 e₃.2 with h | h | h
    · exact Or.inl (Prod.ext (hp₁.trans hp₂.symm) h)
    · exact Or.inr (Or.inl (Prod.ext (hp₁.trans hp₃.symm) h))
    · exact Or.inr (Or.inr (Prod.ext (hp₂.trans hp₃.symm) h))

/-- At a consecutive pair `b = a + ε` every path satisfies the coordinate condition. -/
theorem coordinateCondition_of_succ (ε : Set.Ioi (0 : ℝ)) (X : RootedPath) (p : OrderedPair ε)
    (h : p.val.2.val = p.val.1.val + ε.val) : coordinateCondition ε X p := by
  have hε : 0 < ε.val := ε.property
  have hb : p.val.2.val - ε.val = p.val.1.val := by rw [h]; ring
  have hleft : sInf ((X.val : ℝ → ℝ) '' Set.Icc (p.val.1.val - ε.val) p.val.1.val)
      ≤ X.val p.val.1.val :=
    (isLeast_sInf_image_Icc X (by linarith)).2 ⟨p.val.1.val, ⟨by linarith, le_rfl⟩, rfl⟩
  have hright : sInf ((X.val : ℝ → ℝ) '' Set.Icc (p.val.2.val - ε.val) p.val.2.val)
      ≤ X.val p.val.1.val :=
    (isLeast_sInf_image_Icc X (by linarith)).2 ⟨p.val.1.val, ⟨by linarith, by linarith⟩, rfl⟩
  unfold coordinateCondition
  dsimp only
  refine le_csInf ⟨X.val p.val.1.val, p.val.1.val, ⟨le_rfl, by linarith⟩, rfl⟩ ?_
  rintro _ ⟨t, ⟨h1, h2⟩, rfl⟩
  have ht : t = p.val.1.val := by linarith
  rw [ht]
  exact max_le hleft hright

/-- Every vertex has exactly one edge to its successor. -/
theorem consecutive_edge_unique : ∀ (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath) (a : Vertex ε),
  ∃! e : PotentialEdge ε,
    (fromPaths ε L R).IsLink e a (successor ε a) := by
  intro ε L R a
  have hε : 0 < ε.val := ε.property
  have hlt : a.val < (successor ε a).val := by
    show a.val < a.val + ε.val
    linarith
  let p : OrderedPair ε := ⟨(a, successor ε a), hlt⟩
  have hsucc : p.val.2.val = p.val.1.val + ε.val := rfl
  have key := isLink_orderedPair_iff ε L R p
  refine ⟨(p, 0), (key _).2 ⟨(edgeEnabled_zero_iff ε L R p).2
    (Or.inl (coordinateCondition_of_succ ε L p hsucc)), rfl⟩, ?_⟩
  intro e he
  obtain ⟨hen, hp⟩ := (key e).1 he
  have h0 : e.2 = 0 := by
    rcases hen with ⟨h0, -⟩ | ⟨-, h, -⟩
    · exact h0
    · exfalso
      rw [hp] at h
      change ε.val < a.val + ε.val - a.val at h
      linarith
  exact Prod.ext hp h0

/-- Every nonempty finite vertex set has a vertex adjacent to a vertex outside the set. -/
theorem finite_set_has_outer_neighbor : ∀ (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath)
    (A : Finset (Vertex ε)), A.Nonempty →
  ∃ a ∈ A, ∃ b : Vertex ε,
    b ∉ A ∧ (fromPaths ε L R).Adj a b := by
  intro ε L R A hA
  obtain ⟨a, haA, hmax⟩ := Finset.exists_max_image A (fun v : Vertex ε => v.val) hA
  refine ⟨a, haA, successor ε a, fun hb => ?_, (consecutive_edge_unique ε L R a).exists⟩
  have hε : 0 < ε.val := ε.property
  have h : a.val + ε.val ≤ a.val := hmax _ hb
  linarith

end LatticeProb.MatedCRT
