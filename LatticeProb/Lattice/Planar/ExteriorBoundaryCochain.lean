/- The plaquette argument adapts Leonardo Bonanno's lean-formalizations,
   HigherDimLFPP.Perc.ExtBoundary, commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82,
   https://github.com/leobon12/lean-formalizations. -/
import LatticeProb.Bonanno.HigherDimLFPP.Perc.ExtBoundary
import LatticeProb.Lattice.Planar.ExteriorBoundary

/-!
# Cochains for exterior boundaries

A local identity for the mod-two edge cochain of a boundary component.
-/

set_option autoImplicit false

namespace LatticeProb.Lattice.Planar

open HigherDimLFPP.Perc

/-- On an edge, if every exterior-to-set crossing meets the selected boundary component, the
component cochain agrees with the difference of the exterior indicator. -/
lemma bdryEdge_eq_indExterior {d : ℕ} {D E Γ : Set (Zd d)} {a b : Zd d}
    (hΓE : Γ ⊆ E) (hED : Disjoint E D)
    (haD : a ∈ E → b ∉ E → b ∈ D) (hbD : b ∈ E → a ∉ E → a ∈ D)
    (haΓ : a ∈ E → b ∈ D → a ∈ Γ) (hbΓ : b ∈ E → a ∈ D → b ∈ Γ) :
    bdryEdge D Γ a b = indZ2 E a + indZ2 E b := by
  classical
  have hdis : ∀ x, x ∈ E → x ∉ D := Set.disjoint_left.mp hED
  by_cases ha : a ∈ E <;> by_cases hb : b ∈ E
  · have haD' := hdis a ha
    have hbD' := hdis b hb
    simp [bdryEdge, indZ2, ha, hb, haD', hbD', zmod2_add_self]
  · have hbD' := haD ha hb
    have haΓ' := haΓ ha hbD'
    have haD' := hdis a ha
    have hbΓ' : b ∉ Γ := fun h => hb (hΓE h)
    simp [bdryEdge, indZ2, ha, hb, hbD', haΓ', haD', hbΓ']
  · have haD' := hbD hb ha
    have hbΓ' := hbΓ hb haD'
    have hbD' := hdis b hb
    have haΓ' : a ∉ Γ := fun h => ha (hΓE h)
    simp [bdryEdge, indZ2, ha, hb, haD', hbΓ', hbD', haΓ']
  · have haΓ' : a ∉ Γ := fun h => ha (hΓE h)
    have hbΓ' : b ∉ Γ := fun h => hb (hΓE h)
    simp [bdryEdge, indZ2, ha, hb, haΓ', hbΓ']

/-- In a unit cell meeting a boundary component, its edge cochain is the coboundary of the
exterior indicator. -/
lemma bdryEdge_eq_indExterior_of_cell {d : ℕ} {D E Γ : Set (Zd d)} {q a b c : Zd d}
    (hΓE : Γ ⊆ E) (hED : Disjoint E D)
    (hfront : ∀ x ∈ E, ∀ y, LAdj x y → y ∉ E → y ∈ D)
    (hΓclosed : ∀ x ∈ Γ, ∀ y ∈ E, (∃ z ∈ D, LAdj z y) →
      (x = y ∨ SAdj x y) → y ∈ Γ)
    (hc : c ∈ Γ) (hcq : InCell q c) (haq : InCell q a) (hbq : InCell q b)
    (hab : LAdj a b) :
    bdryEdge D Γ a b = indZ2 E a + indZ2 E b := by
  apply bdryEdge_eq_indExterior hΓE hED
  · exact fun ha hb => hfront a ha b hab hb
  · exact fun hb ha => hfront b hb a hab.symm ha
  · intro ha hb
    apply hΓclosed c hc a ha ⟨b, hb, hab.symm⟩
    by_cases h : c = a
    · exact Or.inl h
    · exact Or.inr ⟨h, hcq.withinInf haq⟩
  · intro hb ha
    apply hΓclosed c hc b hb ⟨a, ha, hab⟩
    by_cases h : c = b
    · exact Or.inl h
    · exact Or.inr ⟨h, hcq.withinInf hbq⟩

/-- The boundary-component cochain has zero sum around every plaquette. -/
lemma bdryEdge_plaquette {d : ℕ} {D E Γ : Set (Zd d)}
    (hΓE : Γ ⊆ E) (hED : Disjoint E D)
    (hfront : ∀ x ∈ E, ∀ y, LAdj x y → y ∉ E → y ∈ D)
    (hΓclosed : ∀ x ∈ Γ, ∀ y ∈ E, (∃ z ∈ D, LAdj z y) →
      (x = y ∨ SAdj x y) → y ∈ Γ)
    (x : Zd d) (i j : Fin d) :
    bdryEdge D Γ x (x + Pi.single i 1) +
      bdryEdge D Γ (x + Pi.single i 1) (x + Pi.single i 1 + Pi.single j 1) +
      bdryEdge D Γ (x + Pi.single j 1) (x + Pi.single j 1 + Pi.single i 1) +
      bdryEdge D Γ x (x + Pi.single j 1) = 0 := by
  by_cases hij : i = j
  · subst hij
    generalize bdryEdge D Γ x (x + Pi.single i 1) = a
    generalize bdryEdge D Γ (x + Pi.single i 1) (x + Pi.single i 1 + Pi.single i 1) = b
    revert a b
    decide
  · rw [show x + Pi.single j 1 + Pi.single i 1 = x + Pi.single i 1 + Pi.single j 1 from
      add_right_comm _ _ _]
    set v₀ := x
    set v₁ := x + Pi.single i 1
    set v₂ := x + Pi.single i 1 + Pi.single j 1
    set v₃ := x + Pi.single j 1
    have c₀ : InCell x v₀ := inCell_self x
    have c₁ : InCell x v₁ := inCell_add_single x i
    have c₂ : InCell x v₂ := inCell_add_single_add_single x hij
    have c₃ : InCell x v₃ := inCell_add_single x j
    have l₀₁ : LAdj v₀ v₁ := lAdj_add_single x i
    have l₁₂ : LAdj v₁ v₂ := lAdj_add_single _ j
    have l₃₂ : LAdj v₃ v₂ := by
      have h := lAdj_add_single (x + Pi.single j 1) i
      rwa [add_right_comm] at h
    have l₀₃ : LAdj v₀ v₃ := lAdj_add_single x j
    by_cases hΓ : ∃ c ∈ Γ, InCell x c
    · obtain ⟨c, hc, hcq⟩ := hΓ
      rw [bdryEdge_eq_indExterior_of_cell hΓE hED hfront hΓclosed hc hcq c₀ c₁ l₀₁,
        bdryEdge_eq_indExterior_of_cell hΓE hED hfront hΓclosed hc hcq c₁ c₂ l₁₂,
        bdryEdge_eq_indExterior_of_cell hΓE hED hfront hΓclosed hc hcq c₃ c₂ l₃₂,
        bdryEdge_eq_indExterior_of_cell hΓE hED hfront hΓclosed hc hcq c₀ c₃ l₀₃]
      generalize indZ2 E v₀ = a₀
      generalize indZ2 E v₁ = a₁
      generalize indZ2 E v₂ = a₂
      generalize indZ2 E v₃ = a₃
      revert a₀ a₁ a₂ a₃
      decide
    · have hnot : ∀ v ∈ Γ, ¬ InCell x v := by
        intro v hv hvq
        exact hΓ ⟨v, hv, hvq⟩
      have n₀ : v₀ ∉ Γ := fun h => hnot v₀ h c₀
      have n₁ : v₁ ∉ Γ := fun h => hnot v₁ h c₁
      have n₂ : v₂ ∉ Γ := fun h => hnot v₂ h c₂
      have n₃ : v₃ ∉ Γ := fun h => hnot v₃ h c₃
      rw [bdryEdge_eq_zero n₀ n₁, bdryEdge_eq_zero n₁ n₂, bdryEdge_eq_zero n₃ n₂,
        bdryEdge_eq_zero n₀ n₃]
      decide

/-- The boundary-component cochain has a mod-two potential. -/
theorem exists_bdryEdge_potential {d : ℕ} {D E Γ : Set (Zd d)}
    (hΓE : Γ ⊆ E) (hED : Disjoint E D)
    (hfront : ∀ x ∈ E, ∀ y, LAdj x y → y ∉ E → y ∈ D)
    (hΓclosed : ∀ x ∈ Γ, ∀ y ∈ E, (∃ z ∈ D, LAdj z y) →
      (x = y ∨ SAdj x y) → y ∈ Γ) :
    ∃ φ : Zd d → ZMod 2, ∀ x i,
      φ (x + Pi.single i 1) - φ x = bdryEdge D Γ x (x + Pi.single i 1) := by
  exact poincareMod2 d _ (bdryEdge_plaquette hΓE hED hfront hΓclosed)

/-- The coordinate cube between two star-neighbours is contained in a unit cell. -/
lemma exists_cell_containing_cube {d : ℕ} {x y : Zd d} (hxy : WithinInf 1 x y) :
    ∃ q, ∀ z ∈ cube x y, InCell q z := by
  refine ⟨fun i => min (x i) (y i), ?_⟩
  intro z hz i
  have hi := (withinInf_iff.mp hxy) i
  have hzi := hz i
  dsimp only [InCell]
  rcases hzi with h | h <;> rw [h] <;> omega

/-- A potential for the component cochain has the stated increment on either orientation of an
edge. -/
lemma bdryEdge_potential_step {d : ℕ} {D Γ : Set (Zd d)} {φ : Zd d → ZMod 2}
    (hφ : ∀ x i, φ (x + Pi.single i 1) - φ x = bdryEdge D Γ x (x + Pi.single i 1))
    {a b : Zd d} (hab : LAdj a b) : φ b = φ a + bdryEdge D Γ a b := by
  obtain ⟨i, hi | hi⟩ := hab.exists_eq_add_single
  · subst hi
    rw [← hφ a i]
    ring
  · subst hi
    rw [bdryEdge_comm, ← hφ b i]
    generalize φ b = p
    generalize φ (b + Pi.single i 1) = q
    revert p q
    decide

/-- A boundary-component potential is constant across star-adjacent sites of the set. -/
lemma bdryEdge_potential_eq_of_sAdj {d : ℕ} {D E Γ : Set (Zd d)}
    (hΓE : Γ ⊆ E) (hED : Disjoint E D)
    (hfront : ∀ x ∈ E, ∀ y, LAdj x y → y ∉ E → y ∈ D)
    (hΓclosed : ∀ x ∈ Γ, ∀ y ∈ E, (∃ z ∈ D, LAdj z y) →
      (x = y ∨ SAdj x y) → y ∈ Γ)
    {φ : Zd d → ZMod 2}
    (hφ : ∀ x i, φ (x + Pi.single i 1) - φ x = bdryEdge D Γ x (x + Pi.single i 1))
    {f g : Zd d} (hf : f ∈ D) (hg : g ∈ D) (hfg : SAdj f g) : φ f = φ g := by
  classical
  obtain ⟨q, hq⟩ := exists_cell_containing_cube hfg.withinInf
  have hp := reflTransGen_cube hfg.withinInf
  by_cases hex : ∃ c ∈ Γ, InCell q c
  · obtain ⟨c, hc, hcq⟩ := hex
    have hkey : ∀ z, Relation.ReflTransGen (StepIn (cube f g) LAdj) f z →
        φ z + indZ2 E z = φ f + indZ2 E f := by
      intro z hz
      induction hz with
      | refl => rfl
      | @tail b c _ hbc ih =>
        rw [← ih, bdryEdge_potential_step hφ hbc.2.2,
          bdryEdge_eq_indExterior_of_cell hΓE hED hfront hΓclosed hc hcq
            (hq b hbc.1) (hq c hbc.2.1) hbc.2.2]
        generalize φ b = p
        generalize indZ2 E b = r
        generalize indZ2 E c = s
        revert p r s
        decide
    have hEf : f ∉ E := fun h => Set.disjoint_left.mp hED h hf
    have hEg : g ∉ E := fun h => Set.disjoint_left.mp hED h hg
    have h := hkey g hp
    simpa [indZ2, hEf, hEg] using h.symm
  · have hnot : ∀ z ∈ cube f g, z ∉ Γ := by
      intro z hz hzΓ
      exact hex ⟨z, hzΓ, hq z hz⟩
    have hkey : ∀ z, Relation.ReflTransGen (StepIn (cube f g) LAdj) f z → φ f = φ z := by
      intro z hz
      induction hz with
      | refl => rfl
      | @tail b c _ hbc ih =>
        rw [bdryEdge_potential_step hφ hbc.2.2,
          bdryEdge_eq_zero (hnot b hbc.1) (hnot c hbc.2.1), add_zero]
        exact ih
    exact hkey g hp

/-- If a star-connected set and a disjoint nearest-neighbour-connected exterior meet all of each
other's incident edges, their nearest-neighbour boundary is star-connected. -/
theorem boundary_conn_of_connected_exterior {d : ℕ} {D E : Set (Zd d)}
    (hED : Disjoint E D) (hD : ConnIn D SAdj) (hE : ConnIn E LAdj)
    (hfront : ∀ x ∈ E, ∀ y, LAdj x y → y ∉ E → y ∈ D) :
    ConnIn {y | y ∈ E ∧ ∃ z ∈ D, LAdj z y} SAdj := by
  classical
  set B : Set (Zd d) := {y | y ∈ E ∧ ∃ z ∈ D, LAdj z y}
  intro y₁ hy₁ y₂ hy₂
  set Γ : Set (Zd d) := {y | Relation.ReflTransGen (StepIn B SAdj) y₁ y}
  have hΓB : Γ ⊆ B := fun _ hy => mem_of_reflTransGen_stepIn hy hy₁
  have hΓE : Γ ⊆ E := fun y hy => (hΓB hy).1
  have hΓclosed : ∀ x ∈ Γ, ∀ y ∈ E, (∃ z ∈ D, LAdj z y) →
      (x = y ∨ SAdj x y) → y ∈ Γ := by
    intro x hx y hy hyD hxy
    rcases hxy with rfl | hxy
    · exact hx
    · exact Relation.ReflTransGen.tail hx ⟨hΓB hx, ⟨hy, hyD⟩, hxy⟩
  obtain ⟨φ, hφ⟩ := exists_bdryEdge_potential hΓE hED hfront hΓclosed
  have hφE : ∀ a ∈ E, ∀ b ∈ E, φ a = φ b := by
    intro a ha b hb
    have hp := hE a ha b hb
    induction hp with
    | refl => rfl
    | @tail u v _ huv ih =>
      rw [bdryEdge_potential_step hφ huv.2.2,
        bdryEdge_of_notMem (Set.disjoint_left.mp hED huv.1)
          (Set.disjoint_left.mp hED huv.2.1), add_zero]
      exact ih huv.1
  have hφD : ∀ a ∈ D, ∀ b ∈ D, φ a = φ b := by
    intro a ha b hb
    have hp := hD a ha b hb
    induction hp with
    | refl => rfl
    | @tail u v _ huv ih =>
      exact (ih huv.1).trans (bdryEdge_potential_eq_of_sAdj hΓE hED hfront hΓclosed hφ
        huv.1 huv.2.1 huv.2.2)
  have hy₁Γ : y₁ ∈ Γ := Relation.ReflTransGen.refl
  by_contra hy₂Γ
  obtain ⟨f₁, hf₁, hf₁y₁⟩ := hy₁.2
  obtain ⟨f₂, hf₂, hf₂y₂⟩ := hy₂.2
  have hf₂Γ : f₂ ∉ Γ := fun h => Set.disjoint_left.mp hED (hΓE h) hf₂
  have h₁ : φ y₁ = φ f₁ + 1 := by
    rw [bdryEdge_potential_step hφ hf₁y₁, bdryEdge_eq_one hf₁ hy₁Γ]
  have h₂ : φ y₂ = φ f₂ := by
    rw [bdryEdge_potential_step hφ hf₂y₂, bdryEdge_eq_zero hf₂Γ hy₂Γ, add_zero]
  have h := hφE y₁ hy₁.1 y₂ hy₂.1
  rw [h₁, h₂, hφD f₁ hf₁ f₂ hf₂] at h
  have : (1 : ZMod 2) = 0 := by
    calc
      1 = (φ f₂ + 1) - φ f₂ := by ring
      _ = φ f₂ - φ f₂ := congrArg (fun z : ZMod 2 => z - φ f₂) h
      _ = 0 := sub_self _
  exact one_ne_zero this

end LatticeProb.Lattice.Planar
