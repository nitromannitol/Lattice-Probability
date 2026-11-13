/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2TraceLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2SubdivTrace

 










set_option autoImplicit false
noncomputable section

open Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem eq_zero_of_sum_powerset_eq_zero {V : Type*} [DecidableEq V] (f : Finset V → ℝ)
    (hf : ∀ B : Finset V, ∑ S ∈ B.powerset, f S = 0) (B : Finset V) : f B = 0 := by
  induction B using Finset.strongInduction with
  | H B ih =>
    have h := hf B
    rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self B)] at h
    have hrest : ∑ S ∈ B.powerset.erase B, f S = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      have hsub : S ⊆ B := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hS)
      have hne : S ≠ B := Finset.ne_of_mem_erase hS
      exact ih S (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    rw [hrest, add_zero] at h
    exact h

 
def Excursion.visitSet {V : Type*} [Fintype V] [DecidableEq V] (γ : Excursion V) : Finset V :=
  Finset.univ.filter fun v => ∃ j, γ.2 j = v

theorem Excursion.mem_visitSet {V : Type*} [Fintype V] [DecidableEq V] (γ : Excursion V) (v : V) :
    v ∈ γ.visitSet ↔ ∃ j, γ.2 j = v := by
  simp [Excursion.visitSet]

namespace EdgeGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (Γ : EdgeGraph V E) (M : ℕ)

 
def traceSet (γ : Excursion (SubV V E M)) : Finset V :=
  Finset.univ.filter fun v => ∃ j, γ.2 j = Sum.inl v

theorem mem_traceSet (γ : Excursion (SubV V E M)) (v : V) :
    v ∈ traceSet M γ ↔ ∃ j, γ.2 j = Sum.inl v := by
  simp [traceSet]

theorem traceSet_subset_iff (γ : Excursion (SubV V E M)) (B : Finset V) :
    traceSet M γ ⊆ B ↔ ∀ j, γ.2 j ∉ (Sum.inl '' ((↑B : Set V)ᶜ) : Set (SubV V E M)) := by
  constructor
  · intro h j hj
    obtain ⟨a, ha, haj⟩ := hj
    exact ha (h ((mem_traceSet M γ a).mpr ⟨j, haj.symm⟩))
  · intro h v hv
    obtain ⟨j, hj⟩ := (mem_traceSet M γ v).mp hv
    by_contra hvB
    exact h j ⟨v, hvB, hj.symm⟩

theorem visitSet_subset_iff (γ : Excursion V) (B : Finset V) :
    γ.visitSet ⊆ B ↔ ∀ j, γ.2 j ∉ ((↑B : Set V)ᶜ) := by
  constructor
  · intro h j hj
    exact hj (h ((γ.mem_visitSet _).mpr ⟨j, rfl⟩))
  · intro h v hv
    obtain ⟨j, hj⟩ := (γ.mem_visitSet v).mp hv
    by_contra hvB
    exact h j (by rw [hj]; exact hvB)

def traceMass (hM : 2 ≤ M) (S : Finset V) : ℝ :=
  ∑' γ : Excursion (SubV V E M), if traceSet M γ = S then (Γ.subdiv M hM).toWired.excursionWeight γ else 0

 
def visitMass (S : Finset V) : ℝ :=
  ∑' γ : Excursion V, if γ.visitSet = S then Γ.toWired.excursionWeight γ else 0

theorem summable_ite_weight {W : Type*} [Fintype W] [DecidableEq W] (G : WiredConductances W)
    (hK : G.precision.PosDef) (P : Excursion W → Prop) [DecidablePred P] :
    Summable fun γ => if P γ then G.excursionWeight γ else 0 :=
  Summable.of_nonneg_of_le (fun γ => by split_ifs; exact G.excursionWeight_nonneg γ; exact le_rfl)
    (fun γ => by split_ifs; exact le_rfl; exact G.excursionWeight_nonneg γ)
    (G.summable_excursionWeight hK)

theorem sum_powerset_traceMass (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef) (B : Finset V) :
    ∑ S ∈ B.powerset, Γ.traceMass M hM S =
      ((M : ℝ) - 1) * Γ.toWired.boundaryTotal + ∑ S ∈ B.powerset, Γ.visitMass S := by
  classical
  have hKM := Γ.subdiv_posDef M hM hK
  obtain ⟨Y, hY⟩ := Γ.toWired.exists_avoidHarmonic hK ((↑B : Set V)ᶜ)
  have hYM := Γ.isAvoidHarmonic_subdiv M hM _ Y hY
  have hav := Γ.toWired.hasSum_excursion_avoid hK _ Y hY
  have havM := (Γ.subdiv M hM).toWired.hasSum_excursion_avoid hKM _ _ hYM
  rw [Γ.sum_boundary_interpAvoid M hM Y] at havM
  have hT : ∑ S ∈ B.powerset, Γ.traceMass M hM S =
      ∑' γ : Excursion (SubV V E M),
        if traceSet M γ ⊆ B then (Γ.subdiv M hM).toWired.excursionWeight γ else 0 := by
    unfold traceMass
    rw [← Summable.tsum_finsetSum (fun S _ => summable_ite_weight _ hKM _)]
    congr 1
    funext γ
    by_cases h : traceSet M γ ⊆ B
    · rw [if_pos h, Finset.sum_eq_single (traceSet M γ)]
      · simp
      · intro S _ hS
        rw [if_neg (Ne.symm hS)]
      · intro hn
        exact absurd (Finset.mem_powerset.mpr h) hn
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro S hS
      rw [if_neg]
      rintro rfl
      exact h (Finset.mem_powerset.mp hS)
  have hV : ∑ S ∈ B.powerset, Γ.visitMass S =
      ∑' γ : Excursion V, if γ.visitSet ⊆ B then Γ.toWired.excursionWeight γ else 0 := by
    unfold visitMass
    rw [← Summable.tsum_finsetSum (fun S _ => summable_ite_weight _ hK _)]
    congr 1
    funext γ
    by_cases h : γ.visitSet ⊆ B
    · rw [if_pos h, Finset.sum_eq_single γ.visitSet]
      · simp
      · intro S _ hS
        rw [if_neg (Ne.symm hS)]
      · intro hn
        exact absurd (Finset.mem_powerset.mpr h) hn
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro S hS
      rw [if_neg]
      rintro rfl
      exact h (Finset.mem_powerset.mp hS)
  rw [hT, hV]
  have e1 : (fun γ : Excursion (SubV V E M) =>
      if traceSet M γ ⊆ B then (Γ.subdiv M hM).toWired.excursionWeight γ else 0) =
      fun γ => if ∀ j, γ.2 j ∉ (Sum.inl '' ((↑B : Set V)ᶜ) : Set (SubV V E M)) then
        (Γ.subdiv M hM).toWired.excursionWeight γ else 0 := by
    funext γ
    exact if_congr (traceSet_subset_iff M γ B) rfl rfl
  have e2 : (fun γ : Excursion V => if γ.visitSet ⊆ B then Γ.toWired.excursionWeight γ else 0) =
      fun γ => if ∀ j, γ.2 j ∉ ((↑B : Set V)ᶜ) then Γ.toWired.excursionWeight γ else 0 := by
    funext γ
    exact if_congr (visitSet_subset_iff γ B) rfl rfl
  rw [e1, e2, havM.tsum_eq, hav.tsum_eq]

 
theorem traceMass_eq_visitMass (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef)
    {S : Finset V} (hS : S ≠ ∅) : Γ.traceMass M hM S = Γ.visitMass S := by
  classical
  set f : Finset V → ℝ := fun S => Γ.traceMass M hM S - Γ.visitMass S -
    (if S = ∅ then ((M : ℝ) - 1) * Γ.toWired.boundaryTotal else 0)
  have hf : ∀ B : Finset V, ∑ S ∈ B.powerset, f S = 0 := by
    intro B
    simp only [f, Finset.sum_sub_distrib, Γ.sum_powerset_traceMass M hM hK B]
    rw [Finset.sum_ite_eq' B.powerset ∅, if_pos (Finset.empty_mem_powerset B)]
    ring
  have := eq_zero_of_sum_powerset_eq_zero f hf S
  simp only [f, if_neg hS, sub_zero] at this
  linarith

 
theorem tsum_trace_event (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef)
    (P : Finset V → Prop) [DecidablePred P] (hP : ¬ P ∅) :
    ∑' γ : Excursion (SubV V E M),
        (if P (traceSet M γ) then (Γ.subdiv M hM).toWired.excursionWeight γ else 0) =
      ∑' γ : Excursion V, (if P γ.visitSet then Γ.toWired.excursionWeight γ else 0) := by
  classical
  have hKM := Γ.subdiv_posDef M hM hK
  have hsplitM : ∑' γ : Excursion (SubV V E M),
      (if P (traceSet M γ) then (Γ.subdiv M hM).toWired.excursionWeight γ else 0) =
      ∑ S : Finset V, if P S then Γ.traceMass M hM S else 0 := by
    unfold traceMass
    have : ∀ S : Finset V, (if P S then ∑' γ : Excursion (SubV V E M),
        (if traceSet M γ = S then (Γ.subdiv M hM).toWired.excursionWeight γ else 0) else 0) =
        ∑' γ : Excursion (SubV V E M), (if traceSet M γ = S ∧ P S then
          (Γ.subdiv M hM).toWired.excursionWeight γ else 0) := by
      intro S
      by_cases hPS : P S
      · simp [hPS]
      · simp [hPS]
    simp_rw [this]
    rw [← Summable.tsum_finsetSum (fun S _ => summable_ite_weight _ hKM _)]
    congr 1
    funext γ
    rw [Finset.sum_eq_single (traceSet M γ)]
    · by_cases h : P (traceSet M γ) <;> simp [h]
    · intro S _ hS
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hS h.symm
    · simp
  have hsplit : ∑' γ : Excursion V, (if P γ.visitSet then Γ.toWired.excursionWeight γ else 0) =
      ∑ S : Finset V, if P S then Γ.visitMass S else 0 := by
    unfold visitMass
    have : ∀ S : Finset V, (if P S then ∑' γ : Excursion V,
        (if γ.visitSet = S then Γ.toWired.excursionWeight γ else 0) else 0) =
        ∑' γ : Excursion V, (if γ.visitSet = S ∧ P S then Γ.toWired.excursionWeight γ else 0) := by
      intro S
      by_cases hPS : P S
      · simp [hPS]
      · simp [hPS]
    simp_rw [this]
    rw [← Summable.tsum_finsetSum (fun S _ => summable_ite_weight _ hK _)]
    congr 1
    funext γ
    rw [Finset.sum_eq_single γ.visitSet]
    · by_cases h : P γ.visitSet <;> simp [h]
    · intro S _ hS
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hS h.symm
    · simp
  rw [hsplitM, hsplit]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hPS : P S
  · have hne : S ≠ ∅ := by rintro rfl; exact hP hPS
    rw [if_pos hPS, if_pos hPS, Γ.traceMass_eq_visitMass M hM hK hne]
  · rw [if_neg hPS, if_neg hPS]

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
