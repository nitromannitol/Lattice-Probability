/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2Subdiv at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2EdgeGraph

 









set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

namespace EdgeGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (Γ : EdgeGraph V E) (M : ℕ)

 
abbrev SubV (V E : Type*) (M : ℕ) := V ⊕ (E × Fin (M - 1))

 
def subPos (e : E) (p : ℕ) : Option (SubV V E M) :=
  if hp : p = 0 then (Γ.tail e).map Sum.inl
  else if h : p < M then some (Sum.inr (e, ⟨p - 1, by omega⟩))
  else (Γ.head e).map Sum.inl

theorem subPos_zero (e : E) : Γ.subPos M e 0 = (Γ.tail e).map Sum.inl := by
  simp [subPos]

theorem subPos_of_lt (e : E) {p : ℕ} (hp0 : p ≠ 0) (hpM : p < M) :
    Γ.subPos M e p = some (Sum.inr (e, ⟨p - 1, by omega⟩)) := by
  simp [subPos, hp0, hpM]

theorem subPos_M (e : E) (hM : 1 ≤ M) : Γ.subPos M e M = (Γ.head e).map Sum.inl := by
  have : M ≠ 0 := by omega
  simp [subPos, this]

theorem subPos_eq_inr_iff {e e' : E} {k : Fin (M - 1)} {p : ℕ} (hp : p ≤ M) :
    Γ.subPos M e' p = some (Sum.inr (e, k)) ↔ e' = e ∧ p = k.val + 1 := by
  have hk := k.isLt
  by_cases hp0 : p = 0
  · subst hp0
    rw [Γ.subPos_zero]
    constructor
    · intro h
      cases ht : Γ.tail e' <;> simp [ht] at h
    · rintro ⟨_, h⟩; omega
  · by_cases hpM : p < M
    · rw [Γ.subPos_of_lt M e' hp0 hpM]
      simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
    · have hpe : M = p := by omega
      subst hpe
      rw [Γ.subPos_M M e' (by omega)]
      constructor
      · intro h
        cases ht : Γ.head e' <;> simp [ht] at h
      · rintro ⟨_, h⟩
        omega

theorem subPos_eq_inl_iff {e : E} {v : V} {p : ℕ} (hp : p ≤ M) (hM : 2 ≤ M) :
    Γ.subPos M e p = some (Sum.inl v) ↔
      (p = 0 ∧ Γ.tail e = some v) ∨ (p = M ∧ Γ.head e = some v) := by
  by_cases hp0 : p = 0
  · subst hp0
    rw [Γ.subPos_zero]
    constructor
    · intro h
      left
      refine ⟨rfl, ?_⟩
      cases ht : Γ.tail e <;> simp_all
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · simp [h]
      · omega
  · by_cases hpM : p < M
    · rw [Γ.subPos_of_lt M e hp0 hpM]
      constructor
      · intro h; simp at h
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega
    · have hpe : M = p := by omega
      subst hpe
      rw [Γ.subPos_M M e (by omega)]
      constructor
      · intro h
        right
        refine ⟨rfl, ?_⟩
        cases ht : Γ.head e <;> simp_all
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · omega
        · simp [h]

theorem subPos_eq_none_iff {e : E} {p : ℕ} (hp : p ≤ M) (hM : 1 ≤ M) :
    Γ.subPos M e p = none ↔ (p = 0 ∧ Γ.tail e = none) ∨ (p = M ∧ Γ.head e = none) := by
  by_cases hp0 : p = 0
  · subst hp0
    rw [Γ.subPos_zero, Option.map_eq_none_iff]
    constructor
    · intro h; exact Or.inl ⟨rfl, h⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · omega
  · by_cases hpM : p < M
    · rw [Γ.subPos_of_lt M e hp0 hpM]
      constructor
      · intro h; simp at h
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega
    · have hpe : M = p := by omega
      subst hpe
      rw [Γ.subPos_M M e hM, Option.map_eq_none_iff]
      constructor
      · intro h; exact Or.inr ⟨rfl, h⟩
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · omega
        · exact h

 
def subdiv (hM : 2 ≤ M) : EdgeGraph (SubV V E M) (E × Fin M) where
  tail ek := Γ.subPos M ek.1 ek.2.val
  head ek := Γ.subPos M ek.1 (ek.2.val + 1)
  cond ek := M * Γ.cond ek.1
  cond_pos ek := mul_pos (by exact_mod_cast (show 0 < M by omega)) (Γ.cond_pos ek.1)
  tail_ne_head ek := by
    obtain ⟨e, k⟩ := ek
    have hk := k.isLt
    simp only
    by_cases hk0 : k.val = 0
    · rw [hk0, Γ.subPos_zero, Γ.subPos_of_lt M e (by omega) (by omega)]
      cases Γ.tail e <;> simp
    · by_cases hk1 : k.val + 1 < M
      · rw [Γ.subPos_of_lt M e hk0 (by omega), Γ.subPos_of_lt M e (by omega) hk1]
        simp
        omega
      · have : k.val + 1 = M := by omega
        rw [Γ.subPos_of_lt M e hk0 (by omega), this, Γ.subPos_M M e (by omega)]
        cases Γ.head e <;> simp

 
def interp (g : Option V → ℝ) : Option (SubV V E M) → ℝ
  | none => g none
  | some (Sum.inl v) => g (some v)
  | some (Sum.inr (e, k)) => g (Γ.tail e) + ((k.val + 1 : ℝ) / M) * (g (Γ.head e) - g (Γ.tail e))

theorem interp_map_inl (g : Option V → ℝ) (a : Option V) :
    Γ.interp M g (a.map Sum.inl) = g a := by
  cases a <;> rfl

theorem interp_subPos (g : Option V → ℝ) (e : E) {p : ℕ} (hp : p ≤ M) (hM : 1 ≤ M) :
    Γ.interp M g (Γ.subPos M e p) =
      g (Γ.tail e) + ((p : ℝ) / M) * (g (Γ.head e) - g (Γ.tail e)) := by
  by_cases hp0 : p = 0
  · subst hp0
    rw [Γ.subPos_zero, interp_map_inl]
    simp
  · by_cases hpM : p < M
    · rw [Γ.subPos_of_lt M e hp0 hpM]
      simp only [interp]
      congr 3
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hp0)]
      push_cast
      ring
    · have hpe : M = p := by omega
      subst hpe
      rw [Γ.subPos_M M e hM, interp_map_inl]
      have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
      field_simp
      ring

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos

namespace SupercriticalLQGUniqueness.B2.QPos

namespace EdgeGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (Γ : EdgeGraph V E) (M : ℕ)

 
theorem sum_subEdge_ite (e : E) {j : ℕ} (hj : j < M) (f : E × Fin M → ℝ) :
    ∑ p : E × Fin M, (if p.1 = e ∧ p.2.val = j then f p else 0) = f (e, ⟨j, hj⟩) := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single e]
  · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin M)]
    · simp
    · intro k _ hk
      have : k.val ≠ j := fun h => hk (Fin.ext h)
      simp [this]
    · simp
  · intro e' _ he'
    apply Finset.sum_eq_zero
    intro k _
    simp [he']
  · simp

theorem sum_fin_val_ite {j : ℕ} (hj : j < M) (c : ℝ) :
    ∑ y : Fin M, (if y.val = j then c else 0) = c := by
  rw [Finset.sum_eq_single ⟨j, hj⟩]
  · simp
  · intro b _ hb
    have : b.val ≠ j := fun h => hb (Fin.ext h)
    simp [this]
  · simp

theorem ind_subPos_inr {e e' : E} {k : Fin (M - 1)} {p : ℕ} (hp : p ≤ M) :
    ind (Γ.subPos M e' p) (Sum.inr (e, k)) = if e' = e ∧ p = k.val + 1 then 1 else 0 := by
  unfold ind
  exact if_congr (Γ.subPos_eq_inr_iff M hp) rfl rfl

theorem ind_subPos_inl {e : E} {v : V} {p : ℕ} (hp : p ≤ M) (hM : 2 ≤ M) :
    ind (Γ.subPos M e p) (Sum.inl v) =
      if (p = 0 ∧ Γ.tail e = some v) ∨ (p = M ∧ Γ.head e = some v) then 1 else 0 := by
  unfold ind
  exact if_congr (Γ.subPos_eq_inl_iff M hp hM) rfl rfl

 
theorem lap_subdiv_interp_inr (hM : 2 ≤ M) (g : Option V → ℝ) (e : E) (k : Fin (M - 1)) :
    (Γ.subdiv M hM).lap (Γ.interp M g) (Sum.inr (e, k)) = 0 := by
  have hk := k.isLt
  have hM1 : 1 ≤ M := by omega
  unfold lap
  simp only [subdiv]
  have hterm : ∀ p : E × Fin M,
      (M : ℝ) * Γ.cond p.1 * (ind (Γ.subPos M p.1 p.2.val) (Sum.inr (e, k)) *
          (Γ.interp M g (some (Sum.inr (e, k))) - Γ.interp M g (Γ.subPos M p.1 (p.2.val + 1))) +
        ind (Γ.subPos M p.1 (p.2.val + 1)) (Sum.inr (e, k)) *
          (Γ.interp M g (some (Sum.inr (e, k))) - Γ.interp M g (Γ.subPos M p.1 p.2.val))) =
      (if p.1 = e ∧ p.2.val = k.val + 1 then (M : ℝ) * Γ.cond e *
          (Γ.interp M g (some (Sum.inr (e, k))) - Γ.interp M g (Γ.subPos M e (k.val + 2)))
        else 0) +
      (if p.1 = e ∧ p.2.val = k.val then (M : ℝ) * Γ.cond e *
          (Γ.interp M g (some (Sum.inr (e, k))) - Γ.interp M g (Γ.subPos M e k.val))
        else 0) := by
    intro p
    rw [Γ.ind_subPos_inr M (by omega), Γ.ind_subPos_inr M (by omega)]
    by_cases h1 : p.1 = e ∧ p.2.val = k.val + 1
    · have h2 : ¬ (p.1 = e ∧ p.2.val = k.val) := fun h => by
        have := h1.2; have := h.2; omega
      have h2' : ¬ (p.1 = e ∧ p.2.val + 1 = k.val + 1) := fun h => by
        have := h1.2; have := h.2; omega
      rw [if_pos h1, if_pos h1, if_neg h2, if_neg h2', h1.1, h1.2]
      ring
    · by_cases h2 : p.1 = e ∧ p.2.val = k.val
      · have h2' : p.1 = e ∧ p.2.val + 1 = k.val + 1 := ⟨h2.1, by have := h2.2; omega⟩
        rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2', h2.1, h2.2]
        ring
      · have h2' : ¬ (p.1 = e ∧ p.2.val + 1 = k.val + 1) := fun h =>
          h2 ⟨h.1, by have := h.2; omega⟩
        rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2']
        ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_add_distrib,
    sum_subEdge_ite M e (by omega : k.val + 1 < M),
    sum_subEdge_ite M e (by omega : k.val < M)]
  have hx : Γ.interp M g (some (Sum.inr (e, k))) =
      g (Γ.tail e) + (((k.val + 1 : ℕ) : ℝ) / M) * (g (Γ.head e) - g (Γ.tail e)) := by
    simp [interp]
  rw [hx, Γ.interp_subPos M g e (by omega) hM1, Γ.interp_subPos M g e (by omega) hM1]
  push_cast
  ring

 
theorem lap_subdiv_interp_inl (hM : 2 ≤ M) (g : Option V → ℝ) (v : V) :
    (Γ.subdiv M hM).lap (Γ.interp M g) (Sum.inl v) = Γ.lap g v := by
  have hM1 : 1 ≤ M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  unfold lap
  simp only [subdiv]
  have hterm : ∀ p : E × Fin M,
      (M : ℝ) * Γ.cond p.1 * (ind (Γ.subPos M p.1 p.2.val) (Sum.inl v) *
          (Γ.interp M g (some (Sum.inl v)) - Γ.interp M g (Γ.subPos M p.1 (p.2.val + 1))) +
        ind (Γ.subPos M p.1 (p.2.val + 1)) (Sum.inl v) *
          (Γ.interp M g (some (Sum.inl v)) - Γ.interp M g (Γ.subPos M p.1 p.2.val))) =
      (if p.2.val = 0 then Γ.cond p.1 * (ind (Γ.tail p.1) v * (g (some v) - g (Γ.head p.1)))
        else 0) +
      (if p.2.val = M - 1 then Γ.cond p.1 * (ind (Γ.head p.1) v * (g (some v) - g (Γ.tail p.1)))
        else 0) := by
    intro p
    have hp := p.2.isLt
    rw [Γ.ind_subPos_inl M (by omega) hM, Γ.ind_subPos_inl M (by omega) hM]
    have hv : Γ.interp M g (some (Sum.inl v)) = g (some v) := rfl
    rw [hv]
    by_cases h0 : p.2.val = 0
    · have hne : p.2.val ≠ M - 1 := by omega
      rw [if_pos h0, if_neg hne]
      have hc1 : ¬ ((p.2.val + 1 = 0 ∧ Γ.tail p.1 = some v) ∨
          (p.2.val + 1 = M ∧ Γ.head p.1 = some v)) := by
        rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega
      rw [if_neg hc1, zero_mul, add_zero]
      simp only [h0, true_and, zero_add]
      by_cases ht : Γ.tail p.1 = some v
      · have : (Γ.tail p.1 = some v ∨ 0 = M ∧ Γ.head p.1 = some v) := Or.inl ht
        rw [if_pos this]
        unfold ind
        rw [if_pos ht, Γ.interp_subPos M g p.1 (by omega) hM1, ht]
        field_simp
        ring
      · have : ¬ (Γ.tail p.1 = some v ∨ 0 = M ∧ Γ.head p.1 = some v) := by
          rintro (h | ⟨h, _⟩)
          · exact ht h
          · omega
        rw [if_neg this]
        unfold ind
        rw [if_neg ht]
        ring
    · by_cases hlast : p.2.val = M - 1
      · rw [if_neg h0, if_pos hlast]
        have hc0 : ¬ ((p.2.val = 0 ∧ Γ.tail p.1 = some v) ∨
            (p.2.val = M ∧ Γ.head p.1 = some v)) := by
          rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega
        rw [if_neg hc0, zero_mul, zero_add, zero_add]
        have hpM : p.2.val + 1 = M := by omega
        by_cases hh : Γ.head p.1 = some v
        · have : ((p.2.val + 1 = 0 ∧ Γ.tail p.1 = some v) ∨
              (p.2.val + 1 = M ∧ Γ.head p.1 = some v)) := Or.inr ⟨hpM, hh⟩
          rw [if_pos this]
          unfold ind
          rw [if_pos hh, Γ.interp_subPos M g p.1 (by omega) hM1, hh]
          rw [show ((p.2.val : ℕ) : ℝ) = (M : ℝ) - 1 by
            rw [show p.2.val = M - 1 from hlast, Nat.cast_sub hM1]; simp]
          field_simp
          ring
        · have : ¬ ((p.2.val + 1 = 0 ∧ Γ.tail p.1 = some v) ∨
              (p.2.val + 1 = M ∧ Γ.head p.1 = some v)) := by
            rintro (⟨h, _⟩ | ⟨_, h⟩)
            · omega
            · exact hh h
          rw [if_neg this]
          unfold ind
          rw [if_neg hh]
          ring
      · rw [if_neg h0, if_neg hlast]
        have hc0 : ¬ ((p.2.val = 0 ∧ Γ.tail p.1 = some v) ∨
            (p.2.val = M ∧ Γ.head p.1 = some v)) := by
          rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega
        have hc1 : ¬ ((p.2.val + 1 = 0 ∧ Γ.tail p.1 = some v) ∨
            (p.2.val + 1 = M ∧ Γ.head p.1 = some v)) := by
          rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega
        rw [if_neg hc0, if_neg hc1]
        ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_add_distrib, Fintype.sum_prod_type,
    Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only []
  rw [sum_fin_val_ite M (by omega : 0 < M), sum_fin_val_ite M (by omega : M - 1 < M)]
  ring

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
