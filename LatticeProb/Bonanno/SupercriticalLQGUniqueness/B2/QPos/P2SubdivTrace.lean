/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2SubdivTrace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2SubdivGreen
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Avoid

 








set_option autoImplicit false
noncomputable section

open Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

namespace EdgeGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (Γ : EdgeGraph V E) (M : ℕ)

theorem sum_ind_mul_some (a : Option V) (F : Option V → ℝ) :
    ∑ x, ind a x * F (some x) = if a = none then 0 else F a := by
  rw [sum_ind_mul a (fun x => F (some x))]
  cases a <;> simp

 
theorem sum_bdryCond_mul (F : Option V → ℝ) :
    ∑ x, Γ.bdryCond x * F (some x) =
      ∑ e, Γ.cond e * ((if Γ.head e = none then F (Γ.tail e) else 0) +
        (if Γ.tail e = none then F (Γ.head e) else 0)) := by
  unfold bdryCond
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have h1 := sum_ind_mul_some (Γ.tail e) F
  have h2 := sum_ind_mul_some (Γ.head e) F
  have key : ∑ x, Γ.cond e * (ind (Γ.tail e) x * (if Γ.head e = none then 1 else 0) +
      (if Γ.tail e = none then 1 else 0) * ind (Γ.head e) x) * F (some x) =
      Γ.cond e * ((if Γ.head e = none then 1 else 0) * ∑ x, ind (Γ.tail e) x * F (some x) +
        (if Γ.tail e = none then 1 else 0) * ∑ x, ind (Γ.head e) x * F (some x)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [key, h1, h2]
  have hne := Γ.tail_ne_head e
  rcases ht : Γ.tail e with _ | v <;> rcases hh : Γ.head e with _ | w
  · exact absurd (ht.trans hh.symm) hne
  all_goals simp

 
def interpAvoid (Y : V → ℝ) : SubV V E M → ℝ := fun x => Γ.interp M (ext 1 Y) (some x)

theorem ext_interpAvoid (Y : V → ℝ) : ext 1 (Γ.interpAvoid M Y) = Γ.interp M (ext 1 Y) := by
  funext x
  cases x <;> rfl

 
theorem isAvoidHarmonic_subdiv (hM : 2 ≤ M) (A : Set V) (Y : V → ℝ)
    (hY : Γ.toWired.IsAvoidHarmonic A Y) :
    (Γ.subdiv M hM).toWired.IsAvoidHarmonic (Sum.inl '' A) (Γ.interpAvoid M Y) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hx
    exact hY.zero_on a ha
  · rw [(Γ.subdiv M hM).precision_mulVec_eq_lap 1, one_mul, Γ.ext_interpAvoid]
    change _ + (Γ.subdiv M hM).bdryCond x = (Γ.subdiv M hM).bdryCond x
    rcases x with v | ⟨e, k⟩
    · rw [Γ.lap_subdiv_interp_inl M hM]
      have hv : v ∉ A := fun hv => hx ⟨v, hv, rfl⟩
      have := hY.harm v hv
      rw [Γ.precision_mulVec_eq_lap 1, one_mul] at this
      change Γ.lap (ext 1 Y) v + Γ.bdryCond v = Γ.bdryCond v at this
      linarith
    · rw [Γ.lap_subdiv_interp_inr M hM, zero_add]

 
theorem sum_bdryCond_subdiv_interp (hM : 2 ≤ M) (g : Option V → ℝ) (hg : g none = 1) :
    ∑ x, (Γ.subdiv M hM).bdryCond x * Γ.interp M g (some x) =
      ((M : ℝ) - 1) * ∑ v, Γ.bdryCond v + ∑ v, Γ.bdryCond v * g (some v) := by
  have hM1 : 1 ≤ M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have h1 : ∑ v, Γ.bdryCond v = ∑ v, Γ.bdryCond v * (fun _ : Option V => (1 : ℝ)) (some v) := by
    simp
  rw [(Γ.subdiv M hM).sum_bdryCond_mul (Γ.interp M g), Γ.sum_bdryCond_mul g, h1,
    Γ.sum_bdryCond_mul (fun _ => 1), Finset.mul_sum, ← Finset.sum_add_distrib,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  have hterm : ∀ k : Fin M, (Γ.subdiv M hM).cond (e, k) *
      ((if (Γ.subdiv M hM).head (e, k) = none then
          Γ.interp M g ((Γ.subdiv M hM).tail (e, k)) else 0) +
        (if (Γ.subdiv M hM).tail (e, k) = none then
          Γ.interp M g ((Γ.subdiv M hM).head (e, k)) else 0)) =
      (if k.val = M - 1 then (M : ℝ) * Γ.cond e *
          (if Γ.head e = none then Γ.interp M g (Γ.subPos M e (M - 1)) else 0) else 0) +
        (if k.val = 0 then (M : ℝ) * Γ.cond e *
          (if Γ.tail e = none then Γ.interp M g (Γ.subPos M e 1) else 0) else 0) := by
    intro k
    simp only [subdiv]
    have hk := k.isLt
    have hn1 : Γ.subPos M e (k.val + 1) = none ↔ k.val = M - 1 ∧ Γ.head e = none := by
      rw [Γ.subPos_eq_none_iff M (by omega) hM1]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, h'⟩)
        · omega
        · exact ⟨by omega, h'⟩
      · rintro ⟨h, h'⟩; exact Or.inr ⟨by omega, h'⟩
    have hn0 : Γ.subPos M e k.val = none ↔ k.val = 0 ∧ Γ.tail e = none := by
      rw [Γ.subPos_eq_none_iff M (by omega) hM1]
      constructor
      · rintro (⟨h, h'⟩ | ⟨h, _⟩)
        · exact ⟨h, h'⟩
        · omega
      · rintro ⟨h, h'⟩; exact Or.inl ⟨h, h'⟩
    simp only [hn1, hn0]
    by_cases h1 : k.val = M - 1
    · have h0 : k.val ≠ 0 := by omega
      have hM1' : M - 1 ≠ 0 := by omega
      simp only [h1, hM1', true_and, false_and, ite_false, ite_true, add_zero]
      try (split_ifs <;> ring)
    · simp only [h1, false_and, ite_false, zero_add]
      by_cases h0 : k.val = 0
      · simp only [h0, true_and, ite_true, zero_add]
        try (split_ifs <;> ring)
      · simp only [h0, false_and, ite_false, mul_zero]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_add_distrib,
    sum_fin_val_ite M (by omega : M - 1 < M), sum_fin_val_ite M (by omega : 0 < M)]
  rw [Γ.interp_subPos M g e (by omega) hM1, Γ.interp_subPos M g e (by omega) hM1]
  rw [Nat.cast_sub hM1]
  push_cast
  have hne := Γ.tail_ne_head e
  rcases ht : Γ.tail e with _ | v <;> rcases hh : Γ.head e with _ | w
  · exact absurd (ht.trans hh.symm) hne
  all_goals simp only [hg, reduceCtorEq, ite_true, ite_false, if_true, if_false]
  all_goals field_simp
  all_goals ring

 

theorem sum_boundary_interpAvoid (hM : 2 ≤ M) (Y : V → ℝ) :
    ∑ x, (Γ.subdiv M hM).toWired.boundary x * Γ.interpAvoid M Y x =
      ((M : ℝ) - 1) * Γ.toWired.boundaryTotal + ∑ v, Γ.toWired.boundary v * Y v :=
  Γ.sum_bdryCond_subdiv_interp M hM (ext 1 Y) rfl

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
