/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2BoxGreen at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2GreenBounds
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2FlipSum

 







set_option autoImplicit false
noncomputable section

open Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

namespace EdgeGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (Γ : EdgeGraph V E) (M : ℕ)

theorem green_inl_ge (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef) (v : V) :
    1 ≤ Γ.toWired.precision v v * (Γ.subdiv M hM).toWired.green (Sum.inl v) (Sum.inl v) := by
  rw [Γ.green_subdiv_inl M hM hK]
  have h := Γ.toWired.sq_le_energy_mul_green hK v (Pi.single v 1)
  simp only [Pi.single_eq_same, one_pow] at h
  have hE : Pi.single v (1 : ℝ) ⬝ᵥ (Γ.toWired.precision *ᵥ Pi.single v 1) =
      Γ.toWired.precision v v := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  rwa [hE] at h

 
def interpInd (A : Finset V) : SubV V E M → ℝ :=
  Γ.interpVec M fun v => if v ∈ A then 1 else 0

theorem energy_interpInd_le (hM : 2 ≤ M) (A : Finset V) :
    Γ.interpInd M A ⬝ᵥ ((Γ.subdiv M hM).toWired.precision *ᵥ Γ.interpInd M A) ≤
      ∑ v ∈ A, Γ.toWired.precision v v := by
  unfold interpInd
  rw [Γ.energy_interpVec M hM]
  exact Γ.toWired.energy_indicator_le A

theorem interpInd_inr (A : Finset V) (e : E) (k : Fin (M - 1)) :
    Γ.interpInd M A (Sum.inr (e, k)) =
      ext 0 (fun v => if v ∈ A then (1 : ℝ) else 0) (Γ.tail e) +
        ((k.val + 1 : ℝ) / M) * (ext 0 (fun v => if v ∈ A then (1 : ℝ) else 0) (Γ.head e) -
          ext 0 (fun v => if v ∈ A then (1 : ℝ) else 0) (Γ.tail e)) := rfl

 
theorem green_inr_ge_interior (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef) (e : E)
    (k : Fin (M - 1)) {v w : V} (ht : Γ.tail e = some v) (hh : Γ.head e = some w) :
    1 ≤ (Γ.toWired.precision v v + Γ.toWired.precision w w) *
      (Γ.subdiv M hM).toWired.green (Sum.inr (e, k)) (Sum.inr (e, k)) := by
  have hKM := Γ.subdiv_posDef M hM hK
  have hvw : v ≠ w := fun h => Γ.tail_ne_head e (by rw [ht, hh, h])
  have h := (Γ.subdiv M hM).toWired.sq_le_energy_mul_green hKM (Sum.inr (e, k))
    (Γ.interpInd M {v, w})
  have hval : Γ.interpInd M {v, w} (Sum.inr (e, k)) = 1 := by
    rw [interpInd_inr, ht, hh]
    simp
  rw [hval, one_pow] at h
  have hE := Γ.energy_interpInd_le M hM {v, w}
  rw [Finset.sum_pair hvw] at hE
  have hG := (Γ.subdiv M hM).toWired.green_diag_pos hKM (Sum.inr (e, k))
  nlinarith

 
theorem green_inr_ge_boundary (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef) (e : E)
    (k : Fin (M - 1)) {v : V} (ht : Γ.tail e = some v) (hh : Γ.head e = none) :
    ((M - (k.val + 1) : ℝ) / M) ^ 2 ≤ Γ.toWired.precision v v *
      (Γ.subdiv M hM).toWired.green (Sum.inr (e, k)) (Sum.inr (e, k)) := by
  have hKM := Γ.subdiv_posDef M hM hK
  have h := (Γ.subdiv M hM).toWired.sq_le_energy_mul_green hKM (Sum.inr (e, k))
    (Γ.interpInd M {v})
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hval : Γ.interpInd M {v} (Sum.inr (e, k)) = (M - (k.val + 1) : ℝ) / M := by
    rw [interpInd_inr, ht, hh]
    simp only [ext_some, Finset.mem_singleton, if_true, ext_none]
    field_simp
    ring
  rw [hval] at h
  have hE := Γ.energy_interpInd_le M hM {v}
  rw [Finset.sum_singleton] at hE
  have hG := (Γ.subdiv M hM).toWired.green_diag_pos hKM (Sum.inr (e, k))
  nlinarith

 
theorem green_inr_le_boundary (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef) (e : E)
    (k : Fin (M - 1)) (hh : Γ.head e = none) :
    (Γ.subdiv M hM).toWired.green (Sum.inr (e, k)) (Sum.inr (e, k)) ≤
      (M - (k.val + 1) : ℝ) / (M * Γ.cond e) := by
  have hKM := Γ.subdiv_posDef M hM hK
  have hk := k.isLt
  have hc := Γ.cond_pos e
  have hMq : (0 : ℝ) < M - (k.val + 1) := by
    have : ((k.val + 1 : ℕ) : ℝ) < M := by exact_mod_cast (show k.val + 1 < M by omega)
    push_cast at this
    linarith
  have hL : 0 < (M : ℝ) * Γ.cond e / (M - (k.val + 1)) := by
    have : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    positivity
  have := (Γ.subdiv M hM).toWired.green_le_of_energy_ge hKM (Sum.inr (e, k)) hL (fun f hf => by
    have h := Γ.energy_subdiv_ge_tail M hM f e hh (q := k.val + 1) (by omega)
    rw [Γ.subPos_of_lt M e (by omega) (by omega)] at h
    simp only [ext_some] at h
    have hk' : (⟨k.val + 1 - 1, by omega⟩ : Fin (M - 1)) = k := Fin.ext (by simp)
    rw [hk', hf, one_pow, mul_one] at h
    push_cast at h
    exact h)
  refine this.trans (le_of_eq ?_)
  field_simp

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
