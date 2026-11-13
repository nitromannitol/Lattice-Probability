/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2SubdivGreen at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Subdiv
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2RayKnight
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2PathSum
import Mathlib
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2VisitGen

 










set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem sq_sub_le_mul_sum_sq (a : ℕ → ℝ) (p j : ℕ) :
    (a p - a (p + j)) ^ 2 ≤ j * ∑ k ∈ Finset.range j, (a (p + k) - a (p + k + 1)) ^ 2 := by
  have htel : ∑ k ∈ Finset.range j, (a (p + k) - a (p + k + 1)) = a p - a (p + j) := by
    have := Finset.sum_range_sub' (fun k => a (p + k)) j
    simpa [add_assoc] using this
  rw [← htel]
  have := sq_sum_le_card_mul_sum_sq (s := Finset.range j)
    (f := fun k => a (p + k) - a (p + k + 1))
  simpa using this

namespace EdgeGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (Γ : EdgeGraph V E) (M : ℕ)

theorem ext_subPos_zero (y : SubV V E M → ℝ) (e : E) :
    ext 0 y (Γ.subPos M e 0) = ext 0 (fun v => y (Sum.inl v)) (Γ.tail e) := by
  rw [Γ.subPos_zero]; cases Γ.tail e <;> rfl

theorem ext_subPos_M (hM : 1 ≤ M) (y : SubV V E M → ℝ) (e : E) :
    ext 0 y (Γ.subPos M e M) = ext 0 (fun v => y (Sum.inl v)) (Γ.head e) := by
  rw [Γ.subPos_M M e hM]; cases Γ.head e <;> rfl

 
theorem energy_subdiv_eq (hM : 2 ≤ M) (y : SubV V E M → ℝ) :
    y ⬝ᵥ ((Γ.subdiv M hM).toWired.precision *ᵥ y) =
      ∑ e, ∑ k ∈ Finset.range M, (M : ℝ) * Γ.cond e *
        (ext 0 y (Γ.subPos M e k) - ext 0 y (Γ.subPos M e (k + 1))) ^ 2 := by
  rw [energy_eq_edge_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Fin.sum_univ_eq_sum_range (fun k => (M : ℝ) * Γ.cond e *
    (ext 0 y (Γ.subPos M e k) - ext 0 y (Γ.subPos M e (k + 1))) ^ 2)]
  rfl

 
theorem energy_subdiv_ge (hM : 2 ≤ M) (y : SubV V E M → ℝ) :
    (fun v => y (Sum.inl v)) ⬝ᵥ (Γ.toWired.precision *ᵥ fun v => y (Sum.inl v)) ≤
      y ⬝ᵥ ((Γ.subdiv M hM).toWired.precision *ᵥ y) := by
  rw [Γ.energy_subdiv_eq M hM, energy_eq_edge_sum]
  apply Finset.sum_le_sum
  intro e _
  have hcs := sq_sub_le_mul_sum_sq (fun k => ext 0 y (Γ.subPos M e k)) 0 M
  simp only [zero_add] at hcs
  rw [Γ.ext_subPos_zero, Γ.ext_subPos_M M (by omega)] at hcs
  rw [← Finset.mul_sum]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hc := Γ.cond_pos e
  calc Γ.cond e * (ext 0 (fun v => y (Sum.inl v)) (Γ.tail e) -
        ext 0 (fun v => y (Sum.inl v)) (Γ.head e)) ^ 2
      ≤ Γ.cond e * (M * ∑ k ∈ Finset.range M,
          (ext 0 y (Γ.subPos M e k) - ext 0 y (Γ.subPos M e (k + 1))) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hc.le
    _ = (M : ℝ) * Γ.cond e * ∑ k ∈ Finset.range M,
          (ext 0 y (Γ.subPos M e k) - ext 0 y (Γ.subPos M e (k + 1))) ^ 2 := by ring

 
theorem subdiv_posDef (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef) :
    (Γ.subdiv M hM).toWired.precision.PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Γ.subdiv M hM).toWired.precision_isHermitian
  intro y hy
  change 0 < y ⬝ᵥ ((Γ.subdiv M hM).toWired.precision *ᵥ y)
  by_cases hinl : (fun v => y (Sum.inl v)) = 0
  · 
    have hex : ∃ e k, y (Sum.inr (e, k)) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hy
      funext x
      rcases x with v | ⟨e, k⟩
      · exact congrFun hinl v
      · exact hcon e k
    obtain ⟨e, k, hek⟩ := hex
    have hk := k.isLt
    rw [Γ.energy_subdiv_eq M hM]
    have hnn : ∀ e' ∈ Finset.univ, 0 ≤ ∑ k ∈ Finset.range M, (M : ℝ) * Γ.cond e' *
        (ext 0 y (Γ.subPos M e' k) - ext 0 y (Γ.subPos M e' (k + 1))) ^ 2 :=
      fun e' _ => Finset.sum_nonneg fun k _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Γ.cond_pos e').le) (sq_nonneg _)
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnn (Finset.mem_univ e))
    rw [← Finset.mul_sum]
    refine mul_pos (mul_pos (by exact_mod_cast (show 0 < M by omega)) (Γ.cond_pos e)) ?_
    have hcs := sq_sub_le_mul_sum_sq (fun k => ext 0 y (Γ.subPos M e k)) 0 (k.val + 1)
    simp only [zero_add] at hcs
    have h0 : ext 0 y (Γ.subPos M e 0) = 0 := by
      rw [Γ.ext_subPos_zero, hinl]; cases Γ.tail e <;> rfl
    have h1 : ext 0 y (Γ.subPos M e (k.val + 1)) = y (Sum.inr (e, k)) := by
      rw [Γ.subPos_of_lt M e (by omega) (by omega)]
      simp
    rw [h0, h1] at hcs
    have hpos : 0 < (0 - y (Sum.inr (e, k))) ^ 2 := by
      have : 0 - y (Sum.inr (e, k)) ≠ 0 := by simpa using hek
      positivity
    have hsub : ∑ k' ∈ Finset.range (k.val + 1),
        (ext 0 y (Γ.subPos M e k') - ext 0 y (Γ.subPos M e (k' + 1))) ^ 2 ≤
        ∑ k' ∈ Finset.range M,
        (ext 0 y (Γ.subPos M e k') - ext 0 y (Γ.subPos M e (k' + 1))) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun _ _ _ => sq_nonneg _)
    by_contra hle
    push_neg at hle
    have : ∑ k' ∈ Finset.range (k.val + 1),
        (ext 0 y (Γ.subPos M e k') - ext 0 y (Γ.subPos M e (k' + 1))) ^ 2 ≤ 0 :=
      le_trans hsub hle
    have := le_trans hcs (mul_le_mul_of_nonneg_left this (by positivity))
    linarith
  · have hpos := hK.dotProduct_mulVec_pos hinl
    simp only [star_trivial] at hpos
    exact lt_of_lt_of_le hpos (Γ.energy_subdiv_ge M hM y)

 
def interpVec (y : V → ℝ) : SubV V E M → ℝ := fun x => Γ.interp M (ext 0 y) (some x)

theorem ext_interpVec (y : V → ℝ) : ext 0 (Γ.interpVec M y) = Γ.interp M (ext 0 y) := by
  funext x
  cases x with
  | none => rfl
  | some x => rfl

 
theorem precision_subdiv_mulVec_interpVec (hM : 2 ≤ M) (y : V → ℝ) (x : SubV V E M) :
    ((Γ.subdiv M hM).toWired.precision *ᵥ Γ.interpVec M y) x =
      match x with
      | Sum.inl v => (Γ.toWired.precision *ᵥ y) v
      | Sum.inr _ => 0 := by
  rw [(Γ.subdiv M hM).precision_mulVec_eq_lap 0, zero_mul, add_zero, Γ.ext_interpVec]
  rcases x with v | ⟨e, k⟩
  · rw [Γ.lap_subdiv_interp_inl M hM]
    show Γ.lap (ext 0 y) v = (Γ.toWired.precision *ᵥ y) v
    rw [Γ.precision_mulVec_eq_lap 0, zero_mul, add_zero]
  · exact Γ.lap_subdiv_interp_inr M hM _ e k

 
theorem green_subdiv_inl (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef) (v w : V) :
    (Γ.subdiv M hM).toWired.green (Sum.inl v) (Sum.inl w) = Γ.toWired.green v w := by
  have hKM := Γ.subdiv_posDef M hM hK
  set y : V → ℝ := fun u => Γ.toWired.green u w
  have hy : Γ.toWired.precision *ᵥ y = Pi.single w 1 := by
    funext u
    have := congrFun (congrFun (Γ.toWired.precision_mul_green hK) u) w
    rw [Matrix.mul_apply] at this
    simp only [Matrix.mulVec, dotProduct, y, this, Matrix.one_apply, Pi.single_apply]
  have hsol : (Γ.subdiv M hM).toWired.precision *ᵥ Γ.interpVec M y = Pi.single (Sum.inl w) 1 := by
    funext x
    rw [Γ.precision_subdiv_mulVec_interpVec M hM y x]
    rcases x with u | ⟨e, k⟩
    · simp only [hy, Pi.single_apply, Sum.inl.injEq]
    · simp [Pi.single_apply]
  have hcol : Γ.interpVec M y = (Γ.subdiv M hM).toWired.green *ᵥ Pi.single (Sum.inl w) 1 := by
    rw [← hsol, Matrix.mulVec_mulVec, (Γ.subdiv M hM).toWired.green_mul_precision hKM,
      Matrix.one_mulVec]
  have := congrFun hcol (Sum.inl v)
  simp only [interpVec, interp, ext_some] at this
  rw [Matrix.mulVec_single_one] at this
  simpa [y] using this.symm

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
