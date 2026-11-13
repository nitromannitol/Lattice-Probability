/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2EdgeGraph at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFCore

 








set_option autoImplicit false
noncomputable section

open Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

 

structure EdgeGraph (V E : Type*) where
  tail : E → Option V
  head : E → Option V
  cond : E → ℝ
  cond_pos : ∀ e, 0 < cond e
  tail_ne_head : ∀ e, tail e ≠ head e

namespace EdgeGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (Γ : EdgeGraph V E)

 
def ext (β : ℝ) (y : V → ℝ) : Option V → ℝ
  | none => β
  | some v => y v

@[simp] theorem ext_none (β : ℝ) (y : V → ℝ) : ext β y none = β := rfl
@[simp] theorem ext_some (β : ℝ) (y : V → ℝ) (v : V) : ext β y (some v) = y v := rfl

 
def ind (a : Option V) (x : V) : ℝ := if a = some x then 1 else 0

 
def edgeCond (i j : V) : ℝ :=
  ∑ e, Γ.cond e * (ind (Γ.tail e) i * ind (Γ.head e) j + ind (Γ.tail e) j * ind (Γ.head e) i)

 
def bdryCond (i : V) : ℝ :=
  ∑ e, Γ.cond e * (ind (Γ.tail e) i * (if Γ.head e = none then 1 else 0) +
    (if Γ.tail e = none then 1 else 0) * ind (Γ.head e) i)

theorem ind_nonneg (a : Option V) (x : V) : 0 ≤ ind a x := by
  unfold ind; split_ifs <;> norm_num

theorem edgeCond_self (i : V) : Γ.edgeCond i i = 0 := by
  unfold edgeCond
  apply Finset.sum_eq_zero
  intro e _
  have h := Γ.tail_ne_head e
  unfold ind
  by_cases h1 : Γ.tail e = some i
  · have h2 : Γ.head e ≠ some i := fun h2 => h (h1.trans h2.symm)
    simp [h1, h2]
  · simp [h1]

 
def toWired : WiredConductances V where
  edge := Γ.edgeCond
  boundary := Γ.bdryCond
  edge_symm i j := by
    unfold edgeCond
    apply Finset.sum_congr rfl
    intro e _
    ring
  edge_self := Γ.edgeCond_self
  edge_nonneg i j := Finset.sum_nonneg fun e _ => mul_nonneg (Γ.cond_pos e).le
    (add_nonneg (mul_nonneg (ind_nonneg _ _) (ind_nonneg _ _))
      (mul_nonneg (ind_nonneg _ _) (ind_nonneg _ _)))
  boundary_nonneg i := Finset.sum_nonneg fun e _ => mul_nonneg (Γ.cond_pos e).le
    (add_nonneg (mul_nonneg (ind_nonneg _ _) (by split_ifs <;> norm_num))
      (mul_nonneg (by split_ifs <;> norm_num) (ind_nonneg _ _)))

 
def lap (F : Option V → ℝ) (x : V) : ℝ :=
  ∑ e, Γ.cond e * (ind (Γ.tail e) x * (F (some x) - F (Γ.head e)) +
    ind (Γ.head e) x * (F (some x) - F (Γ.tail e)))

theorem sum_ind_mul (a : Option V) (f : V → ℝ) : ∑ j, ind a j * f j =
    match a with
    | none => 0
    | some v => f v := by
  cases a with
  | none => simp [ind]
  | some v =>
    simp only [ind, Option.some.injEq, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp

 

theorem precision_mulVec_eq_lap (β : ℝ) (y : V → ℝ) (x : V) :
    (Γ.toWired.precision *ᵥ y) x = Γ.lap (ext β y) x + β * Γ.bdryCond x := by
  rw [Γ.toWired.precision_mulVec]
  change Γ.bdryCond x * y x + ∑ j, Γ.edgeCond x j * (y x - y j) = _
  unfold lap bdryCond edgeCond
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have ht := sum_ind_mul (Γ.tail e) (fun j => Γ.cond e * ind (Γ.head e) x * (y x - y j))
  have hh := sum_ind_mul (Γ.head e) (fun j => Γ.cond e * ind (Γ.tail e) x * (y x - y j))
  have key : ∑ j, Γ.cond e * (ind (Γ.tail e) x * ind (Γ.head e) j +
      ind (Γ.tail e) j * ind (Γ.head e) x) * (y x - y j) =
      ∑ j, ind (Γ.head e) j * (Γ.cond e * ind (Γ.tail e) x * (y x - y j)) +
        ∑ j, ind (Γ.tail e) j * (Γ.cond e * ind (Γ.head e) x * (y x - y j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [key, ht, hh]
  have htx := Γ.tail_ne_head e
  rcases hte : Γ.tail e with _ | v <;> rcases hhe : Γ.head e with _ | w
  · exact absurd (hte.trans hhe.symm) htx
  all_goals simp only [ind, ext_none, ext_some, Option.some.injEq, reduceCtorEq, if_false,
    ite_true, ite_false, ↓reduceIte]
  all_goals first | ring | (split_ifs <;> subst_vars <;> ring)

 
theorem energy_eq_edge_sum (y : V → ℝ) :
    y ⬝ᵥ (Γ.toWired.precision *ᵥ y) = ∑ e, Γ.cond e * (ext 0 y (Γ.tail e) - ext 0 y (Γ.head e)) ^ 2 := by
  have h : y ⬝ᵥ (Γ.toWired.precision *ᵥ y) = ∑ x, y x * Γ.lap (ext 0 y) x := by
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro x _
    rw [Γ.precision_mulVec_eq_lap 0 y x, zero_mul, add_zero]
  rw [h]
  unfold lap
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have ht := sum_ind_mul (Γ.tail e)
    (fun x => Γ.cond e * (y x * (ext 0 y (some x) - ext 0 y (Γ.head e))))
  have hh := sum_ind_mul (Γ.head e)
    (fun x => Γ.cond e * (y x * (ext 0 y (some x) - ext 0 y (Γ.tail e))))
  have key : ∑ x, y x * (Γ.cond e * (ind (Γ.tail e) x * (ext 0 y (some x) - ext 0 y (Γ.head e)) +
      ind (Γ.head e) x * (ext 0 y (some x) - ext 0 y (Γ.tail e)))) =
      ∑ x, ind (Γ.tail e) x * (Γ.cond e * (y x * (ext 0 y (some x) - ext 0 y (Γ.head e)))) +
        ∑ x, ind (Γ.head e) x * (Γ.cond e * (y x * (ext 0 y (some x) - ext 0 y (Γ.tail e)))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [key, ht, hh]
  have htx := Γ.tail_ne_head e
  rcases hte : Γ.tail e with _ | v <;> rcases hhe : Γ.head e with _ | w
  · exact absurd (hte.trans hhe.symm) htx
  all_goals simp only [ind, ext_none, ext_some, Option.some.injEq, reduceCtorEq, if_false,
    ite_true, ite_false, ↓reduceIte]
  all_goals first | ring | (split_ifs <;> subst_vars <;> ring)

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
