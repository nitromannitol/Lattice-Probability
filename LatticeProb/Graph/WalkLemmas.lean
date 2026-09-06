/-
Elementary facts about the finite-horizon walk average `walkExp`, the walk
payoff, and bounded stopping times, used in the proof of `thm:RW`.
-/
import LatticeProb.Graph.Odometer

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The trajectory shifted by one step. -/
def shift (X : ℕ → V) : ℕ → V := fun k => X (k + 1)

@[simp] theorem cons_zero (x : V) (X : ℕ → V) : cons x X 0 = x := rfl

@[simp] theorem cons_succ (x : V) (X : ℕ → V) (k : ℕ) : cons x X (k + 1) = X k := rfl

@[simp] theorem shift_cons (x : V) (X : ℕ → V) : shift (cons x X) = X := rfl

theorem walkExp_succ (n : ℕ) (x : V) (F : (ℕ → V) → ℝ) :
    walkExp G (n + 1) x F
      = (∑ y ∈ G.neighborFinset x, walkExp G n y (fun X => F (cons x X))) / G.degree x :=
  rfl

theorem walkExp_congr {n : ℕ} {x : V} {F F' : (ℕ → V) → ℝ}
    (h : ∀ X : ℕ → V, X 0 = x → F X = F' X) :
    walkExp G n x F = walkExp G n x F' := by
  induction n generalizing x F F' with
  | zero => exact h _ rfl
  | succ n ih =>
      rw [walkExp_succ, walkExp_succ]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      exact ih fun X _ => h (cons x X) rfl

theorem walkExp_const [Infinite V] (hG : G.Connected) (n : ℕ) (x : V) (c : ℝ) :
    walkExp G n x (fun _ => c) = c := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hd : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (degree_pos hG x).ne'
      rw [walkExp_succ]
      simp only [ih]
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
      field_simp

theorem walkExp_add (n : ℕ) (x : V) (F F' : (ℕ → V) → ℝ) :
    walkExp G n x (fun X => F X + F' X) = walkExp G n x F + walkExp G n x F' := by
  induction n generalizing x F F' with
  | zero => rfl
  | succ n ih =>
      rw [walkExp_succ, walkExp_succ, walkExp_succ]
      rw [show (fun y => walkExp G n y (fun X => F (cons x X) + F' (cons x X)))
          = (fun y => walkExp G n y (fun X => F (cons x X))
              + walkExp G n y (fun X => F' (cons x X))) from funext fun y => ih y _ _]
      rw [Finset.sum_add_distrib, add_div]

theorem walkExp_mono {n : ℕ} {x : V} {F F' : (ℕ → V) → ℝ}
    (h : ∀ X : ℕ → V, F X ≤ F' X) :
    walkExp G n x F ≤ walkExp G n x F' := by
  induction n generalizing x F F' with
  | zero => exact h _
  | succ n ih =>
      rw [walkExp_succ, walkExp_succ]
      have hsum : ∑ y ∈ G.neighborFinset x, walkExp G n y (fun X => F (cons x X))
          ≤ ∑ y ∈ G.neighborFinset x, walkExp G n y (fun X => F' (cons x X)) :=
        Finset.sum_le_sum fun y _ => ih fun X => h (cons x X)
      exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _) |>.trans_eq rfl

theorem payoff_cons (ξ : V → ℝ) (m : ℕ) (x : V) (X : ℕ → V) :
    payoff G ξ (m + 1) (cons x X) = ξ x / G.degree x + payoff G ξ m X := by
  simp only [payoff, Finset.sum_range_succ']
  simp only [cons_zero, cons_succ]
  exact add_comm _ _

theorem payoff_zero (ξ : V → ℝ) (X : ℕ → V) : payoff G ξ 0 X = 0 := rfl


theorem stopping_of_zero {τ : (ℕ → V) → ℕ} (hτ : IsStopping τ) {x : V} {X : ℕ → V}
    (hX : X 0 = x) (h0 : τ (fun _ => x) = 0) : τ X = 0 :=
  hτ 0 (fun _ => x) X (fun j hj => by rw [Nat.le_zero.mp hj]; exact hX.symm) h0

theorem stopping_ne_zero {τ : (ℕ → V) → ℕ} (hτ : IsStopping τ) {x : V} {X : ℕ → V}
    (hX : X 0 = x) (h0 : τ (fun _ => x) ≠ 0) : τ X ≠ 0 := by
  intro h
  exact h0 (hτ 0 X (fun _ => x) (fun j hj => by rw [Nat.le_zero.mp hj]; exact hX) h)

theorem isStopping_shift {τ : (ℕ → V) → ℕ} (hτ : IsStopping τ) (x : V)
    (h0 : ∀ X : ℕ → V, X 0 = x → τ X ≠ 0) :
    IsStopping (fun X' => τ (cons x X') - 1) := by
  intro k X Y hXY hk
  have hX : τ (cons x X) ≠ 0 := h0 _ rfl
  have hval : τ (cons x X) = k + 1 := by simp only at hk; omega
  have hY : τ (cons x Y) = k + 1 :=
    hτ (k + 1) (cons x X) (cons x Y)
      (by
        intro j hj
        match j with
        | 0 => rfl
        | i + 1 => exact hXY i (by omega))
      hval
  simp only
  omega

theorem isStopping_prepend {τ : V → (ℕ → V) → ℕ} (hτ : ∀ y, IsStopping (τ y)) :
    IsStopping (fun X => 1 + τ (X 1) (shift X)) := by
  intro k X Y hXY hk
  simp only at hk ⊢
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h1 : X 1 = Y 1 := hXY 1 (by omega)
  have hm : τ (X 1) (shift X) = m := by omega
  have : τ (X 1) (shift Y) = m :=
    hτ (X 1) m (shift X) (shift Y) (fun j hj => hXY (j + 1) (by omega)) hm
  rw [← h1, this]
  omega

theorem walkExp_payoff_succ [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (x : V)
    {τ : (ℕ → V) → ℕ} (h0 : ∀ X : ℕ → V, X 0 = x → τ X ≠ 0) :
    walkExp G (n + 1) x (fun X => payoff G ξ (τ X) X)
      = ξ x / G.degree x
        + walkOp G (fun y => walkExp G n y
            (fun X' => payoff G ξ (τ (cons x X') - 1) X')) x := by
  rw [walkExp_succ]
  have key : ∀ y ∈ G.neighborFinset x,
      walkExp G n y (fun X' => payoff G ξ (τ (cons x X')) (cons x X'))
        = ξ x / G.degree x
          + walkExp G n y (fun X' => payoff G ξ (τ (cons x X') - 1) X') := by
    intro y _
    have hcong : walkExp G n y (fun X' => payoff G ξ (τ (cons x X')) (cons x X'))
        = walkExp G n y (fun X' =>
            ξ x / G.degree x + payoff G ξ (τ (cons x X') - 1) X') := by
      refine walkExp_congr fun X' _ => ?_
      have hne : τ (cons x X') ≠ 0 := h0 _ rfl
      obtain ⟨m, hm⟩ : ∃ m, τ (cons x X') = m + 1 := ⟨τ (cons x X') - 1, by omega⟩
      rw [hm, payoff_cons]
      simp
    rw [hcong, walkExp_add, walkExp_const hG]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, add_div, walkOp]
  have hd : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (degree_pos hG x).ne'
  congr 1
  field_simp

end LatticeProb.Graph
