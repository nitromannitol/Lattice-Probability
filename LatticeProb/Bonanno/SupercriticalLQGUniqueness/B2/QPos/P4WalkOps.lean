/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4WalkOps at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Walk2D

 




















set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

 

 
def avg (f : ℤ × ℤ → ℝ) (a : ℤ × ℤ) : ℝ :=
  (∑ s : Bool × Bool, f (a + stepVec s)) / 4

theorem avg_mono {f g : ℤ × ℤ → ℝ} (h : ∀ c, f c ≤ g c) (a : ℤ × ℤ) :
    avg f a ≤ avg g a := by
  unfold avg
  gcongr with s
  exact h _

theorem avg_nonneg {f : ℤ × ℤ → ℝ} (h : ∀ c, 0 ≤ f c) (a : ℤ × ℤ) :
    0 ≤ avg f a := by
  unfold avg
  have : 0 ≤ ∑ s : Bool × Bool, f (a + stepVec s) :=
    Finset.sum_nonneg fun s _ => h _
  positivity

theorem avg_add (f g : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    avg (fun c => f c + g c) a = avg f a + avg g a := by
  unfold avg
  rw [Finset.sum_add_distrib]
  ring

theorem avg_sub (f g : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    avg (fun c => f c - g c) a = avg f a - avg g a := by
  unfold avg
  rw [Finset.sum_sub_distrib]
  ring

theorem avg_smul (r : ℝ) (f : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    avg (fun c => r * f c) a = r * avg f a := by
  unfold avg
  rw [← Finset.mul_sum]
  ring

theorem avg_const (r : ℝ) (a : ℤ × ℤ) : avg (fun _ => r) a = r := by
  unfold avg
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    nsmul_eq_mul]
  norm_num

theorem avg_eq (f : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    avg f a = (f (a.1 + 1, a.2) + f (a.1, a.2 + 1) + f (a.1, a.2 - 1) +
      f (a.1 - 1, a.2)) / 4 := by
  rcases a with ⟨a1, a2⟩
  unfold avg
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, stepVec, Prod.mk_add_mk, add_zero, sub_eq_add_neg]
  ring_nf

 
theorem avg_sqdist (x a : ℤ × ℤ) :
    avg (fun c => (((c.1 - x.1 : ℤ) : ℝ)) ^ 2 + (((c.2 - x.2 : ℤ) : ℝ)) ^ 2) a =
      (((a.1 - x.1 : ℤ) : ℝ)) ^ 2 + (((a.2 - x.2 : ℤ) : ℝ)) ^ 2 + 1 := by
  rw [avg_eq]
  push_cast
  ring

 
theorem avg_fst_sq (x : ℤ) (a : ℤ × ℤ) :
    avg (fun c => (((c.1 - x : ℤ) : ℝ)) ^ 2) a = (((a.1 - x : ℤ) : ℝ)) ^ 2 + 1 / 2 := by
  rw [avg_eq]
  push_cast
  ring

 

 
def stopOp (U : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℝ) (a : ℤ × ℤ) : ℝ :=
  if a ∈ U then avg f a else f a

theorem stopOp_of_mem {U : Finset (ℤ × ℤ)} {f : ℤ × ℤ → ℝ} {a : ℤ × ℤ} (ha : a ∈ U) :
    stopOp U f a = avg f a := if_pos ha

theorem stopOp_of_not_mem {U : Finset (ℤ × ℤ)} {f : ℤ × ℤ → ℝ} {a : ℤ × ℤ} (ha : a ∉ U) :
    stopOp U f a = f a := if_neg ha

theorem stopIter_out (U : Finset (ℤ × ℤ)) (t : ℕ) (f : ℤ × ℤ → ℝ) {a : ℤ × ℤ}
    (ha : a ∉ U) : (stopOp U)^[t] f a = f a := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', stopOp_of_not_mem ha]
    exact ih

theorem stopIter_mono (U : Finset (ℤ × ℤ)) (t : ℕ) {f g : ℤ × ℤ → ℝ}
    (h : ∀ c, f c ≤ g c) (a : ℤ × ℤ) : (stopOp U)^[t] f a ≤ (stopOp U)^[t] g a := by
  induction t generalizing a with
  | zero => exact h a
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · rw [stopOp_of_mem ha, stopOp_of_mem ha]
      exact avg_mono ih a
    · rw [stopOp_of_not_mem ha, stopOp_of_not_mem ha]
      exact ih a

theorem stopIter_add (U : Finset (ℤ × ℤ)) (t : ℕ) (f g : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    (stopOp U)^[t] (fun c => f c + g c) a = (stopOp U)^[t] f a + (stopOp U)^[t] g a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · rw [stopOp_of_mem ha, stopOp_of_mem ha, stopOp_of_mem ha, ← avg_add]
      congr 1
      funext c
      exact ih c
    · rw [stopOp_of_not_mem ha, stopOp_of_not_mem ha, stopOp_of_not_mem ha]
      exact ih a

theorem stopIter_smul (U : Finset (ℤ × ℤ)) (t : ℕ) (r : ℝ) (f : ℤ × ℤ → ℝ)
    (a : ℤ × ℤ) : (stopOp U)^[t] (fun c => r * f c) a = r * (stopOp U)^[t] f a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · rw [stopOp_of_mem ha, stopOp_of_mem ha, ← avg_smul]
      congr 1
      funext c
      exact ih c
    · rw [stopOp_of_not_mem ha, stopOp_of_not_mem ha]
      exact ih a

theorem stopIter_const (U : Finset (ℤ × ℤ)) (t : ℕ) (r : ℝ) (a : ℤ × ℤ) :
    (stopOp U)^[t] (fun _ => r) a = r := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · have : (stopOp U)^[t] (fun _ => r) = fun _ => r := funext ih
      rw [stopOp_of_mem ha, this, avg_const]
    · rw [stopOp_of_not_mem ha]
      exact ih a

theorem stopIter_nonneg (U : Finset (ℤ × ℤ)) (t : ℕ) {f : ℤ × ℤ → ℝ}
    (h : ∀ c, 0 ≤ f c) (a : ℤ × ℤ) : 0 ≤ (stopOp U)^[t] f a := by
  have := stopIter_mono U t h a
  rwa [stopIter_const] at this

theorem abs_stopIter_le (U : Finset (ℤ × ℤ)) (t : ℕ) (f : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    |(stopOp U)^[t] f a| ≤ (stopOp U)^[t] (fun c => |f c|) a := by
  rw [abs_le]
  constructor
  · have h := stopIter_mono U t (f := fun c => -1 * |f c|) (g := f)
      (fun c => by rw [neg_one_mul]; exact neg_abs_le (f c)) a
    rw [stopIter_smul] at h
    linarith
  · exact stopIter_mono U t (fun c => le_abs_self (f c)) a

 
theorem stopIter_harmonic (U : Finset (ℤ × ℤ)) (t : ℕ) {f : ℤ × ℤ → ℝ}
    (hf : ∀ a ∈ U, f a = avg f a) : (stopOp U)^[t] f = f := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih]
    funext a
    by_cases ha : a ∈ U
    · rw [stopOp_of_mem ha]
      exact (hf a ha).symm
    · rw [stopOp_of_not_mem ha]

 
def exitProb (U : Finset (ℤ × ℤ)) (t : ℕ) (a : ℤ × ℤ) : ℝ :=
  (stopOp U)^[t] (fun c => if c ∈ U then 0 else 1) a

 
def stayProb (U : Finset (ℤ × ℤ)) (t : ℕ) (a : ℤ × ℤ) : ℝ :=
  (stopOp U)^[t] (fun c => if c ∈ U then 1 else 0) a

theorem exitProb_add_stayProb (U : Finset (ℤ × ℤ)) (t : ℕ) (a : ℤ × ℤ) :
    exitProb U t a + stayProb U t a = 1 := by
  unfold exitProb stayProb
  rw [← stopIter_add]
  have : (fun c : ℤ × ℤ => (if c ∈ U then (0 : ℝ) else 1) + (if c ∈ U then 1 else 0)) =
      fun _ => 1 := by
    funext c
    split_ifs <;> norm_num
  rw [this, stopIter_const]

theorem exitProb_nonneg (U : Finset (ℤ × ℤ)) (t : ℕ) (a : ℤ × ℤ) : 0 ≤ exitProb U t a :=
  stopIter_nonneg U t (fun c => by split_ifs <;> norm_num) a

theorem stayProb_nonneg (U : Finset (ℤ × ℤ)) (t : ℕ) (a : ℤ × ℤ) : 0 ≤ stayProb U t a :=
  stopIter_nonneg U t (fun c => by split_ifs <;> norm_num) a

theorem exitProb_out (U : Finset (ℤ × ℤ)) (t : ℕ) {a : ℤ × ℤ} (ha : a ∉ U) :
    exitProb U t a = 1 := by
  unfold exitProb
  rw [stopIter_out U t _ ha, if_neg ha]

 

theorem exitProb_ball_le (U : Finset (ℤ × ℤ)) (x : ℤ × ℤ) (m : ℤ) (hm0 : 0 ≤ m)
    (hball : ∀ c : ℤ × ℤ, |c.1 - x.1| < m → |c.2 - x.2| < m → c ∈ U) (t : ℕ) :
    ((m : ℝ)) ^ 2 * exitProb U t x ≤ t := by
  set g : ℤ × ℤ → ℝ := fun c => (((c.1 - x.1 : ℤ) : ℝ)) ^ 2 + (((c.2 - x.2 : ℤ) : ℝ)) ^ 2
  have key : ∀ (t : ℕ) (a : ℤ × ℤ),
      ((m : ℝ)) ^ 2 * (stopOp U)^[t] (fun c => if c ∈ U then 0 else 1) a ≤ g a + t := by
    intro t
    induction t with
    | zero =>
      intro a
      simp only [Function.iterate_zero, id, Nat.cast_zero, add_zero]
      split_ifs with ha
      · simp only [mul_zero]
        positivity
      · simp only [mul_one]
        have hm : m ≤ |a.1 - x.1| ∨ m ≤ |a.2 - x.2| := by
          by_contra hc
          push_neg at hc
          exact ha (hball a hc.1 hc.2)
        rcases hm with hm | hm
        · have h1 : ((m : ℝ)) ^ 2 ≤ (((a.1 - x.1 : ℤ) : ℝ)) ^ 2 := by
            have : ((m : ℝ)) ≤ |((a.1 - x.1 : ℤ) : ℝ)| := by exact_mod_cast hm
            nlinarith [abs_nonneg ((a.1 - x.1 : ℤ) : ℝ), sq_abs ((a.1 - x.1 : ℤ) : ℝ),
              (show (0 : ℝ) ≤ m by exact_mod_cast hm0)]
          have : (0 : ℝ) ≤ (((a.2 - x.2 : ℤ) : ℝ)) ^ 2 := sq_nonneg _
          simp only [g]
          linarith
        · have h1 : ((m : ℝ)) ^ 2 ≤ (((a.2 - x.2 : ℤ) : ℝ)) ^ 2 := by
            have : ((m : ℝ)) ≤ |((a.2 - x.2 : ℤ) : ℝ)| := by exact_mod_cast hm
            nlinarith [abs_nonneg ((a.2 - x.2 : ℤ) : ℝ), sq_abs ((a.2 - x.2 : ℤ) : ℝ),
              (show (0 : ℝ) ≤ m by exact_mod_cast hm0)]
          have : (0 : ℝ) ≤ (((a.1 - x.1 : ℤ) : ℝ)) ^ 2 := sq_nonneg _
          simp only [g]
          linarith
    | succ t ih =>
      intro a
      rw [Function.iterate_succ_apply']
      by_cases ha : a ∈ U
      · rw [stopOp_of_mem ha]
        have h1 : avg ((stopOp U)^[t] fun c => if c ∈ U then (0 : ℝ) else 1) a * (m : ℝ) ^ 2 ≤
            avg (fun c => g c + t) a := by
          rw [mul_comm, ← avg_smul]
          exact avg_mono ih a
        rw [avg_add, avg_const] at h1
        have h2 : avg g a = g a + 1 := avg_sqdist x a
        push_cast
        nlinarith
      · rw [stopOp_of_not_mem ha, stopIter_out U t _ ha, if_neg ha]
        have h0 := ih a
        rw [stopIter_out U t _ ha, if_neg ha] at h0
        push_cast
        linarith
  have := key t x
  simp only [g, sub_self, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, zero_add] at this
  exact this

 

 
def killOp (U : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℝ) (a : ℤ × ℤ) : ℝ :=
  if a ∈ U then avg (fun c => if c ∈ U then f c else 0) a else 0

theorem killOp_of_mem {U : Finset (ℤ × ℤ)} {f : ℤ × ℤ → ℝ} {a : ℤ × ℤ} (ha : a ∈ U) :
    killOp U f a = avg (fun c => if c ∈ U then f c else 0) a := if_pos ha

theorem killOp_of_not_mem {U : Finset (ℤ × ℤ)} {f : ℤ × ℤ → ℝ} {a : ℤ × ℤ} (ha : a ∉ U) :
    killOp U f a = 0 := if_neg ha

 
def ind (U : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : ℝ := if c ∈ U then 1 else 0

 
def alive (U : Finset (ℤ × ℤ)) (t : ℕ) (a : ℤ × ℤ) : ℝ := (killOp U)^[t] (ind U) a

theorem killIter_mono (U : Finset (ℤ × ℤ)) (t : ℕ) {f g : ℤ × ℤ → ℝ}
    (h : ∀ c, f c ≤ g c) (a : ℤ × ℤ) : (killOp U)^[t] f a ≤ (killOp U)^[t] g a := by
  induction t generalizing a with
  | zero => exact h a
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · rw [killOp_of_mem ha, killOp_of_mem ha]
      apply avg_mono
      intro c
      split_ifs
      · exact ih c
      · exact le_rfl
    · rw [killOp_of_not_mem ha, killOp_of_not_mem ha]

theorem killIter_add (U : Finset (ℤ × ℤ)) (t : ℕ) (f g : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    (killOp U)^[t] (fun c => f c + g c) a = (killOp U)^[t] f a + (killOp U)^[t] g a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · rw [killOp_of_mem ha, killOp_of_mem ha, killOp_of_mem ha, ← avg_add]
      congr 1
      funext c
      split_ifs
      · exact ih c
      · ring
    · rw [killOp_of_not_mem ha, killOp_of_not_mem ha, killOp_of_not_mem ha]
      ring

theorem killIter_smul (U : Finset (ℤ × ℤ)) (t : ℕ) (r : ℝ) (f : ℤ × ℤ → ℝ)
    (a : ℤ × ℤ) : (killOp U)^[t] (fun c => r * f c) a = r * (killOp U)^[t] f a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · rw [killOp_of_mem ha, killOp_of_mem ha, ← avg_smul]
      congr 1
      funext c
      split_ifs
      · exact ih c
      · ring
    · rw [killOp_of_not_mem ha, killOp_of_not_mem ha]
      ring

theorem killIter_sub (U : Finset (ℤ × ℤ)) (t : ℕ) (f g : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    (killOp U)^[t] (fun c => f c - g c) a = (killOp U)^[t] f a - (killOp U)^[t] g a := by
  have h := killIter_add U t f (fun c => -1 * g c) a
  rw [killIter_smul] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  rw [h]

theorem killIter_nonneg (U : Finset (ℤ × ℤ)) (t : ℕ) {f : ℤ × ℤ → ℝ}
    (h : ∀ c, 0 ≤ f c) (a : ℤ × ℤ) : 0 ≤ (killOp U)^[t] f a := by
  induction t generalizing a with
  | zero => exact h a
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · rw [killOp_of_mem ha]
      apply avg_nonneg
      intro c
      split_ifs
      · exact ih c
      · exact le_rfl
    · rw [killOp_of_not_mem ha]

theorem killIter_out (U : Finset (ℤ × ℤ)) (t : ℕ) (f : ℤ × ℤ → ℝ) {a : ℤ × ℤ}
    (ha : a ∉ U) (ht : 0 < t) : (killOp U)^[t] f a = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  rw [Function.iterate_succ_apply']
  simp [killOp, ha]

theorem killIter_succ (U : Finset (ℤ × ℤ)) (t : ℕ) (f : ℤ × ℤ → ℝ) (a : ℤ × ℤ) :
    (killOp U)^[t + 1] f a = (killOp U)^[t] (killOp U f) a := by
  rw [Function.iterate_succ_apply]

theorem alive_nonneg (U : Finset (ℤ × ℤ)) (t : ℕ) (a : ℤ × ℤ) : 0 ≤ alive U t a :=
  killIter_nonneg U t (fun c => by unfold ind; split_ifs <;> norm_num) a

theorem killOp_ind_le (U : Finset (ℤ × ℤ)) (a : ℤ × ℤ) : killOp U (ind U) a ≤ ind U a := by
  by_cases ha : a ∈ U
  · rw [killOp_of_mem ha]
    have h1 : avg (fun c => if c ∈ U then ind U c else 0) a ≤ avg (fun _ => (1 : ℝ)) a :=
      avg_mono (fun c => by unfold ind; split_ifs <;> norm_num) a
    rw [avg_const] at h1
    unfold ind
    rw [if_pos ha]
    exact h1
  · rw [killOp_of_not_mem ha]
    unfold ind
    rw [if_neg ha]

 
theorem alive_succ_le (U : Finset (ℤ × ℤ)) (t : ℕ) (a : ℤ × ℤ) :
    alive U (t + 1) a ≤ alive U t a := by
  unfold alive
  rw [killIter_succ]
  exact killIter_mono U t (killOp_ind_le U) a

theorem alive_anti (U : Finset (ℤ × ℤ)) {s t : ℕ} (hst : s ≤ t) (a : ℤ × ℤ) :
    alive U t a ≤ alive U s a := by
  induction t with
  | zero =>
    have : s = 0 := by omega
    subst this; exact le_rfl
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with h | h
    · exact (alive_succ_le U t a).trans (ih (by omega))
    · have : s = t + 1 := by omega
      subst this; exact le_rfl

theorem killIter_le_alive (U : Finset (ℤ × ℤ)) (t : ℕ) {f : ℤ × ℤ → ℝ} {M : ℝ}
    (hf : ∀ c, f c ≤ M * ind U c) (a : ℤ × ℤ) :
    (killOp U)^[t] f a ≤ M * alive U t a := by
  have := killIter_mono U t hf a
  rwa [killIter_smul] at this

 

theorem sum_alive_le (U : Finset (ℤ × ℤ)) (z1 R : ℤ)
    (hU : ∀ c ∈ U, |c.1 - z1| < R) (t : ℕ) (a : ℤ × ℤ) :
    ∑ s ∈ range t, alive U s a ≤ 2 * (R : ℝ) ^ 2 := by
  set g : ℤ × ℤ → ℝ := fun c =>
    if c ∈ U then (R : ℝ) ^ 2 - (((c.1 - z1 : ℤ) : ℝ)) ^ 2 else 0 with hg
  have hg0 : ∀ c, 0 ≤ g c := by
    intro c
    simp only [hg]
    split_ifs with hc
    · have h := hU c hc
      have h1 : |((c.1 - z1 : ℤ) : ℝ)| < R := by exact_mod_cast h
      have h2 : (0 : ℝ) ≤ |((c.1 - z1 : ℤ) : ℝ)| := abs_nonneg _
      nlinarith [sq_abs ((c.1 - z1 : ℤ) : ℝ)]
    · exact le_rfl
  have hgR : ∀ c, g c ≤ (R : ℝ) ^ 2 := by
    intro c
    simp only [hg]
    split_ifs
    · nlinarith [sq_nonneg (((c.1 - z1 : ℤ) : ℝ))]
    · positivity
  
  have hdrift : ∀ c, ind U c ≤ 2 * (g c - killOp U g c) := by
    intro c
    unfold ind killOp
    split_ifs with hc
    · 
      have hnb : ∀ s : Bool × Bool,
          (if c + stepVec s ∈ U then g (c + stepVec s) else 0) ≤
            (R : ℝ) ^ 2 - (((((c + stepVec s).1 - z1 : ℤ) : ℝ))) ^ 2 := by
        intro s
        have hcR := hU c hc
        have hs : |(stepVec s).1| ≤ 1 := by
          rcases s with ⟨_ | _, _ | _⟩ <;> simp [stepVec]
        have hle : |(c + stepVec s).1 - z1| ≤ R := by
          simp only [Prod.fst_add]
          have : |c.1 + (stepVec s).1 - z1| ≤ |c.1 - z1| + |(stepVec s).1| := by
            have := abs_add_le (c.1 - z1) (stepVec s).1
            rwa [show c.1 - z1 + (stepVec s).1 = c.1 + (stepVec s).1 - z1 by ring] at this
          omega
        have hle' : |(((c + stepVec s).1 - z1 : ℤ) : ℝ)| ≤ R := by exact_mod_cast hle
        split_ifs with hcs
        · simp only [hg, if_pos hcs]; exact le_rfl
        · nlinarith [sq_abs (((c + stepVec s).1 - z1 : ℤ) : ℝ),
            abs_nonneg (((c + stepVec s).1 - z1 : ℤ) : ℝ)]
      have h1 : avg (fun c' => if c' ∈ U then g c' else 0) c ≤
          avg (fun c' => (R : ℝ) ^ 2 - (((c'.1 - z1 : ℤ) : ℝ)) ^ 2) c := by
        unfold avg
        gcongr with s
        exact hnb s
      rw [avg_sub, avg_const, avg_fst_sq] at h1
      have hgc : g c = (R : ℝ) ^ 2 - (((c.1 - z1 : ℤ) : ℝ)) ^ 2 := by simp [hg, hc]
      rw [hgc]
      linarith
    · simp only [hg, if_neg hc]
      norm_num
  
  have key : ∀ t : ℕ, ∀ a : ℤ × ℤ,
      ∑ s ∈ range t, alive U s a ≤ 2 * (g a - (killOp U)^[t] g a) := by
    intro t
    induction t with
    | zero => intro a; simp
    | succ t ih =>
      intro a
      rw [sum_range_succ]
      have h1 := ih a
      have h2 : alive U t a ≤ 2 * ((killOp U)^[t] g a - (killOp U)^[t] (killOp U g) a) := by
        unfold alive
        have := killIter_mono U t hdrift a
        rw [killIter_smul, killIter_sub] at this
        exact this
      rw [← killIter_succ] at h2
      linarith
  have h := key t a
  have h0 : 0 ≤ (killOp U)^[t] g a := killIter_nonneg U t hg0 a
  have := hgR a
  linarith

 
theorem alive_mul_le (U : Finset (ℤ × ℤ)) (z1 R : ℤ)
    (hU : ∀ c ∈ U, |c.1 - z1| < R) (t : ℕ) (a : ℤ × ℤ) :
    (t : ℝ) * alive U t a ≤ 2 * (R : ℝ) ^ 2 := by
  have h := sum_alive_le U z1 R hU t a
  have : ∑ s ∈ range t, alive U t a ≤ ∑ s ∈ range t, alive U s a :=
    Finset.sum_le_sum fun s hs => alive_anti U (mem_range.mp hs).le a
  simp only [sum_const, card_range, nsmul_eq_mul] at this
  linarith

 
theorem stayProb_eq_alive (U : Finset (ℤ × ℤ)) (t : ℕ) (a : ℤ × ℤ) :
    stayProb U t a = alive U t a := by
  unfold stayProb alive
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases ha : a ∈ U
    · rw [stopOp_of_mem ha, killOp_of_mem ha]
      unfold avg
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : a + stepVec s ∈ U
      · dsimp only
        rw [if_pos hs]
        exact ih _
      · dsimp only
        rw [if_neg hs, stopIter_out U t _ hs, if_neg hs]
    · rw [stopOp_of_not_mem ha, killOp_of_not_mem ha, stopIter_out U t _ ha, if_neg ha]

 

theorem abs_le_of_harmonic (U : Finset (ℤ × ℤ)) (z1 R : ℤ)
    (hU : ∀ c ∈ U, |c.1 - z1| < R) {H : ℤ × ℤ → ℝ}
    (hH : ∀ a ∈ U, H a = avg H a) {M : ℝ} (hM : ∀ c, c ∉ U → |H c| ≤ M) :
    ∀ c, |H c| ≤ M := by
  classical
  by_cases hUe : U.Nonempty
  swap
  · intro c
    have : c ∉ U := by
      rw [Finset.not_nonempty_iff_eq_empty] at hUe
      simp [hUe]
    exact hM c this
  obtain ⟨a₀, ha₀, hmax⟩ := Finset.exists_max_image U (fun c => |H c|) hUe
  have hR0 : 0 ≤ R := by
    have := hU a₀ ha₀
    have := abs_nonneg (a₀.1 - z1)
    omega
  
  set T : ℕ := 4 * (R.toNat) ^ 2 + 1 with hT
  have hRT : (2 * (R : ℝ) ^ 2) ≤ (T : ℝ) / 2 := by
    have : ((R.toNat : ℕ) : ℝ) = (R : ℝ) := by
      have h := Int.toNat_of_nonneg hR0
      exact_mod_cast h
    rw [hT]
    push_cast
    rw [this]
    nlinarith [sq_nonneg (R : ℝ)]
  have hTpos : (0 : ℝ) < T := by rw [hT]; positivity
  have halive : alive U T a₀ ≤ 1 / 2 := by
    have h := alive_mul_le U z1 R hU T a₀
    have : (T : ℝ) * alive U T a₀ ≤ (T : ℝ) / 2 := h.trans hRT
    by_contra hc
    push_neg at hc
    nlinarith
  set M' : ℝ := |H a₀|
  have hfix : (stopOp U)^[T] H = H := stopIter_harmonic U T hH
  have h1 : |H a₀| ≤ (stopOp U)^[T] (fun c => |H c|) a₀ := by
    have := abs_stopIter_le U T H a₀
    rwa [hfix] at this
  have h2 : ∀ c, |H c| ≤ M * (if c ∈ U then 0 else 1) + M' * (if c ∈ U then 1 else 0) := by
    intro c
    split_ifs with hc
    · simp only [mul_zero, mul_one, zero_add]; exact hmax c hc
    · simp only [mul_one, mul_zero, add_zero]; exact hM c hc
  have h3 := stopIter_mono U T h2 a₀
  rw [stopIter_add, stopIter_smul, stopIter_smul] at h3
  have he := exitProb_add_stayProb U T a₀
  unfold exitProb stayProb at he
  have hs : (stopOp U)^[T] (fun c => if c ∈ U then (1 : ℝ) else 0) a₀ ≤ 1 / 2 := by
    have := stayProb_eq_alive U T a₀
    unfold stayProb at this
    rw [this]
    exact halive
  have hs0 : 0 ≤ (stopOp U)^[T] (fun c => if c ∈ U then (1 : ℝ) else 0) a₀ :=
    stayProb_nonneg U T a₀
  set e := (stopOp U)^[T] (fun c => if c ∈ U then (0 : ℝ) else 1) a₀
  set q := (stopOp U)^[T] (fun c => if c ∈ U then (1 : ℝ) else 0) a₀
  have hM'le : M' ≤ M := by
    by_contra hc
    push_neg at hc
    have he' : e = 1 - q := by linarith
    have : M' ≤ M * e + M' * q := h1.trans h3
    rw [he'] at this
    nlinarith
  intro c
  by_cases hc : c ∈ U
  · exact (hmax c hc).trans hM'le
  · exact hM c hc

end SupercriticalLQGUniqueness.B2.QPos.P4
