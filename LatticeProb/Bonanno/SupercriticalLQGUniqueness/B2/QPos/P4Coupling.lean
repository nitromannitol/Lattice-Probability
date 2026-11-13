/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4Coupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4Gambler
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4WalkOps

 




















set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

 
abbrev Pair := (ℤ × ℤ) × (ℤ × ℤ)

 
def du (q : Pair) : ℤ := (q.1.1 + q.1.2) - (q.2.1 + q.2.2)

 
def dv (q : Pair) : ℤ := (q.1.1 - q.1.2) - (q.2.1 - q.2.2)

 
def mir (q : Pair) (s : Bool × Bool) : Bool × Bool :=
  (if du q = 0 then s.1 else !s.1, if dv q = 0 then s.2 else !s.2)

theorem mir_mir (q : Pair) (s : Bool × Bool) : mir q (mir q s) = s := by
  unfold mir
  rcases s with ⟨a, b⟩
  by_cases h1 : du q = 0 <;> by_cases h2 : dv q = 0 <;> simp [h1, h2]

theorem sum_mir (q : Pair) (g : Bool × Bool → ℝ) :
    ∑ s : Bool × Bool, g (mir q s) = ∑ s : Bool × Bool, g s := by
  let e : Bool × Bool ≃ Bool × Bool :=
    { toFun := mir q, invFun := mir q, left_inv := mir_mir q, right_inv := mir_mir q }
  exact Fintype.sum_equiv e _ _ (fun s => rfl)

 
def pairAvg (F : Pair → ℝ) (q : Pair) : ℝ :=
  (∑ s : Bool × Bool, F (q.1 + stepVec s, q.2 + stepVec (mir q s))) / 4

theorem pairAvg_fst (f : ℤ × ℤ → ℝ) (q : Pair) : pairAvg (fun p => f p.1) q = avg f q.1 := rfl

theorem pairAvg_snd (f : ℤ × ℤ → ℝ) (q : Pair) : pairAvg (fun p => f p.2) q = avg f q.2 := by
  unfold pairAvg avg
  congr 1
  exact sum_mir q (fun s => f (q.2 + stepVec s))

theorem pairAvg_mono {F G : Pair → ℝ} (h : ∀ p, F p ≤ G p) (q : Pair) :
    pairAvg F q ≤ pairAvg G q := by
  unfold pairAvg
  gcongr with s
  exact h _

theorem pairAvg_add (F G : Pair → ℝ) (q : Pair) :
    pairAvg (fun p => F p + G p) q = pairAvg F q + pairAvg G q := by
  unfold pairAvg
  rw [Finset.sum_add_distrib]
  ring

theorem pairAvg_sub (F G : Pair → ℝ) (q : Pair) :
    pairAvg (fun p => F p - G p) q = pairAvg F q - pairAvg G q := by
  unfold pairAvg
  rw [Finset.sum_sub_distrib]
  ring

theorem pairAvg_smul (r : ℝ) (F : Pair → ℝ) (q : Pair) :
    pairAvg (fun p => r * F p) q = r * pairAvg F q := by
  unfold pairAvg
  rw [← Finset.mul_sum]
  ring

theorem pairAvg_nonneg {F : Pair → ℝ} (h : ∀ p, 0 ≤ F p) (q : Pair) : 0 ≤ pairAvg F q := by
  unfold pairAvg
  have : 0 ≤ ∑ s : Bool × Bool, F (q.1 + stepVec s, q.2 + stepVec (mir q s)) :=
    Finset.sum_nonneg fun s _ => h _
  positivity

theorem du_step (q : Pair) (s : Bool × Bool) :
    du (q.1 + stepVec s, q.2 + stepVec (mir q s)) =
      du q + (if du q = 0 then 0 else 2 * sgn s.1) := by
  have key : du (q.1 + stepVec s, q.2 + stepVec (mir q s)) =
      du q + sgn s.1 - sgn (mir q s).1 := by
    have h1 := stepVec_add s
    have h2 := stepVec_add (mir q s)
    simp only [du, Prod.fst_add, Prod.snd_add]
    linarith
  rw [key]
  by_cases h : du q = 0
  · have : (mir q s).1 = s.1 := by simp [mir, h]
    rw [this, if_pos h]; ring
  · have : (mir q s).1 = !s.1 := by simp [mir, h]
    rw [this, if_neg h]
    rcases s with ⟨_ | _, _⟩ <;> simp [sgn] <;> ring

theorem dv_step (q : Pair) (s : Bool × Bool) :
    dv (q.1 + stepVec s, q.2 + stepVec (mir q s)) =
      dv q + (if dv q = 0 then 0 else 2 * sgn s.2) := by
  have key : dv (q.1 + stepVec s, q.2 + stepVec (mir q s)) =
      dv q + sgn s.2 - sgn (mir q s).2 := by
    have h1 := stepVec_sub s
    have h2 := stepVec_sub (mir q s)
    simp only [dv, Prod.fst_add, Prod.snd_add]
    linarith
  rw [key]
  by_cases h : dv q = 0
  · have : (mir q s).2 = s.2 := by simp [mir, h]
    rw [this, if_pos h]; ring
  · have : (mir q s).2 = !s.2 := by simp [mir, h]
    rw [this, if_neg h]
    rcases s with ⟨_, _ | _⟩ <;> simp [sgn] <;> ring

 
def gam2 (g : ℤ → ℝ) (m : ℤ) : ℝ := if m = 0 then g 0 else (g (m + 2) + g (m - 2)) / 2

theorem gam2_of_zero (g : ℤ → ℝ) : gam2 g 0 = g 0 := if_pos rfl

theorem gam2_of_ne (g : ℤ → ℝ) {m : ℤ} (hm : m ≠ 0) :
    gam2 g m = (g (m + 2) + g (m - 2)) / 2 := if_neg hm

theorem pairAvg_du (g : ℤ → ℝ) (q : Pair) : pairAvg (fun p => g (du p)) q = gam2 g (du q) := by
  unfold pairAvg gam2
  simp_rw [du_step]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  split_ifs with h
  · rw [h]; simp only [add_zero]; ring
  · simp [sgn]; ring_nf

theorem pairAvg_dv (g : ℤ → ℝ) (q : Pair) : pairAvg (fun p => g (dv p)) q = gam2 g (dv q) := by
  unfold pairAvg gam2
  simp_rw [dv_step]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  split_ifs with h
  · rw [h]; simp only [add_zero]; ring
  · simp [sgn]; ring_nf

theorem pairAvgIter_du (t : ℕ) (g : ℤ → ℝ) (q : Pair) :
    pairAvg^[t] (fun p => g (du p)) q = gam2^[t] g (du q) := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have : pairAvg^[t] (fun p => g (du p)) = fun p => gam2^[t] g (du p) := funext ih
    rw [this, pairAvg_du]

theorem pairAvgIter_dv (t : ℕ) (g : ℤ → ℝ) (q : Pair) :
    pairAvg^[t] (fun p => g (dv p)) q = gam2^[t] g (dv q) := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have : pairAvg^[t] (fun p => g (dv p)) = fun p => gam2^[t] g (dv p) := funext ih
    rw [this, pairAvg_dv]

theorem gam2Iter_even (t : ℕ) (g : ℤ → ℝ) (i : ℤ) :
    gam2^[t] g (2 * i) = gam^[t] (fun j => g (2 * j)) i := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases hi : i = 0
    · subst hi
      rw [show (2 : ℤ) * 0 = 0 by ring, gam2_of_zero, gam_of_zero]
      have := ih 0
      rwa [show (2 : ℤ) * 0 = 0 by ring] at this
    · rw [gam2_of_ne _ (by omega), gam_of_ne _ hi]
      rw [show 2 * i + 2 = 2 * (i + 1) by ring, show 2 * i - 2 = 2 * (i - 1) by ring, ih, ih]

theorem pairAvgIter_mono (t : ℕ) {F G : Pair → ℝ} (h : ∀ p, F p ≤ G p) (q : Pair) :
    pairAvg^[t] F q ≤ pairAvg^[t] G q := by
  induction t generalizing q with
  | zero => exact h q
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact pairAvg_mono ih q

theorem pairAvgIter_add (t : ℕ) (F G : Pair → ℝ) (q : Pair) :
    pairAvg^[t] (fun p => F p + G p) q = pairAvg^[t] F q + pairAvg^[t] G q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    have : pairAvg^[t] (fun p => F p + G p) = fun p => pairAvg^[t] F p + pairAvg^[t] G p :=
      funext ih
    rw [this, pairAvg_add]

theorem pairAvgIter_nonneg (t : ℕ) {F : Pair → ℝ} (h : ∀ p, 0 ≤ F p) (q : Pair) :
    0 ≤ pairAvg^[t] F q := by
  induction t generalizing q with
  | zero => exact h q
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact pairAvg_nonneg ih q

 

 
def inT (U : Finset (ℤ × ℤ)) (q : Pair) : Prop := q.1 ∈ U ∧ q.2 ∈ U ∧ q.1 ≠ q.2

instance (U : Finset (ℤ × ℤ)) (q : Pair) : Decidable (inT U q) := by
  unfold inT; infer_instance

 
def pairStop (U : Finset (ℤ × ℤ)) (F : Pair → ℝ) (q : Pair) : ℝ :=
  if inT U q then pairAvg F q else F q

theorem pairStop_of_in {U : Finset (ℤ × ℤ)} {F : Pair → ℝ} {q : Pair} (h : inT U q) :
    pairStop U F q = pairAvg F q := if_pos h

theorem pairStop_of_not_in {U : Finset (ℤ × ℤ)} {F : Pair → ℝ} {q : Pair} (h : ¬ inT U q) :
    pairStop U F q = F q := if_neg h

theorem pairStopIter_out (U : Finset (ℤ × ℤ)) (t : ℕ) (F : Pair → ℝ) {q : Pair}
    (h : ¬ inT U q) : (pairStop U)^[t] F q = F q := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', pairStop_of_not_in h]; exact ih

theorem pairStopIter_mono (U : Finset (ℤ × ℤ)) (t : ℕ) {F G : Pair → ℝ}
    (h : ∀ p, F p ≤ G p) (q : Pair) : (pairStop U)^[t] F q ≤ (pairStop U)^[t] G q := by
  induction t generalizing q with
  | zero => exact h q
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases hq : inT U q
    · rw [pairStop_of_in hq, pairStop_of_in hq]; exact pairAvg_mono ih q
    · rw [pairStop_of_not_in hq, pairStop_of_not_in hq]; exact ih q

theorem pairStopIter_add (U : Finset (ℤ × ℤ)) (t : ℕ) (F G : Pair → ℝ) (q : Pair) :
    (pairStop U)^[t] (fun p => F p + G p) q = (pairStop U)^[t] F q + (pairStop U)^[t] G q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    have : (pairStop U)^[t] (fun p => F p + G p) =
        fun p => (pairStop U)^[t] F p + (pairStop U)^[t] G p := funext ih
    rw [this]
    by_cases hq : inT U q
    · rw [pairStop_of_in hq, pairStop_of_in hq, pairStop_of_in hq, pairAvg_add]
    · rw [pairStop_of_not_in hq, pairStop_of_not_in hq, pairStop_of_not_in hq]

theorem pairStopIter_smul (U : Finset (ℤ × ℤ)) (t : ℕ) (r : ℝ) (F : Pair → ℝ) (q : Pair) :
    (pairStop U)^[t] (fun p => r * F p) q = r * (pairStop U)^[t] F q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have : (pairStop U)^[t] (fun p => r * F p) = fun p => r * (pairStop U)^[t] F p := funext ih
    rw [this]
    by_cases hq : inT U q
    · rw [pairStop_of_in hq, pairStop_of_in hq, pairAvg_smul]
    · rw [pairStop_of_not_in hq, pairStop_of_not_in hq]

theorem abs_pairStopIter_le (U : Finset (ℤ × ℤ)) (t : ℕ) (F : Pair → ℝ) (q : Pair) :
    |(pairStop U)^[t] F q| ≤ (pairStop U)^[t] (fun p => |F p|) q := by
  rw [abs_le]
  constructor
  · have h := pairStopIter_mono U t (F := fun p => -1 * |F p|) (G := F)
      (fun p => by rw [neg_one_mul]; exact neg_abs_le (F p)) q
    rw [pairStopIter_smul] at h
    linarith
  · exact pairStopIter_mono U t (fun p => le_abs_self (F p)) q

 

theorem pairStopIter_indT_le (U : Finset (ℤ × ℤ)) (t : ℕ) (q : Pair) :
    (pairStop U)^[t] (fun p => if inT U p then 1 else 0) q ≤
      pairAvg^[t] (fun p => if p.1 = p.2 then 0 else 1) q := by
  induction t generalizing q with
  | zero =>
    show (if inT U q then (1 : ℝ) else 0) ≤ if q.1 = q.2 then 0 else 1
    by_cases h : inT U q
    · rw [if_pos h, if_neg h.2.2]
    · rw [if_neg h]; split_ifs <;> norm_num
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    by_cases hq : inT U q
    · rw [pairStop_of_in hq]; exact pairAvg_mono ih q
    · rw [pairStop_of_not_in hq, pairStopIter_out U t _ hq]
      show (if inT U q then (1 : ℝ) else 0) ≤ _
      rw [if_neg hq]
      exact pairAvg_nonneg (fun p => pairAvgIter_nonneg t
        (fun p => by split_ifs <;> norm_num) p) q

theorem pairStopIter_indE_le (U : Finset (ℤ × ℤ)) (t : ℕ) (q : Pair) :
    (pairStop U)^[t] (fun p => if p.1 ∉ U ∨ p.2 ∉ U then 1 else 0) q ≤
      exitProb U t q.1 + exitProb U t q.2 := by
  induction t generalizing q with
  | zero =>
    show (if q.1 ∉ U ∨ q.2 ∉ U then (1 : ℝ) else 0) ≤
      (if q.1 ∈ U then 0 else 1) + (if q.2 ∈ U then 0 else 1)
    split_ifs <;> first | tauto | norm_num
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    by_cases hq : inT U q
    · rw [pairStop_of_in hq]
      obtain ⟨h1, h2, _⟩ := hq
      have hle := pairAvg_mono ih q
      rw [pairAvg_add, pairAvg_fst (fun c => exitProb U t c), pairAvg_snd (fun c => exitProb U t c)]
        at hle
      refine hle.trans (le_of_eq ?_)
      have e1 : exitProb U (t + 1) q.1 = avg (fun c => exitProb U t c) q.1 := by
        show (stopOp U)^[t + 1] _ q.1 = _
        rw [Function.iterate_succ_apply', stopOp_of_mem h1]
        rfl
      have e2 : exitProb U (t + 1) q.2 = avg (fun c => exitProb U t c) q.2 := by
        show (stopOp U)^[t + 1] _ q.2 = _
        rw [Function.iterate_succ_apply', stopOp_of_mem h2]
        rfl
      rw [e1, e2]
    · rw [pairStop_of_not_in hq, pairStopIter_out U t _ hq]
      show (if q.1 ∉ U ∨ q.2 ∉ U then (1 : ℝ) else 0) ≤ _
      unfold inT at hq
      by_cases h1 : q.1 ∈ U
      · by_cases h2 : q.2 ∈ U
        · have heq : q.1 = q.2 := by tauto
          rw [if_neg (by tauto)]
          exact add_nonneg (exitProb_nonneg U _ _) (exitProb_nonneg U _ _)
        · rw [if_pos (Or.inr h2), exitProb_out U _ h2]
          linarith [exitProb_nonneg U (t + 1) q.1]
      · rw [if_pos (Or.inl h1), exitProb_out U _ h1]
        linarith [exitProb_nonneg U (t + 1) q.2]

 




theorem harmonic_diff_le (U : Finset (ℤ × ℤ)) {H : ℤ × ℤ → ℝ}
    (hH : ∀ a ∈ U, H a = avg H a) {M : ℝ} (hM : ∀ c, |H c| ≤ M)
    {x y : ℤ × ℤ} (i j : ℤ) (hi : du (x, y) = 2 * i) (hj : dv (x, y) = 2 * j)
    (m : ℤ) (hm : 0 < m)
    (hbx : ∀ c : ℤ × ℤ, |c.1 - x.1| < m → |c.2 - x.2| < m → c ∈ U)
    (hby : ∀ c : ℤ × ℤ, |c.1 - y.1| < m → |c.2 - y.2| < m → c ∈ U)
    (A : ℕ) (hA : 1 ≤ A) :
    |H x - H y| ≤ 2 * M * (2 * |(i : ℝ)| / A + 2 * |(j : ℝ)| / A +
      2 * ((A : ℝ) ^ 2) / ((m : ℝ) ^ 2)) := by
  set Φ : Pair → ℝ := fun p => H p.1 - H p.2
  set t : ℕ := A ^ 2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x)
  
  have hfix : ∀ s, (pairStop U)^[s] Φ = Φ := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]
      funext q
      by_cases hq : inT U q
      · rw [pairStop_of_in hq]
        simp only [Φ]
        rw [pairAvg_sub, pairAvg_fst, pairAvg_snd, ← hH _ hq.1, ← hH _ hq.2.1]
      · rw [pairStop_of_not_in hq]
  
  have hΦ : ∀ p : Pair, |Φ p| ≤ 2 * M * ((if inT U p then 1 else 0) +
      (if p.1 ∉ U ∨ p.2 ∉ U then 1 else 0)) := by
    intro p
    simp only [Φ]
    by_cases heq : p.1 = p.2
    · rw [heq, sub_self, abs_zero]
      have : (0 : ℝ) ≤ (if inT U p then 1 else 0) + (if p.1 ∉ U ∨ p.2 ∉ U then 1 else 0) := by
        split_ifs <;> norm_num
      positivity
    · have hsum : (1 : ℝ) ≤ (if inT U p then 1 else 0) + (if p.1 ∉ U ∨ p.2 ∉ U then 1 else 0) := by
        by_cases h1 : p.1 ∈ U <;> by_cases h2 : p.2 ∈ U <;> simp [inT, h1, h2, heq]
      have h2 : |H p.1 - H p.2| ≤ 2 * M := by
        have := abs_sub (H p.1) (H p.2)
        linarith [hM p.1, hM p.2]
      nlinarith
  have hmain : |Φ (x, y)| ≤ 2 * M * ((pairStop U)^[t] (fun p => if inT U p then 1 else 0) (x, y) +
      (pairStop U)^[t] (fun p => if p.1 ∉ U ∨ p.2 ∉ U then 1 else 0) (x, y)) := by
    have h1 := abs_pairStopIter_le U t Φ (x, y)
    rw [hfix] at h1
    have h2 := pairStopIter_mono U t hΦ (x, y)
    rw [pairStopIter_smul, pairStopIter_add] at h2
    linarith
  
  have hcoup : (pairStop U)^[t] (fun p => if inT U p then 1 else 0) (x, y) ≤
      2 * |(i : ℝ)| / A + 2 * |(j : ℝ)| / A := by
    refine (pairStopIter_indT_le U t (x, y)).trans ?_
    have hN : ∀ p : Pair, (if p.1 = p.2 then (0 : ℝ) else 1) ≤ nz (du p) + nz (dv p) := by
      intro p
      by_cases heq : p.1 = p.2
      · rw [if_pos heq]; exact add_nonneg (nz_nonneg _) (nz_nonneg _)
      · rw [if_neg heq]
        have : du p ≠ 0 ∨ dv p ≠ 0 := by
          by_contra hc
          push_neg at hc
          apply heq
          unfold du dv at hc
          apply Prod.ext <;> omega
        rcases this with h | h
        · unfold nz; rw [if_neg h]; have := nz_nonneg (dv p); unfold nz at this; linarith
        · unfold nz; rw [if_neg h]; have := nz_nonneg (du p); unfold nz at this; linarith
    have h1 := pairAvgIter_mono t hN (x, y)
    rw [pairAvgIter_add, pairAvgIter_du, pairAvgIter_dv, hi, hj, gam2Iter_even,
      gam2Iter_even] at h1
    have hnz : (fun j : ℤ => nz (2 * j)) = nz := by
      funext k; unfold nz; congr 1; apply propext; omega
    rw [hnz] at h1
    have e1 := gamIter_nz_le A hA i
    have e2 := gamIter_nz_le A hA j
    linarith
  
  have hexit : (pairStop U)^[t] (fun p => if p.1 ∉ U ∨ p.2 ∉ U then 1 else 0) (x, y) ≤
      2 * ((A : ℝ) ^ 2) / ((m : ℝ) ^ 2) := by
    refine (pairStopIter_indE_le U t (x, y)).trans ?_
    have hm' : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have e1 := exitProb_ball_le U x m hm.le hbx t
    have e2 := exitProb_ball_le U y m hm.le hby t
    have ht : ((t : ℕ) : ℝ) = (A : ℝ) ^ 2 := by simp only [t]; push_cast; ring
    rw [ht] at e1 e2
    rw [div_eq_mul_inv]
    have hx' : exitProb U t (x, y).1 ≤ (A : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
      rw [le_div_iff₀ hm']; linarith
    have hy' : exitProb U t (x, y).2 ≤ (A : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
      rw [le_div_iff₀ hm']; linarith
    have : 2 * (A : ℝ) ^ 2 * ((m : ℝ) ^ 2)⁻¹ = (A : ℝ) ^ 2 / (m : ℝ) ^ 2 +
        (A : ℝ) ^ 2 / (m : ℝ) ^ 2 := by ring
    rw [this]
    linarith
  have : |H x - H y| = |Φ (x, y)| := rfl
  rw [this]
  calc |Φ (x, y)| ≤ 2 * M * (_ + _) := hmain
    _ ≤ 2 * M * ((2 * |(i : ℝ)| / A + 2 * |(j : ℝ)| / A) +
        2 * ((A : ℝ) ^ 2) / ((m : ℝ) ^ 2)) := by gcongr
    _ = _ := by ring

end SupercriticalLQGUniqueness.B2.QPos.P4
