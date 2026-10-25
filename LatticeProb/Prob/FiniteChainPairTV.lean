module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Pairwise total variation of a finite Markov chain

For a kernel `P` on a finite set `V`, `kpow P t` is the `t`-step transition
kernel, and `pairTV P t x y` is the total variation distance between the
`t`-step laws started from `x` and from `y`.

The main result is submultiplicativity in the time parameter: if every pair of
starting points has `t`-step distance at most `b`, and every pair has
`s`-step distance at most `a`, then every pair has `(s + t)`-step distance at
most `a * b`.
-/

namespace LatticeProb.FiniteChain

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `t`-step transition probabilities of a kernel `P` on a finite set, by the same recursion as a matrix power. -/
noncomputable def kpow (P : V → V → ℝ) : ℕ → V → V → ℝ
  | 0, x, y => if x = y then 1 else 0
  | t + 1, x, y => ∑ z, kpow P t x z * P z y

/-- Total variation between the `t`-step laws from `x` and from `y`. -/
noncomputable def pairTV (P : V → V → ℝ) (t : ℕ) (x y : V) : ℝ :=
  (1 / 2) * ∑ z, |kpow P t x z - kpow P t y z|

/-- The `(s + t)`-step kernel is the composition of the `s`-step and `t`-step kernels. -/
theorem kpow_add (P : V → V → ℝ) (s t : ℕ) (x y : V) :
    kpow P (s + t) x y = ∑ z, kpow P s x z * kpow P t z y := by
  induction t generalizing x y with
  | zero => simp [kpow]
  | succ t ih =>
    show kpow P ((s + t) + 1) x y = _
    simp only [kpow, ih, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring

/-- Transition probabilities of every number of steps are nonnegative when `P` is. -/
theorem kpow_nonneg (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (t : ℕ) (x y : V) :
    0 ≤ kpow P t x y := by
  induction t generalizing x y with
  | zero => simp only [kpow]; split_ifs <;> norm_num
  | succ t ih =>
    simp only [kpow]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP z y)

/-- The `t`-step law from `x` has total mass one when every row of `P` does. -/
theorem sum_kpow (P : V → V → ℝ) (hrow : ∀ x, ∑ y, P x y = 1) (t : ℕ) (x : V) :
    ∑ y, kpow P t x y = 1 := by
  induction t generalizing x with
  | zero => simp [kpow]
  | succ t ih =>
    simp only [kpow]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hrow, mul_one, ih]

/-- Splitting a real number into its positive and negative parts. -/
theorem max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring

/-- The absolute value is the sum of the positive and negative parts. -/
theorem abs_eq_max_add_max_neg (a : ℝ) : |a| = max a 0 + max (-a) 0 := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring

omit [DecidableEq V] in
/-- Bound on a signed combination of the rows of a kernel. If `f = p - q` with
`p` and `q` nonnegative of common mass `c`, and any two rows are within `2 * b`
in `ℓ¹`, then `∑ w, |∑ z, f z * K z w| ≤ 2 * c * b`. -/
theorem l1_signed_comb_le (K : V → V → ℝ) (f p q : V → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hq : ∀ z, 0 ≤ q z) (hf : ∀ z, f z = p z - q z) {c b : ℝ} (hpc : ∑ z, p z = c)
    (hqc : ∑ z, q z = c) (hK : ∀ z z', ∑ w, |K z w - K z' w| ≤ 2 * b) :
    ∑ w, |∑ z, f z * K z w| ≤ 2 * c * b := by
  simp only [hf]
  have hc0 : 0 ≤ c := hpc ▸ Finset.sum_nonneg fun z _ => hp z
  have h1 : ∀ w, ∑ z, ∑ z', p z * q z' * K z w = (∑ z, p z * K z w) * c := by
    intro w
    rw [← hqc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z' _ => by ring
  have h2 : ∀ w, ∑ z, ∑ z', p z * q z' * K z' w = c * ∑ z', q z' * K z' w := by
    intro w
    rw [Finset.sum_comm, ← hpc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z' _ => by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun z _ => by ring
  have hD : ∀ w, c * ∑ z, (p z - q z) * K z w
      = ∑ z, ∑ z', p z * q z' * (K z w - K z' w) := by
    intro w
    have hsplit : ∑ z, ∑ z', p z * q z' * (K z w - K z' w)
        = ∑ z, ∑ z', p z * q z' * K z w - ∑ z, ∑ z', p z * q z' * K z' w := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z' _ => by ring
    rw [hsplit, h1 w, h2 w]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hbound : ∀ w, c * |∑ z, (p z - q z) * K z w|
      ≤ ∑ z, ∑ z', p z * q z' * |K z w - K z' w| := by
    intro w
    rw [← abs_of_nonneg hc0, ← abs_mul, hD w]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (le_of_eq (Finset.sum_congr rfl fun z' _ => ?_))
    rw [abs_mul, abs_of_nonneg (mul_nonneg (hp z) (hq z'))]
  have hsum : ∑ w, ∑ z, ∑ z', p z * q z' * |K z w - K z' w|
      = ∑ z, ∑ z', p z * q z' * ∑ w, |K z w - K z' w| := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [Finset.mul_sum]
  have hb2 : ∑ z, ∑ z', p z * q z' * ∑ w, |K z w - K z' w|
      ≤ ∑ z, ∑ z', p z * q z' * (2 * b) :=
    Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun z' _ =>
      mul_le_mul_of_nonneg_left (hK z z') (mul_nonneg (hp z) (hq z'))
  have hpq : ∑ z, ∑ z', p z * q z' = c * c := by
    have : ∑ z, ∑ z', p z * q z' = (∑ z, p z) * ∑ z', q z' := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]
    rw [this, hpc, hqc]
  have hc2 : ∑ z, ∑ z', p z * q z' * (2 * b) = c * c * (2 * b) := by
    rw [← hpq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by rw [Finset.sum_mul]
  have hS : c * ∑ w, |∑ z, (p z - q z) * K z w| ≤ c * c * (2 * b) := by
    rw [Finset.mul_sum]
    calc ∑ w, c * |∑ z, (p z - q z) * K z w|
        ≤ ∑ w, ∑ z, ∑ z', p z * q z' * |K z w - K z' w| :=
          Finset.sum_le_sum fun w _ => hbound w
      _ = ∑ z, ∑ z', p z * q z' * ∑ w, |K z w - K z' w| := hsum
      _ ≤ ∑ z, ∑ z', p z * q z' * (2 * b) := hb2
      _ = c * c * (2 * b) := hc2
  rcases hc0.eq_or_lt with h | h
  · subst h
    have hp0 : ∀ z, p z = 0 := fun z =>
      (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hp z).1 hpc z (Finset.mem_univ z)
    have hq0 : ∀ z, q z = 0 := fun z =>
      (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hq z).1 hqc z (Finset.mem_univ z)
    simp [hp0, hq0]
  · have h' : c * ∑ w, |∑ z, (p z - q z) * K z w| ≤ c * (2 * c * b) := by
      calc _ ≤ c * c * (2 * b) := hS
        _ = c * (2 * c * b) := by ring
    exact le_of_mul_le_mul_left h' h

/-- The total variation between two `t`-step laws is at most one. -/
theorem pairTV_le_one (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (t : ℕ) (x y : V) : pairTV P t x y ≤ 1 := by
  unfold pairTV
  have h : ∑ z, |kpow P t x z - kpow P t y z| ≤ ∑ z, (kpow P t x z + kpow P t y z) :=
    Finset.sum_le_sum fun z _ => abs_sub_le_iff.2
      ⟨by linarith [kpow_nonneg P hP t y z], by linarith [kpow_nonneg P hP t x z]⟩
  rw [Finset.sum_add_distrib, sum_kpow P hrow t x, sum_kpow P hrow t y] at h
  linarith

/-- Submultiplicativity of the pairwise total variation: if the `s`-step distances are at
most `a` and the `t`-step distances are at most `b`, then the `(s + t)`-step distances are
at most `a * b`. -/
theorem pairTV_add_le (P : V → V → ℝ) (_hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {s t : ℕ} {a b : ℝ}
    (hs : ∀ x y, pairTV P s x y ≤ a) (ht : ∀ x y, pairTV P t x y ≤ b) (x y : V) :
    pairTV P (s + t) x y ≤ a * b := by
  have hb0 : 0 ≤ b := le_trans (by unfold pairTV; positivity) (ht x x)
  have hsum0 : ∑ z, (kpow P s x z - kpow P s y z) = 0 := by
    rw [Finset.sum_sub_distrib, sum_kpow P hrow s x, sum_kpow P hrow s y, sub_self]
  have hpq : ∑ z, max (kpow P s x z - kpow P s y z) 0
      = ∑ z, max (-(kpow P s x z - kpow P s y z)) 0 := by
    have h1 : ∑ z, (max (kpow P s x z - kpow P s y z) 0
        - max (-(kpow P s x z - kpow P s y z)) 0) = 0 := by
      simp only [max_sub_max_neg]; exact hsum0
    rw [Finset.sum_sub_distrib] at h1
    linarith
  have hpc : ∑ z, max (kpow P s x z - kpow P s y z) 0 = pairTV P s x y := by
    have h1 : ∑ z, |kpow P s x z - kpow P s y z|
        = ∑ z, (max (kpow P s x z - kpow P s y z) 0
          + max (-(kpow P s x z - kpow P s y z)) 0) :=
      Finset.sum_congr rfl fun z _ => abs_eq_max_add_max_neg _
    rw [Finset.sum_add_distrib] at h1
    unfold pairTV
    linarith
  have hK : ∀ z z', ∑ w, |kpow P t z w - kpow P t z' w| ≤ 2 * b := by
    intro z z'
    have := ht z z'
    unfold pairTV at this
    linarith
  have hD : ∀ w, kpow P (s + t) x w - kpow P (s + t) y w
      = ∑ z, (kpow P s x z - kpow P s y z) * kpow P t z w := by
    intro w
    simp only [kpow_add, sub_mul, Finset.sum_sub_distrib]
  have hfin : ∑ w, |∑ z, (kpow P s x z - kpow P s y z) * kpow P t z w|
      ≤ 2 * pairTV P s x y * b :=
    l1_signed_comb_le (kpow P t) (fun z => kpow P s x z - kpow P s y z)
      (fun z => max (kpow P s x z - kpow P s y z) 0)
      (fun z => max (-(kpow P s x z - kpow P s y z)) 0)
      (fun z => le_max_right _ _) (fun z => le_max_right _ _)
      (fun z => (max_sub_max_neg _).symm) hpc (hpq.symm.trans hpc) hK
  have hcab : pairTV P s x y * b ≤ a * b := mul_le_mul_of_nonneg_right (hs x y) hb0
  unfold pairTV
  simp only [hD]
  linarith

/-- Iterating the bound: `k` blocks of `t` steps, each block with distances at most `1/2`,
have distances at most `(1/2)^k`. -/
theorem pairTV_mul_le (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {t : ℕ} (ht : ∀ x y, pairTV P t x y ≤ 1 / 2) (k : ℕ) (x y : V) :
    pairTV P (k * t) x y ≤ (1 / 2) ^ k := by
  induction k generalizing x y with
  | zero => simpa using pairTV_le_one P hP hrow 0 x y
  | succ k ih =>
    rw [add_mul, one_mul, pow_succ]
    exact pairTV_add_le P hP hrow ih ht x y

/-- The pairwise total variation is nonincreasing in time: a bound valid at time `s` holds at
every later time `t`. -/
theorem pairTV_mono (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    {s t : ℕ} (hst : s ≤ t) {a : ℝ} (hs : ∀ x y, pairTV P s x y ≤ a) (x y : V) :
    pairTV P t x y ≤ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  simpa using pairTV_add_le P hP hrow hs (fun x y => pairTV_le_one P hP hrow d x y) x y

namespace FiniteChainPairTVExample

/-- The kernel taking the value `1/2` everywhere on two points: from each point, each of
the two points is chosen with probability `1/2`. -/
noncomputable def lazyWalk : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 2

theorem lazyWalk_nonneg : ∀ x y, 0 ≤ lazyWalk x y := fun _ _ => by
  norm_num [lazyWalk]

theorem lazyWalk_rowsum : ∀ x, ∑ y, lazyWalk x y = 1 := fun _ => by
  norm_num [lazyWalk, Fin.sum_univ_two]

/-- One step of the lazy walk from any point has probability `1/2` at every point. -/
theorem kpow_lazyWalk_one (x z : Fin 2) : kpow lazyWalk 1 x z = 1 / 2 := by
  simp [kpow, lazyWalk]

/-- After one step the two starting points give the same law, so their distance is zero. -/
theorem pairTV_lazyWalk_one (x y : Fin 2) : pairTV lazyWalk 1 x y = 0 := by
  simp [pairTV, kpow_lazyWalk_one]

theorem pairTV_lazyWalk_one_zero_one : pairTV lazyWalk 1 0 1 = 0 :=
  pairTV_lazyWalk_one 0 1

/-- The iteration bound applied to the lazy walk. -/
theorem pairTV_lazyWalk_mul_le (k : ℕ) (x y : Fin 2) :
    pairTV lazyWalk (k * 1) x y ≤ (1 / 2) ^ k :=
  pairTV_mul_le lazyWalk lazyWalk_nonneg lazyWalk_rowsum (t := 1)
    (fun x y => by rw [pairTV_lazyWalk_one]; norm_num) k x y

end FiniteChainPairTVExample

end LatticeProb.FiniteChain
