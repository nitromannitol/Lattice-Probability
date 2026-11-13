/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2Griffiths at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib

 













set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos

 
def spin (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem spin_true : spin true = 1 := rfl
@[simp] theorem spin_false : spin false = -1 := rfl

theorem spin_mul_self (b : Bool) : spin b * spin b = 1 := by cases b <;> simp [spin]

theorem exp_mul_spin (c : ℝ) (b : Bool) :
    Real.exp (c * spin b) = Real.cosh c + spin b * Real.sinh c := by
  cases b
  · simp [spin, Real.cosh_eq, Real.sinh_eq]; ring
  · simp [spin, Real.cosh_eq, Real.sinh_eq]; ring

variable {W : Type*} [Fintype W] [DecidableEq W]

 
def spinMono (n : W → ℕ) (s : W → Bool) : ℝ := ∏ i, spin (s i) ^ n i

theorem spinMono_mul (n m : W → ℕ) (s : W → Bool) :
    spinMono n s * spinMono m s = spinMono (n + m) s := by
  simp only [spinMono, ← Finset.prod_mul_distrib, Pi.add_apply, pow_add]

theorem sum_spinMono_nonneg (n : W → ℕ) : 0 ≤ ∑ s : W → Bool, spinMono n s := by
  have h : ∑ s : W → Bool, spinMono n s = ∏ i, ∑ b : Bool, spin b ^ n i := by
    rw [Fintype.prod_sum]
    rfl
  rw [h]
  refine Finset.prod_nonneg fun i _ => ?_
  rw [Fintype.sum_bool]
  simp only [spin_true, one_pow, spin_false]
  rcases Nat.even_or_odd (n i) with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num

theorem spinMono_mul_prod {K : Type*} (n₀ : W → ℕ) (m : K → W → ℕ) (s : W → Bool)
    (T : Finset K) :
    spinMono n₀ s * ∏ k ∈ T, spinMono (m k) s = spinMono (n₀ + ∑ k ∈ T, m k) s := by
  classical
  induction T using Finset.induction_on generalizing n₀ with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← mul_assoc, spinMono_mul, ih]
    congr 1
    funext i
    simp only [Pi.add_apply]
    ring

 
theorem sum_spinMono_mul_prod_nonneg {K : Type*} [Fintype K] (n₀ : W → ℕ)
    (α β : K → ℝ) (hα : ∀ k, 0 ≤ α k) (hβ : ∀ k, 0 ≤ β k) (m : K → W → ℕ) :
    0 ≤ ∑ s : W → Bool, spinMono n₀ s * ∏ k, (α k + β k * spinMono (m k) s) := by
  classical
  have hexp : ∀ s : W → Bool, spinMono n₀ s * ∏ k, (α k + β k * spinMono (m k) s) =
      ∑ T ∈ (Finset.univ : Finset K).powerset,
        ((∏ k ∈ T, β k) * ∏ k ∈ Finset.univ \ T, α k) *
          spinMono (n₀ + ∑ k ∈ T, m k) s := by
    intro s
    simp_rw [add_comm (α _)]
    rw [Finset.prod_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [← spinMono_mul_prod n₀ m s T, Finset.prod_mul_distrib]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun T _ => ?_
  rw [← Finset.mul_sum]
  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun k _ => hβ k)
    (Finset.prod_nonneg fun k _ => hα k)) (sum_spinMono_nonneg _)

 
def isingWeight (h : W → ℝ) (J : W → W → ℝ) (s : W → Bool) : ℝ :=
  Real.exp (∑ i, h i * spin (s i) + (1 / 2 : ℝ) * ∑ i, ∑ j, J i j * (spin (s i) * spin (s j)))

theorem isingWeight_pos (h : W → ℝ) (J : W → W → ℝ) (s : W → Bool) :
    0 < isingWeight h J s := Real.exp_pos _

theorem spinMono_single (i : W) (s : W → Bool) : spinMono (Pi.single i 1) s = spin (s i) := by
  unfold spinMono
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem spinMono_pair (i j : W) (s : W → Bool) :
    spinMono (Pi.single i 1 + Pi.single j 1) s = spin (s i) * spin (s j) := by
  rw [← spinMono_mul, spinMono_single, spinMono_single]

theorem spin_mul_spin (a b : Bool) : spin a * spin b = spin (a == b) := by
  cases a <;> cases b <;> simp [spin]

 
theorem isingWeight_eq_prod (h : W → ℝ) (J : W → W → ℝ) (s : W → Bool) :
    isingWeight h J s =
      (∏ i, (Real.cosh (h i) + Real.sinh (h i) * spinMono (Pi.single i 1) s)) *
        ∏ p : W × W, (Real.cosh (J p.1 p.2 / 2) +
          Real.sinh (J p.1 p.2 / 2) * spinMono (Pi.single p.1 1 + Pi.single p.2 1) s) := by
  unfold isingWeight
  have h2 : (1 / 2 : ℝ) * ∑ i, ∑ j, J i j * (spin (s i) * spin (s j)) =
      ∑ p : W × W, (J p.1 p.2 / 2) * spin (s p.1 == s p.2) := by
    rw [Finset.mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [spin_mul_spin]
    ring
  rw [h2, Real.exp_add, Real.exp_sum, Real.exp_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [spinMono_single, exp_mul_spin]
    ring
  · apply Finset.prod_congr rfl
    intro p _
    rw [spinMono_pair, spin_mul_spin, exp_mul_spin]
    ring

 
theorem griffiths_first (h : W → ℝ) (J : W → W → ℝ) (hh : ∀ i, 0 ≤ h i)
    (hJ : ∀ i j, 0 ≤ J i j) (n₀ : W → ℕ) :
    0 ≤ ∑ s : W → Bool, spinMono n₀ s * isingWeight h J s := by
  simp_rw [isingWeight_eq_prod, ← mul_assoc]
  
  have hcomb : ∀ s : W → Bool,
      spinMono n₀ s * (∏ i, (Real.cosh (h i) + Real.sinh (h i) * spinMono (Pi.single i 1) s)) *
        ∏ p : W × W, (Real.cosh (J p.1 p.2 / 2) +
          Real.sinh (J p.1 p.2 / 2) * spinMono (Pi.single p.1 1 + Pi.single p.2 1) s) =
      spinMono n₀ s * ∏ k : W ⊕ (W × W),
        ((Sum.elim (fun i => Real.cosh (h i)) (fun p => Real.cosh (J p.1 p.2 / 2)) k) +
          (Sum.elim (fun i => Real.sinh (h i)) (fun p => Real.sinh (J p.1 p.2 / 2)) k) *
            spinMono (Sum.elim (fun i => Pi.single i 1)
              (fun p => Pi.single p.1 1 + Pi.single p.2 1) k) s) := by
    intro s
    rw [Fintype.prod_sum_type, mul_assoc]
    rfl
  simp_rw [hcomb]
  refine sum_spinMono_mul_prod_nonneg n₀ _ _ ?_ ?_ _
  · rintro (i | p) <;> exact (Real.cosh_pos _).le
  · rintro (i | p)
    · exact Real.sinh_nonneg_iff.mpr (hh i)
    · exact Real.sinh_nonneg_iff.mpr (div_nonneg (hJ p.1 p.2) zero_le_two)

 
def isingProb (h : W → ℝ) (J : W → W → ℝ) (s : W → Bool) : ℝ :=
  isingWeight h J s / ∑ s', isingWeight h J s'

theorem isingPartition_pos (h : W → ℝ) (J : W → W → ℝ) :
    0 < ∑ s : W → Bool, isingWeight h J s :=
  Finset.sum_pos (fun s _ => isingWeight_pos h J s) Finset.univ_nonempty

def dropPair (J : W → W → ℝ) (v w : W) : W → W → ℝ := fun i j =>
  if (i = v ∧ j = w) ∨ (i = w ∧ j = v) then 0 else J i j

theorem isingWeight_dropPair (h : W → ℝ) (J : W → W → ℝ) (hJs : ∀ i j, J i j = J j i)
    {v w : W} (hvw : v ≠ w) (s : W → Bool) :
    isingWeight h J s =
      Real.exp (J v w * (spin (s v) * spin (s w))) * isingWeight h (dropPair J v w) s := by
  unfold isingWeight
  rw [← Real.exp_add]
  congr 1
  have hsplit : ∀ i j, J i j * (spin (s i) * spin (s j)) =
      dropPair J v w i j * (spin (s i) * spin (s j)) +
        (if (i = v ∧ j = w) ∨ (i = w ∧ j = v) then J i j * (spin (s i) * spin (s j)) else 0) := by
    intro i j
    unfold dropPair
    split_ifs <;> ring
  have hsplit2 : ∑ i, ∑ j, J i j * (spin (s i) * spin (s j)) =
      ∑ i, ∑ j, dropPair J v w i j * (spin (s i) * spin (s j)) +
        ∑ i, ∑ j, (if (i = v ∧ j = w) ∨ (i = w ∧ j = v) then
          J i j * (spin (s i) * spin (s j)) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit i j
  rw [hsplit2]
  have hpair : ∑ i, ∑ j, (if (i = v ∧ j = w) ∨ (i = w ∧ j = v) then
      J i j * (spin (s i) * spin (s j)) else 0) = 2 * (J v w * (spin (s v) * spin (s w))) := by
    have hor : ∀ i j, (if (i = v ∧ j = w) ∨ (i = w ∧ j = v) then
        J i j * (spin (s i) * spin (s j)) else (0 : ℝ)) =
        (if i = v ∧ j = w then J i j * (spin (s i) * spin (s j)) else 0) +
          (if i = w ∧ j = v then J i j * (spin (s i) * spin (s j)) else 0) := by
      intro i j
      by_cases h1 : i = v ∧ j = w
      · have h2 : ¬ (i = w ∧ j = v) := fun h2 => hvw (h1.1.symm.trans h2.1)
        rw [if_pos (Or.inl h1), if_pos h1, if_neg h2, add_zero]
      · by_cases h2 : i = w ∧ j = v
        · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2, zero_add]
        · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2, add_zero]
    have hsingle : ∀ a b : W, ∑ i, ∑ j, (if i = a ∧ j = b then
        J i j * (spin (s i) * spin (s j)) else (0 : ℝ)) = J a b * (spin (s a) * spin (s b)) := by
      intro a b
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro j _
        simp [hi]
      · simp
    simp_rw [hor, Finset.sum_add_distrib, hsingle]
    rw [hJs w v]
    ring
  rw [hpair]
  ring

 

theorem isingProb_disagree_le (h : W → ℝ) (J : W → W → ℝ) (hh : ∀ i, 0 ≤ h i)
    (hJ : ∀ i j, 0 ≤ J i j) (hJs : ∀ i j, J i j = J j i) {v w : W} (hvw : v ≠ w) :
    ∑ s : W → Bool, (if s v = s w then 0 else isingProb h J s) ≤ Real.exp (-2 * J v w) := by
  set J' := dropPair J v w with hJ'def
  have hJ' : ∀ i j, 0 ≤ J' i j := by
    intro i j; unfold J' dropPair; split_ifs; exact le_rfl; exact hJ i j
  set A := ∑ s : W → Bool, (if s v = s w then isingWeight h J' s else 0)
  set B := ∑ s : W → Bool, (if s v = s w then 0 else isingWeight h J' s)
  have hAB : B ≤ A := by
    have hg := griffiths_first h J' hh hJ' (Pi.single v 1 + Pi.single w 1)
    simp_rw [spinMono_pair] at hg
    have : ∑ s : W → Bool, spin (s v) * spin (s w) * isingWeight h J' s = A - B := by
      simp only [A, B, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : s v = s w
      · rw [if_pos hs, if_pos hs, hs, spin_mul_self]; ring
      · rw [if_neg hs, if_neg hs]
        have : spin (s v) * spin (s w) = -1 := by
          cases hv : s v <;> cases hw : s w <;> simp_all [spin]
        rw [this]; ring
    linarith
  have hZ : ∑ s : W → Bool, isingWeight h J s =
      Real.exp (J v w) * A + Real.exp (-J v w) * B := by
    simp only [A, B, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [isingWeight_dropPair h J hJs hvw, ← hJ'def]
    by_cases hs : s v = s w
    · rw [if_pos hs, if_pos hs, hs, spin_mul_self]; ring
    · rw [if_neg hs, if_neg hs]
      have : spin (s v) * spin (s w) = -1 := by
        cases hv : s v <;> cases hw : s w <;> simp_all [spin]
      rw [this]; ring
  have hD : ∑ s : W → Bool, (if s v = s w then 0 else isingProb h J s) =
      Real.exp (-J v w) * B / ∑ s : W → Bool, isingWeight h J s := by
    simp only [isingProb, B, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : s v = s w
    · simp [hs]
    · rw [if_neg hs, if_neg hs, isingWeight_dropPair h J hJs hvw, ← hJ'def]
      have : spin (s v) * spin (s w) = -1 := by
        cases hv : s v <;> cases hw : s w <;> simp_all [spin]
      rw [this, mul_neg_one]
  rw [hD, hZ]
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun s _ => by
    split_ifs; exact le_rfl; exact (isingWeight_pos _ _ _).le
  have hApos : 0 < Real.exp (J v w) * A + Real.exp (-J v w) * B := by
    rw [← hZ]; exact isingPartition_pos h J
  rw [div_le_iff₀ hApos]
  have hexp : Real.exp (-2 * J v w) * Real.exp (J v w) = Real.exp (-J v w) := by
    rw [← Real.exp_add]; ring_nf
  have hexp' : Real.exp (-2 * J v w) * Real.exp (-J v w) ≥ 0 := by positivity
  nlinarith [Real.exp_pos (-J v w), Real.exp_pos (-2 * J v w)]

 
def dropField (h : W → ℝ) (v : W) : W → ℝ := fun i => if i = v then 0 else h i

 
theorem isingProb_neg_le (h : W → ℝ) (J : W → W → ℝ) (hh : ∀ i, 0 ≤ h i)
    (hJ : ∀ i j, 0 ≤ J i j) (v : W) :
    ∑ s : W → Bool, (if s v then 0 else isingProb h J s) ≤ Real.exp (-2 * h v) := by
  set h' := dropField h v
  have hh' : ∀ i, 0 ≤ h' i := by
    intro i; unfold h' dropField; split_ifs; exact le_rfl; exact hh i
  have hsplit : ∀ s : W → Bool, isingWeight h J s =
      Real.exp (h v * spin (s v)) * isingWeight h' J s := by
    intro s
    unfold isingWeight
    rw [← Real.exp_add]
    congr 1
    have : ∑ i, h i * spin (s i) = h v * spin (s v) + ∑ i, h' i * spin (s i) := by
      have hpt : ∀ i, h i * spin (s i) =
          (if i = v then h v * spin (s v) else 0) + h' i * spin (s i) := by
        intro i
        by_cases hi : i = v
        · subst hi; simp [h', dropField]
        · simp [h', dropField, hi]
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    rw [this]
    ring
  set A := ∑ s : W → Bool, (if s v then isingWeight h' J s else 0)
  set B := ∑ s : W → Bool, (if s v then 0 else isingWeight h' J s)
  have hAB : B ≤ A := by
    have hg := griffiths_first h' J hh' hJ (Pi.single v 1)
    simp_rw [spinMono_single] at hg
    have : ∑ s : W → Bool, spin (s v) * isingWeight h' J s = A - B := by
      simp only [A, B, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      cases hs : s v <;> simp [spin]
    linarith
  have hZ : ∑ s : W → Bool, isingWeight h J s =
      Real.exp (h v) * A + Real.exp (-h v) * B := by
    simp only [A, B, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [hsplit]
    cases hs : s v <;> simp [spin]
  have hD : ∑ s : W → Bool, (if s v then 0 else isingProb h J s) =
      Real.exp (-h v) * B / ∑ s : W → Bool, isingWeight h J s := by
    simp only [isingProb, B, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    rw [hsplit]
    cases hs : s v <;> simp [spin]
  rw [hD, hZ]
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun s _ => by
    split_ifs; exact le_rfl; exact (isingWeight_pos _ _ _).le
  have hApos : 0 < Real.exp (h v) * A + Real.exp (-h v) * B := by
    rw [← hZ]; exact isingPartition_pos h J
  rw [div_le_iff₀ hApos]
  have hexp : Real.exp (-2 * h v) * Real.exp (h v) = Real.exp (-h v) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : Real.exp (-h v) * B ≤ Real.exp (-h v) * A :=
    mul_le_mul_of_nonneg_left hAB (Real.exp_pos _).le
  have h2 : 0 ≤ Real.exp (-2 * h v) * (Real.exp (-h v) * B) := by positivity
  calc Real.exp (-h v) * B ≤ Real.exp (-h v) * A := h1
    _ ≤ Real.exp (-h v) * A + Real.exp (-2 * h v) * (Real.exp (-h v) * B) :=
        le_add_of_nonneg_right h2
    _ = Real.exp (-2 * h v) * (Real.exp (h v) * A + Real.exp (-h v) * B) := by
        rw [mul_add, ← mul_assoc (Real.exp (-2 * h v)) (Real.exp (h v)), hexp]

end SupercriticalLQGUniqueness.B2.QPos
