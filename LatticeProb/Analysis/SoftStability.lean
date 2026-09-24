/-
Multiplicative stability of nonnegative functions under uniform field
perturbations (`ExpStable`), preserved by positive sums, products, and by
composing with a smooth maximum's softmax weight.

Moved from Divisible-Sandpile-Percolation, `Sandpile/Support/SoftStability.lean`.
-/
import LatticeProb.Analysis.SoftComposition

namespace LatticeProb

variable {I : Type*} [Fintype I] [Nonempty I]

/-- The smooth maximum is `1`-Lipschitz for the sup norm, stated without a
sign hypothesis on `β` (unlike `abs_softMaximum_sub_le`, which needs `β > 0`). -/
theorem abs_softMaximum_sub_le_signed {β : ℝ} (hβ : β ≠ 0) {x y : I → ℝ} {a : ℝ}
    (h : ∀ i, |x i - y i| ≤ a) : |softMaximum β x - softMaximum β y| ≤ a := by
  rcases lt_or_gt_of_ne hβ with hβ | hβ
  · have hh := abs_softMinimum_sub_le (neg_pos.mpr hβ) h
    simpa only [softMinimum, neg_neg] using hh
  · exact abs_softMaximum_sub_le hβ h

/-- A uniform perturbation of the input changes a softmax weight by at most a
multiplicative factor `exp(2|β|a)`. -/
theorem softWeight_stability {β : ℝ} (hβ : β ≠ 0) {x y : I → ℝ} {a : ℝ}
    (h : ∀ i, |x i - y i| ≤ a) (i : I) :
    softWeight β x i ≤ Real.exp (2 * |β| * a) * softWeight β y i := by
  have hl := abs_softMaximum_sub_le_signed hβ h
  have ha : |(x i - y i) - (softMaximum β x - softMaximum β y)| ≤ 2 * a := by
    apply (abs_sub _ _).trans
    linarith [h i]
  have hm := mul_le_mul_of_nonneg_left ha (abs_nonneg β)
  have he := le_abs_self (β * ((x i - y i) - (softMaximum β x - softMaximum β y)))
  rw [abs_mul] at he
  rw [softWeight_eq_exp hβ x i, softWeight_eq_exp hβ y i, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The matching lower bound to `softWeight_stability`. -/
theorem softWeight_stability_lower {β : ℝ} (hβ : β ≠ 0) {x y : I → ℝ} {a : ℝ}
    (h : ∀ i, |x i - y i| ≤ a) (i : I) :
    Real.exp (-2 * |β| * a) * softWeight β y i ≤ softWeight β x i := by
  have hh := softWeight_stability hβ (x := y) (y := x)
    (fun j => by simpa only [abs_sub_comm] using h j) i
  have he : Real.exp (-2 * |β| * a) * Real.exp (2 * |β| * a) = 1 := by
    rw [← Real.exp_add, show -2 * |β| * a + 2 * |β| * a = 0 by ring, Real.exp_zero]
  calc
    _ ≤ Real.exp (-2 * |β| * a) * (Real.exp (2 * |β| * a) * softWeight β x i) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, he, one_mul]

section Stability

variable {V : Type*}

/-- Nonnegative functions whose ratios change by at most a factor `exp(K a)`
under a uniform perturbation of size `a` of the field. -/
def ExpStable (K : ℝ) (f : (V → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∀ x y a, 0 ≤ a → (∀ j, |x j - y j| ≤ a) →
    f x ≤ Real.exp (K * a) * f y

/-- An `ExpStable` function is nonnegative. -/
theorem ExpStable.nonneg {K : ℝ} {f : (V → ℝ) → ℝ} (hf : ExpStable K f)
    (x : V → ℝ) : 0 ≤ f x := hf.1 x

/-- `ExpStable` is monotone in its stability constant: a smaller constant
implies every larger one. -/
theorem ExpStable.mono {K L : ℝ} {f : (V → ℝ) → ℝ} (hf : ExpStable K f)
    (hKL : K ≤ L) : ExpStable L f := by
  refine ⟨hf.1, fun x y a ha h => (hf.2 x y a ha h).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKL ha)) (hf.1 y)

/-- A nonnegative constant function is `ExpStable` with constant `0`. -/
theorem expStable_const {c : ℝ} (hc : 0 ≤ c) :
    ExpStable 0 (fun _ : V → ℝ => c) := by
  exact ⟨fun _ => hc, by simp⟩

/-- `ExpStable` is closed under addition, with the same constant. -/
theorem ExpStable.add {K : ℝ} {f g : (V → ℝ) → ℝ}
    (hf : ExpStable K f) (hg : ExpStable K g) : ExpStable K (fun x => f x + g x) := by
  refine ⟨fun x => add_nonneg (hf.1 x) (hg.1 x), fun x y a ha h => ?_⟩
  simpa only [mul_add] using add_le_add (hf.2 x y a ha h) (hg.2 x y a ha h)

/-- `ExpStable` is closed under multiplication, with constants adding. -/
theorem ExpStable.mul {K L : ℝ} {f g : (V → ℝ) → ℝ}
    (hf : ExpStable K f) (hg : ExpStable L g) :
    ExpStable (K + L) (fun x => f x * g x) := by
  refine ⟨fun x => mul_nonneg (hf.1 x) (hg.1 x), fun x y a ha h => ?_⟩
  calc
    _ ≤ (Real.exp (K * a) * f y) * (Real.exp (L * a) * g y) :=
      mul_le_mul (hf.2 x y a ha h) (hg.2 x y a ha h) (hg.1 x)
        (mul_nonneg (Real.exp_pos _).le (hf.1 y))
    _ = _ := by rw [add_mul, Real.exp_add]; ring

/-- `ExpStable` is closed under multiplying by a nonnegative constant, with
the same constant. -/
theorem ExpStable.const_mul {K c : ℝ} {f : (V → ℝ) → ℝ}
    (hf : ExpStable K f) (hc : 0 ≤ c) : ExpStable K (fun x => c * f x) := by
  simpa only [zero_add] using (expStable_const (V := V) hc).mul hf

/-- `ExpStable` is closed under a finite sum over an index type, with the
same constant. -/
theorem ExpStable.sum {J : Type*} [Fintype J] {K : ℝ} {f : J → (V → ℝ) → ℝ}
    (hf : ∀ j, ExpStable K (f j)) : ExpStable K (fun x => ∑ j, f j x) := by
  refine ⟨fun x => Finset.sum_nonneg (fun j _ => (hf j).1 x), fun x y a ha h => ?_⟩
  simpa only [Finset.mul_sum] using Finset.sum_le_sum (fun j _ => (hf j).2 x y a ha h)

/-- The matching lower bound implied by `ExpStable`'s upper bound applied in
reverse. -/
theorem ExpStable.lower {K : ℝ} {f : (V → ℝ) → ℝ} (hf : ExpStable K f)
    {x y : V → ℝ} {a : ℝ} (ha : 0 ≤ a) (h : ∀ j, |x j - y j| ≤ a) :
    Real.exp (-K * a) * f y ≤ f x := by
  have hh := hf.2 y x a ha (fun j => by simpa only [abs_sub_comm] using h j)
  calc
    _ ≤ Real.exp (-K * a) * (Real.exp (K * a) * f x) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; simp

/-- A function is field-nonexpansive when a uniform perturbation of size `a`
of the field changes its value by at most `a`. -/
def FieldNonexpansive (f : (V → ℝ) → ℝ) : Prop :=
  ∀ x y a, 0 ≤ a → (∀ j, |x j - y j| ≤ a) → |f x - f y| ≤ a

/-- A single coordinate projection is field-nonexpansive. -/
theorem fieldNonexpansive_coordinate (i : V) :
    FieldNonexpansive (fun x : V → ℝ => x i) := fun _ _ _ _ h => h i

/-- The smooth maximum of a field-nonexpansive family is field-nonexpansive. -/
theorem FieldNonexpansive.softMaximum {β : ℝ} (hβ : β ≠ 0)
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, FieldNonexpansive (f i)) :
    FieldNonexpansive (fun x => LatticeProb.softMaximum β (fun i => f i x)) := by
  intro x y a ha h
  exact abs_softMaximum_sub_le_signed hβ (fun i => hf i x y a ha h)

/-- The smooth minimum of a field-nonexpansive family is field-nonexpansive. -/
theorem FieldNonexpansive.softMinimum {β : ℝ} (hβ : β ≠ 0)
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, FieldNonexpansive (f i)) :
    FieldNonexpansive (fun x => LatticeProb.softMinimum β (fun i => f i x)) :=
  FieldNonexpansive.softMaximum (neg_ne_zero.mpr hβ) hf

/-- A softmax weight built from a field-nonexpansive family is `ExpStable`
with constant `2|β|`. -/
theorem expStable_softWeightComposition {β : ℝ} (hβ : β ≠ 0)
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, FieldNonexpansive (f i)) (i : I) :
    ExpStable (2 * |β|) (fun x => softWeight β (fun i => f i x) i) := by
  refine ⟨fun x => (softWeight_pos β _ i).le, fun x y a ha h => ?_⟩
  exact softWeight_stability hβ (fun i => hf i x y a ha h) i

end Stability

end LatticeProb
