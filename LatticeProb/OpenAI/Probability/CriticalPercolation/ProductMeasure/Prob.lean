/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/CriticalPercolation/ProductMeasure/Prob.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Prob in place of OAI.Probability.CriticalPercolation.ProductMeasure.Prob, and the module paths of local imports are changed in the same way; the import of LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.ExpectMulReal (not copied here) is replaced by the imports of the copied modules it reaches,
   namely LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Distribution, LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Density;
   the unused declarations `expect_mul_ge_antitone`, `prob_harris_decreasing` (they need modules not copied here) are omitted; statements and proofs of the declarations kept are unchanged. -/
import Mathlib
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Distribution
import LatticeProb.OpenAI.Probability.CriticalPercolation.ProductMeasure.Density

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

noncomputable def prob (w : E → Prop → ℝ) (P : Set E → Prop) : ℝ :=
  expect w (fun ω => if P ω then 1 else 0)

lemma prob_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b) (P : Set E → Prop) :
    0 ≤ prob w P := expect_nonneg hp (fun _ => by split_ifs <;> norm_num)

lemma prob_mono (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {P Q : Set E → Prop} (h : ∀ ω, P ω → Q ω) : prob w P ≤ prob w Q := by
  apply expect_mono hp
  intro ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]
  exact (hQ (h ω hP)).elim

lemma prob_split (w : E → Prop → ℝ) (P Q : Set E → Prop) :
    prob w P = prob w (fun ω => P ω ∧ Q ω) + prob w (fun ω => P ω ∧ ¬Q ω) := by
  unfold prob
  rw [← expect_add]
  congr 1
  funext ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

lemma prob_congr (w : E → Prop → ℝ) {P Q : Set E → Prop}
    (h : ∀ ω, P ω ↔ Q ω) : prob w P = prob w Q := by
  congr 1
  funext ω
  exact propext (h ω)

lemma indicator_mask (P Q : Prop) :
    (if P then (if Q then (1 : ℝ) else 0) else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma indicator_mask_mul (P Q R : Prop) :
    (if P then (if Q then (1 : ℝ) else 0)*(if R then 1 else 0) else 0) =
      if P ∧ Q ∧ R then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> simp [hP, hQ, hR]

lemma indicator_antitone {X : Type*} [Preorder X] {P : X → Prop}
    (h : ∀ ⦃x y⦄, x ≤ y → P y → P x) :
    Antitone (fun x => if P x then (1 : ℝ) else 0) := by
  intro x y hxy
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy]
  exact (hx (h hxy hy)).elim

lemma indicator_monotone {X : Type*} [Preorder X] {P : X → Prop}
    (h : ∀ ⦃x y⦄, x ≤ y → P x → P y) :
    Monotone (fun x => if P x then (1 : ℝ) else 0) := by
  intro x y hxy
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy]
  exact (hy (h hxy hx)).elim



end CriticalPercolation.FiniteProduct

end
end

end OAI
