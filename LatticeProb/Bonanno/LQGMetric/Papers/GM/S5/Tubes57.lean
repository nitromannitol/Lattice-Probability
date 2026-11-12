/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes57 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.GoodRadiiLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas

/-!
# GM Lemma 5.7, first step: the event `F_r(z)` is determined by `h` modulo constants (P2-M2L2)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.7 (l. 3001–3004): "First note that the occurrence of `F_r(z)` is unaffected by scaling
each of `D_h` and `D̃_h` by the same constant factor. Therefore, Axiom III (Weyl scaling) implies
that `F_r(z)` is determined by `h`, viewed modulo additive constant. So, we only need to show that
`F_r(z) ∈ σ(h|_{B_{3r}(z)})`."

* `mem_tubeEvent_of_scale`: the first sentence;
* `ae_tubeEvent_shift`: a.s. `h ∈ F_r(z) ⇔ h − h_{4r}(z) ∈ F_r(z)` (Weyl scaling by the constant
  `−h_{4r}(z)`, `IsWeakLQGMetric.ae_dist_addConst`);
* `gm_L5_7_of_loc`: GM Lemma 5.7 (`L5_7`) from the statement `L5_7loc` "`F_r(z) ∈ σ(h|_{B_{3r}(z)})`
  a.s., for every whole-plane GFF `h`" (applied to the whole-plane GFF `h − h_{4r}(z)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

section Scale
variable {d₁ d₂ : ContMetric} {e : ℝ}

lemma ofReal_le_scale_iff (he : 0 < e) (a k : ℝ) (s : ℝ≥0∞) :
    ENNReal.ofReal (e * a) ≤ ENNReal.ofReal k * (ENNReal.ofReal e * s) ↔
      ENNReal.ofReal a ≤ ENNReal.ofReal k * s := by
  rw [ENNReal.ofReal_mul he.le, mul_left_comm]
  exact ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 he).ne' ENNReal.ofReal_ne_top

lemma internal_le_scale_iff (he : 0 < e) (x : ℝ≥0∞) (η a : ℝ) :
    ENNReal.ofReal e * x ≤ ENNReal.ofReal (η * (e * a)) ↔ x ≤ ENNReal.ofReal (η * a) := by
  rw [show η * (e * a) = e * (η * a) by ring, ENNReal.ofReal_mul he.le]
  exact ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 he).ne' ENNReal.ofReal_ne_top

end Scale

/-- **GM l. 3001–3002**: `F_r(z)` is unaffected by scaling `D_h` and `D̃_h` by the same factor -/
theorem mem_tubeEvent_of_scale {D D' : DistC → ContMetric} {cs Cs c₁ η b ε r : ℝ} {z : ℂ}
    {V : Set ℂ} {g₁ g₂ : DistC} {e : ℝ} (he : 0 < e)
    (h : ∀ u v, (D g₂).1 (u, v) = e * (D g₁).1 (u, v))
    (h' : ∀ u v, (D' g₂).1 (u, v) = e * (D' g₁).1 (u, v)) :
    g₂ ∈ tubeEvent D D' cs Cs c₁ η b ε r z V ↔ g₁ ∈ tubeEvent D D' cs Cs c₁ η b ε r z V := by
  have hr : ∀ u v, (D' g₂).1 (u, v) ≤ c₁ * (D g₂).1 (u, v) ↔
      (D' g₁).1 (u, v) ≤ c₁ * (D g₁).1 (u, v) := fun u v => by
    rw [h, h', show c₁ * (e * (D g₁).1 (u, v)) = e * (c₁ * (D g₁).1 (u, v)) by ring]
    exact mul_le_mul_iff_right₀ he
  simp only [tubeEvent, mem_ofPred_eq, hr]
  simp only [h', setDist_of_scale he h', ofReal_le_scale_iff he,
    uniqueGeodIn_iff_of_scale he h', internal_of_scale he h', internal_le_scale_iff he]

end LQGMetric.GM
