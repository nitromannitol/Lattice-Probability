import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W0
import LatticeProb.Prob.UpcrossGlue

/-!
# First hitting times and gluing paths

The two constructions of a glued path agree when the first path hits its
level and both the first path and the continuation start at zero.
-/

open Set
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

/-- The two first-hitting-time conventions agree at an attained finite hit. -/
theorem hitLevel_eq_glueTime {x : C(ℝ≥0, ℝ)} {a : ℝ}
    (h : hitFrom (-a) 0 (x : ℝ≥0 → ℝ) ≠ ⊤) :
    QuantumZipper.Williams.hitLevel x (-a) = glueTime a x := by
  obtain ⟨t, ht, _, hxt, hleast⟩ := exists_hitFrom_eq x.continuous h
  have hmin : IsLeast {s : ℝ≥0 | x s = -a} t :=
    ⟨hxt, fun s hs => hleast s zero_le hs⟩
  rw [QuantumZipper.Williams.hitLevel, hmin.csInf_eq, glueTime, ht,
    ENNReal.toNNReal_coe]

/-- Williams' piecewise gluing and continuous-map gluing agree pathwise. -/
theorem glued_eq_glueC {x z : C(ℝ≥0, ℝ)} {y : ℝ≥0 → ℝ} {a : ℝ}
    (hx : x 0 = 0) (hz : z 0 = 0)
    (h : hitFrom (-a) 0 (x : ℝ≥0 → ℝ) ≠ ⊤)
    (hy : ∀ t, z t = QuantumZipper.Williams.postLast y 0 t) :
    QuantumZipper.Williams.glued a x y = (glueC a x z : ℝ≥0 → ℝ) := by
  funext t
  have hT := hitLevel_eq_glueTime h
  by_cases ht : t ≤ glueTime a x
  · rw [QuantumZipper.Williams.glued, hT, ite_eq_left ht,
      glueC_apply_of_le ht, hz, add_zero]
    simp only [QuantumZipper.Williams.revHit, hT]
    ring
  · have ht' : glueTime a x ≤ t := le_of_not_ge ht
    rw [QuantumZipper.Williams.glued, hT, ite_eq_right ht,
      glueC_apply_of_ge hx ht', hy]

end LatticeProb
