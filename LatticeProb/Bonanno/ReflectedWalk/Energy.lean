/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Energy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Dirichlet energy and the Dirichlet form (Gwynne–Sung, (1.4))

`Energy(f) = ∑_{(x,y) ∈ EG} c(x,y) |f(y) − f(x)|²`, the sum being over *unoriented*
edges.  We realise it as half the sum over ordered pairs `V × V`:

  `Energy f = (∑' p : V × V, c p.1 p.2 * (f p.2 − f p.1)^2) / 2`.

Every ordered pair `(x,y)` and its reverse contribute equally and the diagonal
contributes `0`, so the halved ordered sum equals the paper's unoriented sum.  This
convention is used throughout and is the reason factors of `2` appear in the
single-edge estimates below.

The main result of this file is `abs_sub_le_walkConst_mul`: along any walk, the
increment of a finite-energy function is controlled by `√(Energy f)` times a constant
depending only on the walk.  This is the estimate that makes the Dirichlet space
complete, and it is the quantitative content of Gwynne–Sung Lemma 2.1.
-/

namespace ReflectedWalk

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- The contribution of one *ordered* pair to the Dirichlet energy. -/
noncomputable def gradSq (f : V → ℝ) (p : V × V) : ℝ := G.c p.1 p.2 * (f p.2 - f p.1) ^ 2

lemma gradSq_nonneg (f : V → ℝ) (p : V × V) : 0 ≤ G.gradSq f p :=
  mul_nonneg (G.c_nonneg _ _) (sq_nonneg _)

/-- `f` has finite Dirichlet energy. For a nonnegative family this is the paper's
`Energy(f) < ∞`. -/
def HasFiniteEnergy (f : V → ℝ) : Prop := Summable (G.gradSq f)

/-- The Dirichlet energy (1.4), as half the sum over ordered pairs. -/
noncomputable def Energy (f : V → ℝ) : ℝ := (∑' p : V × V, G.gradSq f p) / 2

lemma Energy_nonneg (f : V → ℝ) : 0 ≤ G.Energy f := by
  apply div_nonneg _ (by norm_num)
  exact tsum_nonneg fun p => G.gradSq_nonneg f p

lemma tsum_gradSq_eq (f : V → ℝ) : ∑' p : V × V, G.gradSq f p = 2 * G.Energy f := by
  rw [Energy]; ring

/-- A single ordered pair contributes at most the whole energy sum. -/
lemma gradSq_le_two_energy {f : V → ℝ} (hf : G.HasFiniteEnergy f) (p : V × V) :
    G.gradSq f p ≤ 2 * G.Energy f := by
  rw [← G.tsum_gradSq_eq f]
  exact hf.le_tsum p fun b _ => G.gradSq_nonneg f b

/-- The single-edge increment bound: crossing an edge of conductance `c x y > 0`
changes a finite-energy function by at most `√(2 Energy f) / √(c x y)`. -/
lemma abs_sub_le_of_adj {f : V → ℝ} (hf : G.HasFiniteEnergy f) {x y : V}
    (hxy : G.Adj x y) :
    |f y - f x| ≤ Real.sqrt (2 * G.Energy f) / Real.sqrt (G.c x y) := by
  have hc : 0 < G.c x y := hxy
  have hkey : G.c x y * (f y - f x) ^ 2 ≤ 2 * G.Energy f :=
    G.gradSq_le_two_energy hf (x, y)
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hc)]
  have h1 : |f y - f x| * Real.sqrt (G.c x y) =
      Real.sqrt ((f y - f x) ^ 2 * G.c x y) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rw [h1]
  apply Real.sqrt_le_sqrt
  rw [mul_comm ((f y - f x) ^ 2)]
  exact hkey

section WalkConst

open SimpleGraph

/-- The constant `∑_j 1/√(c_j)` accumulated along a walk.  It depends only on the
walk, not on the function being estimated. -/
noncomputable def walkConst : {a b : V} → G.toSimpleGraph.Walk a b → ℝ
  | _, _, Walk.nil => 0
  | a, _, Walk.cons (v := v) _ p => 1 / Real.sqrt (G.c a v) + walkConst p

lemma walkConst_nonneg : ∀ {a b : V} (w : G.toSimpleGraph.Walk a b), 0 ≤ G.walkConst w
  | _, _, Walk.nil => le_refl 0
  | a, _, Walk.cons (v := v) _ p => by
      have h1 : (0:ℝ) ≤ 1 / Real.sqrt (G.c a v) := by positivity
      exact add_nonneg h1 (walkConst_nonneg p)

/-- **Key estimate.** Along any walk from `a` to `b`, the increment of a
finite-energy function is at most `walkConst` times `√(2 · Energy f)`.

This is the mechanism behind Gwynne–Sung Lemma 2.1: the value of a finite-energy
function at any vertex is determined, up to a walk-dependent constant, by its energy
and its value at a basepoint.  We bound each edge separately rather than applying
Cauchy–Schwarz to the whole walk; the resulting constant is larger than the paper's
but the estimate is used only qualitatively. -/
lemma abs_sub_le_walkConst_mul {f : V → ℝ} (hf : G.HasFiniteEnergy f) :
    ∀ {a b : V} (w : G.toSimpleGraph.Walk a b),
      |f b - f a| ≤ G.walkConst w * Real.sqrt (2 * G.Energy f)
  | _, _, Walk.nil => by simp [walkConst]
  | a, b, Walk.cons (v := v) h p => by
      have hstep : |f v - f a| ≤ Real.sqrt (2 * G.Energy f) / Real.sqrt (G.c a v) :=
        G.abs_sub_le_of_adj hf h
      have hrest : |f b - f v| ≤ G.walkConst p * Real.sqrt (2 * G.Energy f) :=
        abs_sub_le_walkConst_mul hf p
      have htri : |f b - f a| ≤ |f v - f a| + |f b - f v| := by
        have : f b - f a = (f v - f a) + (f b - f v) := by ring
        rw [this]; exact abs_add_le _ _
      refine htri.trans (le_of_le_of_eq (add_le_add hstep hrest) ?_)
      rw [walkConst]
      ring

end WalkConst

end ConductanceGraph

end ReflectedWalk
