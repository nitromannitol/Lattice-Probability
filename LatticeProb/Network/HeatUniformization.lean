/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: MeshOnly/MeshOnlyHeatUniformization.lean.
-/
import LatticeProb.Network.HeatGenerator
import Mathlib.Algebra.BigOperators.Field

/-!
# Uniformized transition probabilities on a finite network

For a conductance `c` of a locally finite graph `G` and a positive vertex mass `m`, the
uniformization rate `Λ = 1 + ∑_v weight(v) / m(v)` dominates the total conductance of every vertex
relative to its mass: `weight(v) ≤ Λ m(v)`. For a set `W` of vertices, the uniformized transition
`P(v, w)` moves from `v` to a neighbour `w` with probability `c(v, w) / (Λ m(v))` and holds at `v`
with probability `1 - weight(v) / (Λ m(v))` when `v ∈ W`; a vertex outside `W` is absorbing.

The file proves that the uniformization rate is positive, that it dominates the total conductance,
that the uniformized transitions are nonnegative with row sums one, and that on `W` the rate times
the expected increment of `P` is the mass generator `massGenerator`.
-/

namespace LatticeProb.Network

variable {V : Type*} [Fintype V]

/-- The uniformization rate `Λ = 1 + ∑_v weight(v) / m(v)`, a finite rate dominating the total
conductance of every vertex relative to its mass. Only this domination `weight(v) ≤ Λ m(v)` is used:
it makes the holding probabilities of `uniformizedTransition` nonnegative. -/
noncomputable def uniformizationRate (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (m : V → ℝ) : ℝ :=
  1 + ∑ v, weight G c v / m v

/-- Uniformized transition probabilities, with absorption outside `W`: for `v ∈ W` the probability
of moving from `v` to `w` is `c(v, w) / (Λ m(v))` and the holding probability at `v` is the
complement, where `Λ` is the uniformization rate; a vertex outside `W` stays put. -/
noncomputable def uniformizedTransition (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (m : V → ℝ) (W : Set V) (v w : V) : ℝ := by
  classical
  exact if v ∈ W then
    c v w / (uniformizationRate G c m * m v) +
      if w = v then 1 - weight G c v / (uniformizationRate G c m * m v) else 0
  else if w = v then 1 else 0

section Uniformization

variable (G : SimpleGraph V) [G.LocallyFinite]

/-- Bridge lemma: on a finite vertex type the neighbour sum defining `weight` may be replaced by the
sum over all vertices, because `c` vanishes on non-edges. -/
theorem weight_eq_sum_univ {c : V → V → ℝ} (hc : IsCond G c) (v : V) :
    weight G c v = ∑ w, c v w := by
  unfold weight
  exact sum_neighborFinset_eq_sum v Finset.univ (c v)
    (fun y hy => hc.zero_of_not_adj hy) (fun y _ _ => Finset.mem_univ y)

omit [Fintype V] in
/-- The total conductance at each vertex is nonnegative. -/
theorem weight_nonneg {c : V → V → ℝ} (hc : IsCond G c) (v : V) : 0 ≤ weight G c v :=
  Finset.sum_nonneg fun y _ => hc.nonneg v y

/-- The uniformization rate is positive. -/
theorem uniformizationRate_pos {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) : 0 < uniformizationRate G c m := by
  have h : 0 ≤ ∑ v, weight G c v / m v :=
    Finset.sum_nonneg fun v _ => div_nonneg (weight_nonneg G hc v) (hm v).le
  unfold uniformizationRate
  linarith

/-- The total conductance at `v` is at most the uniformization rate times the mass of `v`. -/
theorem weight_le_uniformizationRate_mul {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (v : V) : weight G c v ≤ uniformizationRate G c m * m v := by
  have h : weight G c v / m v ≤ ∑ w, weight G c w / m w :=
    Finset.single_le_sum (fun w _ => div_nonneg (weight_nonneg G hc w) (hm w).le)
      (Finset.mem_univ v)
  apply (div_le_iff₀ (hm v)).mp
  unfold uniformizationRate
  linarith

/-- The uniformized transition probabilities are nonnegative. -/
theorem uniformizedTransition_nonneg {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (W : Set V) (v w : V) : 0 ≤ uniformizedTransition G c m W v w := by
  classical
  have hden : 0 < uniformizationRate G c m * m v :=
    mul_pos (uniformizationRate_pos G hc m hm) (hm v)
  have hrow : weight G c v / (uniformizationRate G c m * m v) ≤ 1 :=
    (div_le_one hden).mpr (weight_le_uniformizationRate_mul G hc m hm v)
  by_cases hv : v ∈ W
  · simp only [uniformizedTransition, hv, ↓reduceIte]
    apply add_nonneg (div_nonneg (hc.nonneg v w) hden.le)
    split_ifs <;> linarith
  · simp only [uniformizedTransition, hv, ↓reduceIte]
    split_ifs <;> norm_num

/-- The uniformized transition probabilities of each vertex sum to one. -/
theorem sum_uniformizedTransition {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ) (W : Set V)
    (v : V) : ∑ w, uniformizedTransition G c m W v w = 1 := by
  classical
  by_cases hv : v ∈ W
  · simp only [uniformizedTransition, hv, ↓reduceIte]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← weight_eq_sum_univ G hc v]
    simp
  · simp [uniformizedTransition, hv]

/-- On `W`, the uniformization rate times the expected increment of the uniformized transition is
the mass generator. -/
theorem uniformizedTransition_generator {c : V → V → ℝ} (hc : IsCond G c) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (W : Set V) (f : V → ℝ) {v : V} (hv : v ∈ W) :
    uniformizationRate G c m *
      (∑ w, uniformizedTransition G c m W v w * (f w - f v)) = massGenerator G c m f v := by
  classical
  have hrate : uniformizationRate G c m ≠ 0 := (uniformizationRate_pos G hc m hm).ne'
  have hmass : m v ≠ 0 := (hm v).ne'
  have hsum : (∑ w, uniformizedTransition G c m W v w * (f w - f v)) =
      netLaplacian G c f v / (uniformizationRate G c m * m v) := by
    simp only [uniformizedTransition, hv, ↓reduceIte, add_mul, Finset.sum_add_distrib]
    have hdiag : (∑ w, (if w = v then
        1 - weight G c v / (uniformizationRate G c m * m v) else 0) * (f w - f v)) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      by_cases hw : w = v <;> simp [hw]
    rw [hdiag, add_zero, netLaplacian_eq_sum_univ G hc f v, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hsum, massGenerator]
  field_simp [hrate, hmass]

end Uniformization

namespace HeatUniformizationExample

open SimpleGraph

attribute [local instance] HeatGeneratorExample.pathLocallyFinite

/-- On the path `0 – 1 – 2` with unit conductance and unit mass, the uniformization rate is
positive, so the hypotheses of `uniformizationRate_pos` are jointly satisfiable. -/
example : 0 < uniformizationRate (pathGraph 3) (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) :=
  uniformizationRate_pos (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ)) (fun _ => one_pos)

/-- On the path `0 – 1 – 2` with unit conductance and unit mass, the uniformized transition
probabilities on the whole vertex set sum to one in each row. -/
example (v : Fin 3) :
    ∑ w, uniformizedTransition (pathGraph 3) (unitCond (pathGraph 3)) (fun _ => (1 : ℝ))
      Set.univ v w = 1 :=
  sum_uniformizedTransition (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ)) Set.univ v

/-- On the path `0 – 1 – 2` with unit conductance and unit mass, the uniformized transitions
generate the mass generator, so the hypotheses of `uniformizedTransition_generator` are jointly
satisfiable. -/
example (f : Fin 3 → ℝ) (v : Fin 3) :
    uniformizationRate (pathGraph 3) (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) *
      (∑ w, uniformizedTransition (pathGraph 3) (unitCond (pathGraph 3)) (fun _ => (1 : ℝ))
        Set.univ v w * (f w - f v)) =
      massGenerator (pathGraph 3) (unitCond (pathGraph 3)) (fun _ => (1 : ℝ)) f v :=
  uniformizedTransition_generator (pathGraph 3) isCond_unitCond (fun _ => (1 : ℝ))
    (fun _ => one_pos) Set.univ f (Set.mem_univ v)

end HeatUniformizationExample

end LatticeProb.Network
