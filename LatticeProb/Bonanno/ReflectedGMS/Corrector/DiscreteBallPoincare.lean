/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.DiscreteBallPoincare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootDensities
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Analysis.Real.Sqrt

/-!
# A discrete Poincaré inequality on a graph ball

This module supplies the deterministic **gradient error → vertex-value error** bridge that
the harmonic-coordinate assembly needs in order to turn specific-energy control of
`θ = φ_m − Φ` into control of the graph-neighbourhood error

`⨆_{H ∈ B(H_0, radius+1)} min(1, |φ_m(H) − φ_m(H_0) − Φ(H)|)`

of `HarmonicMainStatement.graphNeighborhoodError` (equivalently, of
`HarmonicCoordinateAssembly.markedGraphNeighborhoodError`).

## Why this is not the `BouRabeeGwynne` column estimate

`BouRabeeGwynne.OrthogonalTiling.column_poincare_measure_bound` is a *weak-type* bound: it
bounds the `(d−1)`-Hausdorff measure of the projected shadow of the cells on which `|f|` is
large, for an `f` vanishing **outside** a finite interior region `A`, on a genuine
`OrthogonalTiling` (convex polytope cells, an injective position map, codimension-one facets
and conductance `facetVolume / edgeLength`).  Three things make it unusable here:

* the conclusion is about a measure of a set of *spatial points*, not a supremum over
  *vertices* — a set of cells with large `|f|` is allowed, provided their shadow is thin;
* the normalisation is Friedrichs (zero boundary data), while the neighbourhood error is
  anchored at the interior root `H_0` and is unconstrained on the boundary of the ball;
* `ReflectedGMS.IndexedCells` carries arbitrary `NonemptyCompacts` cells and a *free*
  conductance `F.graph.c`, so no `OrthogonalTiling` structure exists on it at all.

The statement below is the one that does transfer: an anchored, strong (supremum) Poincaré
inequality on a graph-metric ball of a `ReflectedWalk.ConductanceGraph`, proved by
telescoping along a geodesic walk.

## Contents

* `endpointEnergy` — the numerator `∑_{H' ∼ H} c(H,H') |g(H')−g(H)|²` of the manuscript
  specific-energy density `RootDensities.specificEnergyDensity`, exposed on its own
  (`specificEnergyDensity_eq_endpointEnergy_div` is definitional).
* `norm_sub_le_of_endpointEnergy_le` — a single edge: an endpoint-energy bound at `v`
  together with a conductance lower bound on `(v,w)` bounds `|g(w) − g(v)|`.
* `norm_sub_le_length_mul` — telescoping along a walk that stays in a prescribed set.
* `norm_le_of_ball_endpointEnergy_le` — **the discrete Poincaré inequality**: if `g` vanishes
  at the centre `r`, the endpoint energy is at most `E` on the ball `B(r,k+1)` and every
  conductance inside that ball is at least `κ > 0`, then `|g(v)| ≤ k √(E/κ)` throughout the
  ball.
* `norm_le_of_ball_specificEnergyDensity_le` — the same with the manuscript density
  `ρ_g ≤ ρ` and a cell-area upper bound `a`, giving `|g(v)| ≤ k √(2 ρ a / κ)`.
* `iSup_min_one_norm_le_of_ball` — the conclusion already in the shape of the neighbourhood
  error: the supremum of `min 1 ‖g v‖` over the ball subtype.

Nothing here is probabilistic.  What still separates this from the open assembly input
`MarkedNeighborhoodConvergence` is that the manuscript specific-energy hypothesis
`MarkedSpecificEnergyConvergence` controls `ρ` at the **root cell only**, whereas the three
hypotheses below are uniform over the ball; supplying them from the root density is a
re-rooting (mass-transport) statement, not a Poincaré inequality.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ReflectedGMS.DiscreteBallPoincare

open RootDensities StatementIngredients

variable {V : Type*}

/-! ### The endpoint energy at a vertex -/

/-- The endpoint energy of `g` at a cell: the manuscript sum `∑_{H' ∼ H} c(H,H') |g(H')−g(H)|²`,
i.e. the numerator of `RootDensities.specificEnergyDensity` before dividing by `2 a_H`. -/
noncomputable def endpointEnergy (F : IndexedCells V) (g : V → Plane) (v : V) : ℝ≥0∞ :=
  ∑' w : V, ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖g w - g v‖ ^ 2)

/-- The manuscript density is the endpoint energy over `2 a_H`.  This is definitional. -/
theorem specificEnergyDensity_eq_endpointEnergy_div (F : IndexedCells V) (g : V → Plane)
    (v : V) :
    specificEnergyDensity F g v =
      endpointEnergy F g v / (2 * ENNReal.ofReal (cellArea F v)) := rfl

/-- The endpoint energy only sees differences, so an additive constant does not change it.
This is what makes the *normalised* field `normalizedPhi F D r m · − Φ ·` appearing in the
neighbourhood error have the *same* specific-energy density as the unnormalised gradient
error `φ_m · − Φ ·` of `MarkedSpecificEnergyConvergence`. -/
theorem endpointEnergy_sub_const (F : IndexedCells V) (g : V → Plane) (z : Plane) (v : V) :
    endpointEnergy F (fun x => g x - z) v = endpointEnergy F g v := by
  unfold endpointEnergy
  simp only [sub_sub_sub_cancel_right]

/-- The manuscript density is likewise invariant under an additive constant. -/
theorem specificEnergyDensity_sub_const (F : IndexedCells V) (g : V → Plane) (z : Plane)
    (v : V) :
    specificEnergyDensity F (fun x => g x - z) v = specificEnergyDensity F g v := by
  rw [specificEnergyDensity_eq_endpointEnergy_div, specificEnergyDensity_eq_endpointEnergy_div,
    endpointEnergy_sub_const]

/-- A single edge contributes at most the whole endpoint energy. -/
theorem le_endpointEnergy (F : IndexedCells V) (g : V → Plane) (v w : V) :
    ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖g w - g v‖ ^ 2) ≤
      endpointEnergy F g v :=
  ENNReal.le_tsum (f := fun u : V =>
    ENNReal.ofReal (F.graph.c v u) * ENNReal.ofReal (‖g u - g v‖ ^ 2)) w

/-- `ENNReal.ofReal` of `2 ρ a`, in the factored shape produced by the division bound. -/
theorem ofReal_two_mul_mul {ρ a : ℝ} (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (2 * ρ * a) = ENNReal.ofReal ρ * (2 * ENNReal.ofReal a) := by
  rw [show (2 : ℝ) * ρ * a = ρ * (2 * a) by ring, ENNReal.ofReal_mul hρ,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp

/-- The manuscript density bound `ρ_g(H) ≤ ρ` together with an upper bound `a` on the cell
area gives the endpoint-energy bound `∑_{H' ∼ H} c |g(H')−g(H)|² ≤ 2 ρ a`.  No positivity of
the cell area is needed: the division bound is inverted through
`ENNReal.div_le_iff_le_mul`, whose side conditions are discharged by finiteness alone. -/
theorem endpointEnergy_le_of_specificEnergyDensity_le (F : IndexedCells V) (g : V → Plane)
    (v : V) {ρ a : ℝ} (hρ0 : 0 ≤ ρ) (hav : cellArea F v ≤ a)
    (h : specificEnergyDensity F g v ≤ ENNReal.ofReal ρ) :
    endpointEnergy F g v ≤ ENNReal.ofReal (2 * ρ * a) := by
  have hdiv : endpointEnergy F g v / (2 * ENNReal.ofReal (cellArea F v)) ≤
      ENNReal.ofReal ρ := by
    rw [← specificEnergyDensity_eq_endpointEnergy_div F g v]
    exact h
  have hb0 : (2 * ENNReal.ofReal (cellArea F v)) ≠ 0 ∨ ENNReal.ofReal ρ ≠ ∞ :=
    Or.inr ENNReal.ofReal_ne_top
  have hbt : (2 * ENNReal.ofReal (cellArea F v)) ≠ ∞ ∨ ENNReal.ofReal ρ ≠ 0 :=
    Or.inl (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
  have hmul := (ENNReal.div_le_iff_le_mul hb0 hbt).mp hdiv
  refine hmul.trans ?_
  rw [ofReal_two_mul_mul (a := a) hρ0]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hav))

/-! ### One edge -/

/-- The single-edge Poincaré step: the endpoint energy at `v` bounds the increment of `g`
across any edge out of `v` whose conductance is at least `κ > 0`. -/
theorem norm_sub_le_of_endpointEnergy_le (F : IndexedCells V) (g : V → Plane) {v w : V}
    {E κ : ℝ} (hE0 : 0 ≤ E) (hκ : 0 < κ) (hc : κ ≤ F.graph.c v w)
    (hE : endpointEnergy F g v ≤ ENNReal.ofReal E) :
    ‖g w - g v‖ ≤ Real.sqrt (E / κ) := by
  have hcnn : (0 : ℝ) ≤ F.graph.c v w := F.graph.c_nonneg v w
  have hmul : ENNReal.ofReal (F.graph.c v w * ‖g w - g v‖ ^ 2) ≤ ENNReal.ofReal E := by
    rw [ENNReal.ofReal_mul hcnn]
    exact (le_endpointEnergy F g v w).trans hE
  have hreal : F.graph.c v w * ‖g w - g v‖ ^ 2 ≤ E :=
    (ENNReal.ofReal_le_ofReal_iff hE0).mp hmul
  have hκle : κ * ‖g w - g v‖ ^ 2 ≤ E :=
    (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans hreal
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hd : κ * (E / κ) = E := by field_simp
  have hcancel : κ * ‖g w - g v‖ ^ 2 ≤ κ * (E / κ) := by rw [hd]; exact hκle
  have hx : ‖g w - g v‖ ^ 2 ≤ E / κ := le_of_mul_le_mul_left hcancel hκ
  exact (Real.le_sqrt (norm_nonneg _) (div_nonneg hE0 hκ.le)).mpr hx

/-! ### Telescoping along a walk -/

/-- Telescoping and the triangle inequality along a walk all of whose vertices lie in a set
on which every edge increment is at most `M`. -/
theorem norm_sub_le_length_mul {G : SimpleGraph V} (g : V → Plane) (S : Set V) {M : ℝ}
    (hb : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → ‖g y - g x‖ ≤ M)
    {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ S) :
    ‖g v - g u‖ ≤ p.length * M := by
  revert hp
  induction p with
  | nil => intro _; simp
  | @cons a b c hadj q ih =>
    intro hp
    have haS : a ∈ S := hp a (SimpleGraph.Walk.start_mem_support _)
    have hbS : b ∈ S := by
      refine hp b ?_
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr q.start_mem_support
    have hq : ∀ x ∈ q.support, x ∈ S := by
      intro x hx
      refine hp x ?_
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr hx
    have h1 : ‖g c - g b‖ ≤ q.length * M := ih hq
    have h2 : ‖g b - g a‖ ≤ M := hb a haS b hbS hadj
    rw [SimpleGraph.Walk.length_cons]
    calc ‖g c - g a‖ = ‖(g c - g b) + (g b - g a)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖g c - g b‖ + ‖g b - g a‖ := norm_add_le _ _
      _ ≤ (q.length : ℝ) * M + M := add_le_add h1 h2
      _ = ((q.length + 1 : ℕ) : ℝ) * M := by push_cast; ring

/-! ### The discrete Poincaré inequality on a graph ball -/

/-- **Discrete Poincaré inequality on a graph ball.**  Let `g` vanish at the centre `r`.  If
the endpoint energy of `g` is at most `E` at every vertex of the graph ball
`B(r, k+1) = {x | edist x r ≤ k}` and every edge inside that ball has conductance at least
`κ > 0`, then `‖g v‖ ≤ k √(E/κ)` for every `v` in the ball.

This is the *strong* (supremum) form the neighbourhood error needs, anchored at the interior
vertex `r` rather than at the boundary of the ball. -/
theorem norm_le_of_ball_endpointEnergy_le [DecidableEq V] (F : IndexedCells V) (g : V → Plane)
    (r : V) (k : ℕ) (hg : g r = 0) {E κ : ℝ} (hE0 : 0 ≤ E) (hκ : 0 < κ)
    (hE : ∀ x ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞),
      endpointEnergy F g x ≤ ENNReal.ofReal E)
    (hc : ∀ x ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞),
      ∀ y ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞),
      F.graph.toSimpleGraph.Adj x y → κ ≤ F.graph.c x y)
    {v : V} (hv : v ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞)) :
    ‖g v‖ ≤ k * Real.sqrt (E / κ) := by
  have hcast : ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := Nat.cast_add_one k
  have hsucc : (k : ℕ∞) < ((k + 1 : ℕ) : ℕ∞) := by
    rw [hcast]
    exact ENat.lt_natCast_add_one_iff.mpr le_rfl
  have hvk : F.graph.toSimpleGraph.edist r v ≤ (k : ℕ∞) := by
    have h1 : F.graph.toSimpleGraph.edist v r < (k : ℕ∞) + 1 := by
      rw [← hcast]
      exact SimpleGraph.mem_ball.mp hv
    have h2 : F.graph.toSimpleGraph.edist v r ≤ (k : ℕ∞) :=
      ENat.lt_natCast_add_one_iff.mp h1
    rwa [SimpleGraph.edist_comm] at h2
  have hne : F.graph.toSimpleGraph.edist r v ≠ ⊤ := by
    intro htop
    rw [htop] at hvk
    exact (ENat.natCast_ne_top k) (top_le_iff.mp hvk)
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  have hpk : p.length ≤ k := by
    have hle : ((p.length : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by rw [hp]; exact hvk
    exact_mod_cast hle
  have hsupp : ∀ x ∈ p.support, x ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞) := by
    intro x hx
    have h1 : F.graph.toSimpleGraph.edist r x ≤ (((p.takeUntil x hx).length : ℕ) : ℕ∞) :=
      SimpleGraph.edist_le (p.takeUntil x hx)
    have h2 : (p.takeUntil x hx).length ≤ k :=
      (p.length_takeUntil_le_length hx).trans hpk
    have h3 : F.graph.toSimpleGraph.edist r x ≤ (k : ℕ∞) := by
      refine h1.trans ?_
      exact_mod_cast h2
    rw [SimpleGraph.mem_ball, SimpleGraph.edist_comm]
    exact lt_of_le_of_lt h3 hsucc
  have hb : ∀ x ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞),
      ∀ y ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞),
      F.graph.toSimpleGraph.Adj x y → ‖g y - g x‖ ≤ Real.sqrt (E / κ) := by
    intro x hx y hy hadj
    exact norm_sub_le_of_endpointEnergy_le F g hE0 hκ (hc x hx y hy hadj) (hE x hx)
  have hmain := norm_sub_le_length_mul (G := F.graph.toSimpleGraph) g
    (F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞)) hb p hsupp
  rw [hg, sub_zero] at hmain
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  exact_mod_cast hpk

/-- The discrete Poincaré inequality in terms of the manuscript specific-energy density
`ρ_g(H) = (2 a_H)⁻¹ ∑_{H' ∼ H} c(H,H') |g(H')−g(H)|²`: with `ρ_g ≤ ρ` and `a_H ≤ a` on the
ball and conductances at least `κ > 0` inside it, `‖g v‖ ≤ k √(2 ρ a / κ)`. -/
theorem norm_le_of_ball_specificEnergyDensity_le [DecidableEq V] (F : IndexedCells V)
    (g : V → Plane) (r : V) (k : ℕ) (hg : g r = 0) {ρ a κ : ℝ} (hρ0 : 0 ≤ ρ) (hκ : 0 < κ)
    (hρ : ∀ x ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞),
      specificEnergyDensity F g x ≤ ENNReal.ofReal ρ)
    (ha : ∀ x ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞), cellArea F x ≤ a)
    (hc : ∀ x ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞),
      ∀ y ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞),
      F.graph.toSimpleGraph.Adj x y → κ ≤ F.graph.c x y)
    {v : V} (hv : v ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞)) :
    ‖g v‖ ≤ k * Real.sqrt (2 * ρ * a / κ) := by
  have hrpos : (0 : ℕ∞) < ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.succ_pos k
  have hrmem : r ∈ F.graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞) :=
    SimpleGraph.mem_ball_self hrpos
  have ha0 : (0 : ℝ) ≤ a := by
    refine le_trans ?_ (ha r hrmem)
    unfold StatementIngredients.cellArea
    exact ENNReal.toReal_nonneg
  have hE0 : (0 : ℝ) ≤ 2 * ρ * a := mul_nonneg (mul_nonneg (by norm_num) hρ0) ha0
  refine norm_le_of_ball_endpointEnergy_le F g r k hg hE0 hκ ?_ hc hv
  intro x hx
  exact endpointEnergy_le_of_specificEnergyDensity_le F g x hρ0 (ha x hx) (hρ x hx)

/-! ### The neighbourhood-error shape -/

/-- The conclusion in the exact shape of `HarmonicMainStatement.graphNeighborhoodError` and
`HarmonicCoordinateAssembly.markedGraphNeighborhoodError`: a bound on the supremum of
`min 1 ‖g v‖` over the ball `B(r, radius+1)` of the graph metric. -/
theorem iSup_min_one_norm_le_of_ball [DecidableEq V] (F : IndexedCells V) (g : V → Plane)
    (r : V) (radius : ℕ) (hg : g r = 0) {ρ a κ : ℝ} (hρ0 : 0 ≤ ρ) (hκ : 0 < κ)
    (hρ : ∀ x ∈ F.graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞),
      specificEnergyDensity F g x ≤ ENNReal.ofReal ρ)
    (ha : ∀ x ∈ F.graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞), cellArea F x ≤ a)
    (hc : ∀ x ∈ F.graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞),
      ∀ y ∈ F.graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞),
      F.graph.toSimpleGraph.Adj x y → κ ≤ F.graph.c x y) :
    (⨆ v : F.graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞), min 1 ‖g v.val‖) ≤
      radius * Real.sqrt (2 * ρ * a / κ) := by
  have hrpos : (0 : ℕ∞) < ((radius + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.succ_pos radius
  have hmem : r ∈ F.graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞) :=
    SimpleGraph.mem_ball_self hrpos
  have hne : Nonempty (F.graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞)) := ⟨⟨r, hmem⟩⟩
  refine ciSup_le ?_
  intro v
  refine (min_le_right _ _).trans ?_
  exact norm_le_of_ball_specificEnergyDensity_le F g r radius hg hρ0 hκ hρ ha hc v.property

/-! ### Graph balls are finite, so the two geometric constants always exist

The area and conductance hypotheses of the Poincaré inequality are not extra assumptions:
under the local finiteness clause of `Geometry` the ball is a finite set, so a finite
`a` and a positive `κ` always exist.  Only the *density* hypothesis is substantive. -/

end ReflectedGMS.DiscreteBallPoincare
