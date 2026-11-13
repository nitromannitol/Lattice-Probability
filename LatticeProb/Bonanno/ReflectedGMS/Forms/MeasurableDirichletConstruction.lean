/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.MeasurableDirichletConstruction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteMinimizerPointwiseConvergence
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The finite free-cut anchored minimizer is an explicit measurable function of the data

Two things are proved.

The first is the composition of the already checked anchored machinery into a
*self-contained* finite approximation theorem: on a countable vertex type an anchored
boundary and one finite-energy reference function are the only inputs, and the canonical
exhaustion `AnchoredFiniteExhaustion.exhaustionLevel`, the finite level minimizers of
`FiniteDirichletEnergyLimit.exists_level_minimizer_family` and the unconditional
convergence of `FiniteMinimizerPointwiseConvergence.exists_tendsto_levelEnergy` are
produced rather than assumed. No family `L` of levels and no family `F` of level
minimizers is supplied from outside.

The second, and the substantive part, is that on a *finite* vertex type the anchored
minimizer with a prescribed trace on a finite anchor set `B` is given by an explicit
finite linear-algebra formula in the conductances and the boundary data, hence is a
measurable function of them. No measurable selection theorem is used.

The Euler–Lagrange equations of the finite anchored problem are already available:
`FiniteDirichletMinimizers.exists_finite_anchored_minimizer_isHarmonicOn` produces a
minimizer which is discrete harmonic off `B`. Written in the unknowns indexed by the
non-anchor vertices `{x // x ∉ B}` those equations are the square linear system

`dirichletMatrix G B *ᵥ (f restricted to the non-anchors) = boundaryLoad G B u`,

whose matrix is the Dirichlet Laplacian `M i i = ∑_y c(i,y)`, `M i j = -c(i,j)`. The
matrix is nonsingular for the stated reason and for no other: the associated quadratic
form is the Dirichlet energy of the zero extension (summation by parts, proved here as
`energy_eq_sum_mul_lap`), so a kernel vector has zero energy and zero trace on `B`, and
`eq_zero_of_zeroTrace_energy_zero` — the anchored walk estimate — forces it to vanish.
`Matrix.exists_mulVec_eq_zero_iff` converts injectivity into `det ≠ 0`, so the minimizer
is `u` on `B` and `(dirichletMatrix G B)⁻¹ *ᵥ boundaryLoad G B u` off `B`.

Measurability is then entrywise and elementary: determinants and adjugates are finite
sums of finite products of the entries, and the inverse entries are adjugate entries
divided by the determinant. The anchoring hypothesis is required pointwise in the
parameter only; the conductances, the positivity pattern, the connectivity structure and
the boundary data may all vary with the parameter, and `B` is an arbitrary finite anchor
set, possibly empty or everything.
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace MeasurableDirichletConstruction

open Filter Topology MeasureTheory
open scoped Matrix
open FiniteDirichletEnergyLimit FiniteMinimizerPointwiseConvergence

/-! ### The canonical finite anchored approximation, with no supplied level family -/

/-! ### The finite free-cut linear system -/

section FiniteSystem

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The free (non-anchor) vertices of a finite anchored problem: the unknowns of the
Dirichlet linear system. -/
abbrev FreeIndex (B : Finset V) : Type _ := {x : V // x ∉ B}

/-- The Dirichlet Laplacian of the free-cut problem with anchors `B`, indexed by the free
vertices: the diagonal is the total conductance and the off-diagonal entries are minus the
conductances. -/
noncomputable def dirichletMatrix (G : ReflectedWalk.ConductanceGraph V) (B : Finset V) :
    Matrix (FreeIndex B) (FreeIndex B) ℝ :=
  Matrix.of fun i j => if i = j then ∑ y : V, G.c ↑i y else -G.c ↑i ↑j

theorem dirichletMatrix_apply (G : ReflectedWalk.ConductanceGraph V) (B : Finset V)
    (i j : FreeIndex B) :
    dirichletMatrix G B i j = if i = j then ∑ y : V, G.c ↑i y else -G.c ↑i ↑j := rfl

/-- The load vector of the free-cut problem: the prescribed boundary values transported
across the anchor edges. -/
noncomputable def boundaryLoad (G : ReflectedWalk.ConductanceGraph V) (B : Finset V)
    (u : V → ℝ) : FreeIndex B → ℝ :=
  fun i => ∑ a ∈ B, G.c ↑i a * u a

theorem boundaryLoad_apply (G : ReflectedWalk.ConductanceGraph V) (B : Finset V)
    (u : V → ℝ) (i : FreeIndex B) :
    boundaryLoad G B u i = ∑ a ∈ B, G.c ↑i a * u a := rfl

/-- Splitting a sum over all vertices into the anchors and the free vertices. -/
theorem sum_eq_anchor_add_free (B : Finset V) (f : V → ℝ) :
    ∑ y : V, f y = (∑ a ∈ B, f a) + ∑ j : FreeIndex B, f ↑j := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : V => x ∈ B) f]
  congr 1
  exact (Finset.sum_subtype B (fun _ => Iff.rfl) f).symm

/-- **The linear system is the discrete Laplacian with the anchor terms moved to the right
hand side.** For an arbitrary function `h` the matrix applied to the free values of `h` is
the negative Laplacian of `h` plus the anchor load of `h`. -/
theorem dirichletMatrix_mulVec_apply (G : ReflectedWalk.ConductanceGraph V) (B : Finset V)
    (h : V → ℝ) (i : FreeIndex B) :
    (dirichletMatrix G B *ᵥ fun j : FreeIndex B => h ↑j) i
      = (∑ y : V, G.c ↑i y * (h ↑i - h y)) + ∑ a ∈ B, G.c ↑i a * h a := by
  classical
  have hterm : ∀ j : FreeIndex B,
      dirichletMatrix G B i j * h ↑j
        = (if i = j then (∑ y : V, G.c ↑i y) * h ↑i else 0) - G.c ↑i ↑j * h ↑j := by
    intro j
    rw [dirichletMatrix_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, G.c_self]
      ring
    · rw [if_neg hij, if_neg hij]
      ring
  have hsum : ∑ y : V, G.c ↑i y * h y
      = (∑ a ∈ B, G.c ↑i a * h a) + ∑ j : FreeIndex B, G.c ↑i ↑j * h ↑j :=
    sum_eq_anchor_add_free B (fun y => G.c ↑i y * h y)
  have hexp : ∑ y : V, G.c ↑i y * (h ↑i - h y)
      = (∑ y : V, G.c ↑i y) * h ↑i - ∑ y : V, G.c ↑i y * h y := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_sub_distrib, Finset.sum_ite_eq]
  rw [hexp, hsum]
  simp only [Finset.mem_univ, if_true]
  ring

/-! ### Summation by parts on a finite vertex type -/

/-- **The Dirichlet energy is the quadratic form of the discrete Laplacian.** On a finite
vertex type, `Energy g = ∑_x g(x) ∑_y c(x,y) (g(x) − g(y))`. -/
theorem energy_eq_sum_mul_lap (G : ReflectedWalk.ConductanceGraph V) (g : V → ℝ) :
    G.Energy g = ∑ x : V, g x * ∑ y : V, G.c x y * (g x - g y) := by
  have hE : ∑ p : V × V, G.gradSq g p = 2 * G.Energy g := by
    rw [← G.tsum_gradSq_eq g, tsum_fintype]
  have hS : ∑ p : V × V, G.gradSq g p
      = ∑ x : V, ∑ y : V, G.c x y * (g y - g x) ^ 2 := by
    rw [Fintype.sum_prod_type]
    rfl
  have hsplit : ∑ x : V, ∑ y : V, G.c x y * (g y - g x) ^ 2
      = (∑ x : V, ∑ y : V, G.c x y * (g y - g x) * g y)
        - ∑ x : V, ∑ y : V, G.c x y * (g y - g x) * g x := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hP : ∑ x : V, ∑ y : V, G.c x y * (g y - g x) * g y
      = ∑ x : V, ∑ y : V, G.c x y * (g x - g y) * g x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [G.c_symm y x]
  have hQ : ∑ x : V, ∑ y : V, G.c x y * (g y - g x) * g x
      = -∑ x : V, ∑ y : V, G.c x y * (g x - g y) * g x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hT : ∑ x : V, ∑ y : V, G.c x y * (g x - g y) * g x
      = ∑ x : V, g x * ∑ y : V, G.c x y * (g x - g y) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hS, hsplit, hP, hQ, hT] at hE
  linarith

/-! ### Nonsingularity of the free-cut Dirichlet matrix -/

/-- The zero extension of a free vector to all vertices. -/
noncomputable def freeExtend (B : Finset V) (w : FreeIndex B → ℝ) : V → ℝ :=
  fun x => if hx : x ∈ B then 0 else w ⟨x, hx⟩

theorem freeExtend_apply_free (B : Finset V) (w : FreeIndex B → ℝ) (j : FreeIndex B) :
    freeExtend B w ↑j = w j := by
  show (if hx : (↑j : V) ∈ B then (0 : ℝ) else w ⟨↑j, hx⟩) = w j
  rw [dif_neg j.2]

theorem freeExtend_apply_anchor (B : Finset V) (w : FreeIndex B → ℝ) {a : V} (ha : a ∈ B) :
    freeExtend B w a = 0 := dif_pos ha

/-- **The free-cut Dirichlet matrix is injective on an anchored graph.** A kernel vector
extends by zero to a function with zero Dirichlet energy and zero trace on the anchors, and
the anchored walk estimate `eq_zero_of_zeroTrace_energy_zero` makes it vanish. This is the
stated reason for nonsingularity: every free vertex is joined to an anchor. -/
theorem eq_zero_of_dirichletMatrix_mulVec_eq_zero (G : ReflectedWalk.ConductanceGraph V)
    {B : Finset V} (hA : BoundaryAnchored G (↑B : Set V)) {w : FreeIndex B → ℝ}
    (hw : dirichletMatrix G B *ᵥ w = 0) : w = 0 := by
  classical
  set g : V → ℝ := freeExtend B w with hgdef
  have hgfree : ∀ j : FreeIndex B, g ↑j = w j := freeExtend_apply_free B w
  have hgrestrict : (fun j : FreeIndex B => g ↑j) = w := funext hgfree
  have hgA : ∀ a ∈ (↑B : Set V), g a = 0 := fun a ha =>
    freeExtend_apply_anchor B w (Finset.mem_coe.1 ha)
  have hlap : ∀ i : FreeIndex B, ∑ y : V, G.c ↑i y * (g ↑i - g y) = 0 := by
    intro i
    have h1 := dirichletMatrix_mulVec_apply G B g i
    have h2 : (dirichletMatrix G B *ᵥ fun j : FreeIndex B => g ↑j) i = 0 := by
      rw [hgrestrict, hw]
      rfl
    have h3 : ∑ a ∈ B, G.c ↑i a * g a = 0 :=
      Finset.sum_eq_zero fun a ha => by
        rw [hgA a (Finset.mem_coe.2 ha), mul_zero]
    rw [h2, h3, add_zero] at h1
    exact h1.symm
  have hE : G.Energy g = 0 := by
    rw [energy_eq_sum_mul_lap G g]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x ∈ B
    · rw [hgA x (Finset.mem_coe.2 hx), zero_mul]
    · exact mul_eq_zero_of_right (g x) (hlap ⟨x, hx⟩)
  have hzero : g = 0 :=
    eq_zero_of_zeroTrace_energy_zero G hA
      (FiniteDirichletMinimizers.hasFiniteEnergy_of_finite G g) hgA hE
  funext j
  rw [← hgfree j, hzero]
  rfl

/-- **The free-cut Dirichlet matrix is nonsingular on an anchored graph.** -/
theorem det_dirichletMatrix_ne_zero (G : ReflectedWalk.ConductanceGraph V) {B : Finset V}
    (hA : BoundaryAnchored G (↑B : Set V)) : (dirichletMatrix G B).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  exact hv (eq_zero_of_dirichletMatrix_mulVec_eq_zero G hA hmul)

theorem isUnit_det_dirichletMatrix (G : ReflectedWalk.ConductanceGraph V) {B : Finset V}
    (hA : BoundaryAnchored G (↑B : Set V)) : IsUnit (dirichletMatrix G B).det :=
  isUnit_iff_ne_zero.2 (det_dirichletMatrix_ne_zero G hA)

/-! ### The explicit anchored minimizer -/

/-- **The explicit finite free-cut anchored minimizer**: the prescribed data on the anchors
and the solution of the Dirichlet linear system elsewhere. -/
noncomputable def anchoredSolution (G : ReflectedWalk.ConductanceGraph V) (B : Finset V)
    (u : V → ℝ) : V → ℝ :=
  fun x => if hx : x ∈ B then u x
    else ((dirichletMatrix G B)⁻¹ *ᵥ boundaryLoad G B u) ⟨x, hx⟩

theorem anchoredSolution_apply (G : ReflectedWalk.ConductanceGraph V) (B : Finset V)
    (u : V → ℝ) (x : V) :
    anchoredSolution G B u x = if hx : x ∈ B then u x
      else ((dirichletMatrix G B)⁻¹ *ᵥ boundaryLoad G B u) ⟨x, hx⟩ := rfl

/-- **Every anchored discrete harmonic function with the prescribed trace is the explicit
solution.** The Euler–Lagrange equations are exactly the Dirichlet linear system, which has
a unique solution by nonsingularity. -/
theorem eq_anchoredSolution (G : ReflectedWalk.ConductanceGraph V) {B : Finset V}
    (hA : BoundaryAnchored G (↑B : Set V)) {u f : V → ℝ} (htrace : ∀ a ∈ B, f a = u a)
    (hharm : G.IsHarmonicOn f ((↑B : Set V))ᶜ) : f = anchoredSolution G B u := by
  have hsolve : dirichletMatrix G B *ᵥ (fun j : FreeIndex B => f ↑j)
      = boundaryLoad G B u := by
    funext i
    rw [dirichletMatrix_mulVec_apply G B f i]
    have hi : (↑i : V) ∈ ((↑B : Set V))ᶜ := fun hmem => i.2 (Finset.mem_coe.1 hmem)
    have h0 : ∑' y, G.lapTerm f (↑i) y = 0 := (hharm _ hi).2
    rw [tsum_fintype] at h0
    have hneg : ∑ y : V, G.c ↑i y * (f ↑i - f y) = 0 := by
      have hrw : ∑ y : V, G.c ↑i y * (f ↑i - f y) = -∑ y : V, G.lapTerm f (↑i) y := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [ReflectedWalk.ConductanceGraph.lapTerm]
        ring
      rw [hrw, h0, neg_zero]
    rw [hneg, zero_add, boundaryLoad_apply]
    exact Finset.sum_congr rfl fun a ha => by rw [htrace a ha]
  have hinv : (fun j : FreeIndex B => f ↑j)
      = (dirichletMatrix G B)⁻¹ *ᵥ boundaryLoad G B u := by
    rw [← hsolve, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_det_dirichletMatrix G hA), Matrix.one_mulVec]
  funext x
  rw [anchoredSolution_apply]
  by_cases hx : x ∈ B
  · rw [dif_pos hx]
    exact htrace x hx
  · rw [dif_neg hx]
    exact congrFun hinv ⟨x, hx⟩

/-- **The explicit solution is the anchored Dirichlet minimizer.** It carries the
prescribed trace on the anchors, is discrete harmonic at every free vertex, and minimizes
the Dirichlet energy against every competitor with that trace. -/
theorem anchoredSolution_spec (G : ReflectedWalk.ConductanceGraph V) {B : Finset V}
    (hA : BoundaryAnchored G (↑B : Set V)) (u : V → ℝ) :
    (∀ a ∈ B, anchoredSolution G B u a = u a) ∧
      G.IsHarmonicOn (anchoredSolution G B u) ((↑B : Set V))ᶜ ∧
      (∀ h : V → ℝ, (∀ a ∈ B, h a = u a) →
        G.Energy (anchoredSolution G B u) ≤ G.Energy h) := by
  obtain ⟨f, htrace, hharm, hmin⟩ :=
    FiniteDirichletMinimizers.exists_finite_anchored_minimizer_isHarmonicOn G hA u
  have htr : ∀ a ∈ B, f a = u a := fun a ha => htrace a (Finset.mem_coe.2 ha)
  have hfeq : f = anchoredSolution G B u := eq_anchoredSolution G hA htr hharm
  rw [← hfeq]
  exact ⟨htr, hharm, fun h hh => hmin h fun a ha => hh a (Finset.mem_coe.1 ha)⟩

end FiniteSystem

/-! ### Measurability of finite determinants, adjugates and inverses -/

section MatrixMeasurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The determinant of a matrix with measurable entries is measurable: it is a finite sum
of finite products of the entries. -/
theorem measurable_det_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {M : Ω → Matrix n n ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j) :
    Measurable fun ω => (M ω).det := by
  simp only [Matrix.det_apply']
  exact Finset.measurable_sum _ fun σ _ =>
    Measurable.const_mul (Finset.measurable_prod _ fun i _ => hM _ _) _

/-- Adjugate entries of a matrix with measurable entries are measurable. -/
theorem measurable_adjugate_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {M : Ω → Matrix n n ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j) (i j : n) :
    Measurable fun ω => (M ω).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine measurable_det_of_entries
    (M := fun ω => (M ω).updateRow j (Pi.single i 1)) ?_
  intro k l
  simp only [Matrix.updateRow_apply]
  by_cases hk : k = j
  · simp only [if_pos hk]
    exact measurable_const
  · simp only [if_neg hk]
    exact hM k l

/-- Entries of the inverse of a matrix with measurable entries are measurable: they are
adjugate entries divided by the determinant. -/
theorem measurable_inv_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {M : Ω → Matrix n n ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j) (i j : n) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  have hpt : ∀ ω, (M ω)⁻¹ i j = (M ω).adjugate i j / (M ω).det := by
    intro ω
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul, div_eq_inv_mul]
  simp only [hpt]
  exact (measurable_adjugate_of_entries hM i j).div (measurable_det_of_entries hM)

end MatrixMeasurability

/-! ### The anchored minimizer is a measurable function of the data -/

section MeasurableMinimizer

variable {V : Type*} [Fintype V] [DecidableEq V] {Ω : Type*} [MeasurableSpace Ω]

/-- Entries of the free-cut Dirichlet matrix are measurable in the conductance data. -/
theorem measurable_dirichletMatrix_entry {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) (B : Finset V)
    (i j : FreeIndex B) :
    Measurable fun ω => dirichletMatrix (G ω) B i j := by
  simp only [dirichletMatrix_apply]
  by_cases hij : i = j
  · simp only [if_pos hij]
    exact Finset.measurable_sum _ fun y _ => hG _ y
  · simp only [if_neg hij]
    exact (hG _ _).neg

/-- The load vector is measurable in the conductance and boundary data. -/
theorem measurable_boundaryLoad {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) (B : Finset V)
    {u : Ω → V → ℝ} (hu : ∀ x : V, Measurable fun ω => u ω x) (i : FreeIndex B) :
    Measurable fun ω => boundaryLoad (G ω) B (u ω) i := by
  simp only [boundaryLoad_apply]
  exact Finset.measurable_sum _ fun a _ => (hG _ a).mul (hu a)

/-- **The explicit anchored minimizer is measurable in the data**, vertex by vertex. The
anchoring hypothesis is not needed for this: the formula is measurable regardless, and the
anchoring is what makes it the minimizer. -/
theorem measurable_anchoredSolution {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) (B : Finset V)
    {u : Ω → V → ℝ} (hu : ∀ x : V, Measurable fun ω => u ω x) (x : V) :
    Measurable fun ω => anchoredSolution (G ω) B (u ω) x := by
  simp only [anchoredSolution_apply]
  by_cases hx : x ∈ B
  · simp only [dif_pos hx]
    exact hu x
  · simp only [dif_neg hx]
    have hpt : ∀ ω : Ω,
        ((dirichletMatrix (G ω) B)⁻¹ *ᵥ boundaryLoad (G ω) B (u ω)) ⟨x, hx⟩
          = ∑ j : FreeIndex B, (dirichletMatrix (G ω) B)⁻¹ ⟨x, hx⟩ j *
              boundaryLoad (G ω) B (u ω) j :=
      fun ω => Matrix.mulVec_apply_eq_sum _ _ _
    simp only [hpt]
    exact Finset.measurable_sum _ fun j _ =>
      (measurable_inv_of_entries (measurable_dirichletMatrix_entry hG B) _ j).mul
        (measurable_boundaryLoad hG B hu j)

end MeasurableMinimizer

end MeasurableDirichletConstruction

end ReflectedGMS
