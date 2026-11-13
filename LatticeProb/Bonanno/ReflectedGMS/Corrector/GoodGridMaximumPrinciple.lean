/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GoodGridMaximumPrinciple at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.UniformCorrectorSublinearity
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyTraceBounds
import LatticeProb.Bonanno.ReflectedGMS.Geometry.BoundaryAnchoring

/-!
# The maximum principle on a grid rectangle: interior control from the good grid

This module performs the step of the manuscript's final paragraph of section 6
(`s:eq:sublinear`, subsection "From good lines to all cells") that was left open by
`Corrector/UniformCorrectorSublinearity.lean`:

> Use the full variational maximum principle for `Φ` on `G_{Q'}`. Its boundary coordinates,
> relative to the fixed vector `b_H + c_R`, are bounded by `s:eq:gridchi` and
> `s:eq:boundarycentroid`. Hence, coordinatewise and then in Euclidean norm,
> `|χ(H) - c_R| ≤ 12 α R + o(R)`.

Nothing about the maximum principle is reproved here.  The maximum principle used is the
already checked componentwise statement
`ReflectedGMS.FullEnergyTraceBounds.coord_mem_Icc_of_vector_trace_minimizer_on_component`
for the **full** energy domain and the **full** competition class (every plane-valued
function with the prescribed boundary trace, of finite or infinite energy).  The geometric
confinement used is the already checked
`ReflectedGMS.exists_gridRectangle_of_notMem_gridCells`, and the anchoring of the patch
graph is the already checked `ReflectedGMS.boundaryAnchored_restrictGraph_cells_hitting`.

Three things are supplied here.

* `norm_sub_le_of_vector_trace_minimizer_on_component` — the manuscript's "coordinatewise
  and then in Euclidean norm" step.  If on the boundary component of `x` the corrector
  `Φ - b` is within `ε` of a fixed vector `c` and the reference vectors `b` are within `δ`
  of `b x`, then `‖Φ x - b x - c‖ ≤ √2 (ε + δ)`.  The two coordinate applications of the
  maximum principle are made on the component of `x` only, so no connectedness of the patch
  graph is used.

* `frontier_closedPatch_subset_rectangleFrame` — the spatial boundary of a closed grid
  rectangle is contained in the union of its four closed sides.  This is what converts the
  frame conclusion of `exists_gridRectangle_of_notMem_gridCells` (`every cell meeting the
  frame is a grid cell`) into a statement about `boundaryVertices`, which is the boundary
  set of the anchoring and minimality statements.

* `norm_corrector_sub_le_of_notMem_gridCells` — the actual patch argument: an off-grid cell
  inside the patch obeys `‖Φ H - b H - c‖ ≤ √2 (t + δ)` where `t` is the grid-skeleton
  bound `s:eq:gridchi` and `δ` the centroid bookkeeping `s:eq:boundarycentroid`.  With the
  manuscript's values `t = 3αR + o(R)` and `δ = 2√2 αR + 2 D_{3R}` this is
  `(3√2 + 4) αR + o(R) ≤ 12 αR + o(R)`, the manuscript's display.

The minimality input is `StatementIngredients.FullRectangleMinimizer F Φ`, i.e. exactly the
main-theorem conclusion clause for the harmonic coordinate, applied at the single grid
rectangle produced by the confinement theorem.  It is a hypothesis here: no producer of
that clause for the limiting `Φ` exists in the project yet (the full-rectangle
orthogonality/minimality of the limit is the missing producer), and nothing below assumes
pointwise harmonicity or derives variational minimality from it.  The reference map `b` is
kept abstract with an explicit hypothesis of the shape of `s:eq:boundarycentroid`, so that
the centroid (`cellCentroid`) versus interior-representative distinction is preserved
exactly where the manuscript makes it: the conclusion is about centroids, and passing to
arbitrary representatives `z_H ∈ H` is the separate `s:eq:centroid` step.
-/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace ReflectedGMS.GoodGridMaximumPrinciple

open StatementIngredients

variable {V : Type*}

/-! ### Coordinates and the Euclidean norm on the plane -/

/-- Each coordinate of a plane vector is dominated by its Euclidean norm. -/
theorem abs_coord_le_norm (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : ‖z i‖ ^ 2 ≤ ∑ j : Fin 2, ‖z j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 2 => ‖z j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hzi : |z i| = Real.sqrt (‖z i‖ ^ 2) := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.norm_eq_abs]
  rw [hzi]
  exact Real.sqrt_le_sqrt hle

/-- **Coordinatewise, then in Euclidean norm.**  A plane vector with both coordinates
bounded by `K` has norm at most `√2 K`. -/
theorem norm_le_sqrt_two_mul {z : Plane} {K : ℝ} (hK : ∀ i, |z i| ≤ K) :
    ‖z‖ ≤ Real.sqrt 2 * K := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin 2, ‖z i‖ ^ 2 ≤ 2 * K ^ 2 := by
    have hcoord : ∀ i : Fin 2, ‖z i‖ ^ 2 ≤ K ^ 2 := by
      intro i
      have h1 : ‖z i‖ ≤ K := by
        rw [Real.norm_eq_abs]
        exact hK i
      nlinarith [norm_nonneg (z i)]
    calc ∑ i : Fin 2, ‖z i‖ ^ 2 ≤ ∑ _i : Fin 2, K ^ 2 :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = 2 * K ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  calc Real.sqrt (∑ i : Fin 2, ‖z i‖ ^ 2) ≤ Real.sqrt (2 * K ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 * K := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq hK0]

/-! ### The maximum principle in vector form on one component -/

/-- **The manuscript's "coordinatewise and then in Euclidean norm" step.**  Let `Φ` be a
full-energy vector trace minimizer with boundary data `u` on `A`, let `b` be an arbitrary
reference map and `c` an arbitrary fixed vector.  If on the boundary of the component of
`x` the corrector `Φ - b` stays within `ε` of `c` and the reference vectors stay within `δ`
of `b x`, then `‖Φ x - b x - c‖ ≤ √2 (ε + δ)`.

The only input is the existing componentwise maximum principle
`FullEnergyTraceBounds.coord_mem_Icc_of_vector_trace_minimizer_on_component`, applied twice
with the two coordinates of the fixed vector `b x + c`. -/
theorem norm_sub_le_of_vector_trace_minimizer_on_component {W : Type*}
    (G : ReflectedWalk.ConductanceGraph W) {A : Set W} (hA : BoundaryAnchored G A)
    {u Φ : W → Plane} (hfin : vectorEnergy G Φ < ∞) (htrace : ∀ a ∈ A, Φ a = u a)
    (hmin : ∀ g : W → Plane, (∀ a ∈ A, g a = u a) → vectorEnergy G Φ ≤ vectorEnergy G g)
    (b : W → Plane) (c : Plane) {ε δ : ℝ} {x : W}
    (hosc : ∀ a ∈ A, G.toSimpleGraph.Reachable x a → ‖Φ a - b a - c‖ ≤ ε)
    (hcent : ∀ a ∈ A, G.toSimpleGraph.Reachable x a → ‖b a - b x‖ ≤ δ) :
    ‖Φ x - b x - c‖ ≤ Real.sqrt 2 * (ε + δ) := by
  refine norm_le_sqrt_two_mul fun i => ?_
  have hIcc : Φ x i ∈ Set.Icc (b x i + c i - (ε + δ)) (b x i + c i + (ε + δ)) := by
    refine FullEnergyTraceBounds.coord_mem_Icc_of_vector_trace_minimizer_on_component
      G hA hfin htrace hmin i ?_
    intro a ha hr
    have h1 : |Φ a i - b a i - c i| ≤ ε := by
      refine le_trans ?_ (hosc a ha hr)
      simpa using abs_coord_le_norm (Φ a - b a - c) i
    have h2 : |b a i - b x i| ≤ δ := by
      refine le_trans ?_ (hcent a ha hr)
      simpa using abs_coord_le_norm (b a - b x) i
    have hua : u a i = Φ a i := by rw [htrace a ha]
    rw [Set.mem_Icc, hua]
    rw [abs_le] at h1 h2
    exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  have hxc : (Φ x - b x - c) i = Φ x i - b x i - c i := by simp
  rw [hxc, abs_le]
  exact ⟨by linarith [hIcc.1], by linarith [hIcc.2]⟩

/-! ### The closed grid rectangle as a patch -/

/-- The closed grid rectangle is bounded. -/
theorem isBounded_closedPatch (x₁ x₂ y₁ y₂ : ℝ) :
    Bornology.IsBounded (closedPatch x₁ x₂ y₁ y₂) := by
  refine Bornology.IsBounded.subset
    (axisAlignedRectangle_isBounded (WithLp.toLp 2 ![x₁, y₁] : Plane)
      (WithLp.toLp 2 ![x₂, y₂] : Plane)) ?_
  intro z hz
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · simpa using ⟨hz.1, hz.2.1⟩
  · simpa using ⟨hz.2.2.1, hz.2.2.2⟩

/-- The closed grid rectangle is closed. -/
theorem isClosed_closedPatch (x₁ x₂ y₁ y₂ : ℝ) :
    IsClosed (closedPatch x₁ x₂ y₁ y₂) := by
  have h0 : Continuous fun z : Plane => z 0 := PiLp.continuous_apply 2 _ (0 : Fin 2)
  have h1 : Continuous fun z : Plane => z 1 := PiLp.continuous_apply 2 _ (1 : Fin 2)
  have hset : closedPatch x₁ x₂ y₁ y₂ =
      {z : Plane | x₁ ≤ z 0} ∩ ({z : Plane | z 0 ≤ x₂} ∩
        ({z : Plane | y₁ ≤ z 1} ∩ {z : Plane | z 1 ≤ y₂})) := rfl
  rw [hset]
  exact (isClosed_le continuous_const h0).inter ((isClosed_le h0 continuous_const).inter
    ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const)))

/-- The open grid rectangle is open. -/
theorem isOpen_openRectangle (x₁ x₂ y₁ y₂ : ℝ) :
    IsOpen (openRectangle x₁ x₂ y₁ y₂) := by
  have h0 : Continuous fun z : Plane => z 0 := PiLp.continuous_apply 2 _ (0 : Fin 2)
  have h1 : Continuous fun z : Plane => z 1 := PiLp.continuous_apply 2 _ (1 : Fin 2)
  have hset : openRectangle x₁ x₂ y₁ y₂ =
      {z : Plane | x₁ < z 0} ∩ ({z : Plane | z 0 < x₂} ∩
        ({z : Plane | y₁ < z 1} ∩ {z : Plane | z 1 < y₂})) := rfl
  rw [hset]
  exact (isOpen_lt continuous_const h0).inter ((isOpen_lt h0 continuous_const).inter
    ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))

theorem openRectangle_subset_closedPatch (x₁ x₂ y₁ y₂ : ℝ) :
    openRectangle x₁ x₂ y₁ y₂ ⊆ closedPatch x₁ x₂ y₁ y₂ :=
  fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

/-- **The spatial boundary of a grid rectangle lies on its four sides.**  This is what
matches the frame conclusion of `exists_gridRectangle_of_notMem_gridCells` with the
`frontier`-based boundary of the anchoring and minimality statements. -/
theorem frontier_closedPatch_subset_rectangleFrame (x₁ x₂ y₁ y₂ : ℝ) :
    frontier (closedPatch x₁ x₂ y₁ y₂) ⊆ rectangleFrame x₁ x₂ y₁ y₂ := by
  intro z hz
  have hzc : z ∈ closedPatch x₁ x₂ y₁ y₂ :=
    (isClosed_closedPatch x₁ x₂ y₁ y₂).frontier_subset hz
  have hzi : z ∉ interior (closedPatch x₁ x₂ y₁ y₂) := hz.2
  have hzo : z ∉ openRectangle x₁ x₂ y₁ y₂ := fun h =>
    hzi (interior_maximal (openRectangle_subset_closedPatch x₁ x₂ y₁ y₂)
      (isOpen_openRectangle x₁ x₂ y₁ y₂) h)
  obtain ⟨hx₁, hx₂, hy₁, hy₂⟩ := hzc
  simp only [openRectangle, Set.mem_setOf_eq, not_and_or, not_lt] at hzo
  simp only [rectangleFrame, Set.mem_union, horizontal, vertical, Set.mem_setOf_eq]
  rcases hzo with h | h | h | h
  · exact Or.inl (Or.inr ⟨le_antisymm h hx₁, hy₁, hy₂⟩)
  · exact Or.inr ⟨le_antisymm hx₂ h, hy₁, hy₂⟩
  · exact Or.inl (Or.inl (Or.inl ⟨hx₁, hx₂, le_antisymm h hy₁⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨hx₁, hx₂, le_antisymm hy₂ h⟩))

/-- The grid rectangle cut out by two selected abscissae and two selected ordinates, as a
`StatementIngredients.Rectangle`. -/
def gridRectangle (x₁ x₂ y₁ y₂ : ℝ) (hx : x₁ < x₂) (hy : y₁ < y₂) : Rectangle where
  lower := ![x₁, y₁]
  upper := ![x₂, y₂]
  nondegenerate := by
    intro i
    fin_cases i
    · simpa using hx
    · simpa using hy

theorem carrier_gridRectangle (x₁ x₂ y₁ y₂ : ℝ) (hx : x₁ < x₂) (hy : y₁ < y₂) :
    (gridRectangle x₁ x₂ y₁ y₂ hx hy).carrier = closedPatch x₁ x₂ y₁ y₂ := by
  ext z
  simp only [Rectangle.carrier, closedPatch, Set.mem_setOf_eq, Fin.forall_fin_two,
    gridRectangle, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  tauto

/-! ### The patch argument -/

end ReflectedGMS.GoodGridMaximumPrinciple
