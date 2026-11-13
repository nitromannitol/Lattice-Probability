/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.LocalHarmonicClockOrthogonality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpatialCutoffFromLocalMass
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LimitingPotentialFreeOrthogonality

/-!
# `p:eq:parttest`: the full spatial variational test for a spatial cutoff of `Φ`

This is step (a) of the bracket atom `CoordinateLocallySquareIntegrable`.  It produces the
`hU` hypothesis of
`Forms/StoppedFormAssociationFastStopped.martingale_stopped_fullEnergyPath_exit_completed`
— the *drift-elimination* clause of `p:lem:localharm` — for the spatial cutoff `U` of one
coordinate `Φ · i`, out of clause **H5c** (`FullRectangleOrthogonality`, the first half of
`EnvironmentFields.FullSpatialHarmonicity`).

## The statement being produced

The fast-side martingale theorem consumes

```
hU : ∀ w : hilbertDomain G m,
       (∀ x ∉ A, unweight m (valueInclusion G m w) x = 0) →
       G.dirichletForm (unweight m (valueInclusion G m U)) (unweight m (valueInclusion G m w)) = 0
```

for the *vertex region* `A` at whose spatial exit the path is stopped.  H5c, by contrast, is
a statement about a bounded **rectangle** `Q`: `Φ` pairs to zero, in the restricted graph of
the patch of `Q`, with every plane-valued finite-energy variation vanishing on the cells that
meet `∂Q`.  Three moves turn one into the other.

* **Localisation.** The pairing against a variation supported in `A` is unchanged when the
  ambient graph is replaced by the restriction to any vertex set containing `A` and all its
  graph neighbours (`LimitingPotentialFreeOrthogonality.dirichletForm_eq_restricted`; no
  energy of the left argument is used).  Applied to `{‖z v‖ ≤ R}` it replaces the cutoff `U`
  by `Φ · i` — that is the *only* place the cutoff identity `hUeq` is used — and applied to
  `patchVertices F Q` it lands the pairing on the patch of `Q`.
* **Coordinates.** `vectorPairing` against the plane test `PiLp.single i g` is the single
  scalar Dirichlet pairing of the `i`-th coordinate (`vectorPairing_coordTest`), and the
  corresponding `vectorEnergy` is the single scalar energy (`vectorEnergy_coordTest`), so a
  scalar finite-energy variation supported in `A` *is* a `FullZeroBoundaryVariation`.
* **Geometry.** For the concentric box of half-side `2R` and the region
  `A = {‖z v‖ ≤ R/2}`, the local diameter bound `diam (cell v) ≤ R/100` of `r:prop:log`
  (`Spatial/AlmostSureCutoffBounds.ae_exists_diameter_bound`, which needs only mass transport
  and the (FE) moment) gives all three containments at once: `A ∪ N(A) ⊆ {‖z v‖ ≤ R}`,
  `A ∪ N(A) ⊆ patchVertices F Q`, and `A ∩ boundaryVertices F Q = ∅`.  The neighbour step
  uses `Geometry` clause 8 — adjacent cells touch.

Nothing here is probabilistic, and nothing here concerns any clock: the speed `m` is an
arbitrary function (in the consumer it is the **summable fast speed** `fastSpeed`, never the
area speed).  No hypothesis is `Summable (cellArea …)` or a global `HasFiniteEnergy`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.LocalHarmonicClock

open StatementIngredients ReflectedWalk FullNetworkForm

universe u

variable {V : Type u}

/-! ## The single-coordinate plane test field -/

/-- The plane-valued test field with only the `i`-th coordinate nonzero. -/
def coordTest (S : Set V) (i : Fin 2) (g : V → ℝ) : S → Plane :=
  fun v => PiLp.single 2 i (g (v : V))

theorem coordTest_apply (S : Set V) (i : Fin 2) (g : V → ℝ) (v : S) (j : Fin 2) :
    coordTest S i g v j = if j = i then g (v : V) else 0 :=
  PiLp.single_apply 2 ℝ i (g (v : V)) j

theorem coordTest_same (S : Set V) (i : Fin 2) (g : V → ℝ) :
    (fun v : S => coordTest S i g v i) = fun v : S => g (v : V) := by
  funext v
  rw [coordTest_apply]
  simp

theorem coordTest_other (S : Set V) {i j : Fin 2} (hj : j ≠ i) (g : V → ℝ) :
    (fun v : S => coordTest S i g v j) = fun _ : S => (0 : ℝ) := by
  funext v
  rw [coordTest_apply]
  simp [hj]

theorem coordTest_eq_zero (S : Set V) (i : Fin 2) (g : V → ℝ) {v : S}
    (hv : g (v : V) = 0) : coordTest S i g v = 0 := by
  simp only [coordTest, hv]
  exact (PiLp.single_eq_zero_iff (β := fun _ : Fin 2 => ℝ) 2 i).2 rfl

/-! ## Two degenerate evaluations -/

theorem dirichletForm_zero_right (G : ConductanceGraph V) (f : V → ℝ) :
    G.dirichletForm f (fun _ : V => (0 : ℝ)) = 0 := by
  have hz : (fun p : V × V => G.gradProd f (fun _ : V => (0 : ℝ)) p)
      = fun _ : V × V => (0 : ℝ) := by
    funext p
    simp [ConductanceGraph.gradProd]
  simp only [ConductanceGraph.dirichletForm, hz, tsum_zero, zero_div]

theorem energyENN_zero_fun (G : ConductanceGraph V) :
    energyENN G (fun _ : V => (0 : ℝ)) = 0 := by
  have hz : (fun p : V × V => ENNReal.ofReal (G.gradSq (fun _ : V => (0 : ℝ)) p))
      = fun _ : V × V => (0 : ℝ≥0∞) := by
    funext p
    simp [ConductanceGraph.gradSq]
  simp only [energyENN, hz, tsum_zero, ENNReal.zero_div]

/-! ## The pairing and the energy of the coordinate test -/

/-- The plane pairing against a single-coordinate test is one scalar Dirichlet pairing. -/
theorem vectorPairing_coordTest (G : ConductanceGraph V) (S : Set V) (i : Fin 2)
    (Ψ : S → Plane) (g : V → ℝ) :
    vectorPairing (restrictGraph G S) Ψ (coordTest S i g)
      = (restrictGraph G S).dirichletForm (fun v : S => Ψ v i)
          (fun v : S => g (v : V)) := by
  show (∑ j : Fin 2, (restrictGraph G S).dirichletForm (fun v : S => Ψ v j)
      (fun v : S => coordTest S i g v j)) = _
  rw [Finset.sum_eq_single i]
  · rw [coordTest_same]
  · intro j _ hj
    rw [coordTest_other S hj g]
    exact dirichletForm_zero_right _ _
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The plane energy of a single-coordinate test is one scalar energy. -/
theorem vectorEnergy_coordTest (G : ConductanceGraph V) (S : Set V) (i : Fin 2)
    (g : V → ℝ) :
    vectorEnergy (restrictGraph G S) (coordTest S i g)
      = energyENN (restrictGraph G S) (fun v : S => g (v : V)) := by
  show (∑ j : Fin 2, energyENN (restrictGraph G S)
      (fun v : S => coordTest S i g v j)) = _
  rw [Finset.sum_eq_single i]
  · rw [coordTest_same]
  · intro j _ hj
    rw [coordTest_other S hj g]
    exact energyENN_zero_fun _
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- A scalar finite-energy function supported away from the boundary cells of `Q` gives an
admissible plane variation for `Q`. -/
theorem fullZeroBoundaryVariation_coordTest [Countable V] (F : IndexedCells V)
    (Q : Rectangle) (i : Fin 2) {A : Set V} {g : V → ℝ}
    (hgE : F.graph.HasFiniteEnergy g) (hg0 : ∀ x, x ∉ A → g x = 0)
    (hbd : ∀ x ∈ A, x ∉ boundaryVertices F Q) :
    FullZeroBoundaryVariation F Q (coordTest (patchVertices F Q) i g) := by
  constructor
  · rw [vectorEnergy_coordTest]
    refine lt_top_iff_ne_top.2 ((energyENN_ne_top_iff _ _).2 ?_)
    exact LimitingPotentialFreeOrthogonality.hasFiniteEnergy_restrict F.graph
      (patchVertices F Q) hgE
  · intro v hv
    refine coordTest_eq_zero _ _ _ (hg0 (v : V) ?_)
    intro hA
    exact hbd (v : V) hA hv

/-! ## The transported variational identity -/

/-- **`p:eq:parttest` for `Φ` itself.**  `Φ · i` pairs to zero, in the *ambient* graph, with
every finite-energy scalar variation supported in a region `A` whose closed neighbourhood
sits in the patch of `Q` and which misses the boundary cells of `Q`. -/
theorem dirichletForm_coord_eq_zero_of_orthogonality [Countable V] (F : IndexedCells V)
    (Φ : V → Plane) (hΦ : FullRectangleOrthogonality F Φ) (Q : Rectangle) (i : Fin 2)
    {A : Set V} (hAQ : A ⊆ patchVertices F Q)
    (hnbrQ : ∀ x ∈ A, ∀ y : V, F.graph.Adj x y → y ∈ patchVertices F Q)
    (hbd : ∀ x ∈ A, x ∉ boundaryVertices F Q)
    {g : V → ℝ} (hgE : F.graph.HasFiniteEnergy g) (hg0 : ∀ x, x ∉ A → g x = 0) :
    F.graph.dirichletForm (fun v => Φ v i) g = 0 := by
  have h1 := LimitingPotentialFreeOrthogonality.dirichletForm_eq_restricted F.graph hAQ
    hnbrQ hg0 (fun v => Φ v i)
  have h2 := vectorPairing_coordTest F.graph (patchVertices F Q) i
    (fun v : patchVertices F Q => Φ (v : V)) g
  have h3 := (hΦ Q).2 (coordTest (patchVertices F Q) i g)
    (fullZeroBoundaryVariation_coordTest F Q i hgE hg0 hbd)
  rw [h2] at h3
  rw [h1]
  exact h3

/-- **The `hU` hypothesis of the fast-side martingale theorem, for an abstract region.**
`U` need only agree with `Φ · i` on a set `B` containing `A` and all its graph neighbours. -/
theorem hU_of_orthogonality_of_eqOn [Countable V] (F : IndexedCells V)
    (Φ : V → Plane) (hΦ : FullRectangleOrthogonality F Φ) (Q : Rectangle) (i : Fin 2)
    {A B : Set V} (m : V → ℝ) (U : hilbertDomain F.graph m)
    (hUeq : Set.EqOn (unweight m (valueInclusion F.graph m U)) (fun v => Φ v i) B)
    (hAB : A ⊆ B) (hnbrB : ∀ x ∈ A, ∀ y : V, F.graph.Adj x y → y ∈ B)
    (hAQ : A ⊆ patchVertices F Q)
    (hnbrQ : ∀ x ∈ A, ∀ y : V, F.graph.Adj x y → y ∈ patchVertices F Q)
    (hbd : ∀ x ∈ A, x ∉ boundaryVertices F Q) :
    ∀ w : hilbertDomain F.graph m,
      (∀ x ∉ A, unweight m (valueInclusion F.graph m w) x = 0) →
      F.graph.dirichletForm (unweight m (valueInclusion F.graph m U))
        (unweight m (valueInclusion F.graph m w)) = 0 := by
  intro w hw
  have hgE : F.graph.HasFiniteEnergy (unweight m (valueInclusion F.graph m w)) :=
    hilbertDomain_hasFiniteEnergy F.graph m w
  have hg0 : ∀ x, x ∉ A → unweight m (valueInclusion F.graph m w) x = 0 := hw
  have hUB := LimitingPotentialFreeOrthogonality.dirichletForm_eq_restricted F.graph hAB
    hnbrB hg0 (unweight m (valueInclusion F.graph m U))
  have hΦB := LimitingPotentialFreeOrthogonality.dirichletForm_eq_restricted F.graph hAB
    hnbrB hg0 (fun v => Φ v i)
  have hcongr : (fun z : B => unweight m (valueInclusion F.graph m U) (z : V))
      = fun z : B => (fun v => Φ v i) (z : V) := funext fun z => hUeq z.2
  rw [hUB, hcongr, ← hΦB]
  exact dirichletForm_coord_eq_zero_of_orthogonality F Φ hΦ Q i hAQ hnbrQ hbd hgE hg0

/-! ## The concentric box and the region `{‖z v‖ ≤ R/2}` -/

/-- The closed axis-parallel box of half-side `2R` centred at the origin. -/
def bigBox {R : ℝ} (hR : 0 < R) : Rectangle where
  lower := fun _ => -(2 * R)
  upper := fun _ => 2 * R
  nondegenerate := fun _ => by linarith

theorem mem_bigBox_carrier {R : ℝ} (hR : 0 < R) {y : Plane} (hy : ‖y‖ ≤ 2 * R) :
    y ∈ (bigBox hR).carrier := by
  show ∀ j : Fin 2, -(2 * R) ≤ y j ∧ y j ≤ 2 * R
  intro j
  have hj : |y j| ≤ 2 * R := (SpatialCutoff.abs_coord_le_norm y j).trans hy
  exact ⟨(abs_le.1 hj).1, (abs_le.1 hj).2⟩

theorem isOpen_openBox (Q : Rectangle) :
    IsOpen {y : Plane | ∀ j : Fin 2, Q.lower j < y j ∧ y j < Q.upper j} := by
  have h0 : Continuous fun y : Plane => y 0 := PiLp.continuous_apply 2 _ (0 : Fin 2)
  have h1 : Continuous fun y : Plane => y 1 := PiLp.continuous_apply 2 _ (1 : Fin 2)
  have hset : {y : Plane | ∀ j : Fin 2, Q.lower j < y j ∧ y j < Q.upper j}
      = ((fun y : Plane => y 0) ⁻¹' Set.Ioo (Q.lower 0) (Q.upper 0))
        ∩ ((fun y : Plane => y 1) ⁻¹' Set.Ioo (Q.lower 1) (Q.upper 1)) := by
    apply Set.eq_of_subset_of_subset
    · intro y hy
      exact ⟨⟨(hy 0).1, (hy 0).2⟩, (hy 1).1, (hy 1).2⟩
    · intro y hy
      show ∀ j : Fin 2, Q.lower j < y j ∧ y j < Q.upper j
      rw [Fin.forall_fin_two]
      exact ⟨⟨hy.1.1, hy.1.2⟩, hy.2.1, hy.2.2⟩
  rw [hset]
  exact (isOpen_Ioo.preimage h0).inter (isOpen_Ioo.preimage h1)

theorem openBox_subset_interior (Q : Rectangle) :
    {y : Plane | ∀ j : Fin 2, Q.lower j < y j ∧ y j < Q.upper j} ⊆ interior Q.carrier :=
  interior_maximal (fun _ hy j => ⟨(hy j).1.le, (hy j).2.le⟩) (isOpen_openBox Q)

theorem notMem_frontier_bigBox {R : ℝ} (hR : 0 < R) {y : Plane} (hy : ‖y‖ < 2 * R) :
    y ∉ frontier (bigBox hR).carrier := by
  intro hyf
  refine hyf.2 (openBox_subset_interior (bigBox hR) ?_)
  show ∀ j : Fin 2, -(2 * R) < y j ∧ y j < 2 * R
  intro j
  have hj : |y j| < 2 * R := lt_of_le_of_lt (SpatialCutoff.abs_coord_le_norm y j) hy
  exact ⟨(abs_lt.1 hj).1, (abs_lt.1 hj).2⟩

/-! ## The geometric containments -/

/-- **Neighbours of a half-ball vertex stay in the ball.**  Uses only `Geometry` clause 8
(adjacent cells touch) and the local diameter bound of `r:prop:log`. -/
theorem norm_le_of_adj [Countable V] {F : IndexedCells V} (hF : Geometry F) {z : V → Plane}
    (hz : CellRepresentatives F z) {R : ℝ} (hR : 0 < R)
    (hD : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    {x y : V} (hx : ‖z x‖ ≤ R / 2) (hxy : F.graph.Adj x y) :
    ‖z y‖ ≤ R := by
  have hxhit : Hits F (Metric.closedBall (0 : Plane) R) x := by
    refine ⟨z x, hz x, ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hdx : Metric.diam (F.cell x : Set Plane) ≤ R / 100 := hD x hxhit
  obtain ⟨p, hpx, hpy⟩ :=
    hF.2.2.2.2.2.2.2 (show F.graph.toSimpleGraph.Adj x y from hxy)
  have hdistx : dist (z x) p ≤ Metric.diam (F.cell x : Set Plane) :=
    Metric.dist_le_diam_of_mem (F.cell x).isCompact.isBounded (hz x) hpx
  have htri : ‖p‖ ≤ dist (z x) p + ‖z x‖ := by
    have h := dist_triangle p (z x) 0
    simp only [dist_zero_right] at h
    rwa [dist_comm p (z x)] at h
  have hpn : ‖p‖ ≤ R := by linarith
  have hyhit : Hits F (Metric.closedBall (0 : Plane) R) y := by
    refine ⟨p, hpy, ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hpn
  have hdy : Metric.diam (F.cell y : Set Plane) ≤ R / 100 := hD y hyhit
  have hdisty : dist (z y) p ≤ Metric.diam (F.cell y : Set Plane) :=
    Metric.dist_le_diam_of_mem (F.cell y).isCompact.isBounded (hz y) hpy
  have htri2 : ‖z y‖ ≤ dist (z y) p + ‖p‖ := by
    have h := dist_triangle (z y) p 0
    simpa only [dist_zero_right] using h
  linarith

/-- **Step (a).**  The `hU` input of
`StoppedFormAssociationFastStopped.martingale_stopped_fullEnergyPath_exit_completed`, for
the region `A = {‖z v‖ ≤ R/2}` and the cutoff `U` of `Φ · i` at radius `R`, from H5c and the
local diameter bound alone. -/
theorem hU_of_fullRectangleOrthogonality [Countable V] {F : IndexedCells V}
    (hF : Geometry F) {z : V → Plane} (hz : CellRepresentatives F z) {Φ : V → Plane}
    (hΦ : FullRectangleOrthogonality F Φ) {R : ℝ} (hR : 0 < R)
    (hD : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (m : V → ℝ) (i : Fin 2) (U : hilbertDomain F.graph m)
    (hUeq : Set.EqOn (unweight m (valueInclusion F.graph m U)) (fun v => Φ v i)
      {v : V | ‖z v‖ ≤ R}) :
    ∀ w : hilbertDomain F.graph m,
      (∀ x ∉ {v : V | ‖z v‖ ≤ R / 2}, unweight m (valueInclusion F.graph m w) x = 0) →
      F.graph.dirichletForm (unweight m (valueInclusion F.graph m U))
        (unweight m (valueInclusion F.graph m w)) = 0 := by
  have hAB : {v : V | ‖z v‖ ≤ R / 2} ⊆ {v : V | ‖z v‖ ≤ R} := by
    intro v hv
    have hv' : ‖z v‖ ≤ R / 2 := hv
    show ‖z v‖ ≤ R
    linarith
  have hnbrB : ∀ x ∈ {v : V | ‖z v‖ ≤ R / 2}, ∀ y : V, F.graph.Adj x y →
      y ∈ {v : V | ‖z v‖ ≤ R} := by
    intro x hx y hxy
    exact norm_le_of_adj hF hz hR hD (show ‖z x‖ ≤ R / 2 from hx) hxy
  have hAQ : {v : V | ‖z v‖ ≤ R / 2} ⊆ patchVertices F (bigBox hR) := by
    intro v hv
    have hv' : ‖z v‖ ≤ R / 2 := hv
    exact ⟨z v, hz v, mem_bigBox_carrier hR (by linarith)⟩
  have hnbrQ : ∀ x ∈ {v : V | ‖z v‖ ≤ R / 2}, ∀ y : V, F.graph.Adj x y →
      y ∈ patchVertices F (bigBox hR) := by
    intro x hx y hxy
    have hy : ‖z y‖ ≤ R := hnbrB x hx y hxy
    exact ⟨z y, hz y, mem_bigBox_carrier hR (by linarith)⟩
  have hbd : ∀ x ∈ {v : V | ‖z v‖ ≤ R / 2}, x ∉ boundaryVertices F (bigBox hR) := by
    intro x hx hcon
    have hx' : ‖z x‖ ≤ R / 2 := hx
    obtain ⟨y, hyc, hyf⟩ := hcon
    have hxhit : Hits F (Metric.closedBall (0 : Plane) R) x := by
      refine ⟨z x, hz x, ?_⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hdx : Metric.diam (F.cell x : Set Plane) ≤ R / 100 := hD x hxhit
    have hdist : dist (z x) y ≤ Metric.diam (F.cell x : Set Plane) :=
      Metric.dist_le_diam_of_mem (F.cell x).isCompact.isBounded (hz x) hyc
    have htri : ‖y‖ ≤ dist (z x) y + ‖z x‖ := by
      have h := dist_triangle y (z x) 0
      simp only [dist_zero_right] at h
      rwa [dist_comm y (z x)] at h
    exact notMem_frontier_bigBox hR (show ‖y‖ < 2 * R by linarith) hyf
  exact hU_of_orthogonality_of_eqOn F Φ hΦ (bigBox hR) i m U hUeq hAB hnbrB hAQ hnbrQ hbd

end ReflectedGMS.LocalHarmonicClock
