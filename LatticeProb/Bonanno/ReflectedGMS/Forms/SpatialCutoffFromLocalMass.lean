/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SpatialCutoffFromLocalMass at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpatialHarmonicCutoff
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpatialRadiusEnergy

/-!
# The spatial cutoff family of `p:lem:spatialcutoffs`, deterministically

This is the deterministic half of the `hcut` input of
`Process/SpatialExtensionEnvironment.ae_hreg_of_cutoffs_and_continuity`: for a fixed
environment, every coordinate of a potential `Φ` agrees on every ball of representatives
with a vector of the **full Hilbert energy domain** of an arbitrary positive summable speed.

The construction is the radial cutoff `Forms/SpatialHarmonicCutoff`; all that is supplied
here are its three analytic inputs, from objects the manuscript already provides:

* **boundedness of `Φ` on the patch** — from the corrector sublinearity
  `StatementIngredients.UniformlySublinearError` against the cell representatives `z`,
  together with the local diameter bound;
* **local energy of the radius `‖z ·‖`** — from the manuscript's diameter-weighted
  conductance mass (`Forms/SpatialRadiusEnergy`, in the `π`-only form proved below);
* **local energy of `Φ`** — from the rectangle-patch finiteness
  `vectorEnergy (restrictGraph … (patchVertices F Q)) Φ < ∞`, which is the first conjunct
  of `StatementIngredients.FullRectangleOrthogonality`, restricted from a large rectangle
  to the ball patch;
* **the collar condition** — `collar_subset_cells_hitting_closedBall`.

Nothing here is probabilistic and nothing here certifies any main theorem.
-/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace ReflectedGMS.SpatialCutoff

open StatementIngredients ReflectedWalk FullNetworkForm

variable {V : Type*}

/-! ## Two small bridges -/

/-- Each coordinate of a plane vector is dominated by its Euclidean norm. -/
theorem abs_coord_le_norm (x : Plane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : ‖x i‖ ^ 2 ≤ ∑ j : Fin 2, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 2 => ‖x j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hxi : |x i| = Real.sqrt (‖x i‖ ^ 2) := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.norm_eq_abs]
  rw [hxi]
  exact Real.sqrt_le_sqrt hle

/-- Finite energy on a patch restricts to any smaller patch. -/
theorem hasFiniteEnergy_restrict_subset {G : ReflectedWalk.ConductanceGraph V}
    {A B : Set V} (hAB : A ⊆ B) {f : V → ℝ}
    (h : (restrictGraph G B).HasFiniteEnergy (fun v : B => f v.1)) :
    (restrictGraph G A).HasFiniteEnergy (fun v : A => f v.1) := by
  have hinj : Function.Injective (fun p : A × A =>
      ((⟨p.1.1, hAB p.1.2⟩ : B), (⟨p.2.1, hAB p.2.2⟩ : B))) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ hEq
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hEq
    exact Prod.ext (Subtype.ext hEq.1) (Subtype.ext hEq.2)
  exact (h.comp_injective hinj).congr fun _ => rfl

/-! ## The radius energy from the `π`-part of the local mass alone -/

/-- The ordered edge family with the diameter of its first endpoint is summable under the
`π`-part of the manuscript's local mass.  This is
`summable_localDiameterSq_mul_conductance` with the (unused) `π*` part of the hypothesis
removed: the local mass bound `hW` of `Spatial/AlmostSureCutoffBounds` controls exactly
`∑ d² π`. -/
theorem summable_diamSq_mul_conductance_of_localPiMass [Countable V]
    (F : IndexedCells V) (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.pi v.1)) :
    Summable (fun p : A × A =>
      Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 * F.graph.c p.1.1 p.2.1) := by
  let d2 : A → ℝ := fun v => Metric.diam (F.cell v.1 : Set Plane) ^ 2
  have hpi : Summable (fun v : A => d2 v * F.graph.pi v.1) := hmass
  rw [summable_prod_of_nonneg]
  · constructor
    · intro v
      exact ((F.graph.summable_c v.1).subtype fun w => w ∈ A).mul_left (d2 v)
    · apply Summable.of_nonneg_of_le
        (fun v => tsum_nonneg fun w => mul_nonneg (sq_nonneg _) (F.graph.c_nonneg _ _))
        _ hpi
      intro v
      change (∑' w : A, d2 v * F.graph.c v.1 w.1) ≤ d2 v * F.graph.pi v.1
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left
        ((F.graph.summable_c v.1).tsum_subtype_le (F.graph.c v.1) A
          (fun w => F.graph.c_nonneg v.1 w)) (sq_nonneg _)
  · intro p
    exact mul_nonneg (sq_nonneg _) (F.graph.c_nonneg _ _)

/-- The local radius belongs to the finite-energy domain required by
`spatialHarmonicCutoff_hasFiniteEnergy`, using only the `π`-part of the local mass. -/
theorem restrictGraph_hasFiniteEnergy_norm_representative_of_localPiMass [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane)
    (hz : CellRepresentatives F z) (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.pi v.1)) :
    (restrictGraph F.graph A).HasFiniteEnergy (fun v => ‖z v.1‖) := by
  have hfirst := summable_diamSq_mul_conductance_of_localPiMass F A hmass
  have hsecond : Summable (fun p : A × A =>
      F.graph.c p.1.1 p.2.1 * Metric.diam (F.cell p.2.1 : Set Plane) ^ 2) := by
    refine hfirst.prod_symm.congr fun p => ?_
    rcases p with ⟨v, w⟩
    simp only [Prod.swap_prod_mk]
    rw [F.graph.c_symm]
    ring
  apply Summable.of_nonneg_of_le
    (fun p => (restrictGraph F.graph A).gradSq_nonneg _ p) _
    ((hfirst.add hsecond).mul_left 2)
  intro p
  by_cases hc : F.graph.c p.1.1 p.2.1 = 0
  · simp [ReflectedWalk.ConductanceGraph.gradSq, restrictGraph, hc, Metric.diam_nonneg]
  · have hadj : F.graph.toSimpleGraph.Adj p.1.1 p.2.1 :=
      lt_of_le_of_ne (F.graph.c_nonneg _ _) (Ne.symm hc)
    have hinc := abs_norm_sub_norm_le_cellDiameters F hF z hz hadj
    have hsq : (‖z p.2.1‖ - ‖z p.1.1‖) ^ 2 ≤
        2 * (Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 +
          Metric.diam (F.cell p.2.1 : Set Plane) ^ 2) := by
      have hsquare := (sq_le_sq₀ (abs_nonneg _)
        (add_nonneg Metric.diam_nonneg Metric.diam_nonneg)).2 hinc
      rw [sq_abs] at hsquare
      nlinarith [hsquare, Metric.diam_nonneg (s := (F.cell p.1.1 : Set Plane)),
        Metric.diam_nonneg (s := (F.cell p.2.1 : Set Plane)),
        sq_nonneg (Metric.diam (F.cell p.1.1 : Set Plane) -
          Metric.diam (F.cell p.2.1 : Set Plane))]
    simp only [ReflectedWalk.ConductanceGraph.gradSq, restrictGraph]
    have hmul := mul_le_mul_of_nonneg_left hsq (F.graph.c_nonneg p.1.1 p.2.1)
    nlinarith

/-! ## One cutoff, from a patch with the three analytic inputs -/

/-- **The cutoff of `p:lem:spatialcutoffs` at one radius.**  On a patch `P`-ball containing
the collar of the radius-`ρ` ball, local boundedness of `f`, local `π`-mass and local energy
of `f` put the radial cutoff of `f` into the full Hilbert domain of every positive summable
speed, where it agrees with `f` throughout `{‖z v‖ ≤ ρ}`. -/
theorem exists_hilbertDomain_eqOn_of_patch [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane)
    (hz : CellRepresentatives F z) (f : V → ℝ)
    {ρ D P B : ℝ} (hB : 0 ≤ B) (hD0 : 0 ≤ D)
    (hDcol : ∀ v : V, ‖z v‖ < ρ + 1 → Metric.diam (F.cell v : Set Plane) ≤ D)
    (hP : ρ + 1 + D ≤ P)
    (hf : ∀ v ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) P) v}, |f v| ≤ B)
    (hmass : Summable (fun v : {v : V | Hits F (Metric.closedBall (0 : Plane) P) v} =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.pi v.1))
    (hfE : (restrictGraph F.graph
        {v : V | Hits F (Metric.closedBall (0 : Plane) P) v}).HasFiniteEnergy
      (fun v => f v.1))
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (hmsum : Summable m) :
    ∃ U : hilbertDomain F.graph m,
      Set.EqOn (unweight m (valueInclusion F.graph m U)) f {v | ‖z v‖ ≤ ρ} := by
  have hball : Metric.closedBall (0 : Plane) (ρ + 1 + D) ⊆
      Metric.closedBall (0 : Plane) P := Metric.closedBall_subset_closedBall hP
  have hhit : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) (ρ + 1 + D)) v →
      v ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) P) v} := by
    rintro v ⟨y, hy1, hy2⟩
    exact ⟨y, hy1, hball hy2⟩
  have hA : ∀ v : V, ‖z v‖ < ρ + 1 →
      v ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) P) v} := by
    intro v hv
    refine ⟨z v, hz v, ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hcollar : ∀ v w : V, F.graph.c v w ≠ 0 →
      (‖z v‖ < ρ + 1 ∨ ‖z w‖ < ρ + 1) →
      v ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) P) v} ∧
        w ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) P) v} := by
    intro v w hc hin
    obtain ⟨h1, h2⟩ :=
      collar_subset_cells_hitting_closedBall F hF z hz ρ D hDcol v w hc hin
    exact ⟨hhit v h1, hhit w h2⟩
  have hrE := restrictGraph_hasFiniteEnergy_norm_representative_of_localPiMass F hF z hz
    {v : V | Hits F (Metric.closedBall (0 : Plane) P) v} hmass
  obtain ⟨U, -, hU⟩ := exists_spatialHarmonicCutoff_hilbertDomain F.graph z ρ f
    {v : V | Hits F (Metric.closedBall (0 : Plane) P) v} hB hA hf hrE hfE hcollar m hm hmsum
  exact ⟨U, hU⟩

/-! ## The full family, from the manuscript's random-radius hypotheses -/

/-- **`p:lem:spatialcutoffs` at one environment.**  For every coordinate `i` and every
radius `R`, the coordinate `Φ · i` agrees on `{‖z v‖ ≤ R}` with a vector of the full Hilbert
energy domain of the speed `m`.

The hypotheses are exactly the manuscript's: the local diameter bound `hD` and the
diameter-weighted conductance mass bound `hmass` of Proposition `r:prop:log`
(`Spatial/AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses`), the corrector
sublinearity `hsub` against the representatives `z`, and the rectangle-patch energy
finiteness `hpatch` of `FullRectangleOrthogonality`. -/
theorem exists_hilbertDomain_eqOn_closedBall [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane)
    (hz : CellRepresentatives F z) (Φ : V → Plane)
    (hsub : UniformlySublinearError F Φ z)
    (hpatch : ∀ Q : Rectangle,
      vectorEnergy (restrictGraph F.graph (patchVertices F Q)) (fun v => Φ v.1) < ∞)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hmass : ∀ R : ℝ, r₀ ≤ R →
      Summable (fun v : {v : V | Hits F (Metric.closedBall (0 : Plane) R) v} =>
        Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.pi v.1))
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (hmsum : Summable m)
    (i : Fin 2) (R : ℕ) :
    ∃ U : hilbertDomain F.graph m,
      Set.EqOn (unweight m (valueInclusion F.graph m U)) (fun v => Φ v i)
        {v | ‖z v‖ ≤ (R : ℝ)} := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := hsub 1 one_pos
  obtain ⟨ρ, hρR, hρr₀, hρR₀⟩ : ∃ ρ : ℝ, (R : ℝ) ≤ ρ ∧ r₀ ≤ ρ ∧ R₀ ≤ ρ :=
    ⟨max (max (R : ℝ) r₀) R₀, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  have hρpos : 0 < ρ := lt_of_lt_of_le hr₀ hρr₀
  have hr₀1 : r₀ ≤ ρ + 1 := by linarith
  have hDcol : ∀ v : V, ‖z v‖ < ρ + 1 →
      Metric.diam (F.cell v : Set Plane) ≤ (ρ + 1) / 100 := by
    intro v hv
    refine hD (ρ + 1) hr₀1 v ⟨z v, hz v, ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hv.le
  have hPpos : 0 < ρ + 1 + (ρ + 1) / 100 := by linarith
  have hr₀P : r₀ ≤ ρ + 1 + (ρ + 1) / 100 := by linarith
  have hR₀P : R₀ ≤ ρ + 1 + (ρ + 1) / 100 := by linarith
  -- the local bound on the coordinate
  have hbound : ∀ v ∈ {v : V | Hits F (Metric.closedBall (0 : Plane)
        (ρ + 1 + (ρ + 1) / 100)) v}, |Φ v i| ≤ 3 * (ρ + 1 + (ρ + 1) / 100) := by
    rintro v hv
    obtain ⟨y, hyc, hyB⟩ := hv
    have hyn : ‖y‖ ≤ ρ + 1 + (ρ + 1) / 100 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hyB
    have hdiam : Metric.diam (F.cell v : Set Plane) ≤ (ρ + 1 + (ρ + 1) / 100) / 100 :=
      hD _ hr₀P v ⟨y, hyc, hyB⟩
    have hdist : dist (z v) y ≤ Metric.diam (F.cell v : Set Plane) :=
      Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded (hz v) hyc
    have htri : ‖z v‖ ≤ dist (z v) y + ‖y‖ := by
      simpa only [dist_zero_right] using dist_triangle (z v) y 0
    have hΦz : ‖Φ v - z v‖ ≤ 1 * (ρ + 1 + (ρ + 1) / 100) :=
      hR₀ _ hR₀P v ⟨y, hyc, hyB⟩
    have hnorm : ‖Φ v‖ - ‖z v‖ ≤ ‖Φ v - z v‖ := norm_sub_norm_le (Φ v) (z v)
    have hfin : ‖Φ v‖ ≤ 3 * (ρ + 1 + (ρ + 1) / 100) := by linarith
    exact le_trans (abs_coord_le_norm (Φ v) i) hfin
  -- the local energy of the coordinate, from a rectangle patch
  have hfE : (restrictGraph F.graph {v : V | Hits F (Metric.closedBall (0 : Plane)
        (ρ + 1 + (ρ + 1) / 100)) v}).HasFiniteEnergy (fun v => Φ v.1 i) := by
    obtain ⟨Q, hQcar⟩ : ∃ Q : Rectangle,
        Metric.closedBall (0 : Plane) (ρ + 1 + (ρ + 1) / 100) ⊆ Q.carrier := by
      refine ⟨⟨fun _ => -(ρ + 1 + (ρ + 1) / 100), fun _ => ρ + 1 + (ρ + 1) / 100,
        fun _ => by linarith⟩, ?_⟩
      intro y hy j
      have hyn : ‖y‖ ≤ ρ + 1 + (ρ + 1) / 100 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hy
      have hj : |y j| ≤ ρ + 1 + (ρ + 1) / 100 :=
        le_trans (abs_coord_le_norm y j) hyn
      exact ⟨(abs_le.1 hj).1, (abs_le.1 hj).2⟩
    have hAQ : {v : V | Hits F (Metric.closedBall (0 : Plane)
        (ρ + 1 + (ρ + 1) / 100)) v} ⊆ patchVertices F Q := by
      rintro v ⟨y, hy1, hy2⟩
      exact ⟨y, hy1, hQcar hy2⟩
    have hvec : vectorEnergy (restrictGraph F.graph (patchVertices F Q))
        (fun v => Φ v.1) =
        ∑ j : Fin 2, energyENN (restrictGraph F.graph (patchVertices F Q))
          (fun v => Φ v.1 j) := rfl
    have hcoord : energyENN (restrictGraph F.graph (patchVertices F Q))
        (fun v => Φ v.1 i) ≤
        vectorEnergy (restrictGraph F.graph (patchVertices F Q)) (fun v => Φ v.1) := by
      rw [hvec]
      exact Finset.single_le_sum
        (f := fun j : Fin 2 => energyENN (restrictGraph F.graph (patchVertices F Q))
          (fun v => Φ v.1 j)) (fun _ _ => zero_le) (Finset.mem_univ i)
    have hne : energyENN (restrictGraph F.graph (patchVertices F Q))
        (fun v => Φ v.1 i) ≠ ∞ := (lt_of_le_of_lt hcoord (hpatch Q)).ne
    have hQfin : (restrictGraph F.graph (patchVertices F Q)).HasFiniteEnergy
        (fun v => Φ v.1 i) :=
      (energyENN_ne_top_iff (restrictGraph F.graph (patchVertices F Q))
        (fun v => Φ v.1 i)).1 hne
    exact hasFiniteEnergy_restrict_subset (G := F.graph) (f := fun v => Φ v i) hAQ hQfin
  obtain ⟨U, hU⟩ := exists_hilbertDomain_eqOn_of_patch F hF z hz (fun v => Φ v i)
    (B := 3 * (ρ + 1 + (ρ + 1) / 100)) (by linarith) (by linarith) hDcol (le_refl _)
    hbound (hmass _ hr₀P) hfE m hm hmsum
  exact ⟨U, hU.mono fun v hv => le_trans hv hρR⟩

end ReflectedGMS.SpatialCutoff
