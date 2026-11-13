/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.DirectionalNondegeneracy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea
import LatticeProb.Bonanno.ReflectedGMS.Environment.UncoveredFacts
import LatticeProb.Bonanno.ReflectedGMS.HarmonicLawIngredients
import Mathlib.Analysis.Convex.Integral

/-!
# Directional nondegeneracy of the ordinary-edge bracket density

This file supplies the deterministic half of the positive-definiteness clause
`StatementIngredients.SymmetricPositiveDefinite (meanCovariance ν Φ)`.

Two independent pieces are proved.

* An exact **quadratic-form identity** for the existing bracket density
  `StatementIngredients.bracketDensity`: for every direction `ξ : Fin 2 → ℝ`,
  `ξᵀ Γ(H) ξ` equals `a_H⁻¹ ∑_{H'} c(H,H') ⟨ξ, Φ(H') - Φ(H)⟩²`, the directional
  edge energy at `H`.  In particular the form is always nonnegative, is positive
  as soon as a single incident edge has a nonzero directional gradient, and the
  same statements transfer verbatim to `RootDensities.rootedGamma` and, by
  linearity of the Bochner integral, to `HarmonicLawIngredients.meanCovariance`.

* A **geometric contradiction**: on a connected plane-covering cell environment
  with a uniformly sublinear corrector and submacroscopic cell diameters, no
  nonzero direction `ξ` can have identically vanishing directional gradient.
  Indeed such a `ξ` would make `⟨ξ, Φ⟩` constant along every edge, hence (by
  connectedness) globally constant, while the two cells containing the points
  `±R ξ/‖ξ‖` have centroids separated by `2R‖ξ‖` in the direction `ξ`; the
  corrector and diameter errors are both `o(R)`, which is impossible.

  The diameter control is genuinely used: coverage plus a sublinear centroid
  error alone does not force two cells meeting `B(0,R)` to have well-separated
  centroids (large concentric cells are a counterexample).

Combining the two gives `exists_vertex_quadraticForm_bracketDensity_pos`: some
vertex has a strictly positive directional bracket form.

## `SymmetricPositiveDefinite (meanCovariance ν Φ)` — CLOSED elsewhere, not open

`meanCovariance` integrates `rootedGamma` at the **single** root cell of the
origin.  What is proved *here* is nonnegativity of its directional form together
with strict positivity of the directional form at *some* vertex of *every*
admissible environment.  The step from "some vertex" to "the root cell" is a
**mass-transport / stationarity propagation** statement: if the directional form
of `rootedGamma (decode e)` at the root of `0` vanishes for `ν`-a.e. `e`, then
for `ν`-a.e. `e` *every* vertex of `decode e` — equivalently every edge — has
vanishing directional gradient.

That statement is **proved**, in `Limit/CovarianceRootPropagation.lean`, by the
"the root sees every cell" transport argument under `EnvironmentLaws.MassTransport`:

* `CovarianceRootPropagation.ae_forall_not_mem_of_ae_root_not_mem` — the
  transport step itself;
* `CovarianceRootPropagation.ae_forall_directionalGradient_eq_zero_of_ae_rooted_quadraticForm_eq_zero`
  — its specialization to the directional energy property;
* `CovarianceRootPropagation.quadraticForm_meanCovariance_pos` (:836) — the
  conclusion, which consumes `exists_edge_directionalGradient_ne_zero` from this
  file.

`InvarianceAssembly.symmetricPositiveDefinite_meanCovariance` (:179) then adds
`meanCovariance_symm` to obtain the full `SymmetricPositiveDefinite` clause, and
`InvarianceAssembly.exists_anisotropicBrownianTarget_of_symmetricPositiveDefinite`
(:286) turns it into the target with `target.covariance = meanCovariance ν Φ`.
Inside the assembly the three side hypotheses are all discharged from the main
theorem's own data: `hint` by `integrableBracket_of_aestronglyMeasurable` (:135)
from `MassTransport` plus the `FiniteSpecificEnergy` clause of
`IsHarmonicCoordinate`, `hsub` by the `SublinearCorrector` clause of
`IsHarmonicCoordinate`, and `hdiam` by `ae_submacroscopicDiameters` from
`MassTransport` and `FiniteEnergyMoment`.  So **neither Σ-nondegeneracy clause of
`InvarianceMainStatement.ReflectedInvarianceConclusions` is an open input**; this
section previously read as an open gap and was stale.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace ReflectedGMS.DirectionalNondegeneracy

open StatementIngredients RootDensities

variable {V : Type*}

/-! ## Directions and directional gradients -/

/-- The plane vector with coordinates `ξ`. -/
noncomputable def directionVector (ξ : Fin 2 → ℝ) : Plane := WithLp.toLp 2 ξ

@[simp] theorem directionVector_apply (ξ : Fin 2 → ℝ) (i : Fin 2) :
    directionVector ξ i = ξ i := rfl

/-- Pairing of a direction with a plane vector, in the coordinates already used
by `StatementIngredients.bracketDensity`. -/
noncomputable def dirPairing (ξ : Fin 2 → ℝ) (y : Plane) : ℝ := ∑ i : Fin 2, ξ i * y i

/-- Directional increment of `Phi` along the ordered pair `(v, w)`. -/
noncomputable def directionalGradient (Phi : V → Plane) (ξ : Fin 2 → ℝ) (v w : V) : ℝ :=
  ∑ i : Fin 2, ξ i * (Phi w i - Phi v i)

theorem dirPairing_eq_inner (ξ : Fin 2 → ℝ) (y : Plane) :
    dirPairing ξ y = ⟪directionVector ξ, y⟫_ℝ := by
  simp only [dirPairing, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.inner_apply, mul_comm]

theorem abs_dirPairing_le (ξ : Fin 2 → ℝ) (y : Plane) :
    |dirPairing ξ y| ≤ ‖directionVector ξ‖ * ‖y‖ := by
  rw [dirPairing_eq_inner]
  exact abs_real_inner_le_norm _ _

theorem dirPairing_sub (ξ : Fin 2 → ℝ) (y z : Plane) :
    dirPairing ξ (y - z) = dirPairing ξ y - dirPairing ξ z := by
  simp only [dirPairing, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dirPairing_smul_directionVector (ξ : Fin 2 → ℝ) (c : ℝ) :
    dirPairing ξ (c • directionVector ξ) = c * ∑ i : Fin 2, ξ i * ξ i := by
  simp only [dirPairing, PiLp.smul_apply, directionVector_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem directionalGradient_eq_sub (Phi : V → Plane) (ξ : Fin 2 → ℝ) (v w : V) :
    directionalGradient Phi ξ v w = dirPairing ξ (Phi w) - dirPairing ξ (Phi v) := by
  simp only [directionalGradient, dirPairing, mul_sub, Finset.sum_sub_distrib]

theorem norm_directionVector_pos {ξ : Fin 2 → ℝ} (hξ : ξ ≠ 0) :
    0 < ‖directionVector ξ‖ := by
  rw [norm_pos_iff]
  intro h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hξ
  apply hi
  have : directionVector ξ i = (0 : Plane) i := by rw [h]
  simpa using this

theorem sum_mul_self_pos {ξ : Fin 2 → ℝ} (hξ : ξ ≠ 0) : 0 < ∑ i : Fin 2, ξ i * ξ i := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hξ
  refine Finset.sum_pos' (fun j _ => mul_self_nonneg (ξ j)) ⟨i, Finset.mem_univ i, ?_⟩
  exact mul_self_pos.mpr (by simpa using hi)

/-! ## The directional quadratic form of the bracket density -/

theorem conductance_eq_zero_of_not_mem_neighborFinset (F : IndexedCells V) (v : V)
    (hfin : (F.graph.toSimpleGraph.neighborSet v).Finite) {w : V} (hw : w ∉ hfin.toFinset) :
    F.graph.c v w = 0 := by
  have hnadj : ¬ F.graph.toSimpleGraph.Adj v w := fun hadj =>
    hw (hfin.mem_toFinset.mpr ((SimpleGraph.mem_neighborSet _ _ _).mpr hadj))
  have h0 : ¬ (0 < F.graph.c v w) := fun hpos =>
    hnadj (F.graph.toSimpleGraph_adj.mpr hpos)
  exact le_antisymm (not_lt.mp h0) (F.graph.c_nonneg v w)

/-- The exact directional quadratic form of the manuscript bracket density:
`ξᵀ Γ(H) ξ = a_H⁻¹ ∑_{H'} c(H,H') ⟨ξ, Φ(H') - Φ(H)⟩²`. -/
theorem quadraticForm_bracketDensity (F : IndexedCells V) (Phi : V → Plane) (v : V)
    (hfin : (F.graph.toSimpleGraph.neighborSet v).Finite) (ξ : Fin 2 → ℝ) :
    ∑ i : Fin 2, ∑ j : Fin 2, ξ i * bracketDensity F Phi v i j * ξ j
      = (cellArea F v)⁻¹ *
        ∑' w : V, F.graph.c v w * directionalGradient Phi ξ v w ^ 2 := by
  classical
  have hsum : ∀ i j : Fin 2,
      (∑' w : V, F.graph.c v w * (Phi w i - Phi v i) * (Phi w j - Phi v j))
        = ∑ w ∈ hfin.toFinset,
            F.graph.c v w * (Phi w i - Phi v i) * (Phi w j - Phi v j) := by
    intro i j
    refine tsum_eq_sum fun w hw => ?_
    rw [conductance_eq_zero_of_not_mem_neighborFinset F v hfin hw]
    ring
  have hsum2 : (∑' w : V, F.graph.c v w * directionalGradient Phi ξ v w ^ 2)
      = ∑ w ∈ hfin.toFinset, F.graph.c v w * directionalGradient Phi ξ v w ^ 2 := by
    refine tsum_eq_sum fun w hw => ?_
    rw [conductance_eq_zero_of_not_mem_neighborFinset F v hfin hw]
    ring
  rw [hsum2]
  simp only [bracketDensity, hsum, directionalGradient, Fin.sum_univ_two,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem summable_conductance_mul_directionalGradient_sq (F : IndexedCells V) (Phi : V → Plane)
    (v : V) (hfin : (F.graph.toSimpleGraph.neighborSet v).Finite) (ξ : Fin 2 → ℝ) :
    Summable (fun w : V => F.graph.c v w * directionalGradient Phi ξ v w ^ 2) := by
  classical
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun w hw => ?_
  rw [conductance_eq_zero_of_not_mem_neighborFinset F v hfin hw]
  ring

theorem quadraticForm_bracketDensity_nonneg [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (Phi : V → Plane) (v : V) (ξ : Fin 2 → ℝ) :
    0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ξ i * bracketDensity F Phi v i j * ξ j := by
  rw [quadraticForm_bracketDensity F Phi v (hF.2.2.2.2.2.2.1 v) ξ]
  refine mul_nonneg (inv_nonneg.mpr (cellArea_pos F hF v).le) ?_
  exact tsum_nonneg fun w => mul_nonneg (F.graph.c_nonneg v w) (sq_nonneg _)

/-- A single incident edge with nonzero directional gradient already makes the
directional bracket form strictly positive. -/
theorem quadraticForm_bracketDensity_pos [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (Phi : V → Plane) (v : V) (ξ : Fin 2 → ℝ) {w : V}
    (hw : 0 < F.graph.c v w) (hgrad : directionalGradient Phi ξ v w ≠ 0) :
    0 < ∑ i : Fin 2, ∑ j : Fin 2, ξ i * bracketDensity F Phi v i j * ξ j := by
  have hfin := hF.2.2.2.2.2.2.1 v
  rw [quadraticForm_bracketDensity F Phi v hfin ξ]
  refine mul_pos (inv_pos.mpr (cellArea_pos F hF v)) ?_
  refine (summable_conductance_mul_directionalGradient_sq F Phi v hfin ξ).tsum_pos
    (fun w' => mul_nonneg (F.graph.c_nonneg v w') (sq_nonneg _)) w ?_
  exact mul_pos hw (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hgrad)))

/-! ## Transfer to the rooted density -/

theorem quadraticForm_rootedGamma_eq (F : IndexedCells V) (Phi : V → Plane) (z : Plane)
    {v : V} (hv : rootAt F z = some v)
    (hfin : (F.graph.toSimpleGraph.neighborSet v).Finite) (ξ : Fin 2 → ℝ) :
    ∑ i : Fin 2, ∑ j : Fin 2, ξ i * rootedGamma F Phi z i j * ξ j
      = (cellArea F v)⁻¹ *
        ∑' w : V, F.graph.c v w * directionalGradient Phi ξ v w ^ 2 := by
  have hΓ : rootedGamma F Phi z = bracketDensity F Phi v := by
    simp [rootedGamma, hv]
  rw [hΓ]
  exact quadraticForm_bracketDensity F Phi v hfin ξ

theorem quadraticForm_rootedGamma_nonneg [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (Phi : V → Plane) (z : Plane) (ξ : Fin 2 → ℝ) :
    0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ξ i * rootedGamma F Phi z i j * ξ j := by
  generalize hroot : rootAt F z = root
  cases root with
  | none => simp [rootedGamma, hroot]
  | some v =>
      have hΓ : rootedGamma F Phi z = bracketDensity F Phi v := by
        simp [rootedGamma, hroot]
      rw [hΓ]
      exact quadraticForm_bracketDensity_nonneg F hF Phi v ξ

/-! ## Constancy of a directional coordinate along a connected graph -/

theorem dirPairing_eq_of_forall_edge_directionalGradient_eq_zero (F : IndexedCells V)
    (hconn : F.graph.toSimpleGraph.Connected) (Phi : V → Plane) (ξ : Fin 2 → ℝ)
    (hzero : ∀ v w : V, 0 < F.graph.c v w → directionalGradient Phi ξ v w = 0) (v w : V) :
    dirPairing ξ (Phi v) = dirPairing ξ (Phi w) := by
  obtain ⟨p⟩ := hconn.preconnected v w
  induction p with
  | nil => rfl
  | cons hadj q ih =>
      have h := hzero _ _ (F.graph.toSimpleGraph_adj.mp hadj)
      rw [directionalGradient_eq_sub] at h
      linarith

/-! ## Centroids stay within one cell diameter -/

/-- **Covered points are dense.**  The covering clause of `Geometry` only asks that the
uncovered set be `H¹`-null, so a prescribed point need not lie in a cell; what survives is
that every ball around it contains a point that does.  The extra radius `r` is what the
estimate below has to absorb. -/
theorem exists_cell_mem_near [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (z : Plane) {r : ℝ} (hr : 0 < r) :
    ∃ (z' : Plane) (v : V), dist z' z < r ∧ z' ∈ (F.cell v : Set Plane) := by
  obtain ⟨z', hz', v, hv⟩ :=
    exists_mem_cell_of_isOpen hF (U := Metric.ball z r) Metric.isOpen_ball
      ⟨z, Metric.mem_ball_self hr⟩
  exact ⟨z', v, Metric.mem_ball.mp hz', hv⟩

theorem dist_cellCentroid_le_diam [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (v : V) {z : Plane} (hz : z ∈ (F.cell v : Set Plane)) :
    dist (cellCentroid F v) z ≤ Metric.diam (F.cell v : Set Plane) := by
  have hcompact : IsCompact (F.cell v : Set Plane) := (F.cell v).isCompact
  have hvol := cellVolume_pos_lt_top F hF v
  have hcentroid : cellCentroid F v = ⨍ x in (F.cell v : Set Plane), x ∂volume := by
    rw [setAverage_eq, measureReal_def]
    rfl
  have hmem : cellCentroid F v ∈
      Metric.closedBall z (Metric.diam (F.cell v : Set Plane)) := by
    rw [hcentroid]
    refine (convex_closedBall z _).set_average_mem Metric.isClosed_closedBall
      hvol.1.ne' hvol.2.ne ?_ ?_
    · filter_upwards [ae_restrict_mem hcompact.measurableSet] with x hx
      exact Metric.mem_closedBall.mpr
        (Metric.dist_le_diam_of_mem hcompact.isBounded hx hz)
    · exact ContinuousOn.integrableOn_compact hcompact continuous_id'.continuousOn
  exact Metric.mem_closedBall.mp hmem

/-! ## Submacroscopic cell diameters -/

/-- Uniformly submacroscopic cell diameters: every cell meeting `B(0,R)` has
diameter at most `η R` once `R` is large.  This is the exact analogue of
`StatementIngredients.UniformlySublinearError`, and it is the geometric input
that rules out a covering by huge concentric cells. -/
def SubmacroscopicDiameters (F : IndexedCells V) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ R₀ : ℝ, 0 < R₀ ∧
    ∀ R : ℝ, R₀ ≤ R → ∀ v : V,
      Hits F (Metric.closedBall (0 : Plane) R) v →
        Metric.diam (F.cell v : Set Plane) ≤ η * R

/-! ## The geometric contradiction -/

/-- Quantitative core: at a single scale `R`, constancy of `⟨ξ, Φ⟩` forces the
`2R‖ξ‖` directional separation of two antipodal cells to be absorbed by four
`η (R + r)` errors, plus the radius `r` within which the two antipodal points can be
approximated by covered points. -/
theorem two_mul_le_of_dirPairing_const [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (Phi : V → Plane) {ξ : Fin 2 → ℝ} (hξ : ξ ≠ 0) {η R r : ℝ} (hRpos : 0 < R)
    (hrpos : 0 < r)
    (hsubR : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) (R + r)) v →
      ‖Phi v - cellCentroid F v‖ ≤ η * (R + r))
    (hdiamR : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) (R + r)) v →
      Metric.diam (F.cell v : Set Plane) ≤ η * (R + r))
    (hconst : ∀ v w : V, dirPairing ξ (Phi v) = dirPairing ξ (Phi w)) :
    2 * R * (∑ i : Fin 2, ξ i * ξ i)
      ≤ 4 * ‖directionVector ξ‖ ^ 2 * (η * (R + r))
        + 2 * ‖directionVector ξ‖ ^ 2 * r := by
  have hKpos : 0 < ‖directionVector ξ‖ := norm_directionVector_pos hξ
  have hKne : ‖directionVector ξ‖ ≠ 0 := ne_of_gt hKpos
  obtain ⟨t, htpos, ht⟩ : ∃ t : ℝ, 0 < t ∧ t * ‖directionVector ξ‖ = R :=
    ⟨R / ‖directionVector ξ‖, div_pos hRpos hKpos, by field_simp⟩
  obtain ⟨zp, vp, hzp, hvp⟩ := exists_cell_mem_near F hF (t • directionVector ξ) hrpos
  obtain ⟨zm, vm, hzm, hvm⟩ := exists_cell_mem_near F hF ((-t) • directionVector ξ) hrpos
  have hnp : ‖t • directionVector ξ‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht]
  have hnm : ‖(-t) • directionVector ξ‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos htpos, ht]
  have hitp : Hits F (Metric.closedBall (0 : Plane) (R + r)) vp := by
    refine ⟨zp, hvp, Metric.mem_closedBall.mpr ?_⟩
    have h := dist_triangle zp (t • directionVector ξ) (0 : Plane)
    rw [dist_zero_right (t • directionVector ξ), hnp] at h
    linarith
  have hitm : Hits F (Metric.closedBall (0 : Plane) (R + r)) vm := by
    refine ⟨zm, hvm, Metric.mem_closedBall.mpr ?_⟩
    have h := dist_triangle zm ((-t) • directionVector ξ) (0 : Plane)
    rw [dist_zero_right ((-t) • directionVector ξ), hnm] at h
    linarith
  have hdp : ‖Phi vp - t • directionVector ξ‖ ≤ 2 * (η * (R + r)) + r := by
    rw [← dist_eq_norm]
    have h1 : dist (Phi vp) (cellCentroid F vp) ≤ η * (R + r) := by
      rw [dist_eq_norm]; exact hsubR vp hitp
    have h2 : dist (cellCentroid F vp) zp ≤ η * (R + r) :=
      (dist_cellCentroid_le_diam F hF vp hvp).trans (hdiamR vp hitp)
    have h3 := dist_triangle (Phi vp) (cellCentroid F vp) zp
    have h4 := dist_triangle (Phi vp) zp (t • directionVector ξ)
    linarith
  have hdm : ‖Phi vm - (-t) • directionVector ξ‖ ≤ 2 * (η * (R + r)) + r := by
    rw [← dist_eq_norm]
    have h1 : dist (Phi vm) (cellCentroid F vm) ≤ η * (R + r) := by
      rw [dist_eq_norm]; exact hsubR vm hitm
    have h2 : dist (cellCentroid F vm) zm ≤ η * (R + r) :=
      (dist_cellCentroid_le_diam F hF vm hvm).trans (hdiamR vm hitm)
    have h3 := dist_triangle (Phi vm) (cellCentroid F vm) zm
    have h4 := dist_triangle (Phi vm) zm ((-t) • directionVector ξ)
    linarith
  have hbp : |dirPairing ξ (Phi vp) - dirPairing ξ (t • directionVector ξ)|
      ≤ ‖directionVector ξ‖ * (2 * (η * (R + r)) + r) := by
    rw [← dirPairing_sub]
    exact (abs_dirPairing_le ξ _).trans (mul_le_mul_of_nonneg_left hdp (norm_nonneg _))
  have hbm : |dirPairing ξ (Phi vm) - dirPairing ξ ((-t) • directionVector ξ)|
      ≤ ‖directionVector ξ‖ * (2 * (η * (R + r)) + r) := by
    rw [← dirPairing_sub]
    exact (abs_dirPairing_le ξ _).trans (mul_le_mul_of_nonneg_left hdm (norm_nonneg _))
  rw [dirPairing_smul_directionVector] at hbp hbm
  have h1 := abs_le.mp hbp
  have h2 := abs_le.mp hbm
  have hc := hconst vp vm
  have hcore : 2 * t * (∑ i : Fin 2, ξ i * ξ i)
      ≤ 2 * (‖directionVector ξ‖ * (2 * (η * (R + r)) + r)) := by
    linarith [h1.1, h1.2, h2.1, h2.2]
  calc 2 * R * (∑ i : Fin 2, ξ i * ξ i)
      = 2 * t * (∑ i : Fin 2, ξ i * ξ i) * ‖directionVector ξ‖ := by rw [← ht]; ring
    _ ≤ 2 * (‖directionVector ξ‖ * (2 * (η * (R + r)) + r)) * ‖directionVector ξ‖ :=
        mul_le_mul_of_nonneg_right hcore (norm_nonneg _)
    _ = 4 * ‖directionVector ξ‖ ^ 2 * (η * (R + r))
          + 2 * ‖directionVector ξ‖ ^ 2 * r := by ring

/-- **Deterministic directional nondegeneracy.**  On a connected plane-covering
cell environment with uniformly sublinear corrector and submacroscopic cell
diameters, no nonzero direction has identically vanishing directional gradient. -/
theorem exists_edge_directionalGradient_ne_zero [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (Phi : V → Plane)
    (hsub : UniformlySublinearCorrector F Phi) (hdiam : SubmacroscopicDiameters F)
    {ξ : Fin 2 → ℝ} (hξ : ξ ≠ 0) :
    ∃ v w : V, 0 < F.graph.c v w ∧ directionalGradient Phi ξ v w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hKpos : 0 < ‖directionVector ξ‖ := norm_directionVector_pos hξ
  have hKne : ‖directionVector ξ‖ ≠ 0 := ne_of_gt hKpos
  have hQpos : 0 < ∑ i : Fin 2, ξ i * ξ i := sum_mul_self_pos hξ
  have h4 : (4 : ℝ) * ‖directionVector ξ‖ ^ 2 ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) (pow_pos hKpos 2))
  obtain ⟨η, hηpos, hηeq⟩ : ∃ η : ℝ, 0 < η ∧
      4 * ‖directionVector ξ‖ ^ 2 * η = ∑ i : Fin 2, ξ i * ξ i :=
    ⟨(∑ i : Fin 2, ξ i * ξ i) / (4 * ‖directionVector ξ‖ ^ 2),
      div_pos hQpos (mul_pos (by norm_num) (pow_pos hKpos 2)), by field_simp⟩
  obtain ⟨R₁, hR₁, hsubR⟩ := hsub η hηpos
  obtain ⟨R₂, hR₂, hdiamR⟩ := hdiam η hηpos
  have hRpos : 0 < max R₁ R₂ := lt_of_lt_of_le hR₁ (le_max_left _ _)
  -- the covered points approximating the two antipodal points are only nearby, so the
  -- estimate carries an extra error linear in the approximation radius; choose the radius
  -- small enough that the error is strictly smaller than the slack
  obtain ⟨r, hrpos, hrlt⟩ := exists_pos_mul_lt (mul_pos hRpos hQpos)
    ((∑ i : Fin 2, ξ i * ξ i) + 2 * ‖directionVector ξ‖ ^ 2)
  have hconst := dirPairing_eq_of_forall_edge_directionalGradient_eq_zero F
    hF.2.2.2.2.2.1 Phi ξ hcon
  have hmain := two_mul_le_of_dirPairing_const F hF Phi hξ hRpos hrpos
    (hsubR (max R₁ R₂ + r) (by linarith [le_max_left R₁ R₂]))
    (hdiamR (max R₁ R₂ + r) (by linarith [le_max_right R₁ R₂])) hconst
  have hrw : 4 * ‖directionVector ξ‖ ^ 2 * (η * (max R₁ R₂ + r))
      = (∑ i : Fin 2, ξ i * ξ i) * (max R₁ R₂ + r) := by
    rw [← hηeq]; ring
  rw [hrw] at hmain
  nlinarith [hrlt, hmain]

/-! ## The directional form of the deterministic mean covariance -/

section MeanCovariance

open Code EnvironmentFields HarmonicLawIngredients

theorem quadraticForm_meanCovariance_eq_integral (ν : Measure Env) (Φ : CellField)
    (hint : IntegrableBracket ν Φ) (ξ : Fin 2 → ℝ) :
    ∑ i : Fin 2, ∑ j : Fin 2, ξ i * meanCovariance ν Φ i j * ξ j
      = ∫ e, (∑ i : Fin 2, ∑ j : Fin 2,
          ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j) ∂ν := by
  have hintegrable : ∀ i j : Fin 2,
      Integrable (fun e => ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j) ν :=
    fun i j => ((hint i j).const_mul (ξ i)).mul_const (ξ j)
  have hterm : ∀ i j : Fin 2,
      ∫ e, ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j ∂ν
        = ξ i * meanCovariance ν Φ i j * ξ j := by
    intro i j
    have hfun : (fun e => ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j)
        = fun e => (ξ i * ξ j) * rootedGamma (decode e) (Φ.at e) 0 i j := by
      funext e; ring
    rw [hfun, integral_const_mul]
    show (ξ i * ξ j) * (∫ e, rootedGamma (decode e) (Φ.at e) 0 i j ∂ν)
      = ξ i * (∫ e, rootedGamma (decode e) (Φ.at e) 0 i j ∂ν) * ξ j
    ring
  symm
  calc ∫ e, (∑ i : Fin 2, ∑ j : Fin 2,
          ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j) ∂ν
      = ∑ i : Fin 2, ∫ e, (∑ j : Fin 2,
          ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j) ∂ν :=
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hintegrable i j
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
          ∫ e, ξ i * rootedGamma (decode e) (Φ.at e) 0 i j * ξ j ∂ν :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hintegrable i j
    _ = ∑ i : Fin 2, ∑ j : Fin 2, ξ i * meanCovariance ν Φ i j * ξ j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j

theorem quadraticForm_meanCovariance_nonneg (ν : Measure Env) (Φ : CellField)
    (hint : IntegrableBracket ν Φ) (ξ : Fin 2 → ℝ) :
    0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ξ i * meanCovariance ν Φ i j * ξ j := by
  rw [quadraticForm_meanCovariance_eq_integral ν Φ hint ξ]
  refine integral_nonneg fun e => ?_
  exact quadraticForm_rootedGamma_nonneg (decode e) (decode_geometry e) (Φ.at e) 0 ξ

end MeanCovariance

end ReflectedGMS.DirectionalNondegeneracy
