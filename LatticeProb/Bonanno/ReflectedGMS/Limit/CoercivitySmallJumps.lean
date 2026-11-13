/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CoercivitySmallJumps at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalNondegeneracy
import LatticeProb.Bonanno.ReflectedGMS.Spatial.LargeCellDiameterDecay

/-!
# Coercivity and small potential jumps from a bounded region

This file proves the manuscript's Lemma `p:lem:coercive` in full, deterministically,
for a cell environment `F` with

* cell representatives `z` (`StatementIngredients.CellRepresentatives`),
* a uniformly sublinear corrector error against those representatives
  (`StatementIngredients.UniformlySublinearError`, the manuscript's `p:eq:corrector`), and
* submacroscopic cell diameters
  (`DirectionalNondegeneracy.SubmacroscopicDiameters`, the manuscript's `D_R = o(R)`
  from `p:eq:mesh`, which `Spatial.maxDiamHittingBall_sublinear` already proves).

Both clauses are obtained.

* **Coercivity `p:eq:coercive`** (`exists_coercivity_constant`): there is a finite
  `K₀` with `‖z v‖ ≤ 2‖Φ v‖ + K₀` for *every* vertex.  At a vertex with
  `r = ‖z v‖` large the cell meets `B̄(0, r)`, so sublinearity at scale `η = 1/2`
  gives `‖Φ v - z v‖ ≤ r/2`, hence `r ≤ 2‖Φ v‖`; on the remaining bounded region
  `‖z v‖` is bounded by the sublinearity threshold itself.  No boundedness of the
  corrector on a finite ball is assumed: one sufficiently large scale suffices.

* **Small jumps `p:eq:allpossiblejumps`** (`tendsto_maxNeighborJump`): for each
  fixed `R ≥ 0`, `ε ↦ sup {ε‖Φ w - Φ v‖ : 0 < c v w, ‖z v‖ ≤ R/ε}` tends to `0` as
  `ε ↓ 0`.  Writing `L = R'/ε` with `R' = max R 1 > 0`, a vertex with `‖z v‖ ≤ L`
  has its whole cell inside `B̄(0, 2L)` once the diameters are submacroscopic, so
  *every* neighbour `w` — including those leaving the starting ball — also meets
  `B̄(0, 2L)`.  Four `o(L)` errors (two corrector errors and two cell diameters
  across the contact point) then bound `‖Φ w - Φ v‖`, and `εL = R'` is fixed.
  The `ε`-`δ` form `exists_pos_forall_neighbor_smallJump` avoids any supremum
  convention; the supremum form is connected through `Real.sSup_le` and
  `Real.sSup_nonneg` (over `ℝ` the empty supremum is `0`, which is the limit).

The corrector's existence is not addressed here; it is the upstream theorem.  Two
small bridges are included so that the hypotheses are the ones already available:
`submacroscopicDiameters_of_finite_scaledNear` derives the diameter hypothesis
from the proved large-cell decay, and
`uniformlySublinearError_representative_of_corrector` converts the centroid form
of sublinearity into the representative form using
`DirectionalNondegeneracy.dist_cellCentroid_le_diam`.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS.CoercivitySmallJumps

open StatementIngredients DirectionalNondegeneracy

variable {V : Type*}

/-! ## Elementary hitting geometry -/

/-- A cell containing a point of norm at most `R` meets `B̄(0, R)`. -/
theorem hits_closedBall_of_mem (F : IndexedCells V) {v : V} {x : Plane}
    (hx : x ∈ (F.cell v : Set Plane)) {R : ℝ} (hR : ‖x‖ ≤ R) :
    Hits F (Metric.closedBall (0 : Plane) R) v :=
  ⟨x, hx, Metric.mem_closedBall.mpr (by rwa [dist_zero_right])⟩

/-- Two points of one cell differ in norm by at most the cell diameter. -/
theorem norm_le_of_mem_cell (F : IndexedCells V) {v : V} {x y : Plane}
    (hx : x ∈ (F.cell v : Set Plane)) (hy : y ∈ (F.cell v : Set Plane)) :
    ‖x‖ ≤ ‖y‖ + Metric.diam (F.cell v : Set Plane) := by
  have hd : dist x y ≤ Metric.diam (F.cell v : Set Plane) :=
    Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded hx hy
  have ht : dist x (0 : Plane) ≤ dist x y + dist y (0 : Plane) := dist_triangle _ _ _
  rw [dist_zero_right, dist_zero_right] at ht
  linarith

/-- A cell with a representative in `B̄(0, L)` and diameter at most `d` is contained
in `B̄(0, L + d)`. -/
theorem cell_subset_closedBall (F : IndexedCells V) {v : V} {x : Plane}
    (hx : x ∈ (F.cell v : Set Plane)) {L d : ℝ} (hL : ‖x‖ ≤ L)
    (hd : Metric.diam (F.cell v : Set Plane) ≤ d) :
    (F.cell v : Set Plane) ⊆ Metric.closedBall (0 : Plane) (L + d) := by
  intro y hy
  have h := norm_le_of_mem_cell F hy hx
  refine Metric.mem_closedBall.mpr ?_
  rw [dist_zero_right]
  linarith

/-! ## Clause one: coercivity -/

/-- **Manuscript `p:eq:coercive`.**  There is a finite environment-dependent `K₀`
with `|z_H| ≤ 2|Φ(H)| + K₀` at every vertex.  Only the corrector sublinearity at
the single scale `η = 1/2` is used. -/
theorem exists_coercivity_constant (F : IndexedCells V) (Φ z : V → Plane)
    (hz : CellRepresentatives F z) (hsub : UniformlySublinearError F Φ z) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ v : V, ‖z v‖ ≤ 2 * ‖Φ v‖ + K₀ := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := hsub (1 / 2) (by norm_num)
  refine ⟨R₀, hR₀pos.le, fun v => ?_⟩
  rcases le_or_gt (‖z v‖) R₀ with h | h
  · linarith [norm_nonneg (Φ v)]
  · have hhit : Hits F (Metric.closedBall (0 : Plane) ‖z v‖) v :=
      hits_closedBall_of_mem F (hz v) le_rfl
    have hb := hR₀ ‖z v‖ h.le v hhit
    have h1 : ‖z v‖ ≤ ‖Φ v‖ + ‖Φ v - z v‖ := by
      calc ‖z v‖ = ‖Φ v - (Φ v - z v)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖Φ v‖ + ‖Φ v - z v‖ := norm_sub_le _ _
    linarith

/-! ## Clause two: all neighbour jumps from a bounded region -/

/-- The single-scale geometric core.  If `‖z v‖ ≤ L` and both the corrector error
and the cell diameters are at most `η · 2L` on all cells meeting `B̄(0, 2L)`, then
*every* neighbour `w` of `v` satisfies `‖Φ w - Φ v‖ ≤ 8ηL`.  The neighbour is not
assumed to meet the starting ball: its own cell touches the cell of `v`, which is
contained in `B̄(0, 2L)`. -/
theorem norm_gradient_le_of_norm_representative_le [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (Φ z : V → Plane) (hz : CellRepresentatives F z)
    {η L : ℝ} (hη : 0 ≤ η) (hη2 : η ≤ 1 / 2) (hL : 0 ≤ L)
    (hsubL : ∀ u : V, Hits F (Metric.closedBall (0 : Plane) (2 * L)) u →
      ‖Φ u - z u‖ ≤ η * (2 * L))
    (hdiamL : ∀ u : V, Hits F (Metric.closedBall (0 : Plane) (2 * L)) u →
      Metric.diam (F.cell u : Set Plane) ≤ η * (2 * L))
    {v w : V} (hadj : 0 < F.graph.c v w) (hv : ‖z v‖ ≤ L) :
    ‖Φ w - Φ v‖ ≤ 8 * (η * L) := by
  have hvL : Hits F (Metric.closedBall (0 : Plane) (2 * L)) v :=
    hits_closedBall_of_mem F (hz v) (by linarith)
  have hdv := hdiamL v hvL
  have hsubv := hsubL v hvL
  have hcellv : (F.cell v : Set Plane) ⊆ Metric.closedBall (0 : Plane) (2 * L) := by
    refine (cell_subset_closedBall F (hz v) hv hdv).trans
      (Metric.closedBall_subset_closedBall ?_)
    nlinarith [mul_nonneg hL (sub_nonneg.mpr hη2)]
  obtain ⟨p, hpv, hpw⟩ := hF.2.2.2.2.2.2.2 (F.graph.toSimpleGraph_adj.mpr hadj)
  have hwL : Hits F (Metric.closedBall (0 : Plane) (2 * L)) w := ⟨p, hpw, hcellv hpv⟩
  have hdw := hdiamL w hwL
  have hsubw := hsubL w hwL
  have hzv : dist p (z v) ≤ η * (2 * L) :=
    (Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded hpv (hz v)).trans hdv
  have hzw : dist p (z w) ≤ η * (2 * L) :=
    (Metric.dist_le_diam_of_mem (F.cell w).isCompact.isBounded hpw (hz w)).trans hdw
  have hzz : ‖z w - z v‖ ≤ 2 * (η * (2 * L)) := by
    rw [← dist_eq_norm]
    calc dist (z w) (z v) ≤ dist (z w) p + dist p (z v) := dist_triangle _ _ _
      _ ≤ η * (2 * L) + η * (2 * L) := add_le_add (by rw [dist_comm]; exact hzw) hzv
      _ = 2 * (η * (2 * L)) := by ring
  have heq : Φ w - Φ v = (Φ w - z w) + ((z w - z v) + (z v - Φ v)) := by abel
  have hfin : ‖Φ w - Φ v‖ ≤ ‖Φ w - z w‖ + (‖z w - z v‖ + ‖z v - Φ v‖) := by
    rw [heq]
    exact (norm_add_le _ _).trans
      (add_le_add (le_refl ‖Φ w - z w‖) (norm_add_le (z w - z v) (z v - Φ v)))
  have hrev : ‖z v - Φ v‖ = ‖Φ v - z v‖ := norm_sub_rev _ _
  rw [hrev] at hfin
  have hrw : η * (2 * L) = 2 * (η * L) := by ring
  rw [hrw] at hsubv hsubw hzz
  linarith

/-- **Manuscript `p:eq:allpossiblejumps`, `ε`-`δ` form.**  For each fixed `R ≥ 0`
and each `δ > 0` there is `ε₀ > 0` such that for all `0 < ε ≤ ε₀`, every vertex
`v` with `‖z v‖ ≤ R/ε` and every neighbour `w` of `v` satisfy
`ε‖Φ w - Φ v‖ ≤ δ`.  The case `R = 0` is covered by enlarging `R` to `max R 1`. -/
theorem exists_pos_forall_neighbor_smallJump [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (Φ z : V → Plane) (hz : CellRepresentatives F z)
    (hsub : UniformlySublinearError F Φ z) (hdiam : SubmacroscopicDiameters F)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ v w : V, 0 < F.graph.c v w →
      ‖z v‖ ≤ R / ε → ε * ‖Φ w - Φ v‖ ≤ δ := by
  obtain ⟨R', hR'pos, hRR'le⟩ : ∃ R' : ℝ, 0 < R' ∧ R ≤ R' :=
    ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), le_max_left _ _⟩
  obtain ⟨η, hηpos, hη2, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ 8 * (η * R') ≤ δ := by
    refine ⟨min (1 / 2) (δ / (16 * R')),
      lt_min (by norm_num) (div_pos hδ (by linarith)), min_le_left _ _, ?_⟩
    have h : min (1 / 2) (δ / (16 * R')) ≤ δ / (16 * R') := min_le_right _ _
    have h16 : (0 : ℝ) < 16 * R' := by linarith
    have h2 : min (1 / 2) (δ / (16 * R')) * (16 * R') ≤ δ := (le_div_iff₀ h16).mp h
    have h3 : 0 ≤ min (1 / 2) (δ / (16 * R')) * R' :=
      mul_nonneg (le_min (by norm_num) (div_pos hδ h16).le) hR'pos.le
    linarith
  obtain ⟨R₁, hR₁pos, hR₁⟩ := hsub η hηpos
  obtain ⟨R₂, hR₂pos, hR₂⟩ := hdiam η hηpos
  have hMpos : 0 < max R₁ R₂ := lt_of_lt_of_le hR₁pos (le_max_left _ _)
  refine ⟨2 * R' / max R₁ R₂, div_pos (by linarith) hMpos, ?_⟩
  intro ε hε hεle v w hc hzv
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hLpos : 0 < R' / ε := div_pos hR'pos hε
  -- the working scale `L = R'/ε`, with `2L` beyond both sublinearity thresholds
  have hML : max R₁ R₂ ≤ 2 * (R' / ε) := by
    have h1 : ε * max R₁ R₂ ≤ 2 * R' := (le_div_iff₀ hMpos).mp hεle
    rw [mul_comm] at h1
    calc max R₁ R₂ ≤ 2 * R' / ε := (le_div_iff₀ hε).mpr h1
      _ = 2 * (R' / ε) := by rw [mul_div_assoc]
  have hsubL : ∀ u : V, Hits F (Metric.closedBall (0 : Plane) (2 * (R' / ε))) u →
      ‖Φ u - z u‖ ≤ η * (2 * (R' / ε)) :=
    hR₁ (2 * (R' / ε)) (le_trans (le_max_left _ _) hML)
  have hdiamL : ∀ u : V, Hits F (Metric.closedBall (0 : Plane) (2 * (R' / ε))) u →
      Metric.diam (F.cell u : Set Plane) ≤ η * (2 * (R' / ε)) :=
    hR₂ (2 * (R' / ε)) (le_trans (le_max_right _ _) hML)
  have hRR' : R / ε ≤ R' / ε := by
    have hinv : (0 : ℝ) ≤ ε⁻¹ := (inv_pos.mpr hε).le
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hRR'le hinv
  have hcore := norm_gradient_le_of_norm_representative_le F hF Φ z hz hηpos.le hη2
    hLpos.le hsubL hdiamL hc (le_trans hzv hRR')
  have hmul : ε * ‖Φ w - Φ v‖ ≤ ε * (8 * (η * (R' / ε))) :=
    mul_le_mul_of_nonneg_left hcore hε.le
  have hsimp : ε * (8 * (η * (R' / ε))) = 8 * (η * R') * (ε * ε⁻¹) := by
    rw [div_eq_mul_inv]; ring
  rw [hsimp, mul_inv_cancel₀ hεne, mul_one] at hmul
  linarith

/-! ## The manuscript supremum -/

/-! ## The full manuscript lemma -/

/-! ## Discharging the two geometric hypotheses from existing results -/

/-- `D_R ≤ ηR` in the `ℝ≥0∞` form proved in `Spatial.LargeCellDiameterDecay` gives
the `SubmacroscopicDiameters` predicate used above. -/
theorem submacroscopicDiameters_of_maxDiamHittingBall_sublinear (F : IndexedCells V)
    (h : ∀ η : ℝ, 0 < η → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      Spatial.maxDiamHittingBall F R ≤ ENNReal.ofReal (η * R)) :
    SubmacroscopicDiameters F := by
  intro η hη
  obtain ⟨R₀, hR₀pos, hR₀⟩ := h η hη
  refine ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun R hR v hv => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right R₀ 1)) hR
  have hmem : ENNReal.ofReal (Metric.diam (F.cell v : Set Plane))
      ≤ Spatial.maxDiamHittingBall F R :=
    le_iSup (fun u : {u : V // Hits F (Metric.closedBall (0 : Plane) R) u} =>
      ENNReal.ofReal (Metric.diam (F.cell u.1 : Set Plane))) ⟨v, hv⟩
  have hle := hmem.trans (hR₀ R (le_trans (le_max_left _ _) hR))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hη.le hRpos.le)).mp hle

/-- The manuscript's `p:eq:mesh` input, straight from the proved large-cell decay. -/
theorem submacroscopicDiameters_of_finite_scaledNear (F : IndexedCells V)
    (hfin : ∀ n : ℕ,
      {v : V | (0 : Plane) ∈ Spatial.cellScaledNeighborhood (n : ℝ) (F.cell v)}.Finite) :
    SubmacroscopicDiameters F :=
  submacroscopicDiameters_of_maxDiamHittingBall_sublinear F
    (Spatial.maxDiamHittingBall_sublinear F hfin)

end ReflectedGMS.CoercivitySmallJumps
