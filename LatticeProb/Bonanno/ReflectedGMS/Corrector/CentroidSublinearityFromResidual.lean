/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.CentroidSublinearityFromResidual at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ActualUniformSublinearity
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GoodOffsetWindowAssembly
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ResidualEnergyLineVariation

/-!
# `s:eq:sublinear` for the limiting corrector, from small residuals

This module closes the deterministic half of the manuscript's uniform sublinearity
display `s:eq:sublinear` **for the limit** `Φ`, not merely for a fixed block approximant
`φ_m`.  The fixed-parameter statement is the already checked
`Corrector/ActualUniformSublinearity`; it does *not* imply the limiting one, because the
radius threshold of `s:eq:fixedapprox` depends on the block parameter `m` and the
`m`-selected blocks grow with `m`.  The manuscript's own argument is followed instead:

1. the residual `r = Φ - φ_m` has small mean line variation on `Q_R = [-2R,2R]²`
   (`s:eq:smallmeanTV`), so a whole grid of good horizontal and vertical offsets can be
   selected window by window — the checked
   `GoodOffsetWindowAssembly.exists_goodOffsetGrid_of_patchSmallness`;
2. along the selected lines the oscillation of each coordinate of `r` is small, hence any
   two cells of the grid skeleton `𝒯` differ by at most `3 t` — the checked
   `abs_sub_le_three_mul_of_mem_gridCells` (`s:eq:gridresidual`);
3. every remaining cell of the patch is confined to a grid rectangle with small sides all
   of whose boundary cells lie in `𝒯` — the checked
   `exists_gridRectangle_of_notMem_gridCells`;
4. the **full variational maximum principle** on that rectangle transfers the boundary
   bound to the interior cell.  Nothing about the maximum principle is reproved: the
   single analytic input is the checked componentwise
   `FullEnergyTraceBounds.coord_mem_Icc_of_vector_trace_minimizer_on_component`, exactly
   as in `GoodGridMaximumPrinciple.norm_corrector_sub_le_of_notMem_gridCells`.  The only
   new thing here is a *coordinatewise* repackaging of that step
   (`abs_coord_sub_le_of_notMem_gridCells`), which is what allows the two coordinates to
   use **two different** good grids — the offset selector selects for one scalar function
   at a time, and a common grid for both coordinates is produced nowhere in the project;
5. the fixed-parameter centroid bound `s:eq:fixedapprox` converts the bound on `r` into a
   bound on `Φ - b`, and root normalization `Φ(H_0) = 0` removes the free vector `c_R`.

Everything below is deterministic and pathwise.

## What is **not** reproved

`GoodGridMaximumPrinciple.norm_sub_le_of_vector_trace_minimizer_on_component`,
`exists_gridRectangle_of_notMem_gridCells`, `boundaryAnchored_restrictGraph_cells_hitting`,
`abs_sub_le_three_mul_of_mem_gridCells`,
`ActualUniformSublinearity.norm_sub_cellCentroid_le_of_isBlockInterpolation`,
`NonmacroscopicSelectedBlocks.maxSelectedSide_le_ofReal`,
`GoodOffsetWindowAssembly.exists_goodOffsetGrid_of_patchSmallness`,
`ResidualEnergyLineVariation.sqrt_mass_mul_sqrt_energy_le` and
`ResidualEnergyLineVariation.ballPatchVectorEnergy_le_of_maxDiam` are used verbatim.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS.CentroidSublinearityFromResidual

open StatementIngredients DyadicApproximation NonmacroscopicSelectedBlocks Spatial
open RootDensities ResidualEnergyLineVariation GoodOffsetWindowAssembly
open ActualUniformSublinearity GoodGridMaximumPrinciple

variable {V : Type*}

/-! ### Elementary plane and `ℝ≥0∞` arithmetic -/

theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h : Real.sqrt 2 ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h

/-- A plane vector with both coordinates bounded by `K` has norm at most `2 K`. -/
theorem norm_le_two_mul_of_coord_le {z : Plane} {K : ℝ} (h : ∀ j : Fin 2, |z j| ≤ K) :
    ‖z‖ ≤ 2 * K := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (h 0)
  exact le_trans (norm_le_sqrt_two_mul h) (mul_le_mul_of_nonneg_right sqrt_two_le_two hK0)

/-- Two points of a closed patch with both sides at most `L` have coordinates within `L`. -/
theorem abs_coord_sub_le_of_mem_closedPatch {x₁ x₂ y₁ y₂ L : ℝ} {z p : Plane}
    (hz : z ∈ closedPatch x₁ x₂ y₁ y₂) (hp : p ∈ closedPatch x₁ x₂ y₁ y₂)
    (hx : x₂ - x₁ ≤ L) (hy : y₂ - y₁ ≤ L) (j : Fin 2) : |z j - p j| ≤ L := by
  have h0 : |z 0 - p 0| ≤ L := by
    rw [abs_le]
    exact ⟨by linarith [hz.1, hz.2.1, hp.1, hp.2.1],
      by linarith [hz.1, hz.2.1, hp.1, hp.2.1]⟩
  have h1 : |z 1 - p 1| ≤ L := by
    rw [abs_le]
    exact ⟨by linarith [hz.2.2.1, hz.2.2.2, hp.2.2.1, hp.2.2.2],
      by linarith [hz.2.2.1, hz.2.2.2, hp.2.2.1, hp.2.2.2]⟩
  fin_cases j
  · exact h0
  · exact h1

/-- One coordinate of the centroid is within the cell diameter of the same coordinate of
any point of the cell. -/
theorem abs_coord_cellCentroid_sub_le_diam [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (v : V) {q : Plane} (hq : q ∈ (F.cell v : Set Plane)) (j : Fin 2) :
    |cellCentroid F v j - q j| ≤ Metric.diam (F.cell v : Set Plane) := by
  have hc : (cellCentroid F v - q) j = cellCentroid F v j - q j := by simp
  have h := abs_coord_le_norm (cellCentroid F v - q) j
  rw [hc, ← dist_eq_norm] at h
  exact le_trans h (dist_cellCentroid_le_diam F hF v hq)

/-- A cell meeting `clB R` has all its points within `R + d` of the origin, coordinatewise,
when `d` bounds its diameter. -/
theorem abs_coord_le_of_hits_closedBall (F : IndexedCells V) {R d : ℝ} {v : V}
    (hv : Hits F (Metric.closedBall (0 : Plane) R) v)
    (hd : Metric.diam (F.cell v : Set Plane) ≤ d) {z : Plane}
    (hz : z ∈ (F.cell v : Set Plane)) (i : Fin 2) : |z i| ≤ R + d := by
  obtain ⟨p, hpc, hpb⟩ := hv
  have hbdd : Bornology.IsBounded (F.cell v : Set Plane) := (F.cell v).isCompact.isBounded
  have hdist : dist z p ≤ Metric.diam (F.cell v : Set Plane) :=
    Metric.dist_le_diam_of_mem hbdd hz hpc
  have hpn : ‖p‖ ≤ R := by
    rw [Metric.mem_closedBall, dist_zero_right] at hpb
    exact hpb
  have hzp : |(z - p) i| ≤ ‖z - p‖ := abs_coord_le_norm (z - p) i
  have hzpc : (z - p) i = z i - p i := by simp
  have hpi : |p i| ≤ ‖p‖ := abs_coord_le_norm p i
  rw [hzpc, ← dist_eq_norm] at hzp
  have h1 : |z i - p i| ≤ d := le_trans (le_trans hzp hdist) hd
  calc |z i| = |(z i - p i) + p i| := by ring_nf
    _ ≤ |z i - p i| + |p i| := abs_add_le _ _
    _ ≤ d + R := add_le_add h1 (le_trans hpi hpn)
    _ = R + d := by ring

/-- If `L` is finite and `c` is a positive finite target, then `L · √M < c` for all
sufficiently small `M`. -/
theorem exists_pos_forall_lt_of_mul_rpow_half (L c : ℝ≥0∞) (hL : L ≠ ∞) (hc0 : 0 < c)
    (hc : c ≠ ∞) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ M : ℝ≥0∞, M < ε → L * M ^ (2⁻¹ : ℝ) < c := by
  have hL'0 : L + 1 ≠ 0 := by simp
  have hL'top : L + 1 ≠ ∞ := by simp [hL]
  have hcL : 0 < c / (L + 1) := ENNReal.div_pos hc0.ne' hL'top
  have hcLtop : c / (L + 1) ≠ ∞ := (ENNReal.div_lt_top hc hL'0).ne
  have hd0 : 0 < c / (L + 1) / 2 := ENNReal.div_pos hcL.ne' (by norm_num)
  have hdtop : c / (L + 1) / 2 ≠ ∞ := (ENNReal.div_lt_top hcLtop (by norm_num)).ne
  refine ⟨(c / (L + 1) / 2) ^ (2 : ℝ), ENNReal.rpow_pos hd0 hdtop, ?_⟩
  intro M hM
  have hMhalf : M ^ (2⁻¹ : ℝ) < ((c / (L + 1) / 2) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) :=
    ENNReal.rpow_lt_rpow hM (by norm_num)
  have hdd : ((c / (L + 1) / 2) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) = c / (L + 1) / 2 := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hdd] at hMhalf
  have hmul : M ^ (2⁻¹ : ℝ) * (L + 1) < c / (L + 1) / 2 * (L + 1) :=
    ENNReal.mul_lt_mul_left hL'0 hL'top hMhalf
  have hcancel : (L + 1) * (c / (L + 1)) = c :=
    ENNReal.mul_div_cancel' (fun h => absurd h hL'0) (fun h => absurd h hL'top)
  have hL'd : c / (L + 1) / 2 * (L + 1) = c / 2 := by
    rw [mul_comm, ← mul_div_assoc, hcancel]
  calc L * M ^ (2⁻¹ : ℝ) = M ^ (2⁻¹ : ℝ) * L := mul_comm _ _
    _ ≤ M ^ (2⁻¹ : ℝ) * (L + 1) := mul_le_mul' le_rfl le_self_add
    _ < c / (L + 1) / 2 * (L + 1) := hmul
    _ = c / 2 := hL'd
    _ < c := ENNReal.half_lt_self hc0.ne' hc

/-! ### The coordinatewise maximum-principle step -/

/-- **The manuscript's final paragraph, one coordinate at a time.**  This is
`GoodGridMaximumPrinciple.norm_corrector_sub_le_of_notMem_gridCells` with the vector
conclusion replaced by a single coordinate, so that the two coordinates may be run on two
*different* good grids.  The analytic input is unchanged: the checked componentwise
maximum principle
`FullEnergyTraceBounds.coord_mem_Icc_of_vector_trace_minimizer_on_component`
on the grid rectangle produced by the checked
`exists_gridRectangle_of_notMem_gridCells`. -/
theorem abs_coord_sub_le_of_notMem_gridCells [Countable V] (F : IndexedCells V)
    (hF : Geometry F) {Φ b : V → Plane} (hΦ : FullRectangleMinimizer F Φ) (i : Fin 2)
    {ci : ℝ} {A B C D g t δ : ℝ} {xs ys : Set ℝ}
    (hxs : xs ⊆ Set.Icc A B) (hys : ys ⊆ Set.Icc C D)
    (hxfwd : ∀ u ∈ Set.Icc A B, ∃ x ∈ xs, u ≤ x ∧ x ≤ u + g)
    (hxbwd : ∀ u ∈ Set.Icc A B, ∃ x ∈ xs, u - g ≤ x ∧ x ≤ u)
    (hyfwd : ∀ u ∈ Set.Icc C D, ∃ y ∈ ys, u ≤ y ∧ y ≤ u + g)
    (hybwd : ∀ u ∈ Set.Icc C D, ∃ y ∈ ys, u - g ≤ y ∧ y ≤ u)
    (hgrid : ∀ u ∈ gridCells F A B C D xs ys, |Φ u i - b u i - ci| ≤ t)
    {v : V} (hv : v ∉ gridCells F A B C D xs ys)
    (hcell : (F.cell v : Set Plane) ⊆ closedPatch A B C D)
    (hcent : ∀ x₁ x₂ y₁ y₂ : ℝ, (F.cell v : Set Plane) ⊆ closedPatch x₁ x₂ y₁ y₂ →
      x₂ - x₁ ≤ 2 * g → y₂ - y₁ ≤ 2 * g →
      ∀ u : V, Hits F (closedPatch x₁ x₂ y₁ y₂) u → |b u i - b v i| ≤ δ) :
    |Φ v i - b v i - ci| ≤ t + δ := by
  obtain ⟨x₁, hx₁, x₂, hx₂, y₁, hy₁, y₂, hy₂, hxlen, hylen, hsub, hframe⟩ :=
    exists_gridRectangle_of_notMem_gridCells F hF.1 hxs hys hxfwd hxbwd hyfwd hybwd hv hcell
  obtain ⟨z, hz⟩ := (hF.1 v).nonempty
  have hzo := hsub hz
  have hxlt : x₁ < x₂ := lt_trans hzo.1 hzo.2.1
  have hylt : y₁ < y₂ := lt_trans hzo.2.2.1 hzo.2.2.2
  set Q : Rectangle := gridRectangle x₁ x₂ y₁ y₂ hxlt hylt with hQ
  have hQc : Q.carrier = closedPatch x₁ x₂ y₁ y₂ := carrier_gridRectangle x₁ x₂ y₁ y₂ hxlt hylt
  have hcellQ : (F.cell v : Set Plane) ⊆ Q.carrier := by
    rw [hQc]
    exact hsub.trans (openRectangle_subset_closedPatch x₁ x₂ y₁ y₂)
  have hvQ : v ∈ patchVertices F Q := ⟨z, hz, hcellQ hz⟩
  have hbdry : ∀ a : V, a ∈ boundaryVertices F Q → a ∈ gridCells F A B C D xs ys := by
    intro a ha
    obtain ⟨p, hp, hpf⟩ := ha
    rw [hQc] at hpf
    exact hframe a ⟨p, hp, frontier_closedPatch_subset_rectangleFrame x₁ x₂ y₁ y₂ hpf⟩
  have hanch : BoundaryAnchored (restrictGraph F.graph (patchVertices F Q))
      {a : patchVertices F Q | a.1 ∈ boundaryVertices F Q} :=
    boundaryAnchored_restrictGraph_cells_hitting F hF Q.carrier
      (by rw [hQc]; exact isBounded_closedPatch x₁ x₂ y₁ y₂)
  obtain ⟨hfin, hmin⟩ := hΦ Q
  have hIcc : (fun a : patchVertices F Q => Φ a.1) ⟨v, hvQ⟩ i ∈
      Set.Icc (b v i + ci - (t + δ)) (b v i + ci + (t + δ)) := by
    refine FullEnergyTraceBounds.coord_mem_Icc_of_vector_trace_minimizer_on_component
      (restrictGraph F.graph (patchVertices F Q)) hanch
      (u := fun a : patchVertices F Q => Φ a.1) hfin (fun _ _ => rfl)
      (fun gg hgg => (hmin gg hgg).1) i ?_
    intro a ha _
    have h1 : |Φ a.1 i - b a.1 i - ci| ≤ t := hgrid a.1 (hbdry a.1 ha)
    have h2 : |b a.1 i - b v i| ≤ δ :=
      hcent x₁ x₂ y₁ y₂ (by rw [← hQc]; exact hcellQ) hxlen hylen a.1
        (by
          have haQ : Hits F Q.carrier a.1 := a.2
          rwa [hQc] at haQ)
    rw [Set.mem_Icc]
    rw [abs_le] at h1 h2
    exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  rw [abs_le]
  exact ⟨by linarith [hIcc.1], by linarith [hIcc.2]⟩

/-! ### The centroid bookkeeping `s:eq:boundarycentroid` -/

/-- **`s:eq:boundarycentroid`, coordinatewise.**  A cell meeting a rectangle with sides at
most `4 w` that contains the cell of `v` has its centroid within `2 α R` of the centroid of
`v`, once `w ≤ α R / 8` and the cells near `clB 3R` have diameter at most `α R / 16`. -/
theorem abs_coord_cellCentroid_sub_le_of_smallRectangle [Countable V] (F : IndexedCells V)
    (hF : Geometry F) {R α w : ℝ} (hα : 0 < α) (hR : 0 < R) (hαR : α * R ≤ R)
    (hw : 0 < w) (hwsmall : w ≤ α * R / 8)
    (hdiam : ∀ u : V, Hits F (Metric.closedBall (0 : Plane) (3 * R)) u →
      Metric.diam (F.cell u : Set Plane) ≤ α * R / 16)
    {v : V} (hv : Hits F (Metric.closedBall (0 : Plane) R) v) (i : Fin 2)
    (x₁ x₂ y₁ y₂ : ℝ) (hcellv : (F.cell v : Set Plane) ⊆ closedPatch x₁ x₂ y₁ y₂)
    (hxl : x₂ - x₁ ≤ 2 * (2 * w)) (hyl : y₂ - y₁ ≤ 2 * (2 * w))
    (u : V) (hu : Hits F (closedPatch x₁ x₂ y₁ y₂) u) :
    |cellCentroid F u i - cellCentroid F v i| ≤ 2 * (α * R) := by
  have hαRpos : 0 < α * R := mul_pos hα hR
  have hv3 : Hits F (Metric.closedBall (0 : Plane) (3 * R)) v := by
    obtain ⟨p, hpc, hpb⟩ := hv
    exact ⟨p, hpc, Metric.closedBall_subset_closedBall (by linarith) hpb⟩
  obtain ⟨qv, hqv⟩ := (hF.1 v).nonempty
  obtain ⟨qu, hquc, hqup⟩ := hu
  have hqvp := hcellv hqv
  have hdv := hdiam v hv3
  -- the small rectangle lies inside `clB 3R`
  have hrect : closedPatch x₁ x₂ y₁ y₂ ⊆ Metric.closedBall (0 : Plane) (3 * R) := by
    intro z hz
    have hnorm : ‖z - qv‖ ≤ 2 * (4 * w) := by
      refine norm_le_two_mul_of_coord_le ?_
      intro j
      have hc : (z - qv) j = z j - qv j := by simp
      rw [hc]
      exact abs_coord_sub_le_of_mem_closedPatch hz hqvp (by linarith) (by linarith) j
    have hqvn : ‖qv‖ ≤ R + α * R / 16 := by
      obtain ⟨p, hpc, hpb⟩ := hv
      have hbdd : Bornology.IsBounded (F.cell v : Set Plane) :=
        (F.cell v).isCompact.isBounded
      have hdist : dist qv p ≤ Metric.diam (F.cell v : Set Plane) :=
        Metric.dist_le_diam_of_mem hbdd hqv hpc
      have hpn : ‖p‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_zero_right] at hpb
        exact hpb
      have htri : ‖qv‖ ≤ ‖qv - p‖ + ‖p‖ := by
        calc ‖qv‖ = ‖qv - p + p‖ := by rw [sub_add_cancel]
          _ ≤ ‖qv - p‖ + ‖p‖ := norm_add_le _ _
      rw [← dist_eq_norm] at htri
      linarith
    have hzn : ‖z‖ ≤ 3 * R := by
      have htri : ‖z‖ ≤ ‖z - qv‖ + ‖qv‖ := by
        calc ‖z‖ = ‖z - qv + qv‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - qv‖ + ‖qv‖ := norm_add_le _ _
      linarith
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hzn
  have hu3 : Hits F (Metric.closedBall (0 : Plane) (3 * R)) u := ⟨qu, hquc, hrect hqup⟩
  have hdu := hdiam u hu3
  have hcu : |cellCentroid F u i - qu i| ≤ α * R / 16 :=
    le_trans (abs_coord_cellCentroid_sub_le_diam F hF u hquc i) hdu
  have hcv : |qv i - cellCentroid F v i| ≤ α * R / 16 := by
    have h := abs_coord_cellCentroid_sub_le_diam F hF v hqv i
    rw [abs_sub_comm] at h
    exact le_trans h hdv
  have hmid : |qu i - qv i| ≤ 4 * w :=
    abs_coord_sub_le_of_mem_closedPatch hqup hqvp (by linarith) (by linarith) i
  have hsplit : cellCentroid F u i - cellCentroid F v i
      = (cellCentroid F u i - qu i) + (qu i - qv i) + (qv i - cellCentroid F v i) := by ring
  rw [hsplit]
  calc |cellCentroid F u i - qu i + (qu i - qv i) + (qv i - cellCentroid F v i)|
      ≤ |cellCentroid F u i - qu i + (qu i - qv i)| + |qv i - cellCentroid F v i| :=
        abs_add_le _ _
    _ ≤ (|cellCentroid F u i - qu i| + |qu i - qv i|) + |qv i - cellCentroid F v i| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (α * R / 16 + 4 * w) + α * R / 16 := add_le_add (add_le_add hcu hmid) hcv
    _ ≤ 2 * (α * R) := by linarith

/-! ### The estimate at one radius -/

set_option maxHeartbeats 1000000 in
/-- **The manuscript's `|χ(H) − c_R| ≤ 12 α R + o(R)`, assembled at one radius.**

All hypotheses are at the single radius `R`: `f` is within `α R` of the centroids on
`clB 3R` (`s:eq:fixedapprox`), the cells meeting `clB 3R` have diameter at most `α R / 16`
(`s:eq:DR`), and for each coordinate the Cauchy–Schwarz product of the two patch
quantities of `s:eq:lineenergy` is smaller than `t · w` with `t = α R` and `w` the window
length (`s:eq:smallmeanTV`).  Then every cell meeting `clB R` obeys
`‖Φ H − b_H‖ ≤ 24 α R + 2 d_{H₀}`, where `H₀` is the root cell. -/
theorem norm_sub_cellCentroid_le_at_radius [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (hline : AELineConnected F)
    {Φ f : V → Plane} (hmin : FullRectangleMinimizer F Φ)
    {α R : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hR : 0 < R)
    {N : ℕ} (hN2 : 2 ≤ N) (hNw : 4 * R / (N : ℝ) ≤ α * R / 8)
    (hblock : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) (3 * R)) v →
      ‖f v - cellCentroid F v‖ ≤ α * R)
    (hdiam : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) (3 * R)) v →
      Metric.diam (F.cell v : Set Plane) ≤ α * R / 16)
    (hsmall : ∀ i : Fin 2,
      patchDiameterReciprocalConductanceMass F
            (hittingVertices F (Metric.closedBall (0 : Plane) (3 * R))) ^ (2⁻¹ : ℝ) *
          patchEnergyENN F (hittingVertices F (Metric.closedBall (0 : Plane) (3 * R)))
            (fun v => Φ v i - f v i) ^ (2⁻¹ : ℝ)
        < ENNReal.ofReal (α * R) * ENNReal.ofReal (4 * R / (N : ℝ)))
    {vr : V} (hvr : (0 : Plane) ∈ (F.cell vr : Set Plane)) (hΦr : Φ vr = 0) :
    ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      ‖Φ v - cellCentroid F v‖ ≤ 24 * (α * R) + 2 * Metric.diam (F.cell vr : Set Plane) := by
  classical
  -- The exceptional offsets.  The covering clause of `Geometry` only makes the uncovered
  -- set `H¹`-null, so a selected line is covered in its entirety exactly when its offset
  -- avoids the corresponding coordinate projection of the uncovered set, and both of those
  -- projections are Lebesgue-null in `ℝ`.
  have hNe :
      volume ((coordProj 0 '' uncoveredSet F) ∪ (coordProj 1 '' uncoveredSet F)) = 0 :=
    measure_union_null (volume_coordProj_uncoveredSet hF 0)
      (volume_coordProj_uncoveredSet hF 1)
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN2
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hαR : 0 < α * R := mul_pos hα hR
  have hαRle : α * R ≤ R := by nlinarith
  set w : ℝ := 4 * R / (N : ℝ) with hwdef
  have hw : 0 < w := by
    rw [hwdef]
    positivity
  have hNw4 : (N : ℝ) * w = 4 * R := by
    rw [hwdef]
    field_simp
  have hwsmall : w ≤ α * R / 8 := hNw
  have hw1 : w ≤ R / 8 := by linarith
  have harith2 : -(2 * R) + (N : ℝ) * w = 2 * R := by rw [hNw4]; ring
  have harith1 : -(2 * R) + ((N : ℝ) - 1) * w = 2 * R - w := by
    have hh : ((N : ℝ) - 1) * w = (N : ℝ) * w - w := by ring
    rw [hh, hNw4]; ring
  -- the window patch is inside `clB 3R`
  have hQsub : closedPatch (-(2 * R)) (-(2 * R) + (N : ℝ) * w) (-(2 * R))
      (-(2 * R) + (N : ℝ) * w) ⊆ Metric.closedBall (0 : Plane) (3 * R) := by
    rw [harith2]
    intro z hz
    exact squareBox_subset_closedBall hR.le ⟨abs_le.2 ⟨hz.1, hz.2.1⟩, abs_le.2 ⟨hz.2.2.1, hz.2.2.2⟩⟩
  -- the main coordinate estimate, on its own good grid
  have key : ∀ i : Fin 2, ∃ ci : ℝ, ∀ v : V,
      Hits F (Metric.closedBall (0 : Plane) R) v →
      |Φ v i - cellCentroid F v i - ci| ≤ 6 * (α * R) := by
    intro i
    obtain ⟨A, B, C, D, xs, ys, hA₀A, hAw, hBlow, hBhigh, hA₀C, hCw, hDlow, hDhigh,
      hxne, hyne, hxs, hys, hxfwd, hxbwd, hyfwd, hybwd, hhor, hver, hxsNe, hysNe⟩ :=
      exists_goodOffsetGrid_of_patchSmallness F (fun v => Φ v i - f v i) hline
        (Metric.closedBall (0 : Plane) (3 * R)) hNe hw hN0 hQsub (hsmall i)
    have hysgood : ∀ y ∈ ys, y ∉ coordProj 1 '' uncoveredSet F :=
      fun y hy hc => hysNe y hy (Or.inr hc)
    have hxsgood : ∀ x ∈ xs, x ∉ coordProj 0 '' uncoveredSet F :=
      fun x hx hc => hxsNe x hx (Or.inl hc)
    have hAlo : -(2 * R) ≤ A := hA₀A
    have hAhi : A ≤ -(2 * R) + w := hAw
    have hBlo : 2 * R - w ≤ B := by rw [← harith1]; exact hBlow
    have hBhi : B ≤ 2 * R := by rw [← harith2]; exact hBhigh
    have hClo : -(2 * R) ≤ C := hA₀C
    have hChi : C ≤ -(2 * R) + w := hCw
    have hDlo : 2 * R - w ≤ D := by rw [← harith1]; exact hDlow
    have hDhi : D ≤ 2 * R := by rw [← harith2]; exact hDhigh
    have hAB : A ≤ B := by linarith
    have hCD : C ≤ D := by linarith
    have hpatch : closedPatch A B C D ⊆ Metric.closedBall (0 : Plane) (3 * R) := by
      intro z hz
      exact squareBox_subset_closedBall hR.le
        ⟨abs_le.2 ⟨by linarith [hz.1], by linarith [hz.2.1]⟩,
          abs_le.2 ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩⟩
    have hgridhit : ∀ u : V, u ∈ gridCells F A B C D xs ys →
        Hits F (Metric.closedBall (0 : Plane) (3 * R)) u := by
      rintro u (⟨y, hy, p, hpc, hp⟩ | ⟨x, hx, p, hpc, hp⟩)
      · refine ⟨p, hpc, hpatch ⟨hp.1, hp.2.1, ?_, ?_⟩⟩
        · rw [hp.2.2]; exact (hys hy).1
        · rw [hp.2.2]; exact (hys hy).2
      · refine ⟨p, hpc, hpatch ⟨?_, ?_, hp.2.1, hp.2.2⟩⟩
        · rw [hp.1]; exact (hxs hx).1
        · rw [hp.1]; exact (hxs hx).2
    obtain ⟨x₀, hx₀⟩ := id hxne
    obtain ⟨p₀, hp₀⟩ := vertical_nonempty (x := x₀) hCD
    -- the whole selected vertical line `{x₀} × ℝ` is covered, because `x₀` avoids the
    -- projection of the uncovered set to the first coordinate axis
    obtain ⟨u₀, hu₀⟩ : ∃ u : V, p₀ ∈ (F.cell u : Set Plane) :=
      exists_cell_of_coordProj_notMem (i := 0) (by
        rw [coordProj_apply, hp₀.1]
        exact hxsgood x₀ hx₀)
    have hu₀grid : u₀ ∈ gridCells F A B C D xs ys :=
      mem_gridCells_of_hits_vertical F hx₀ ⟨p₀, hu₀, hp₀⟩
    refine ⟨Φ u₀ i - f u₀ i, ?_⟩
    have hskel : ∀ u ∈ gridCells F A B C D xs ys,
        |Φ u i - cellCentroid F u i - (Φ u₀ i - f u₀ i)| ≤ 4 * (α * R) := by
      intro u hu
      have h3 : |(Φ u i - f u i) - (Φ u₀ i - f u₀ i)| ≤ 3 * (α * R) :=
        abs_sub_le_three_mul_of_mem_gridCells F (fun v => Φ v i - f v i) hysgood hαR.le hxs
          hys hxne hyne hhor hver hu₀grid hu
      have hb : |f u i - cellCentroid F u i| ≤ α * R := by
        have hc : (f u - cellCentroid F u) i = f u i - cellCentroid F u i := by simp
        have h := abs_coord_le_norm (f u - cellCentroid F u) i
        rw [hc] at h
        exact le_trans h (hblock u (hgridhit u hu))
      have hsplit : Φ u i - cellCentroid F u i - (Φ u₀ i - f u₀ i)
          = ((Φ u i - f u i) - (Φ u₀ i - f u₀ i)) + (f u i - cellCentroid F u i) := by ring
      rw [hsplit]
      calc |((Φ u i - f u i) - (Φ u₀ i - f u₀ i)) + (f u i - cellCentroid F u i)|
          ≤ |(Φ u i - f u i) - (Φ u₀ i - f u₀ i)| + |f u i - cellCentroid F u i| :=
            abs_add_le _ _
        _ ≤ 3 * (α * R) + α * R := add_le_add h3 hb
        _ = 4 * (α * R) := by ring
    have hinside : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
        (F.cell v : Set Plane) ⊆ closedPatch A B C D := by
      intro v hv z hz
      have hv3 : Hits F (Metric.closedBall (0 : Plane) (3 * R)) v := by
        obtain ⟨p, hpc, hpb⟩ := hv
        exact ⟨p, hpc, Metric.closedBall_subset_closedBall (by linarith) hpb⟩
      have hd := hdiam v hv3
      have h0 := abs_coord_le_of_hits_closedBall F hv hd hz 0
      have h1 := abs_coord_le_of_hits_closedBall F hv hd hz 1
      rw [abs_le] at h0 h1
      exact ⟨by linarith [h0.1], by linarith [h0.2], by linarith [h1.1], by linarith [h1.2]⟩
    intro v hv
    by_cases hvg : v ∈ gridCells F A B C D xs ys
    · exact le_trans (hskel v hvg) (by linarith)
    · have hmaxp := abs_coord_sub_le_of_notMem_gridCells F hF hmin i hxs hys hxfwd hxbwd
        hyfwd hybwd hskel hvg (hinside v hv)
        (abs_coord_cellCentroid_sub_le_of_smallRectangle F hF hα hR hαRle hw hwsmall hdiam
          hv i)
      linarith
  choose c hc using key
  have hvrhit : Hits F (Metric.closedBall (0 : Plane) R) vr := ⟨0, hvr, by simpa using hR.le⟩
  have hcbound : ∀ i : Fin 2, |c i| ≤ 6 * (α * R) + Metric.diam (F.cell vr : Set Plane) := by
    intro i
    have h := hc i vr hvrhit
    have hzero : (0 : Plane) i = 0 := by simp
    rw [hΦr, hzero] at h
    have hdi : |cellCentroid F vr i| ≤ Metric.diam (F.cell vr : Set Plane) := by
      have h2 := abs_coord_cellCentroid_sub_le_diam F hF vr hvr i
      have hz0 : (0 : Plane) i = 0 := by simp
      rwa [hz0, sub_zero] at h2
    rw [abs_le] at h hdi ⊢
    exact ⟨by linarith [h.1, hdi.2], by linarith [h.2, hdi.1]⟩
  intro v hv
  have hall : ∀ j : Fin 2, |(Φ v - cellCentroid F v) j|
      ≤ 12 * (α * R) + Metric.diam (F.cell vr : Set Plane) := by
    intro j
    have hcj : (Φ v - cellCentroid F v) j = Φ v j - cellCentroid F v j := by simp
    rw [hcj]
    have h := hc j v hv
    have hcb := hcbound j
    rw [abs_le] at h hcb ⊢
    exact ⟨by linarith [h.1, hcb.2], by linarith [h.2, hcb.1]⟩
  have hnorm := norm_le_two_mul_of_coord_le hall
  linarith

/-! ### From small residuals to uniform sublinearity -/

/-- **`s:eq:smallresidual`, maximal-function form.**  Arbitrarily good block interpolants
exist for `Φ`: for every `ε > 0` there is a nonzero stage `n`, an actual `n`-block
interpolant `f` (`DyadicApproximation.IsBlockInterpolation`, the specification of the
manuscript's `φ_n`), and a maximal constant `M < ε` dominating every ball average of the
specific energy of the residual `Φ - f`.

This is the manuscript's `s:eq:residualchoice` together with the maximal bound of
`s:prop:maximal` applied to the residual field.  Besides the quadratic geometric-mass
bound `s:eq:Wbound` it is the **only** input of
`uniformlySublinearCorrector_of_smallBlockResidual`. -/
def SmallBlockResidual (F : IndexedCells V) (D : Grid) (Φ : V → Plane) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ n : ℕ, n ≠ 0 ∧ ∃ f : V → Plane,
    IsBlockInterpolation F D n f ∧ ∃ M : ℝ≥0∞, M < ε ∧ ∀ s : ℝ, 0 < s →
      (∫⁻ z in Metric.closedBall (0 : Plane) s,
          rootedSpecificEnergyDensity F (fun v => Φ v - f v) z ∂volume)
        ≤ ENNReal.ofReal (s ^ 2) * M

set_option maxHeartbeats 1000000 in
/-- **`s:eq:sublinear`, centroid half, for the limiting corrector.**  A full-rectangle
energy minimizer normalized to vanish on a cell containing the origin, which is
approximable by block interpolants in the maximal-function sense of `SmallBlockResidual`,
is uniformly sublinear against the cell centroids.

The environmental inputs are the manuscript's own: `s:eq:DR` in the `ε`-form
`SublinearDiameterDecay` and `s:eq:Wbound` in the quadratic form `hW`. -/
theorem uniformlySublinearCorrector_of_smallBlockResidual [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (hline : AELineConnected F) (D : Grid)
    (hdec : SublinearDiameterDecay F)
    {Φ : V → Plane} (hmin : FullRectangleMinimizer F Φ)
    {K : ℝ} (hK : 0 ≤ K)
    (hW : ∀ᶠ R : ℝ in atTop, patchDiameterReciprocalConductanceMass F
        (hittingVertices F (Metric.closedBall (0 : Plane) R)) ≤ ENNReal.ofReal (K * R ^ 2))
    (hres : SmallBlockResidual F D Φ)
    {vr : V} (hvr : (0 : Plane) ∈ (F.cell vr : Set Plane)) (hΦr : Φ vr = 0) :
    UniformlySublinearCorrector F Φ := by
  intro η hη
  have hη'0 : 0 < min η 1 := lt_min hη one_pos
  have hη'1 : min η 1 ≤ 1 := min_le_right _ _
  have hη'η : min η 1 ≤ η := min_le_left _ _
  set η' : ℝ := min η 1 with hη'def
  set α : ℝ := η' / 64 with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith
  have hα1 : α ≤ 1 := by rw [hαdef]; linarith
  set s : ℝ := α / 48 with hsdef
  have hs : 0 < s := by rw [hsdef]; linarith
  have hs1 : s ≤ 1 := by rw [hsdef]; linarith
  have hs48 : 48 * s = α := by rw [hsdef]; ring
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (32 / α)
  have hN2 : 2 ≤ max N₀ 2 := le_max_right _ _
  have hNcast : (32 : ℝ) / α ≤ ((max N₀ 2 : ℕ) : ℝ) :=
    le_trans hN₀ (by exact_mod_cast le_max_left N₀ 2)
  set N : ℕ := max N₀ 2 with hNdef
  have hNnat : 0 < N := lt_of_lt_of_le (by norm_num) hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  have h32 : (32 : ℝ) ≤ α * (N : ℝ) := by
    have h := (div_le_iff₀ hα).mp hNcast
    linarith
  have hαN : 4 / (N : ℝ) ≤ α / 8 := by
    rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 8)]
    linarith
  -- the residual, chosen small enough for the offset selection
  have hc0 : 0 < ENNReal.ofReal (4 * α / (N : ℝ)) := by
    refine ENNReal.ofReal_pos.2 ?_
    positivity
  obtain ⟨ε, hε, hεprop⟩ := exists_pos_forall_lt_of_mul_rpow_half (lineVariationConstant K)
    (ENNReal.ofReal (4 * α / (N : ℝ))) (lineVariationConstant_ne_top K) hc0
    ENNReal.ofReal_ne_top
  obtain ⟨n, hn, f, hf, M, hMε, hMb⟩ := hres ε hε
  have hLM := hεprop M hMε
  obtain ⟨R₁, hR₁pos, hR₁⟩ := maxSelectedSide_le_ofReal F D (n : ℝ) hdec hs
  obtain ⟨R₂, hR₂pos, hR₂⟩ := hdec s hs
  have hdil : Tendsto (fun R : ℝ => 3 * R) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) tendsto_id
  obtain ⟨R₃, hR₃⟩ := eventually_atTop.1 (hdil.eventually hW)
  set d₀ : ℝ := Metric.diam (F.cell vr : Set Plane) with hd₀def
  have hd₀0 : 0 ≤ d₀ := Metric.diam_nonneg
  set R₀ : ℝ := max (max R₁ R₂) (max R₃ (max 1 (4 * d₀ / η' + 1))) with hR₀def
  have e1 : R₁ ≤ R₀ := le_max_of_le_left (le_max_left _ _)
  have e2 : R₂ ≤ R₀ := le_max_of_le_left (le_max_right _ _)
  have e3 : R₃ ≤ R₀ := le_max_of_le_right (le_max_left _ _)
  have e4 : (1 : ℝ) ≤ R₀ := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have e5 : 4 * d₀ / η' + 1 ≤ R₀ := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  refine ⟨R₀, lt_of_lt_of_le one_pos e4, fun R hR v hv => ?_⟩
  have hR1 : (1 : ℝ) ≤ R := le_trans e4 hR
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hRR₁ : R₁ ≤ 3 * R := by linarith [le_trans e1 hR]
  have hRR₂ : R₂ ≤ 3 * R := by linarith [le_trans e2 hR]
  have hRR₃ : R₃ ≤ R := le_trans e3 hR
  have hRd : 4 * d₀ / η' + 1 ≤ R := le_trans e5 hR
  have hd₀R : 2 * d₀ ≤ η' * R / 2 := by
    have hle : 4 * d₀ / η' ≤ R := by linarith
    have h := (div_le_iff₀ hη'0).mp hle
    linarith
  have hαR : 0 < α * R := mul_pos hα hRpos
  have hαRle : α * R ≤ R := by nlinarith [hα1, hRpos]
  have hNwR : 4 * R / (N : ℝ) ≤ α * R / 8 := by
    calc 4 * R / (N : ℝ) = 4 / (N : ℝ) * R := by ring
      _ ≤ α / 8 * R := mul_le_mul_of_nonneg_right hαN hRpos.le
      _ = α * R / 8 := by ring
  -- `s:eq:fixedapprox` at radius `3R`
  have hs3 : (0 : ℝ) ≤ s * (3 * R) := by positivity
  have hℓ : maxSelectedSide F D (n : ℝ) (3 * R) ≤ ENNReal.ofReal (s * (3 * R)) :=
    hR₁ (3 * R) hRR₁
  have hdd0 : (0 : ℝ) ≤ s * (3 * R + 2 * (s * (3 * R))) := by positivity
  have hdd : maxDiamHittingBall F (3 * R + 2 * (s * (3 * R)))
      ≤ ENNReal.ofReal (s * (3 * R + 2 * (s * (3 * R)))) := by
    refine hR₂ _ ?_
    have hnn : (0 : ℝ) ≤ 2 * (s * (3 * R)) := by positivity
    linarith
  have hkey : s * (s * R) ≤ s * R := by nlinarith [hs, hs1, hRpos]
  have hblock : ∀ u : V, Hits F (Metric.closedBall (0 : Plane) (3 * R)) u →
      ‖f u - cellCentroid F u‖ ≤ α * R := by
    intro u hu
    have hb := norm_sub_cellCentroid_le_of_isBlockInterpolation F hF D hdec hn hf hs3 hdd0
      hℓ hdd hu
    have hX0 : (0 : ℝ) ≤ 2 * (s * (3 * R)) + 2 * (s * (3 * R + 2 * (s * (3 * R)))) := by
      positivity
    have h2 := mul_le_mul_of_nonneg_right sqrt_two_le_two hX0
    have hXexp : 2 * (2 * (s * (3 * R)) + 2 * (s * (3 * R + 2 * (s * (3 * R)))))
        = 24 * (s * R) + 24 * (s * (s * R)) := by ring
    have hαRexp : α * R = 48 * (s * R) := by rw [← hs48]; ring
    linarith
  -- `s:eq:DR` at radius `3R`
  have hD3 : maxDiamHittingBall F (3 * R) ≤ ENNReal.ofReal (s * (3 * R)) := hR₂ (3 * R) hRR₂
  have hdiam : ∀ u : V, Hits F (Metric.closedBall (0 : Plane) (3 * R)) u →
      Metric.diam (F.cell u : Set Plane) ≤ α * R / 16 := by
    intro u hu
    have h := diam_le_of_maxDiamHittingBall_le F hs3 hD3 hu
    have harith : s * (3 * R) = α * R / 16 := by rw [← hs48]; ring
    linarith
  -- `s:eq:smallmeanTV`: the Cauchy–Schwarz product is below `t · w`
  have hWR := hR₃ R hRR₃
  have hmass : patchDiameterReciprocalConductanceMass F
      (hittingVertices F (Metric.closedBall (0 : Plane) (3 * R)))
      ≤ ENNReal.ofReal (9 * K) * ENNReal.ofReal (R ^ 2) := by
    refine hWR.trans (le_of_eq ?_)
    have harg : K * (3 * R) ^ 2 = 9 * K * R ^ 2 := by ring
    rw [harg, ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 9 * K)]
  have hD3' : maxDiamHittingBall F (3 * R) ≤ ENNReal.ofReal (3 * R) := by
    refine le_trans hD3 (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [hs1, hRpos]
  have henergy : ∀ i : Fin 2, patchEnergyENN F
      (hittingVertices F (Metric.closedBall (0 : Plane) (3 * R))) (fun u => Φ u i - f u i)
      ≤ ENNReal.ofReal 36 * ENNReal.ofReal (R ^ 2) * M := by
    intro i
    have hfun : (fun u : V => Φ u i - f u i) = fun u : V => (Φ u - f u) i := by
      funext u
      simp
    rw [hfun]
    refine (patchEnergyENN_coord_le_vectorEnergy F _ (fun u => Φ u - f u) i).trans ?_
    have hball : vectorEnergy (restrictGraph F.graph
        (hittingVertices F (Metric.closedBall (0 : Plane) (3 * R))))
        (fun u : hittingVertices F (Metric.closedBall (0 : Plane) (3 * R)) => Φ u.1 - f u.1)
        ≤ ENNReal.ofReal ((3 * R + 3 * R) ^ 2) * M :=
      ballPatchVectorEnergy_le_of_maxDiam F hF (fun u => Φ u - f u) (by linarith)
        (by linarith) hD3' hMb
    have harg : (3 * R + 3 * R) ^ 2 = 36 * R ^ 2 := by ring
    rw [harg, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 36)] at hball
    exact hball
  have hR2ne0 : ENNReal.ofReal (R ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hsmall : ∀ i : Fin 2,
      patchDiameterReciprocalConductanceMass F
            (hittingVertices F (Metric.closedBall (0 : Plane) (3 * R))) ^ (2⁻¹ : ℝ) *
          patchEnergyENN F (hittingVertices F (Metric.closedBall (0 : Plane) (3 * R)))
            (fun u => Φ u i - f u i) ^ (2⁻¹ : ℝ)
        < ENNReal.ofReal (α * R) * ENNReal.ofReal (4 * R / (N : ℝ)) := by
    intro i
    refine lt_of_le_of_lt (sqrt_mass_mul_sqrt_energy_le hmass (henergy i)) ?_
    have hlt := ENNReal.mul_lt_mul_left hR2ne0 ENNReal.ofReal_ne_top hLM
    refine lt_of_lt_of_le hlt (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * α / (N : ℝ)),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α * R)]
    congr 1
    field_simp
  have hfinal := norm_sub_cellCentroid_le_at_radius F hF hline hmin hα hα1 hRpos hN2 hNwR
    hblock hdiam hsmall hvr hΦr v hv
  have h24 : 24 * (α * R) = 3 * (η' * R) / 8 := by rw [hαdef]; ring
  have hη'R : η' * R ≤ η * R := mul_le_mul_of_nonneg_right hη'η hRpos.le
  linarith

end ReflectedGMS.CentroidSublinearityFromResidual
