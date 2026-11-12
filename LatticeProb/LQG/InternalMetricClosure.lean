import LatticeProb.LQG.LengthMetricDerived
import LatticeProb.LQG.LQGMetricMeasurable
import LatticeProb.Topology.RectangleSquareCover

/-! # Internal metric of a closed set from the internal metric of a dense subset

Let `D` be a Euclidean length metric on `ℂ` (`IsEuclideanLengthMetric`), `C` a closed bounded set and `U ⊆ C` a set
whose closure contains `C`. Then the internal diameter of `C` is at most the internal diameter of `U`:
  `sup_{u, v ∈ C} D(u, v; C) ≤ sup_{x, y ∈ U} D(x, y; U)`.

The proof is deterministic. For a closed bounded set, `D(u, v; C)` is the limit of the internal metrics
`D(u, v; B_δ(C))` of the open `δ`-neighbourhoods (`internalMetricClosedEqIInfThickening_derived`, an Arzelà-Ascoli
argument for paths of bounded length). In the open set `B_δ(C)` the internal metric `D(u, ·; B_δ(C))` is continuous at
`u` and vanishes there, so `u` and `v` can be replaced by points `x, y ∈ U` at an arbitrarily small internal distance,
and `D(x, y; B_δ(C)) ≤ D(x, y; U)`.

For a closed square `Q` this bounds the internal diameter of `Q` in its own internal metric (paths may run along the
boundary, and the endpoints may lie on the boundary) by the internal diameter of the open square `int Q` in the internal
metric of `int Q`, the quantity bounded in the multiscale estimates for the LQG metric of Ding, Dubédat, Falconet,
Gwynne and Pfeffer (arXiv:1905.00380, Proposition 3.10).

Main results:
* `IsEuclideanLengthMetric.internalMetric_le_of_subset_closure`: `D(u, v; C) ≤ M` for `u, v ∈ C` when
  `D(x, y; U) ≤ M` for all `x, y ∈ U`.
* `IsEuclideanLengthMetric.internalMetric_closedSquare_le`: the same for a closed square `Q` and `U = int Q`.
* `IsEuclideanLengthMetric.exists_internalMetric_closedSquare_le_ofReal`: a real bound for the internal diameter of the
  open square `int Q` gives a real bound for the internal diameter of `Q`.
-/

namespace LatticeProb.LQG

open Set Filter
open scoped ENNReal _root_.Topology

/-- Points of the closure of `U` inside an open set `W` are at arbitrarily small `W`-internal distance from `U`: for a
Euclidean length metric `D`, an open set `W`, `w ∈ W ∩ closure U` and `ε > 0` there is `x ∈ U` with
`D(w, x; W) < ε`. -/
theorem IsEuclideanLengthMetric.exists_mem_internalMetric_lt_of_mem_closure {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {U W : Set ℂ} (hW : IsOpen W) {w : ℂ} (hwW : w ∈ W)
    (hwU : w ∈ closure U) {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ x ∈ U, internalMetric D W w x < ε := by
  have hnn : ∀ x y, 0 ≤ D x y := fun x y => by
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  have hc := hD.continuousAt_internalMetric_self hnn hW hwW
  have h0 : internalMetric D W w w = 0 := hD.internalMetric_self_of_mem_open hnn hW hwW
  have hev : ∀ᶠ x in 𝓝 w, internalMetric D W w x < ε :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by rw [h0]; exact hε))
  obtain ⟨x, hx, hxU⟩ := (hev.and_frequently (mem_closure_iff_frequently.mp hwU)).exists
  exact ⟨x, hxU, hx⟩

/-- **Internal metric of a closed set from a dense subset.** For a Euclidean length metric `D`, a closed bounded set `C`
and a set `U ⊆ C` with `C ⊆ closure U`: if `D(x, y; U) ≤ M` for all `x, y ∈ U`, then `D(u, v; C) ≤ M` for all
`u, v ∈ C`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_subset_closure {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {C U : Set ℂ} (hC : IsClosed C) (hCb : Bornology.IsBounded C)
    (hUC : U ⊆ C) (hCU : C ⊆ closure U) {M : ℝ≥0∞}
    (hM : ∀ x ∈ U, ∀ y ∈ U, internalMetric D U x y ≤ M) {u v : ℂ} (hu : u ∈ C) (hv : v ∈ C) :
    internalMetric D C u v ≤ M := by
  obtain ⟨r, hr⟩ := hCb.subset_closedBall 0
  obtain ⟨n, hn⟩ := exists_nat_ge r
  rw [internalMetricClosedEqIInfThickening_derived D C hC hD hu hv]
  refine iInf_le_of_le n (iSup_le fun k => ?_)
  have hsub : C ⊆ Metric.closedBall 0 ((n : ℝ) + 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (by linarith))
  rw [inter_eq_left.mpr hsub]
  have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
  set W := Metric.thickening (((k : ℝ) + 1)⁻¹) C with hWdef
  have hWo : IsOpen W := Metric.isOpen_thickening
  have hCW : C ⊆ W := Metric.self_subset_thickening hδ C
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 :=
    ENNReal.half_pos (by exact_mod_cast hε.ne')
  obtain ⟨x, hxU, hx⟩ := hD.exists_mem_internalMetric_lt_of_mem_closure hWo (hCW hu) (hCU hu) hε2
  obtain ⟨y, hyU, hy⟩ := hD.exists_mem_internalMetric_lt_of_mem_closure hWo (hCW hv) (hCU hv) hε2
  calc internalMetric D W u v
      ≤ internalMetric D W u x + internalMetric D W x v := hD.internalMetric_triangle W u x v
    _ ≤ internalMetric D W u x + (internalMetric D W x y + internalMetric D W y v) := by
        gcongr
        exact hD.internalMetric_triangle W x y v
    _ ≤ (ε : ℝ≥0∞) / 2 + (M + (ε : ℝ≥0∞) / 2) :=
        add_le_add hx.le (add_le_add ((internalMetric_anti D (hUC.trans hCW) x y).trans (hM x hxU y hyU))
          ((hD.internalMetric_symm W y v).le.trans hy.le))
    _ = M + ε := by rw [add_left_comm, ENNReal.add_halves]

/-- **Internal diameter of a closed square.** For a Euclidean length metric `D` and a closed square `Q`: if
`D(x, y; int Q) ≤ M` for all `x, y` in the open square `int Q`, then `D(u, v; Q) ≤ M` for all `u, v ∈ Q`. -/
theorem IsEuclideanLengthMetric.internalMetric_closedSquare_le {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {Q : Set ℂ} (hQ : LatticeProb.Topology.IsClosedSquare Q) {M : ℝ≥0∞}
    (hM : ∀ x ∈ interior Q, ∀ y ∈ interior Q, internalMetric D (interior Q) x y ≤ M) {u v : ℂ}
    (hu : u ∈ Q) (hv : v ∈ Q) : internalMetric D Q u v ≤ M := by
  obtain ⟨a, b, s, hs, rfl⟩ := hQ
  refine hD.internalMetric_le_of_subset_closure (isClosed_Icc.reProdIm isClosed_Icc)
    ((isCompact_Icc.reProdIm isCompact_Icc).isBounded) interior_subset ?_ hM hu hv
  have ha : a ≠ a + s := by intro h; linarith
  have hb : b ≠ b + s := by intro h; linarith
  rw [Complex.interior_reProdIm, interior_Icc, interior_Icc, Complex.closure_reProdIm, closure_Ioo ha, closure_Ioo hb]

/-- A real bound for the internal diameter of the open square `int Q` in its own internal metric gives a real bound
for the internal diameter of the closed square `Q` in its own internal metric. -/
theorem IsEuclideanLengthMetric.exists_internalMetric_closedSquare_le_ofReal {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {Q : Set ℂ} (hQ : LatticeProb.Topology.IsClosedSquare Q)
    (h : ∃ a : ℝ, ∀ x ∈ interior Q, ∀ y ∈ interior Q, internalMetric D (interior Q) x y ≤ ENNReal.ofReal a) :
    ∃ a : ℝ, ∀ u ∈ Q, ∀ v ∈ Q, internalMetric D Q u v ≤ ENNReal.ofReal a := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun u hu v hv => hD.internalMetric_closedSquare_le hQ ha hu hv⟩

end LatticeProb.LQG
