/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCChordApprox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.LQGMetric.LFPP.Length
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PolygonCofinality

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP

open SupercriticalLQGUniqueness.Exponent.PolygonCofinality

theorem laneC_chord_cost_le_mul_distance
    {ξ : ℝ} {φ : ℂ → ℝ} {z w : ℂ} {r m B δ : ℝ}
    (hr : 0 < r) (hm : 0 < m) (hδ : 0 ≤ δ)
    (hzw : ‖w - z‖ ≤ r)
    (hlo : ∀ x ∈ closedBall z r, m ≤ Real.exp (ξ * φ x))
    (hhi : ∀ x ∈ closedBall z ‖w - z‖, Real.exp (ξ * φ x) ≤ B)
    (hBm : B ≤ (1 + δ) * m) :
    lfppLen ξ φ (segPath z w) ≤
      ENNReal.ofReal (1 + δ) * lfppD ξ φ z w := by
  have hmzw : 0 ≤ m * ‖w - z‖ := mul_nonneg hm.le (norm_nonneg _)
  have hδ0 : 0 ≤ 1 + δ := by linarith
  have hbound : lfppLen ξ φ (segPath z w) ≤
      ENNReal.ofReal ((1 + δ) * (m * ‖w - z‖)) := by
    calc
      lfppLen ξ φ (segPath z w)
          ≤ ENNReal.ofReal (B * ‖w - z‖) := lfppLen_segPath_le z w hhi
      _ ≤ ENNReal.ofReal ((1 + δ) * (m * ‖w - z‖)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_right hBm (norm_nonneg (w - z))]
  have hlow : ENNReal.ofReal (m * ‖w - z‖) ≤ lfppD ξ φ z w := by
    simpa [min_eq_right hzw] using
      le_lfppD (ξ := ξ) (φ := φ) (z := z) (w := w) hr hm.le hlo
  calc
    lfppLen ξ φ (segPath z w)
        ≤ ENNReal.ofReal ((1 + δ) * (m * ‖w - z‖)) := hbound
    _ = ENNReal.ofReal (1 + δ) * ENNReal.ofReal (m * ‖w - z‖) := by
      rw [ENNReal.ofReal_mul hδ0]
    _ ≤ ENNReal.ofReal (1 + δ) * lfppD ξ φ z w := by
      simpa only [mul_comm] using mul_le_mul_left hlow (ENNReal.ofReal (1 + δ))

 


theorem laneC_sampled_polygon_cost_le
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {P : ℝ → ℂ} {a b : ℝ} (t : ℕ → ℝ) (N : ℕ)
    (ht : Monotone t)
    (htmem : ∀ i ≤ N, t i ∈ Set.Icc a b)
    {δ : ℝ}
    (hchord : ∀ i < N,
      lfppLen ξ φ (segPath (P (t i)) (P (t (i + 1)))) ≤
        ENNReal.ofReal (1 + δ) * lfppD ξ φ (P (t i)) (P (t (i + 1)))) :
    IsPiecewiseC1Path
      (polygonPath (fun i => P (t i)) N) (P (t 0)) (P (t N)) ∧
    lfppLen ξ φ (polygonPath (fun i => P (t i)) N) ≤
      ENNReal.ofReal (1 + δ) * (lfppContMetric ξ φ hφ).len P a b := by
  obtain ⟨hpath, -, hlen⟩ :=
    polygonPath_data (ξ := ξ) (f := φ) (S := Set.univ)
      (convex_univ : Convex ℝ (Set.univ : Set ℂ))
      (fun i => P (t i)) N (fun _ _ => Set.mem_univ _)
  refine ⟨hpath, ?_⟩
  rw [hlen]
  calc
    (∑ i ∈ Finset.range N,
      segCost ξ φ (P (t i)) (P (t (i + 1))))
        ≤ ∑ i ∈ Finset.range N,
            ENNReal.ofReal (1 + δ) *
              lfppD ξ φ (P (t i)) (P (t (i + 1))) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hchord i (Finset.mem_range.mp hi)
    _ = ENNReal.ofReal (1 + δ) *
          ∑ i ∈ Finset.range N,
            lfppD ξ φ (P (t i)) (P (t (i + 1))) := by
          rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (1 + δ) * (lfppContMetric ξ φ hφ).len P a b := by
      have hsum : (∑ i ∈ Finset.range N,
          lfppD ξ φ (P (t i)) (P (t (i + 1)))) ≤
          (lfppContMetric ξ φ hφ).len P a b := by
        calc
          (∑ i ∈ Finset.range N,
              lfppD ξ φ (P (t i)) (P (t (i + 1))))
              = ∑ i ∈ Finset.range N,
                  edist ((lfppContMetric ξ φ hφ).pt (P (t i)))
                    ((lfppContMetric ξ φ hφ).pt (P (t (i + 1)))) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact (edist_lfppContMetric hφ _ _).symm
          _ ≤ (lfppContMetric ξ φ hφ).len P a b := by
                let u : ℕ → ℝ := fun i => t (min i N)
                have hu : Monotone u := fun i j hij =>
                  ht (min_le_min_right N hij)
                have humem : ∀ i, u i ∈ Set.Icc a b := fun i =>
                  htmem (min i N) (min_le_right i N)
                have hvar := eVariationOn.sum_le
                  (f := (lfppContMetric ξ φ hφ).pt ∘ P) (n := N) hu humem
                have heq : (∑ i ∈ Finset.range N,
                    edist ((lfppContMetric ξ φ hφ).pt (P (t i)))
                      ((lfppContMetric ξ φ hφ).pt (P (t (i + 1))))) =
                    ∑ i ∈ Finset.range N,
                      edist ((lfppContMetric ξ φ hφ).pt (P (u i)))
                        ((lfppContMetric ξ φ hφ).pt (P (u (i + 1)))) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  have hiN : i < N := Finset.mem_range.mp hi
                  simp only [u, min_eq_left hiN.le, min_eq_left (by omega : i + 1 ≤ N)]
                rw [heq]
                simpa only [Function.comp_apply, edist_comm,
                  ContMetric.len, LQGMetric.MetricGeometry.curveLength] using hvar
      simpa only [mul_comm] using mul_le_mul_left hsum (ENNReal.ofReal (1 + δ))

end SupercriticalLQGUniqueness.B2.DG20Conc
