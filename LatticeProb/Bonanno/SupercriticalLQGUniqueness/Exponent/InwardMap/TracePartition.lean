/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.TracePartition at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.SegmentImageCost




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped Convex

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

private theorem interval_partition (v : ℕ → ℝ)
    (hv : ∀ i, v i ≤ v (i+1)) (n : ℕ) :
    Icc (v 0) (v n) = {v 0} ∪ ⋃ j ∈ Finset.range n, Icc (v j) (v (j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0n : v 0 ≤ v n := (monotone_nat_of_le_succ hv) (Nat.zero_le n)
    calc
      Icc (v 0) (v (n+1)) = Icc (v 0) (v n) ∪ Icc (v n) (v (n+1)) :=
        (Icc_union_Icc_eq_Icc h0n (hv n)).symm
      _ = {v 0} ∪ ⋃ j ∈ Finset.range (n+1), Icc (v j) (v (j+1)) := by
        rw [ih, Finset.range_add_one]
        simp only [Finset.set_biUnion_insert]
        ac_rfl

theorem segment_trace_map (F : ℂ → ℂ) (z w : ℂ)
    (hF : ∀ u ∈ Icc (0:ℝ) 1,
      F (LQGMetric.LFPP.segPath z w u) =
        LQGMetric.LFPP.segPath (F z) (F w) u) :
    F '' [z -[ℝ] w] = [F z -[ℝ] F w] := by
  rw [← Exponent.PaidDuality.segPath_trace, ← Exponent.PaidDuality.segPath_trace]
  ext x
  constructor
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, (hF u hu).symm⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨LQGMetric.LFPP.segPath z w u, ⟨u, hu, rfl⟩, hF u hu⟩

theorem polygon_trace_map (F : ℂ → ℂ) (v : ℕ → ℂ) (n : ℕ)
    (hF : ∀ j < n, ∀ u ∈ Icc (0:ℝ) 1,
      F (LQGMetric.LFPP.segPath (v j) (v (j+1)) u) =
        LQGMetric.LFPP.segPath (F (v j)) (F (v (j+1))) u) :
    Exponent.PolygonCofinality.polygonPath (fun j => F (v j)) n '' Icc (0:ℝ) 1 =
      F '' (Exponent.PolygonCofinality.polygonPath v n '' Icc (0:ℝ) 1) := by
  rw [Exponent.PaidDuality.polygonPath_trace, Exponent.PaidDuality.polygonPath_trace, image_union]
  congr 1
  · simp
  · simp only [image_iUnion]
    apply iUnion_congr
    intro j
    apply iUnion_congr
    intro hj
    exact (segment_trace_map F (v j) (v (j+1)) (hF j (Finset.mem_range.mp hj))).symm

private theorem interval_affine_range (s t : ℝ) (hst : s ≤ t) :
    (fun u : ℝ => (t-s)*u+s) '' Icc (0:ℝ) 1 = Icc s t := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hst) hu.1,
      mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr hu.2)]
  · intro hx
    by_cases heq : s = t
    · subst t
      refine ⟨0, by norm_num, ?_⟩
      simp only [sub_self, zero_mul, zero_add]
      exact hx.1.antisymm hx.2
    have hpos : 0 < t-s := sub_pos.mpr (lt_of_le_of_ne hst heq)
    refine ⟨(x-s)/(t-s), ⟨div_nonneg (sub_nonneg.mpr hx.1) hpos.le, ?_⟩, ?_⟩
    · exact (div_le_iff₀ hpos).mpr (by linarith [hx.2])
    · dsimp
      field_simp
      ring

theorem segment_trace_interval (z w : ℂ) (s t : ℝ) (hst : s ≤ t) :
    LQGMetric.LFPP.segPath z w '' Icc s t =
      [LQGMetric.LFPP.segPath z w s -[ℝ] LQGMetric.LFPP.segPath z w t] := by
  rw [← Exponent.PaidDuality.segPath_trace]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨v, hv, heq⟩ := (Set.ext_iff.mp (interval_affine_range s t hst) u).2 hu
    refine ⟨v, hv, ?_⟩
    rw [← Exponent.LatticePath.segPath_subPath_eq]
    simp [LQGMetric.LFPP.subPath, ← heq]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(t-s)*u+s, ?_, ?_⟩
    · exact (Set.ext_iff.mp (interval_affine_range s t hst) _).1 ⟨u, hu, rfl⟩
    · rw [← Exponent.LatticePath.segPath_subPath_eq]
      rfl

theorem polygon_trace_of_segment_partition (z w : ℂ) (v : ℕ → ℝ)
    (hv : ∀ i, v i ≤ v (i+1)) (n : ℕ) :
    Exponent.PolygonCofinality.polygonPath (fun j => LQGMetric.LFPP.segPath z w (v j)) n '' Icc (0:ℝ) 1 =
      LQGMetric.LFPP.segPath z w '' Icc (v 0) (v n) := by
  rw [Exponent.PaidDuality.polygonPath_trace, interval_partition v hv n, image_union]
  congr 1
  · simp
  · simp only [image_iUnion]
    apply iUnion_congr
    intro j
    apply iUnion_congr
    intro hj
    exact (segment_trace_interval z w (v j) (v (j+1)) (hv j)).symm


end SupercriticalLQGUniqueness.Exponent.InwardMap
