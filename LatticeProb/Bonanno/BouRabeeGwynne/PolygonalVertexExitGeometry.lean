/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.PolygonalVertexExitGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveProperties
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Floor.Semiring

/-! The first vertex exit on a fixed continuous representative of a finite walk.
The reparametrizing clock may have constant intervals, including at the exit. -/

open Set
open scoped unitInterval

namespace BouRabeeGwynne

lemma polygonalCurve_at_scaled_vertex {d : ℕ} {V : Type*}
    (pos : V → Euc d) (ω : ℕ → V) {M m : ℕ} (hmM : m ≤ M)
    (t : unitInterval) (ht : (M : ℝ) * (t : ℝ) = m) :
    polygonalCurve pos ω M t = pos (ω m) := by
  by_cases hM : M = 0
  · have hm : m = 0 := Nat.eq_zero_of_le_zero (hM ▸ hmM)
    subst M
    subst m
    simp only [polygonalCurve_zero, ContinuousMap.const_apply]
  by_cases hm : m = 0
  · subst m
    have htzero : t = 0 := by
      apply Subtype.ext
      change (t : ℝ) = 0
      exact (mul_eq_zero.mp (by simpa only [Nat.cast_zero] using ht)).resolve_left
        (Nat.cast_ne_zero.mpr hM)
    rw [htzero, polygonalCurve_start]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hj : j < M := lt_of_lt_of_le (Nat.lt_succ_self j) hmM
  have ht' : (M : ℝ) * (t : ℝ) = (j : ℝ) + 1 := by
    simpa only [Nat.cast_succ] using ht
  rw [polygonalCurve_on_segment_scaled pos ω hj t (by linarith) ht'.le]
  rw [ht', add_sub_cancel_left, one_smul, add_sub_cancel]

/-- Before the first outside vertex, including that vertex, interpolation is
within one pre-exit edge length of an interior vertex. -/
lemma polygonalCurve_mem_cthickening_before_vertex {d : ℕ} {V : Type*}
    (pos : V → Euc d) (ω : ℕ → V) {U : Set (Euc d)} {M m : ℕ}
    (hm : 0 < m) (hmM : m ≤ M) {ε : ℝ}
    (hinside : ∀ k < m, pos (ω k) ∈ U)
    (hedge : ∀ k < m, dist (pos (ω (k + 1))) (pos (ω k)) ≤ ε)
    (t : unitInterval) (ht : (M : ℝ) * (t : ℝ) ≤ m) :
    polygonalCurve pos ω M t ∈ Metric.cthickening ε U := by
  by_cases heq : (M : ℝ) * (t : ℝ) = m
  · rw [polygonalCurve_at_scaled_vertex pos ω hmM t heq]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    exact Metric.mem_cthickening_of_dist_le _ _ ε U
      (hinside j (Nat.lt_succ_self j)) (hedge j (Nat.lt_succ_self j))
  have hnonneg : 0 ≤ (M : ℝ) * (t : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) t.property.1
  let j : ℕ := ⌊(M : ℝ) * (t : ℝ)⌋₊
  have hjm : j < m := (Nat.floor_lt hnonneg).mpr (lt_of_le_of_ne ht heq)
  have hlo : (j : ℝ) ≤ (M : ℝ) * (t : ℝ) := Nat.floor_le hnonneg
  have hhi : (M : ℝ) * (t : ℝ) ≤ (j : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  apply Metric.mem_cthickening_of_dist_le _ (pos (ω j)) ε U (hinside j hjm)
  rw [polygonalCurve_on_segment_scaled pos ω (hjm.trans_le hmM) t hlo hhi,
    dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hlo)]
  calc
    ((M : ℝ) * (t : ℝ) - j) * ‖pos (ω (j + 1)) - pos (ω j)‖ ≤
        ‖pos (ω (j + 1)) - pos (ω j)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    _ ≤ ε := by simpa only [dist_eq_norm] using hedge j hjm

/-- Realize the first outside vertex on the same fixed pasted curve, without
inverting its weak clock. Both zero exit and a zero-length walk are included. -/
theorem exists_vertexExit_parameter_comp_monotone {d : ℕ} {V : Type*}
    (pos : V → Euc d) (ω : ℕ → V) {U : Set (Euc d)} {M m : ℕ}
    (hmM : m ≤ M) {ε : ℝ}
    (hinside : ∀ k < m, pos (ω k) ∈ U) (hout : pos (ω m) ∉ U)
    (hedge : ∀ k < m, dist (pos (ω (k + 1))) (pos (ω k)) ≤ ε)
    (f : C(unitInterval, Euc d)) (φ : C(unitInterval, unitInterval))
    (hmono : Monotone φ) (hzero : φ 0 = 0) (hone : φ 1 = 1)
    (hf : f = (polygonalCurve pos ω M).comp φ) :
    ∃ a b : unitInterval, (b : ℝ) = (m : ℝ) / M ∧ φ a = b ∧
      f a = pos (ω m) ∧ f a ∉ U ∧
      ∀ t < a, f t ∈ Metric.cthickening ε U := by
  by_cases hm : m = 0
  · subst m
    have hfzero : f 0 = pos (ω 0) := by
      rw [hf, ContinuousMap.comp_apply, hzero, polygonalCurve_start]
    refine ⟨0, 0, by simp, hzero, hfzero, hfzero ▸ hout, ?_⟩
    intro t ht
    exact False.elim ((not_lt_of_ge t.property.1) ht)
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hmpos.trans_le hmM
  let b : unitInterval := ⟨(m : ℝ) / M,
    ⟨div_nonneg (Nat.cast_nonneg _) hMpos.le,
      (div_le_one hMpos).mpr (by exact_mod_cast hmM)⟩⟩
  have hb : b ∈ Icc (φ 0) (φ 1) := by
    rw [hzero, hone]
    exact b.property
  obtain ⟨a, _, hab⟩ :=
    intermediate_value_Icc (show (0 : unitInterval) ≤ 1 by exact zero_le_one)
      φ.continuous.continuousOn hb
  have hbscale : (M : ℝ) * (b : ℝ) = m := by
    change (M : ℝ) * ((m : ℝ) / M) = m
    field_simp
  have hfa : f a = pos (ω m) := by
    rw [hf, ContinuousMap.comp_apply, hab]
    exact polygonalCurve_at_scaled_vertex pos ω hmM b hbscale
  refine ⟨a, b, rfl, hab, hfa, hfa ▸ hout, ?_⟩
  intro t ht
  rw [hf, ContinuousMap.comp_apply]
  apply polygonalCurve_mem_cthickening_before_vertex pos ω hmpos hmM hinside hedge
  calc
    (M : ℝ) * (φ t : ℝ) ≤ (M : ℝ) * (φ a : ℝ) :=
      mul_le_mul_of_nonneg_left (hmono ht.le) hMpos.le
    _ = m := by rw [hab]; exact hbscale

/-- The same conclusion with the exit index supplied by the genuine discrete
first-exit definition. -/
theorem exists_vertexExit_parameter_of_exitTime {d : ℕ} {V : Type*}
    (pos : V → Euc d) (ω : ℕ → V) {U : Set (Euc d)} {M m : ℕ}
    (hmM : m ≤ M)
    (hτ : FiniteConductanceNetwork.exitTime (pos ⁻¹' U) ω = (m : WithTop ℕ))
    {ε : ℝ}
    (hedge : ∀ k < m, dist (pos (ω (k + 1))) (pos (ω k)) ≤ ε)
    (f : C(unitInterval, Euc d)) (φ : C(unitInterval, unitInterval))
    (hmono : Monotone φ) (hzero : φ 0 = 0) (hone : φ 1 = 1)
    (hf : f = (polygonalCurve pos ω M).comp φ) :
    ∃ a b : unitInterval, (b : ℝ) = (m : ℝ) / M ∧ φ a = b ∧
      f a = pos (ω m) ∧ f a ∉ U ∧
      ∀ t < a, f t ∈ Metric.cthickening ε U := by
  apply exists_vertexExit_parameter_comp_monotone pos ω hmM ?_ ?_ hedge
    f φ hmono hzero hone hf
  · intro k hk
    change ω k ∈ pos ⁻¹' U
    apply FiniteConductanceNetwork.mem_of_lt_exitTime
    rw [hτ]
    exact WithTop.coe_lt_coe.mpr hk
  · have hfin : FiniteConductanceNetwork.exitTime (pos ⁻¹' U) ω ≠ ⊤ := by
      rw [hτ]
      exact WithTop.coe_ne_top
    have hmem := FiniteConductanceNetwork.exitTime_mem_compl_of_ne_top hfin
    rw [hτ] at hmem
    exact hmem

end BouRabeeGwynne
