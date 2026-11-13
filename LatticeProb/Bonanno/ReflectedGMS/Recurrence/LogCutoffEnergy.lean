/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.LogCutoffEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpatialRadiusEnergy
import LatticeProb.Bonanno.ReflectedGMS.Analysis.ExtendedEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Annular logarithmic cutoff estimates

The cutoff and edge estimates use actual cell representatives and adjacent-cell
intersection. No spatial local finiteness is used.
-/

set_option autoImplicit false
open Set Classical
open scoped ENNReal

namespace ReflectedGMS.LogCutoff

variable {V : Type*}

noncomputable def radius (r₀ : ℝ) (z : V → Plane) (v : V) : ℝ := max r₀ ‖z v‖

noncomputable def clippedLog (r₀ : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  min 1 (Real.log (r / r₀) / ((n : ℝ) * Real.log 2))

noncomputable def cutoff (r₀ : ℝ) (n : ℕ) (z : V → Plane) (v : V) : ℝ :=
  clippedLog r₀ n (radius r₀ z v)

theorem logDenom_pos {n : ℕ} (hn : 1 ≤ n) : 0 < (n : ℝ) * Real.log 2 :=
  mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) (Real.log_pos (by norm_num))

theorem cutoff_eq_zero {r₀ : ℝ} (hr₀ : 0 < r₀) (n : ℕ) (z : V → Plane)
    {v : V} (hv : ‖z v‖ ≤ r₀) : cutoff r₀ n z v = 0 := by
  simp [cutoff, radius, clippedLog, max_eq_left hv, div_self hr₀.ne']

theorem clippedLog_eq_one {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ} (hn : 1 ≤ n)
    {r : ℝ} (hr : (2 : ℝ) ^ n * r₀ ≤ r) : clippedLog r₀ n r = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ (logDenom_pos hn)).2
  have hrat : (2 : ℝ) ^ n ≤ r / r₀ := (le_div_iff₀ hr₀).2 hr
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) n) hrat
  simpa only [Real.log_pow, one_mul] using hlog

theorem cutoff_eq_one {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ} (hn : 1 ≤ n)
    (z : V → Plane) {v : V} (hv : (2 : ℝ) ^ n * r₀ ≤ ‖z v‖) :
    cutoff r₀ n z v = 1 :=
  clippedLog_eq_one hr₀ hn (hv.trans (le_max_right _ _))

theorem abs_log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |Real.log a - Real.log b| ≤ |a - b| / min a b := by
  wlog hab : b ≤ a generalizing a b
  · simpa only [abs_sub_comm, min_comm] using this hb ha (le_of_not_ge hab)
  rw [min_eq_right hab, abs_of_nonneg (sub_nonneg.mpr hab),
    abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hab))]
  calc
    Real.log a - Real.log b = Real.log (a / b) := (Real.log_div ha.ne' hb.ne').symm
    _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
    _ = (a - b) / b := by field_simp

/-- The clipped logarithm estimate, valid across both cutoff interfaces. -/
theorem abs_clippedLog_sub_le {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ} (hn : 1 ≤ n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |clippedLog r₀ n a - clippedLog r₀ n b| ≤
      |a - b| / (((n : ℝ) * Real.log 2) * min a b) := by
  have hmin := abs_min_sub_min_le_max (1 : ℝ)
    (Real.log (a / r₀) / ((n : ℝ) * Real.log 2)) 1
    (Real.log (b / r₀) / ((n : ℝ) * Real.log 2))
  simp only [sub_self, abs_zero] at hmin
  calc
    |clippedLog r₀ n a - clippedLog r₀ n b| ≤
        |Real.log (a / r₀) / ((n : ℝ) * Real.log 2) -
          Real.log (b / r₀) / ((n : ℝ) * Real.log 2)| :=
      hmin.trans (max_le (abs_nonneg _) le_rfl)
    _ = |Real.log a - Real.log b| / ((n : ℝ) * Real.log 2) := by
      rw [Real.log_div ha.ne' hr₀.ne', Real.log_div hb.ne' hr₀.ne', ← sub_div,
        abs_div, abs_of_pos (logDenom_pos hn)]
      congr 2
      ring
    _ ≤ (|a - b| / min a b) / ((n : ℝ) * Real.log 2) :=
      div_le_div_of_nonneg_right (abs_log_sub_log_le ha hb) (logDenom_pos hn).le
    _ = _ := by ring

/-- Inner clipping does not increase radial increments. -/
theorem abs_radius_sub_le [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (z : V → Plane) (hz : StatementIngredients.CellRepresentatives F z) (r₀ : ℝ)
    {v w : V} (hvw : F.graph.toSimpleGraph.Adj v w) :
    |radius r₀ z w - radius r₀ z v| ≤
      Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane) := by
  have h := abs_max_sub_max_le_max r₀ ‖z w‖ r₀ ‖z v‖
  simp only [sub_self, abs_zero] at h
  exact h.trans (max_le (by positivity)
    (abs_norm_sub_norm_le_cellDiameters F hF z hz hvw))

/-- The deterministic diameter hypothesis is only imposed on cells hitting a ball. -/
theorem point_diameter_le [Countable V] (F : IndexedCells V)
    (z : V → Plane) (hz : StatementIngredients.CellRepresentatives F z) (r₀ : ℝ)
    (hD : ∀ R, r₀ ≤ R → ∀ v, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100) (v : V) :
    Metric.diam (F.cell v : Set Plane) ≤ radius r₀ z v / 100 := by
  apply hD _ (le_max_left _ _)
  exact ⟨z v, hz v, by simpa only [Metric.mem_closedBall, dist_zero_right] using
    (le_max_right r₀ ‖z v‖)⟩

/-- The paper's edge difference bound at an arbitrary positive shell radius. -/
theorem edge_difference_le [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (z : V → Plane) (hz : StatementIngredients.CellRepresentatives F z)
    {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ} (hn : 1 ≤ n)
    {v w : V} (hvw : F.graph.toSimpleGraph.Adj v w)
    {L : ℝ} (hL : 0 < L) (hLv : L ≤ radius r₀ z v) (hLw : L ≤ radius r₀ z w) :
    |cutoff r₀ n z w - cutoff r₀ n z v| ≤
      (Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane)) /
        (((n : ℝ) * Real.log 2) * L) := by
  have hv := hr₀.trans_le (le_max_left r₀ ‖z v‖)
  have hw := hr₀.trans_le (le_max_left r₀ ‖z w‖)
  calc
    |cutoff r₀ n z w - cutoff r₀ n z v| ≤
        |radius r₀ z w - radius r₀ z v| /
          (((n : ℝ) * Real.log 2) * min (radius r₀ z w) (radius r₀ z v)) :=
      abs_clippedLog_sub_le hr₀ hn hw hv
    _ ≤ (Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane)) /
          (((n : ℝ) * Real.log 2) * L) :=
      div_le_div₀ (by positivity) (abs_radius_sub_le F hF z hz r₀ hvw)
        (mul_pos (logDenom_pos hn) hL)
        (mul_le_mul_of_nonneg_left (le_min hLw hLv) (logDenom_pos hn).le)

/-- Adjacent radii have ratio below two; hence a shell edge's two representatives
lie in the ball four times the shell's lower radius. -/
theorem shell_endpoints_lt [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (z : V → Plane) (hz : StatementIngredients.CellRepresentatives F z)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hD : ∀ R, r₀ ≤ R → ∀ v, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    {v w : V} (hvw : F.graph.toSimpleGraph.Adj v w) {L : ℝ}
    (hupper : min (radius r₀ z v) (radius r₀ z w) < 2 * L) :
    ‖z v‖ < 4 * L ∧ ‖z w‖ < 4 * L := by
  have hinc := abs_radius_sub_le F hF z hz r₀ hvw
  have hdv := point_diameter_le F z hz r₀ hD v
  have hdw := point_diameter_le F z hz r₀ hD w
  have hv : 0 < radius r₀ z v := hr₀.trans_le (le_max_left _ _)
  have hw : 0 < radius r₀ z w := hr₀.trans_le (le_max_left _ _)
  have hvz : ‖z v‖ ≤ radius r₀ z v := le_max_right _ _
  have hwz : ‖z w‖ ≤ radius r₀ z w := le_max_right _ _
  have hdiff := abs_le.mp hinc
  rcases le_total (radius r₀ z v) (radius r₀ z w) with h | h
  · rw [min_eq_left h] at hupper
    constructor <;> linarith
  · rw [min_eq_right h] at hupper
    constructor <;> linarith

/-- The manuscript's diameter-weighted conductance mass as a nonnegative
countable sum. This definition makes no summability or local finiteness assumption. -/
noncomputable def localMassENN (F : IndexedCells V) (A : Set V) : ℝ≥0∞ := by
  classical
  exact ∑' v, if v ∈ A then
    ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2 * F.graph.pi v) else 0

/-- Half of the ordered-edge sum restricted to a specified family of edges. -/
noncomputable def maskedEnergyENN (F : IndexedCells V) (f : V → ℝ)
    (S : Set (V × V)) : ℝ≥0∞ := by
  classical
  exact (∑' p, if p ∈ S then ENNReal.ofReal (F.graph.gradSq f p) else 0) / 2

/-- Tonelli regrouping by the first endpoint gives exactly the local incidence mass. -/
theorem incidence_tsum_eq (F : IndexedCells V) (A : Set V) :
    (∑' p : V × V, if p.1 ∈ A then
      ENNReal.ofReal (F.graph.c p.1 p.2) *
        ENNReal.ofReal (Metric.diam (F.cell p.1 : Set Plane) ^ 2) else 0) =
      localMassENN F A := by
  classical
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro v
  by_cases hv : v ∈ A
  · simp only [hv, if_true]
    rw [ENNReal.tsum_mul_right,
      ← ENNReal.ofReal_tsum_of_nonneg (F.graph.c_nonneg v) (F.graph.summable_c v)]
    change ENNReal.ofReal (F.graph.pi v) *
      ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) = _
    rw [← ENNReal.ofReal_mul (F.graph.pi_nonneg v)]
    congr 1
    exact mul_comm _ _
  · simp [hv]

/-- Countable annular incidence estimate. The hypotheses are pointwise edge
bounds and endpoint membership; no finite edge set is introduced. -/
theorem maskedEnergy_le_localMass (F : IndexedCells V) (f : V → ℝ)
    (S : Set (V × V)) (A : Set V) {K : ℝ} (hK : 0 ≤ K)
    (hends : ∀ p ∈ S, F.graph.c p.1 p.2 ≠ 0 → p.1 ∈ A ∧ p.2 ∈ A)
    (hstep : ∀ p ∈ S, F.graph.c p.1 p.2 ≠ 0 →
      |f p.2 - f p.1| ≤ K * (Metric.diam (F.cell p.1 : Set Plane) +
        Metric.diam (F.cell p.2 : Set Plane))) :
    maskedEnergyENN F f S ≤ ENNReal.ofReal (2 * K ^ 2) * localMassENN F A := by
  classical
  let a : V × V → ℝ≥0∞ := fun p => if p.1 ∈ A then
    ENNReal.ofReal (F.graph.c p.1 p.2) *
      ENNReal.ofReal (Metric.diam (F.cell p.1 : Set Plane) ^ 2) else 0
  have ha : ∑' p, a p = localMassENN F A := incidence_tsum_eq F A
  have hb : ∑' p : V × V, a p.swap = localMassENN F A := by
    change (∑' p : V × V, a ((Equiv.prodComm V V) p)) = _
    rw [(Equiv.prodComm V V).tsum_eq a]
    exact ha
  have hpoint : ∀ p : V × V,
      (if p ∈ S then ENNReal.ofReal (F.graph.gradSq f p) else 0) ≤
        ENNReal.ofReal (2 * K ^ 2) * (a p + a p.swap) := by
    intro p
    by_cases hp : p ∈ S
    · by_cases hc : F.graph.c p.1 p.2 = 0
      · simp [hp, ReflectedWalk.ConductanceGraph.gradSq, hc]
      · obtain ⟨hv, hw⟩ := hends p hp hc
        have hdv : 0 ≤ Metric.diam (F.cell p.1 : Set Plane) := Metric.diam_nonneg
        have hdw : 0 ≤ Metric.diam (F.cell p.2 : Set Plane) := Metric.diam_nonneg
        have hs := hstep p hp hc
        have hsquare : (f p.2 - f p.1) ^ 2 ≤
            2 * K ^ 2 * (Metric.diam (F.cell p.1 : Set Plane) ^ 2 +
              Metric.diam (F.cell p.2 : Set Plane) ^ 2) := by
          have hsq := sq_le_sq₀ (abs_nonneg (f p.2 - f p.1))
            (mul_nonneg hK (add_nonneg hdv hdw)) |>.2 hs
          rw [sq_abs] at hsq
          nlinarith [mul_nonneg (sq_nonneg K)
            (sq_nonneg (Metric.diam (F.cell p.1 : Set Plane) -
              Metric.diam (F.cell p.2 : Set Plane)))]
        have hgrad := mul_le_mul_of_nonneg_left hsquare (F.graph.c_nonneg p.1 p.2)
        simp only [hp, if_true, a, Prod.swap, hv, hw, F.graph.c_symm p.2 p.1]
        rw [← ENNReal.ofReal_mul (F.graph.c_nonneg p.1 p.2),
          ← ENNReal.ofReal_mul (F.graph.c_nonneg p.1 p.2),
          ← ENNReal.ofReal_add (mul_nonneg (F.graph.c_nonneg _ _) (sq_nonneg _))
            (mul_nonneg (F.graph.c_nonneg _ _) (sq_nonneg _)),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * K ^ 2)]
        apply ENNReal.ofReal_le_ofReal
        unfold ReflectedWalk.ConductanceGraph.gradSq
        exact hgrad.trans_eq (by ring)
    · simp only [hp, if_false]
      exact zero_le
  calc
    maskedEnergyENN F f S ≤
        (∑' p : V × V, ENNReal.ofReal (2 * K ^ 2) * (a p + a p.swap)) / 2 :=
      ENNReal.div_le_div_right (ENNReal.tsum_le_tsum hpoint) 2
    _ = (ENNReal.ofReal (2 * K ^ 2) * (localMassENN F A + localMassENN F A)) / 2 := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ha, hb]
    _ = ENNReal.ofReal (2 * K ^ 2) * localMassENN F A := by
      rw [← two_mul]
      calc
        _ = (ENNReal.ofReal (2 * K ^ 2) * localMassENN F A) *
            ((2 : ℝ≥0∞) * 2⁻¹) := by simp only [div_eq_mul_inv]; ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- Every shell is controlled by the mass in its fourfold enlarged ball. -/
theorem annularEnergy_le [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (z : V → Plane) (hz : StatementIngredients.CellRepresentatives F z)
    {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ} (hn : 1 ≤ n)
    (hD : ∀ R, r₀ ≤ R → ∀ v, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    {L : ℝ} (hL : 0 < L) :
    maskedEnergyENN F (cutoff r₀ n z)
      {p | L ≤ min (radius r₀ z p.1) (radius r₀ z p.2) ∧
        min (radius r₀ z p.1) (radius r₀ z p.2) < 2 * L} ≤
      ENNReal.ofReal (2 * (1 / (((n : ℝ) * Real.log 2) * L)) ^ 2) *
        localMassENN F {v | Hits F (Metric.closedBall (0 : Plane) (4 * L)) v} := by
  apply maskedEnergy_le_localMass F _ _ _
    (one_div_nonneg.mpr (mul_pos (logDenom_pos hn) hL).le)
  · intro p hp hc
    have hadj : F.graph.toSimpleGraph.Adj p.1 p.2 :=
      lt_of_le_of_ne (F.graph.c_nonneg _ _) (Ne.symm hc)
    obtain ⟨hv, hw⟩ := shell_endpoints_lt F hF z hz hr₀ hD hadj hp.2
    exact ⟨⟨z p.1, hz p.1, by simpa using hv.le⟩,
      ⟨z p.2, hz p.2, by simpa using hw.le⟩⟩
  · intro p hp hc
    have hadj : F.graph.toSimpleGraph.Adj p.1 p.2 :=
      lt_of_le_of_ne (F.graph.c_nonneg _ _) (Ne.symm hc)
    have h := edge_difference_le F hF z hz hr₀ hn hadj hL
      (hp.1.trans (min_le_left _ _)) (hp.1.trans (min_le_right _ _))
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

end ReflectedGMS.LogCutoff
