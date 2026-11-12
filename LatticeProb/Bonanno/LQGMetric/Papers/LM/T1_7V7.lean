/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V5

/-!
# LM Lemma 5.3 (restricted to `B_m`), the deterministic per-metric core

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Lemma 5.3 (`lem-internal-msrble`, l. 964–986): "fix `z, w`
and `δ > 0` and let `P` be a path from `z` to `w` with `D`-length at most `D(z,w) + δ`, chosen in a
manner depending only on `D`. By Lemma 5.2 … By (5.6) … Consequently (5.8) … Since the internal
metrics of `D` and `D'` on `S ∩ U` coincide … `len(P; D) = len(P; D')`. Since `D'` is a length
metric and by our choice of `P`, `D'(z,w) ≤ D(z,w) + δ`."

Here with `U = ℂ`, the internal metric `F = D(z,w;B_m)` (chain formula `t17F`) and only the
squares `t17Box ε R` meeting `cl B_R ⊇ B_m` (D107 §3(i)): `t17v_l53_perD` — for a length metric `d`,
for a.e. `θ ∈ [0,1]²`, every `d' ≤ c d` with the same internal metrics on all these squares has
`F(d') ≤ F(d)`. The length property of `d'` is not needed (`chainInf ≤ internal ≤ len` holds for
every metric). The near-geodesics depend only on `d` and `δ = 1/(j+1)`; the exceptional `θ`-set is
the countable union of the `θ`-null sets of LM Lemma 5.2 (`t17_grid_null`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric.LM

open MetricGeometry

/-- **LM l. 975–981**: one near-geodesic and one grid -/
theorem t17v_l53_core {d d' : ContMetric} {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x y : ℂ, d'.1 (x, y) ≤ c * d.1 (x, y)) {ε R : ℝ} (hε : 0 < ε) {θ : ℝ × ℝ}
    (hθ1 : θ.1 ∈ Icc (0 : ℝ) 1) (hθ2 : θ.2 ∈ Icc (0 : ℝ) 1) {P : ℝ → ℂ} (hP : Continuous P)
    (hfin : d.len P 0 1 ≠ ⊤) (hPR : MapsTo P (Icc 0 1) (Metric.closedBall 0 R)) {m : ℕ}
    {z w : ℂ} (hPm : MapsTo P (Icc 0 1) (Metric.ball 0 (m : ℝ))) (hP0 : P 0 = z) (hP1 : P 1 = w)
    (hnull : t17LenMeas (d.pt ∘ P) 0 1 (Icc 0 1 ∩ P ⁻¹' t17Grid ε θ) = 0)
    (hS : ∀ k ∈ t17Box ε R, ∀ u ∈ t17Square ε θ k, ∀ v ∈ t17Square ε θ k,
      d.internal (t17Square ε θ k) u v = d'.internal (t17Square ε θ k) u v) :
    t17F m z w d' ≤ d.len P 0 1 := by
  -- choose `k₀ ∉ t17Box ε R`, so that the metrics agree on every square of the box
  obtain ⟨k₀, hk₀⟩ := (t17Box ε R).exists_notMem
  obtain ⟨-, -, hs'', hs, hfin''⟩ := t17v_resample hc hle hε hθ1 hθ2 hP zero_le_one hfin hPR
    hnull (k₀ := k₀) (fun k hk _ => hS k hk)
  have heq : d'.len P 0 1 = d.len P 0 1 := by
    have hsum : ∑ k ∈ t17Box ε R, t17Piece d' P 0 1 ε θ k =
        ∑ k ∈ t17Box ε R, t17Piece d P 0 1 ε θ k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have := t17v_resample hc hle hε hθ1 hθ2 hP zero_le_one hfin hPR hnull (k₀ := k₀)
        (fun k hk _ => hS k hk)
      exact this.1 k hk (fun h => hk₀ (h ▸ hk))
    rw [← ENNReal.ofReal_toReal hfin'', ← ENNReal.ofReal_toReal hfin, hs'', hs, hsum]
  rw [← heq]
  refine (d'.chainInf_le_internal Metric.isOpen_ball z w).trans ?_
  have := internalEDist_le_curveLength (X := d'.Space) (Y := d'.pt '' Metric.ball 0 (m : ℝ))
    (P := d'.pt ∘ P) zero_le_one (d'.continuous_pt.comp_continuousOn hP.continuousOn)
    (fun t ht => ⟨P t, hPm ht, rfl⟩)
  rw [← hP0, ← hP1]
  exact this

/-- **LM Lemma 5.3, per metric** (l. 975–986): for a length metric `d` and `‖z‖, ‖w‖ < m ≤ R`,
for a.e. `θ ∈ [0,1]²`, every `d' ≤ c d` with the same internal metrics as `d` on all squares of
`t17Box ε R` has `d'(z,w;B_m) ≤ d(z,w;B_m)`. -/
theorem t17v_l53_perD {d : ContMetric} (hd : d.IsLength) {c : ℝ} (hc : 0 ≤ c) {m : ℕ} {R : ℝ}
    (hmR : (m : ℝ) ≤ R) {z w : ℂ} (hz : ‖z‖ < m) (hw : ‖w‖ < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)), θ.1 ∈ Icc (0 : ℝ) 1 → θ.2 ∈ Icc (0 : ℝ) 1 →
      ∀ d' : ContMetric, (∀ x y : ℂ, d'.1 (x, y) ≤ c * d.1 (x, y)) →
        (∀ k ∈ t17Box ε R, ∀ u ∈ t17Square ε θ k, ∀ v ∈ t17Square ε θ k,
          d.internal (t17Square ε θ k) u v = d'.internal (t17Square ε θ k) u v) →
        t17F m z w d' ≤ t17F m z w d := by
  have hzm : z ∈ Metric.ball (0 : ℂ) (m : ℝ) := mem_ball_zero_iff.2 hz
  have hwm : w ∈ Metric.ball (0 : ℂ) (m : ℝ) := mem_ball_zero_iff.2 hw
  have hI : d.internal (Metric.ball 0 (m : ℝ)) z w ≠ ⊤ :=
    DFGPS.T12.internal_ne_top d hd Metric.isOpen_ball (convex_ball _ _).isPreconnected hzm hwm
  have e : t17F m z w d = d.internal (Metric.ball 0 (m : ℝ)) z w :=
    (d.internal_eq_chainInf hd Metric.isOpen_ball z w).symm
  have hδ : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  choose P hPc hP0 hP1 hPm hPl using fun j : ℕ => t17v_near_path d hI (hδ j)
  have hg : ∀ j, ∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)),
      t17LenMeas (d.pt ∘ P j) 0 1 {t | P j t ∈ t17Grid ε θ} = 0 := fun j =>
    @t17_grid_null ε hε (P j) (hPc j).measurable _ (t17v_sfinite d (P j) 0 1)
  filter_upwards [ae_all_iff.2 hg] with θ hθ hθ1 hθ2 d' hle hS
  refine ENNReal.le_of_forall_pos_le_add fun δ hδpos _ => ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ from hδpos)
  have hfin : d.len (P j) 0 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hI, ENNReal.ofReal_ne_top⟩) (hPl j)
  have hPR : MapsTo (P j) (Icc 0 1) (Metric.closedBall 0 R) := fun t ht =>
    Metric.closedBall_subset_closedBall hmR (Metric.ball_subset_closedBall (hPm j ht))
  have h1 := t17v_l53_core hc hle hε hθ1 hθ2 (hPc j) hfin hPR (hPm j) (hP0 j) (hP1 j)
    (measure_mono_null inter_subset_right (hθ j)) hS
  calc t17F m z w d' ≤ d.len (P j) 0 1 := h1
    _ ≤ d.internal (Metric.ball 0 (m : ℝ)) z w + ENNReal.ofReal (1 / ((j : ℝ) + 1)) := hPl j
    _ ≤ t17F m z w d + δ := by
        rw [e]
        refine add_le_add le_rfl (ENNReal.ofReal_le_of_le_toReal ?_)
        rw [ENNReal.coe_toReal]
        exact hj.le

end LQGMetric.LM
