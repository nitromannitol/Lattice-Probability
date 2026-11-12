/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.ContMetric at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable
import LatticeProb.Bonanno.LQGMetric.Statement.Metric

/-!
# LFPP with a continuous density is a continuous metric on ℂ

Task P2-LFPP, item 1. For continuous `φ`, `D^φ(z,w) := inf_P ∫₀¹ e^{ξφ(P)}|P'|` (GM (1.4),
`uniqueness-final.tex` l. 216–220) satisfies, locally, `m min(r, |z-w|) ≤ D^φ(z,w) ≤ B |z-w|`
(`m`, `B` the min/max of `e^{ξφ}` on a ball), hence `(D^φ).toReal` is a continuous metric
inducing the Euclidean topology (`ContMetric`, FOUNDATIONS §4). Applied to `φ = h*_ε` on the
a.s. event where it is continuous (`HeatMollifyUnif.lean`), this packages `lfppDist ξ ε h` as a
`ContMetric`. Own elementary arguments (DFGPS §2 states this without proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

variable {ξ : ℝ} {φ : ℂ → ℝ}

theorem exists_pos_le_exp_on (hφ : Continuous φ) (z : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ m > 0, ∀ x ∈ Metric.closedBall z r, m ≤ Real.exp (ξ * φ x) := by
  obtain ⟨x0, -, hx0⟩ := (isCompact_closedBall z r).exists_isMinOn
    ⟨z, Metric.mem_closedBall_self hr⟩
    (Real.continuous_exp.comp (continuous_const.mul hφ)).continuousOn
  exact ⟨_, Real.exp_pos _, fun x hx => hx0 hx⟩

theorem exists_exp_le_on (hφ : Continuous φ) (R : ℝ) :
    ∃ B, ∀ x ∈ Metric.closedBall (0 : ℂ) R, Real.exp (ξ * φ x) ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (Real.continuous_exp.comp (continuous_const.mul hφ)).continuousOn
  exact ⟨B, fun x hx => (Real.le_norm_self _).trans (hB x hx)⟩

/-- **Lower bound for a single path**: a path from `z` to `w` costs at least
`m · min(r, |w - z|)` if `m ≤ e^{ξφ}` on `B(z, r)`. -/
theorem le_lfppLen_of_path {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) {r m : ℝ}
    (hr : 0 < r) (hm : 0 ≤ m) (hmE : ∀ x ∈ Metric.closedBall z r, m ≤ Real.exp (ξ * φ x)) :
    ENNReal.ofReal (m * min r ‖w - z‖) ≤ lfppLen ξ φ P := by
  set g : ℝ → ℝ := fun t => ‖P t - z‖
  have hg : ContinuousOn g (Icc 0 1) := (hP.continuousOn.sub continuousOn_const).norm
  have hg0 : g 0 = 0 := by simp [g, hP.source]
  by_cases hin : ∀ t ∈ Icc (0 : ℝ) 1, g t ≤ r
  · have := hP.ofReal_mul_norm_sub_le (ξ := ξ) (φ := φ) hm le_rfl zero_le_one le_rfl
      fun t ht => hmE _ (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hin t ht)
    rw [hP.source, hP.target] at this
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) this
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hm
  simp only [not_forall, not_le] at hin
  obtain ⟨t1, ht1, hgt1⟩ := hin
  set T := Icc (0 : ℝ) 1 ∩ g ⁻¹' Ici r
  have hTc : IsClosed T := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hTne : T.Nonempty := ⟨t1, ht1, hgt1.le⟩
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf T
  have hτT : τ ∈ T := hTc.csInf_mem hTne hTb
  have hτ0 : 0 ≤ τ := hτT.1.1
  have hτ1 : τ ≤ 1 := hτT.1.2
  -- `g τ = r` by the intermediate value theorem
  obtain ⟨σ, hσ, hgσ⟩ := intermediate_value_Icc hτ0 (hg.mono (Icc_subset_Icc le_rfl hτ1))
    (show r ∈ Icc (g 0) (g τ) from ⟨by rw [hg0]; exact hr.le, hτT.2⟩)
  have hστ : σ = τ := le_antisymm hσ.2
    (csInf_le hTb ⟨⟨hσ.1, hσ.2.trans hτ1⟩, show r ≤ g σ from hgσ.ge⟩)
  have hgτ : g τ = r := hστ ▸ hgσ
  have hin' : ∀ s ∈ Icc (0 : ℝ) τ, g s ≤ r := by
    intro s hs
    rcases hs.2.lt_or_eq with h | h
    · by_contra hc
      exact absurd (csInf_le hTb ⟨⟨hs.1, hs.2.trans hτ1⟩, (not_le.1 hc).le⟩) (not_le.2 h)
    · rw [h, hgτ]
  have := hP.ofReal_mul_norm_sub_le (ξ := ξ) (φ := φ) hm le_rfl hτ0 hτ1
    fun t ht => hmE _ (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hin' t ht)
  rw [hP.source] at this
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (this.trans
    (lintegral_mono_set (Icc_subset_Icc le_rfl hτ1)))
  exact mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hgτ.ge) hm

/-- the LFPP distance on ℂ with density `e^{ξ φ}` -/
abbrev lfppD (ξ : ℝ) (φ : ℂ → ℝ) : ℂ → ℂ → ℝ≥0∞ := lfppDOn ξ φ univ

theorem le_lfppD {z w : ℂ} {r m : ℝ} (hr : 0 < r) (hm : 0 ≤ m)
    (hmE : ∀ x ∈ Metric.closedBall z r, m ≤ Real.exp (ξ * φ x)) :
    ENNReal.ofReal (m * min r ‖w - z‖) ≤ lfppD ξ φ z w :=
  le_iInf fun P => le_lfppLen_of_path P.2.1 hr hm hmE

theorem lfppD_le {z w : ℂ} {B : ℝ}
    (hB : ∀ x ∈ Metric.closedBall z ‖w - z‖, Real.exp (ξ * φ x) ≤ B) :
    lfppD ξ φ z w ≤ ENNReal.ofReal (B * ‖w - z‖) :=
  (lfppDOn_le_segCost convex_univ (mem_univ _) (mem_univ _)).trans (segCost_le hB)

theorem lfppD_ne_top (hφ : Continuous φ) (z w : ℂ) : lfppD ξ φ z w ≠ ∞ := by
  obtain ⟨B, hB⟩ := exists_exp_le_on (ξ := ξ) hφ (‖z‖ + ‖w - z‖)
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lfppD_le fun x hx => hB x ?_)
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith [norm_le_norm_add_norm_sub' x z]

/-- local Lipschitz bound: on `B(0,R)`, `D^φ(z,z') ≤ B |z - z'|` -/
theorem exists_lfppD_le_mul (hφ : Continuous φ) (R : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) R, ∀ z' ∈ Metric.closedBall (0 : ℂ) R,
      (lfppD ξ φ z z').toReal ≤ B * ‖z' - z‖ := by
  obtain ⟨B, hB⟩ := exists_exp_le_on (ξ := ξ) hφ (3 * R)
  refine ⟨max B 0, le_max_right _ _, fun z hz z' hz' => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hz hz'
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (lfppD_le fun x hx => ?_)
  refine (hB x ?_).trans (le_max_left _ _)
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith [norm_le_norm_add_norm_sub' x z, norm_sub_le z' z]

/-! ### The real-valued metric -/

/-- `D^φ` as a function on `ℂ × ℂ` -/
def lfppDReal (ξ : ℝ) (φ : ℂ → ℝ) (p : ℂ × ℂ) : ℝ := (lfppD ξ φ p.1 p.2).toReal

theorem lfppDReal_triangle (hφ : Continuous φ) (x y z : ℂ) :
    lfppDReal ξ φ (x, z) ≤ lfppDReal ξ φ (x, y) + lfppDReal ξ φ (y, z) :=
  ENNReal.toReal_le_add (lfppDOn_triangle x y z) (lfppD_ne_top hφ _ _) (lfppD_ne_top hφ _ _)

theorem continuous_lfppDReal (hφ : Continuous φ) : Continuous (lfppDReal ξ φ) := by
  rw [Metric.continuous_iff]
  rintro ⟨z0, w0⟩ ε hε
  obtain ⟨B, hB0, hB⟩ := exists_lfppD_le_mul (ξ := ξ) hφ (‖z0‖ + ‖w0‖ + 1)
  refine ⟨min 1 (ε / (2 * (B + 1))), lt_min one_pos (by positivity), ?_⟩
  rintro ⟨z, w⟩ hd
  have hd1 := hd.trans_le (min_le_left _ _)
  have hd2 := hd.trans_le (min_le_right _ _)
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hd1 hd2
  simp only at hd1 hd2
  have mem : ∀ x : ℂ, ‖x‖ ≤ ‖z0‖ + ‖w0‖ + 1 → x ∈ Metric.closedBall (0 : ℂ) (‖z0‖ + ‖w0‖ + 1) :=
    fun x hx => by rwa [Metric.mem_closedBall, dist_zero_right]
  have hz : ‖z‖ ≤ ‖z0‖ + ‖w0‖ + 1 := by linarith [norm_le_norm_add_norm_sub' z z0, norm_nonneg w0]
  have hw : ‖w‖ ≤ ‖z0‖ + ‖w0‖ + 1 := by linarith [norm_le_norm_add_norm_sub' w w0, norm_nonneg z0]
  have hz0 : ‖z0‖ ≤ ‖z0‖ + ‖w0‖ + 1 := by linarith [norm_nonneg w0]
  have hw0 : ‖w0‖ ≤ ‖z0‖ + ‖w0‖ + 1 := by linarith [norm_nonneg z0]
  have e1 := hB z (mem z hz) z0 (mem z0 hz0)
  have e2 := hB z0 (mem z0 hz0) z (mem z hz)
  have e3 := hB w (mem w hw) w0 (mem w0 hw0)
  have e4 := hB w0 (mem w0 hw0) w (mem w hw)
  have t1 := lfppDReal_triangle (ξ := ξ) hφ z z0 w
  have t2 := lfppDReal_triangle (ξ := ξ) hφ z0 w0 w
  have t3 := lfppDReal_triangle (ξ := ξ) hφ z0 z w0
  have t4 := lfppDReal_triangle (ξ := ξ) hφ z w w0
  simp only [lfppDReal] at t1 t2 t3 t4 ⊢
  rw [norm_sub_rev z0 z] at e1
  rw [norm_sub_rev w0 w] at e3
  have hBε : B * (2 * (ε / (2 * (B + 1)))) < ε := by
    rw [mul_div_assoc', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hd2.1.le hB0,
    mul_le_mul_of_nonneg_left hd2.2.le hB0]

theorem lfppDReal_eq_zero (hφ : Continuous φ) {z w : ℂ} (h : lfppDReal ξ φ (z, w) = 0) :
    z = w := by
  obtain ⟨m, hm, hmE⟩ := exists_pos_le_exp_on (ξ := ξ) hφ z 1 zero_le_one
  have h0 : lfppD ξ φ z w = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
    · exact h
    · exact absurd h (lfppD_ne_top hφ z w)
  have := (le_lfppD (w := w) one_pos hm.le hmE).trans h0.le
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  have h2 : min 1 ‖w - z‖ ≤ 0 := by
    by_contra hc
    exact absurd this (not_le.2 (mul_pos hm (not_le.1 hc)))
  rcases min_le_iff.1 h2 with h3 | h3
  · linarith
  · exact (sub_eq_zero.1 (norm_le_zero_iff.1 h3)).symm

theorem lfppDReal_euclidean_of_small (hφ : Continuous φ) (x : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, lfppDReal ξ φ (x, y) < δ → ‖x - y‖ < ε := by
  obtain ⟨m, hm, hmE⟩ := exists_pos_le_exp_on (ξ := ξ) hφ x ε hε.le
  refine ⟨m * ε, by positivity, fun y hy => ?_⟩
  have h1 := le_lfppD (w := y) hε hm.le hmE
  have h2 : m * min ε ‖y - x‖ ≤ lfppDReal ξ φ (x, y) :=
    (ENNReal.ofReal_le_iff_le_toReal (lfppD_ne_top hφ x y)).1 h1
  have h3 : min ε ‖y - x‖ < ε := by
    by_contra hc
    nlinarith [not_lt.1 hc]
  rw [norm_sub_rev]
  rcases min_lt_iff.1 h3 with h | h
  · linarith
  · exact h

/-- **LFPP with a continuous density as a `ContMetric`.** -/
def lfppContMetric (ξ : ℝ) (φ : ℂ → ℝ) (hφ : Continuous φ) : ContMetric :=
  ⟨⟨lfppDReal ξ φ, continuous_lfppDReal hφ⟩,
    { self_eq_zero := fun x => by
        simp [lfppDReal, lfppDOn_self convex_univ (mem_univ x)]
      eq_of_eq_zero := fun x y h => lfppDReal_eq_zero hφ h
      symm := fun x y => by
        show lfppDReal ξ φ (x, y) = lfppDReal ξ φ (y, x)
        simp only [lfppDReal]; exact congrArg ENNReal.toReal (lfppDOn_comm x y)
      triangle := fun x y z => lfppDReal_triangle hφ x y z
      euclidean_of_small := fun x ε hε => lfppDReal_euclidean_of_small hφ x ε hε }⟩

theorem lfppContMetric_apply (ξ : ℝ) (φ : ℂ → ℝ) (hφ : Continuous φ) (p : ℂ × ℂ) :
    (lfppContMetric ξ φ hφ).1 p = (lfppD ξ φ p.1 p.2).toReal := rfl

theorem lfppDist_eq_lfppDReal (ξ ε : ℝ) (h : DistC) :
    lfppDist ξ ε h = lfppDReal ξ (heatMollify ε h) := by
  funext p
  simp only [lfppDist, lfppDReal, lfppDistE_eq_lfppDOn]

/-- **`D^ε_h` as a `ContMetric`** when `h*_ε` is continuous (a.s., `HeatMollifyUnif.lean`). -/
def lfppDistCM (ξ ε : ℝ) (h : DistC) (hc : Continuous (heatMollify ε h)) : ContMetric :=
  lfppContMetric ξ (heatMollify ε h) hc

theorem lfppDistCM_coe (ξ ε : ℝ) (h : DistC) (hc : Continuous (heatMollify ε h)) :
    ⇑(lfppDistCM ξ ε h hc).1 = lfppDist ξ ε h := by
  rw [lfppDist_eq_lfppDReal]; rfl

end LFPP
end LQGMetric
