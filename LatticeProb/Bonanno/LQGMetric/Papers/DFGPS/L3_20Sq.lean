/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_20Sq at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20Concat
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20Ball

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 3.20, second display
(`eqn-holder-upper-square`, T:2322–2325) for the closed squares `S` of `Blueprint.DFGPSLem3_20`,
proof T:2330 "similarly follows from (eqn-ep-diam-square)". Lemma 3.19's square estimate
controls the internal diameters of open squares; a point `u` of the closed square `S` is reached
from the centre of `S` through the centres of nested open dyadic sub-squares `Q_j ∋ ` (closure)
`u`, of side `2^{-j}σ`, and `L3_20Concat.internalEDist_le_tsum_of_chain` gives
`D(centre, u; S) ≤ Σ_j diam(Q_j) ≤ B/(1 − 2^{-s})` if `diam(Q_j) ≤ B 2^{-js}` (`sq_det`). Own
elementary argument for the passage from open to closed squares (proposed DEVIATIONS DFA7-2).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L320

open Blueprint Complex

/-- the open square with lower-left corner `p` and side `s` -/
def osq (s : ℝ) (p : ℂ) : Set ℂ :=
  {x | p.re < x.re ∧ x.re < p.re + s ∧ p.im < x.im ∧ x.im < p.im + s}

/-- the closed square with lower-left corner `p` and side `s` -/
def csq (s : ℝ) (p : ℂ) : Set ℂ :=
  {x | p.re ≤ x.re ∧ x.re ≤ p.re + s ∧ p.im ≤ x.im ∧ x.im ≤ p.im + s}

/-- nested dyadic indices: `n_j ≤ 2^j y ≤ n_j + 1`, `n_{j+1} ∈ {2n_j, 2n_j + 1}` -/
def nn (y : ℝ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => if (2 : ℝ) ^ (j + 1) * y ≤ 2 * (nn y j : ℝ) + 1 then 2 * nn y j else 2 * nn y j + 1

lemma nn_spec {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : ∀ j,
    (nn y j : ℝ) ≤ 2 ^ j * y ∧ 2 ^ j * y ≤ nn y j + 1 ∧ 0 ≤ (nn y j : ℝ) ∧
      (nn y j : ℝ) + 1 ≤ 2 ^ j
  | 0 => by simp [nn]; exact ⟨hy0, hy1⟩
  | j + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := nn_spec hy0 hy1 j
    simp only [nn]
    split_ifs with h
    · push_cast; rw [pow_succ] at h ⊢
      refine ⟨by nlinarith, by linarith, by linarith, by nlinarith⟩
    · push_cast; rw [pow_succ] at h ⊢
      push Not at h
      refine ⟨by linarith, by nlinarith, by linarith, by nlinarith⟩

lemma nn_succ (y : ℝ) (j : ℕ) :
    2 * (nn y j : ℝ) ≤ nn y (j + 1) ∧ (nn y (j + 1) : ℝ) ≤ 2 * nn y j + 1 := by
  simp only [nn]
  split_ifs <;> push_cast <;> constructor <;> linarith

lemma re_aux (c : ℂ) (a p q : ℝ) : (c + (a : ℂ) * ((p : ℂ) + (q : ℂ) * I)).re = c.re + a * p := by
  simp
lemma im_aux (c : ℂ) (a p q : ℝ) : (c + (a : ℂ) * ((p : ℂ) + (q : ℂ) * I)).im = c.im + a * q := by
  simp

/-- the corner of the level-`j` dyadic sub-square containing `u` in its closure -/
def cornerJ (σ : ℝ) (c u : ℂ) (j : ℕ) : ℂ :=
  c + ((σ * (1 / 2) ^ j : ℝ) : ℂ) * (((nn ((u.re - c.re) / σ) j : ℝ) : ℂ) +
    ((nn ((u.im - c.im) / σ) j : ℝ) : ℂ) * I)

/-- its centre -/
def centreJ (σ : ℝ) (c u : ℂ) (j : ℕ) : ℂ :=
  c + ((σ * (1 / 2) ^ j : ℝ) : ℂ) * ((((nn ((u.re - c.re) / σ) j : ℝ) + 1 / 2 : ℝ) : ℂ) +
    (((nn ((u.im - c.im) / σ) j : ℝ) + 1 / 2 : ℝ) : ℂ) * I)

lemma half_pow_succ (σ : ℝ) (j : ℕ) : σ * (1 / 2 : ℝ) ^ (j + 1) = σ * (1 / 2) ^ j / 2 := by
  rw [pow_succ]; ring

lemma two_pow_mul_half_pow' (j : ℕ) : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := by
  rw [← mul_pow]; norm_num

/-- coordinate facts: with `y ∈ [0,1]`, `σ_j = σ 2^{-j}`, `n_j = nn y j` -/
lemma coord_facts {σ y : ℝ} (hσ : 0 < σ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (j : ℕ) :
    let a := σ * (1 / 2 : ℝ) ^ j
    0 ≤ a * nn y j ∧ a * nn y j + a ≤ σ ∧
    a * nn y j < a * (nn y j + 1 / 2) ∧ a * (nn y j + 1 / 2) < a * nn y j + a ∧
    a * nn y j < σ * (1 / 2) ^ (j + 1) * (nn y (j + 1) + 1 / 2) ∧
    σ * (1 / 2) ^ (j + 1) * (nn y (j + 1) + 1 / 2) < a * nn y j + a ∧
    |a * (nn y j + 1 / 2) - σ * y| ≤ a := by
  intro a
  have ha : 0 < a := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := nn_spec hy0 hy1 j
  obtain ⟨h5, h6⟩ := nn_succ y j
  have hp : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := two_pow_mul_half_pow' j
  have hay : a * 2 ^ j = σ := by simp only [a]; rw [mul_assoc, mul_comm ((1/2 : ℝ) ^ j), hp, mul_one]
  have hs : σ * (1 / 2 : ℝ) ^ (j + 1) = a / 2 := half_pow_succ σ j
  rw [hs]
  refine ⟨by positivity, ?_, by nlinarith, by nlinarith, by nlinarith, by nlinarith, ?_⟩
  · calc a * nn y j + a = a * (nn y j + 1) := by ring
      _ ≤ a * 2 ^ j := by gcongr
      _ = σ := hay
  · rw [abs_le]
    have e1 : a * (2 ^ j * y) = σ * y := by rw [← mul_assoc, hay]
    constructor <;> nlinarith

lemma tsum_ofReal_geom {B r : ℝ} (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ, ENNReal.ofReal (B * r ^ n) = ENNReal.ofReal (B / (1 - r)) := by
  simp_rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_pow hr0]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have h1 : (1 : ℝ≥0∞) - ENNReal.ofReal r = ENNReal.ofReal (1 - r) := by
    rw [ENNReal.ofReal_sub _ hr0, ENNReal.ofReal_one]
  rw [h1, ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul hB, div_eq_mul_inv]

/-- **deterministic part of the second display**: bounds on the internal diameters of the open
dyadic sub-squares `Q` of level `j` of the closed square `csq σ c` by `B 2^{-js}` give
`sup_{u,v ∈ S} D(u,v;S) ≤ 2B/(1 − 2^{-s})` -/
theorem sq_det (Dg : ContMetric) {σ s B : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hB : 0 ≤ B) (c : ℂ)
    (hgood : ∀ (j : ℕ) (n1 n2 : ℤ), 0 ≤ (n1 : ℝ) → (n1 : ℝ) + 1 ≤ 2 ^ j → 0 ≤ (n2 : ℝ) →
      (n2 : ℝ) + 1 ≤ 2 ^ j →
      internalDiam Dg (osq (σ * (1 / 2) ^ j)
          (c + ((σ * (1 / 2) ^ j : ℝ) : ℂ) * (((n1 : ℝ) : ℂ) + ((n2 : ℝ) : ℂ) * I)))
        (osq (σ * (1 / 2) ^ j)
          (c + ((σ * (1 / 2) ^ j : ℝ) : ℂ) * (((n1 : ℝ) : ℂ) + ((n2 : ℝ) : ℂ) * I))) ≤
        ENNReal.ofReal (B * ((1 / 2) ^ s) ^ j)) :
    internalDiam Dg (csq σ c) (csq σ c) ≤ ENNReal.ofReal (2 * (B / (1 - (1 / 2) ^ s))) := by
  have hr0 : (0 : ℝ) ≤ (1 / 2) ^ s := Real.rpow_nonneg (by norm_num) _
  have hr1 : ((1 : ℝ) / 2) ^ s < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hs
  set M := ENNReal.ofReal (B / (1 - (1 / 2) ^ s)) with hM
  have key : ∀ u ∈ csq σ c, Dg.internal (csq σ c) (centreJ σ c u 0) u ≤ M := by
    intro u hu
    obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
    set y1 := (u.re - c.re) / σ with hy1
    set y2 := (u.im - c.im) / σ with hy2
    have hy10 : 0 ≤ y1 := div_nonneg (by linarith) hσ.le
    have hy11 : y1 ≤ 1 := (div_le_one hσ).2 (by linarith)
    have hy20 : 0 ≤ y2 := div_nonneg (by linarith) hσ.le
    have hy21 : y2 ≤ 1 := (div_le_one hσ).2 (by linarith)
    have hσy1 : σ * y1 = u.re - c.re := by rw [hy1]; field_simp
    have hσy2 : σ * y2 = u.im - c.im := by rw [hy2]; field_simp
    have hlim : Tendsto (fun j => centreJ σ c u j) atTop (𝓝 u) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : Tendsto (fun j : ℕ => 2 * (σ * (1 / 2 : ℝ) ^ j)) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).const_mul σ |>.const_mul 2
      refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hb
      have f1 := (coord_facts hσ hy10 hy11 j).2.2.2.2.2.2
      have f2 := (coord_facts hσ hy20 hy21 j).2.2.2.2.2.2
      refine (norm_le_abs_re_add_abs_im _).trans ?_
      simp only [centreJ, sub_re, sub_im, re_aux, im_aux]
      rw [← hy1, ← hy2]
      have e1 : c.re + σ * (1 / 2) ^ j * ((nn y1 j : ℝ) + 1 / 2) - u.re =
          σ * (1 / 2) ^ j * ((nn y1 j : ℝ) + 1 / 2) - σ * y1 := by rw [hσy1]; ring
      have e2 : c.im + σ * (1 / 2) ^ j * ((nn y2 j : ℝ) + 1 / 2) - u.im =
          σ * (1 / 2) ^ j * ((nn y2 j : ℝ) + 1 / 2) - σ * y2 := by rw [hσy2]; ring
      rw [e1, e2]; linarith
    have hstep : ∀ j, Dg.internal (csq σ c) (centreJ σ c u j) (centreJ σ c u (j + 1)) ≤
        ENNReal.ofReal (B * ((1 / 2) ^ s) ^ j) := by
      intro j
      obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := coord_facts hσ hy10 hy11 j
      obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := coord_facts hσ hy20 hy21 j
      obtain ⟨n1, n1', n10, n11⟩ := nn_spec hy10 hy11 j
      obtain ⟨n2, n2', n20, n21⟩ := nn_spec hy20 hy21 j
      have hsub : osq (σ * (1 / 2) ^ j) (cornerJ σ c u j) ⊆ csq σ c := by
        intro x ⟨x1, x2, x3, x4⟩
        simp only [cornerJ, re_aux, im_aux] at x1 x2 x3 x4
        rw [← hy1] at x1 x2; rw [← hy2] at x3 x4
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      have hmem0 : centreJ σ c u j ∈ osq (σ * (1 / 2) ^ j) (cornerJ σ c u j) := by
        simp only [osq, centreJ, cornerJ, re_aux, im_aux, mem_setOf_eq]
        rw [← hy1, ← hy2]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      have hmem1 : centreJ σ c u (j + 1) ∈ osq (σ * (1 / 2) ^ j) (cornerJ σ c u j) := by
        simp only [osq, centreJ, cornerJ, re_aux, im_aux, mem_setOf_eq]
        rw [← hy1, ← hy2]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      calc Dg.internal (csq σ c) (centreJ σ c u j) (centreJ σ c u (j + 1))
          ≤ Dg.internal (osq (σ * (1 / 2) ^ j) (cornerJ σ c u j)) (centreJ σ c u j)
              (centreJ σ c u (j + 1)) := internal_anti Dg hsub _ _
        _ ≤ internalDiam Dg (osq (σ * (1 / 2) ^ j) (cornerJ σ c u j))
              (osq (σ * (1 / 2) ^ j) (cornerJ σ c u j)) := internal_le_internalDiam Dg hmem0 hmem1
        _ ≤ _ := hgood j _ _ (by rw [← hy1]; exact n10) (by rw [← hy1]; exact n11)
              (by rw [← hy2]; exact n20) (by rw [← hy2]; exact n21)
    have hfin : ∑' j : ℕ, ENNReal.ofReal (B * ((1 / 2) ^ s) ^ j) ≠ ∞ := by
      rw [tsum_ofReal_geom hB hr0 hr1]; exact ENNReal.ofReal_ne_top
    have := internalEDist_le_tsum_of_chain (Y := Dg.pt '' csq σ c)
      (x := fun j => Dg.pt (centreJ σ c u j)) (u := Dg.pt u) ⟨u, ⟨hu1, hu2, hu3, hu4⟩, rfl⟩
      (Dg.continuous_pt.continuousAt.tendsto.comp hlim) hfin hstep
    rw [tsum_ofReal_geom hB hr0 hr1] at this
    exact this
  have hc0 : ∀ u v : ℂ, centreJ σ c u 0 = centreJ σ c v 0 := by
    intro u v; simp [centreJ, nn]
  refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
  calc Dg.internal (csq σ c) u v ≤ Dg.internal (csq σ c) u (centreJ σ c u 0) +
        Dg.internal (csq σ c) (centreJ σ c u 0) v := MetricGeometry.internalEDist_triangle _ _ _ _
    _ ≤ M + M := by
        refine add_le_add ?_ ?_
        · rw [ContMetric.internal, MetricGeometry.internalEDist_comm]; exact key u hu
        · rw [hc0 u v]; exact key v hv
    _ = ENNReal.ofReal (2 * (B / (1 - (1 / 2) ^ s))) := by
        have h1 : 0 < 1 - ((1 : ℝ) / 2) ^ s := by linarith
        have h2 : 0 ≤ B / (1 - ((1 : ℝ) / 2) ^ s) := div_nonneg hB h1.le
        rw [hM, ← ENNReal.ofReal_add h2 h2, two_mul]

end L320
end LQGMetric.DFGPS
