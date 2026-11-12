/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S6.Prop61RestDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.Prop61Det
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedP36Conf
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L4_5Det

/-!
# GM Proposition 6.1, Steps 2–4 on a fixed sample (task P2-M2O2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Prop 6.1, l. 3601–3643.

* `p61_exists_grid_near`: every `z` is within `s` of `sℤ²` (GM Step 3, l. 3628);
* `p61_geod_sub_at_dist`: along a geodesic, a pair `P(s), P(t)` with `|P(s) − P(t)| ≥ x` contains
  a pair `P(s), P(t')` at Euclidean distance exactly `x` and with smaller `D`-distance (used to
  apply the Hölder lower bound (6.3) at scale `x ≤ ε''𝕣`; GM apply (6.3) to `P(s), P(t)` directly
  in (6.2), l. 3613, which needs `|P(s) − P(t)|` in the range of (6.3));
* `p61_det`: GM Steps 2–4 on a fixed sample: the Step 1 conclusion (6.1) on the grid, the
  geodesic confinement (l. 3605), the Hölder bounds (6.3) (in the form of DFGPS Prop 3.18) and the
  diameter bound of Step 4 give `D̃(z,w) < (C_* − δ) D(z,w)` for `z, w ∈ B_𝕣(0)` with
  `|z − w| ≥ β̄𝕣`, for every `δ < (C_* − c₂')(bε^{1+ν}ρ⁻¹)^{χ'}/(2S)`.
  Step 4 uses `D_h(z,w) ≤ S 𝔠_𝕣 e^{ξh_𝕣(0)}` (GM.S2.4c) in place of GM's `𝔠_𝕣e^{ξh_𝕣(0)} ε^{-χ'}`
  (l. 3644); the grid pair is required to satisfy `|𝕫 − 𝕨| ≥ β̄𝕣/2` instead of `β̄𝕣` (l. 3628).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- every point is within `s` of the grid `sℤ²` -/
theorem p61_exists_grid_near {s : ℝ} (hs : 0 < s) (z : ℂ) :
    ∃ a ∈ gridPts s, ‖z - a‖ ≤ s := by
  refine ⟨(s : ℂ) * ((round (z.re / s) : ℤ) + (round (z.im / s) : ℤ) * Complex.I),
    ⟨(round (z.re / s), round (z.im / s)), rfl⟩, ?_⟩
  set a : ℂ := (s : ℂ) * ((round (z.re / s) : ℤ) + (round (z.im / s) : ℤ) * Complex.I)
  have hre : (z - a).re = s * (z.re / s - round (z.re / s)) := by
    simp only [a, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    field_simp; ring
  have him : (z - a).im = s * (z.im / s - round (z.im / s)) := by
    simp only [a, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    field_simp; ring
  have h1 : |(z - a).re| ≤ s / 2 := by
    rw [hre, abs_mul, abs_of_pos hs]
    have := abs_sub_round (z.re / s); nlinarith
  have h2 : |(z - a).im| ≤ s / 2 := by
    rw [him, abs_mul, abs_of_pos hs]
    have := abs_sub_round (z.im / s); nlinarith
  have := Complex.norm_le_abs_re_add_abs_im (z - a)
  linarith

/-- `|D(a,b) − D(a',b')| ≤ D(a,a') + D(b,b')` -/
theorem p61_abs_dist_sub_le (d : ContMetric) (a b a' b' : ℂ) :
    |d.1 (a, b) - d.1 (a', b')| ≤ d.1 (a', a) + d.1 (b', b) := by
  have t1 := d.2.triangle a a' b
  have t2 := d.2.triangle a' b' b
  have t3 := d.2.triangle a' a b'
  have t4 := d.2.triangle a b b'
  have s1 := d.2.symm a a'
  have s2 := d.2.symm b b'
  rw [abs_le]; constructor <;> linarith

/-- `u ∈ 𝕣 B̄_ρ(0)` when `|u| ≤ 𝕣ρ` -/
theorem p61_mem_scaleSet {R r : ℝ} (hR : 0 < R) {u : ℂ} (hu : ‖u‖ ≤ R * r) :
    u ∈ scaleSet R 0 (closedBall 0 r) := by
  refine ⟨u / R, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
      div_le_iff₀ hR]
    linarith
  · have : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
    simp only [add_zero]; field_simp

theorem p61_norm_div {R : ℝ} (hR : 0 < R) (u : ℂ) : ‖u / R‖ = ‖u‖ / R := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]

/-- along a geodesic, from `|P(s) − P(t)| ≥ x` to a time `t'` with `|P(s) − P(t')| = x` and
`D(P(s),P(t')) ≤ D(P(s),P(t))` (intermediate value theorem) -/
theorem p61_geod_sub_at_dist {d : ContMetric} {a b : ℂ} {P : C(unitInterval, ℂ)}
    (hP : IsGeod01 d a b P) {s t : unitInterval} (hst : s < t) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ ‖P s - P t‖) :
    ∃ t' : unitInterval, ‖P s - P t'‖ = x ∧ d.1 (P s, P t') ≤ d.1 (P s, P t) := by
  set g : ℝ → ℝ := fun τ => ‖P s - P (pj τ)‖ with hg
  have hgc : Continuous g :=
    (continuous_const.sub (P.continuous.comp (continuous_projIcc (h := zero_le_one)))).norm
  have hpj : ∀ u : unitInterval, pj (u : ℝ) = u := fun u => by rw [pj_eq_of_mem u.2]
  have hst' : (s : ℝ) ≤ t := le_of_lt hst
  obtain ⟨τ, hτ, hgτ⟩ := intermediate_value_Icc hst' hgc.continuousOn
    (show x ∈ Icc (g s) (g t) by
      simp only [hg, hpj, sub_self, norm_zero]; exact ⟨hx0, hx⟩)
  refine ⟨pj τ, hgτ, ?_⟩
  have hτ1 : τ ∈ Icc (0 : ℝ) 1 := ⟨s.2.1.trans hτ.1, hτ.2.trans t.2.2⟩
  rw [hP.2.2, hP.2.2, pj_coe_of_mem hτ1]
  refine mul_le_mul_of_nonneg_right ?_ (ContMetric.nonneg d a b)
  rw [abs_of_nonneg (sub_nonneg.2 hτ.1), abs_of_nonneg (sub_nonneg.2 hst')]
  linarith [hτ.2]

/-- **GM Prop 6.1, Steps 2–4 on a fixed sample** (l. 3601–3650) -/
theorem p61_det {d d' : ContMetric} {Cs c₂ Kb sf S R R₂ ε q ρ ν bb βb χ χ' ε'' δ : ℝ}
    (hup : ∀ u v, d'.1 (u, v) ≤ Cs * d.1 (u, v))
    (hbl : ∀ u v, d'.1 (u, v) ≤ Kb * d.1 (u, v))
    (hR : 0 < R) (hR₂ : 1 < R₂) (hsf : 0 < sf) (hS : 0 < S) (hc₂ : c₂ < Cs)
    (hβb1 : βb < 1) (hχ : 0 < χ)
    (hX0 : 0 ≤ bb * ε ^ (1 + ν) * ρ⁻¹) (hY0 : 0 < ε ^ q * ρ⁻¹)
    (hstep1 : ∀ a b : ℂ, a ∈ gridPts (ε ^ q * ρ⁻¹ * R) → b ∈ gridPts (ε ^ q * ρ⁻¹ * R) →
      a ∈ ball (0 : ℂ) (2 * R) → b ∈ ball (0 : ℂ) (2 * R) → βb / 2 * R ≤ ‖a - b‖ →
      ∃ P' : C(unitInterval, ℂ), IsGeod01 d a b P' ∧ ∃ s t : unitInterval, s < t ∧
        bb * ε ^ (1 + ν) * ρ⁻¹ * R ≤ ‖P' s - P' t‖ ∧ d'.1 (P' s, P' t) ≤ c₂ * d.1 (P' s, P' t))
    (hconf : d ∈ confSet (2 * R) R₂)
    (hhol : ∀ u ∈ scaleSet R 0 (closedBall 0 (2 * R₂)), ∀ v ∈ scaleSet R 0 (closedBall 0 (2 * R₂)),
      ‖u - v‖ ≤ ε'' * R →
        ‖(u - v) / R‖ ^ χ' ≤ sf⁻¹ * d.1 (u, v) ∧ sf⁻¹ * d.1 (u, v) ≤ ‖(u - v) / R‖ ^ χ)
    (hdiam : internalDiam d (scaleSet R 0 (closedBall 0 1)) (scaleSet R 0 (ball 0 2)) ≤
      ENNReal.ofReal (S * sf))
    (hXε : bb * ε ^ (1 + ν) * ρ⁻¹ ≤ ε'') (hYε : ε ^ q * ρ⁻¹ ≤ ε'')
    (hgrid : 2 * (ε ^ q * ρ⁻¹) ≤ βb / 2)
    (herr : (Cs + Kb) * 2 * (ε ^ q * ρ⁻¹) ^ χ ≤ (Cs - c₂) * (bb * ε ^ (1 + ν) * ρ⁻¹) ^ χ' / 2)
    (hδ : δ < (Cs - c₂) * (bb * ε ^ (1 + ν) * ρ⁻¹) ^ χ' / (2 * S)) :
    ∀ z ∈ ball (0 : ℂ) R, ∀ w ∈ ball (0 : ℂ) R, βb * R ≤ ‖z - w‖ →
      d'.1 (z, w) < (Cs - δ) * d.1 (z, w) := by
  intro z hz w hw hzw
  have hz' := mem_ball_zero_iff.1 hz
  have hw' := mem_ball_zero_iff.1 hw
  set Y := ε ^ q * ρ⁻¹ with hYdef
  set X := bb * ε ^ (1 + ν) * ρ⁻¹ with hXdef
  have h01 : (0 : ℂ) ≠ 1 := zero_ne_one
  have hd01 := pos_of_ne d h01
  have hCs : 0 ≤ Cs := by
    have := (ContMetric.nonneg d' 0 1).trans (hup 0 1)
    exact nonneg_of_mul_nonneg_left this hd01
  have hKb : 0 ≤ Kb := by
    have := (ContMetric.nonneg d' 0 1).trans (hbl 0 1)
    exact nonneg_of_mul_nonneg_left this hd01
  have hYR : 0 < Y * R := mul_pos hY0 hR
  have hY4 : Y ≤ 1 / 4 := by linarith
  have hRR : 2 * R ≤ R * (2 * R₂) := by
    have : 0 ≤ R * (R₂ - 1) := mul_nonneg hR.le (by linarith)
    linarith
  have hYR4 : Y * R ≤ R / 4 := by
    have := mul_le_mul_of_nonneg_right hY4 hR.le; linarith
  have hgR : 2 * (Y * R) ≤ βb / 2 * R := by
    have := mul_le_mul_of_nonneg_right hgrid hR.le; linarith
  have hRK : ∀ u : ℂ, ‖u‖ < 2 * R → u ∈ scaleSet R 0 (closedBall 0 (2 * R₂)) := fun u hu =>
    p61_mem_scaleSet hR (by linarith)
  -- the Hölder upper bound at scale `Y𝕣`
  have hU : ∀ u v : ℂ, ‖u‖ < 2 * R → ‖v‖ < 2 * R → ‖u - v‖ ≤ Y * R →
      d.1 (u, v) ≤ sf * Y ^ χ := by
    intro u v hu hv huv
    have h1 := (hhol u (hRK u hu) v (hRK v hv) (huv.trans (mul_le_mul_of_nonneg_right hYε hR.le))).2
    have h2 : ‖(u - v) / R‖ ^ χ ≤ Y ^ χ := by
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ hχ.le
      rw [p61_norm_div hR, div_le_iff₀ hR]; exact huv
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hsf.le
    rwa [← mul_assoc, mul_inv_cancel₀ hsf.ne', one_mul] at h3
  -- grid points (GM Step 3, l. 3628)
  obtain ⟨a, ha, hza⟩ := p61_exists_grid_near hYR z
  obtain ⟨b, hb, hwb⟩ := p61_exists_grid_near hYR w
  have hna : ‖a‖ < 2 * R := by
    have := norm_sub_le z (z - a); rw [sub_sub_cancel] at this; linarith
  have hnb : ‖b‖ < 2 * R := by
    have := norm_sub_le w (w - b); rw [sub_sub_cancel] at this; linarith
  have hab : βb / 2 * R ≤ ‖a - b‖ := by
    have e : z - w = (z - a) + (a - b) - (w - b) := by ring
    have := norm_sub_le ((z - a) + (a - b)) (w - b)
    have := norm_add_le (z - a) (a - b)
    rw [← e] at *
    linarith
  obtain ⟨P', hP', s, t, hst, hdist, hc⟩ :=
    hstep1 a b ha hb (mem_ball_zero_iff.2 hna) (mem_ball_zero_iff.2 hnb) hab
  -- Step 2: the lower bound (6.2) on `D(P(s), P(t))`
  obtain ⟨t', ht'x, ht'le⟩ := p61_geod_sub_at_dist hP' hst (mul_nonneg hX0 hR.le) hdist
  have hrange := range_subset_of_confSet hR₂ hconf (mem_ball_zero_iff.2 hna)
    (mem_ball_zero_iff.2 hnb) hP'
  have hmem : ∀ τ, P' τ ∈ scaleSet R 0 (closedBall 0 (2 * R₂)) := fun τ => by
    have := mem_closedBall_zero_iff.1 (hrange ⟨τ, rfl⟩)
    exact p61_mem_scaleSet hR (by rw [show R * (2 * R₂) = R₂ * (2 * R) by ring]; exact this)
  have hlow : sf * X ^ χ' ≤ d.1 (P' s, P' t) := by
    have h1 := (hhol _ (hmem s) _ (hmem t') (by rw [ht'x]; exact mul_le_mul_of_nonneg_right hXε hR.le)).1
    rw [p61_norm_div hR, ht'x, mul_div_assoc, div_self hR.ne', mul_one] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hsf.le
    rw [← mul_assoc, mul_inv_cancel₀ hsf.ne', one_mul] at h3
    exact h3.trans ht'le
  -- (6.4)
  have hsep := away_sep hP' hup hst.le hc
  set A := (Cs - c₂) * (sf * X ^ χ') with hA
  have hsep' : d'.1 (a, b) ≤ Cs * d.1 (a, b) - A := by
    have := mul_le_mul_of_nonneg_left hlow (sub_nonneg.2 hc₂.le); linarith
  -- (6.5): errors between the grid pair and `(z, w)`
  have hza' : d.1 (a, z) ≤ sf * Y ^ χ := by
    rw [d.2.symm]; exact hU z a (by linarith) hna hza
  have hwb' : d.1 (b, w) ≤ sf * Y ^ χ := by
    rw [d.2.symm]; exact hU w b (by linarith) hnb hwb
  have hy : |d.1 (a, b) - d.1 (z, w)| ≤ 2 * (sf * Y ^ χ) := by
    have := p61_abs_dist_sub_le d a b z w
    rw [d.2.symm z a, d.2.symm w b] at this; linarith
  have hy' : |d'.1 (a, b) - d'.1 (z, w)| ≤ Kb * (2 * (sf * Y ^ χ)) := by
    have := p61_abs_dist_sub_le d' a b z w
    have e1 := hbl z a; have e2 := hbl w b
    rw [d.2.symm z a, d'.2.symm z a] at e1
    rw [d.2.symm w b, d'.2.symm w b] at e2
    rw [d'.2.symm z a, d'.2.symm w b] at this
    have : Kb * d.1 (a, z) + Kb * d.1 (b, w) ≤ Kb * (2 * (sf * Y ^ χ)) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hKb
    linarith
  have herr' : Cs * (2 * (sf * Y ^ χ)) + Kb * (2 * (sf * Y ^ χ)) ≤ A / 2 := by
    calc Cs * (2 * (sf * Y ^ χ)) + Kb * (2 * (sf * Y ^ χ))
        = ((Cs + Kb) * 2 * Y ^ χ) * sf := by ring
      _ ≤ ((Cs - c₂) * X ^ χ' / 2) * sf := mul_le_mul_of_nonneg_right herr hsf.le
      _ = A / 2 := by rw [hA]; ring
  -- Step 4: the diameter bound
  have hxM : d.1 (z, w) ≤ S * sf := by
    have hzK : z ∈ scaleSet R 0 (closedBall 0 1) :=
      p61_mem_scaleSet hR (by rw [mul_one]; exact hz'.le)
    have hwK : w ∈ scaleSet R 0 (closedBall 0 1) :=
      p61_mem_scaleSet hR (by rw [mul_one]; exact hw'.le)
    have h2 : d.internal (scaleSet R 0 (ball 0 2)) z w ≤
        internalDiam d (scaleSet R 0 (closedBall 0 1)) (scaleSet R 0 (ball 0 2)) := by
      unfold internalDiam
      exact le_iSup₂_of_le z hzK (le_iSup₂_of_le w hwK le_rfl)
    have h1 := ((DFGPS.L45.ofReal_le_internal d (scaleSet R 0 (ball 0 2)) z w).trans h2).trans
      hdiam
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hM : 0 < S * sf := mul_pos hS hsf
  have hfin := away_transfer hCs hM hsep' hy hy' herr' hxM
  have hAM : A / (2 * (S * sf)) = (Cs - c₂) * X ^ χ' / (2 * S) := by
    rw [hA]; field_simp
  rw [hAM] at hfin
  have hzw0 : z ≠ w := by
    intro h
    have h0 : ‖z - w‖ = 0 := by rw [sub_eq_zero.2 h, norm_zero]
    linarith
  have hdzw := pos_of_ne d hzw0
  calc d'.1 (z, w) ≤ (Cs - (Cs - c₂) * X ^ χ' / (2 * S)) * d.1 (z, w) := hfin
    _ < (Cs - δ) * d.1 (z, w) := mul_lt_mul_of_pos_right (by linarith) hdzw

end LQGMetric.GM
