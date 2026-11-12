/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_22 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20Ball
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightE
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.22 (`lem-holder-inverse`) from Lemma 3.21 (task P2-DFA7)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 3.22 (T:2367–2373) in the
corrected form `Blueprint.DFGPSLem3_22` (`u, v ∈ 𝕣K`, `|u − v| ≤ ε𝕣`, BP-M2-3) and its proof
(T:2375–2377): a union bound over `z ∈ B_{ε𝕣}(K) ∩ (2^{-k-2}ε𝕣ℤ²)` and `k ∈ ℕ₀`. The proof
printed in T cites "(eqn-ep-diam), applied with `s = χ′`"; the estimate that gives a lower bound
for `D_h` is Lemma 3.21 (`eqn-ep-cross`), which was proved just before for this purpose
(T:2333 "plays a role analogous to Lemma 3.19") and whose condition `s > ξQ` matches; we use it,
with `s = (ξ(Q+2) + χ′)/2` (so that its exponent `(s − ξQ)²/(2ξ²)` exceeds `2`, and `s < χ′`
absorbs the constant of the scale choice for small `ε`).

Geometry (own elementary choice, DFA7-1 as in `L3_20.lean`): scale `t_k = ε(3/4)^k` with
`15|u−v|/41 < t_k𝕣 ≤ 20|u−v|/41`, `z` the grid point of mesh `t_k𝕣/40` nearest `u`; then
`u ∈ B_{t_k𝕣}(z)` and `|v − z| ≥ 2t_k𝕣`, and in the length metric `D_h` (Axiom I, a.s.) every
path from `u` to `v` crosses from `∂B_{|u−z|}(z)` to `∂B_{2t_k𝕣}(z)` (`GM.Tight.le_of_forall_crossing`),
so `D_h(u,v) ≥ D_h(B_{t_k𝕣}(z), ∂B_{2t_k𝕣}(z)) ≥ t_k^s 𝔠_𝕣 e^{ξh_𝕣(0)}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L322

open Blueprint LQGDimension.LFPPRecords L320

/-- deterministic part of Lemma 3.22 -/
theorem cross_det (Dg : ContMetric) (hlen : Dg.IsLength) {F 𝕣 ε s χ' R : ℝ} (hF : 0 < F)
    (h𝕣 : 0 < 𝕣) (hε0 : 0 < ε) (hs : 0 < s) (hsχ : s < χ')
    (hεs : ε ^ (χ' - s) ≤ (15 / 41 : ℝ) ^ s) {u v : ℂ} (hd : ‖u - v‖ ≤ ε * 𝕣)
    (hu : ‖u‖ + ε * 𝕣 ≤ R * 𝕣)
    (hgood : ∀ (k : ℕ) (a : ℤ × ℤ), a ∈ gridSel ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) (R * 𝕣) →
      ENNReal.ofReal ((ε * (3 / 4) ^ k) ^ s * F) ≤
        setDist Dg (Metric.ball (gridPt ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) a)
          ((ε * (3 / 4) ^ k) * 𝕣))
        (Metric.sphere (gridPt ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) a) (2 * (ε * (3 / 4) ^ k) * 𝕣))) :
    ‖(u - v) / 𝕣‖ ^ χ' ≤ F⁻¹ * Dg.1 (u, v) := by
  have hχ' : 0 < χ' := hs.trans hsχ
  rcases eq_or_ne u v with rfl | huv
  · rw [sub_self, zero_div, norm_zero, Real.zero_rpow hχ'.ne']
    exact mul_nonneg (inv_nonneg.2 hF.le) (ContMetric.nonneg Dg _ _)
  set d := ‖u - v‖ with hd_def
  have hd0 : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 huv)
  obtain ⟨k, hk1, hk2⟩ := exists_scale hε0 h𝕣 hd0 hd (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num) (by norm_num : (0 : ℝ) < 20 / 41) (by norm_num)
  set t := ε * (3 / 4 : ℝ) ^ k with ht
  have ht0 : 0 < t := by positivity
  set m := (1 / 40) * t * 𝕣 with hm
  have hm0 : 0 < m := by positivity
  set a := gridIdx m u with ha
  set z := gridPt m a with hz
  have huz : ‖u - z‖ ≤ 2 * m := norm_sub_gridPt_le hm0 u
  have hvz : 2 * t * 𝕣 ≤ ‖v - z‖ := by
    have : d ≤ ‖v - z‖ + ‖u - z‖ := by
      rw [hd_def, norm_sub_rev u v]
      calc ‖v - u‖ ≤ ‖v - z‖ + ‖z - u‖ := norm_sub_le_norm_sub_add_norm_sub v z u
        _ = ‖v - z‖ + ‖u - z‖ := by rw [norm_sub_rev z u]
    rw [hm] at huz; nlinarith
  have hzR : a ∈ gridSel m (R * 𝕣) := by
    show ‖z‖ ≤ R * 𝕣
    calc ‖z‖ ≤ ‖u‖ + ‖u - z‖ := by
          calc ‖z‖ = ‖u - (u - z)‖ := by ring_nf
            _ ≤ ‖u‖ + ‖u - z‖ := norm_sub_le _ _
      _ ≤ R * 𝕣 := by rw [hm] at huz; nlinarith
  have hg := hgood k a hzR
  have hcross : t ^ s * F ≤ Dg.1 (u, v) := by
    refine GM.Tight.le_of_forall_crossing hlen (a := ‖u - z‖) (b := 2 * t * 𝕣) ?_ le_rfl hvz ?_
    · rw [hm] at huz; nlinarith
    intro u' hu' v' hv'
    have hu'b : u' ∈ Metric.ball z (t * 𝕣) := by
      rw [Metric.mem_ball, dist_eq_norm, mem_sphere_iff_norm.1 hu']; rw [hm] at huz; nlinarith
    have h1 : setDist Dg (Metric.ball z (t * 𝕣)) (Metric.sphere z (2 * t * 𝕣)) ≤
        ENNReal.ofReal (Dg.1 (u', v')) := by
      rw [← ContMetric.edist_pt]
      exact MetricGeometry.setEDist_le_edist ⟨u', hu'b, rfl⟩ ⟨v', hv', rfl⟩
    exact (ENNReal.ofReal_le_ofReal_iff (ContMetric.nonneg Dg _ _)).1 (hg.trans h1)
  -- compare `t^s` with `|(u−v)/𝕣|^{χ'}`
  set x := ‖(u - v) / 𝕣‖ with hx
  have hxd : x = d / 𝕣 := by
    rw [hx, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣]
  have hx0 : 0 < x := by rw [hxd]; positivity
  have hxε : x ≤ ε := by rw [hxd, div_le_iff₀ h𝕣]; exact hd
  have htx : 15 / 41 * x ≤ t := by
    rw [hxd]; rw [le_iff_lt_or_eq]; left
    rw [mul_div_assoc', div_lt_iff₀ h𝕣]; nlinarith
  have hpow : x ^ χ' ≤ t ^ s := by
    calc x ^ χ' = x ^ s * x ^ (χ' - s) := by
          rw [← Real.rpow_add hx0]; ring_nf
      _ ≤ x ^ s * (15 / 41 : ℝ) ^ s := by
          gcongr
          exact (Real.rpow_le_rpow hx0.le hxε (by linarith)).trans hεs
      _ = (15 / 41 * x) ^ s := by
          rw [Real.mul_rpow (by norm_num) hx0.le]; ring
      _ ≤ t ^ s := Real.rpow_le_rpow (by positivity) htx hs.le
  calc x ^ χ' ≤ t ^ s := hpow
    _ = F⁻¹ * (t ^ s * F) := by field_simp
    _ ≤ F⁻¹ * Dg.1 (u, v) := mul_le_mul_of_nonneg_left hcross (inv_nonneg.2 hF.le)

end L322
end LQGMetric.DFGPS
