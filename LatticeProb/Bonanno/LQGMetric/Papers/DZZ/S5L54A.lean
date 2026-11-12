/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Adapt

/-!
# DZZ Lemma 5.4, upper half (P2-DZZ54)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 5.4
(`lem-exponent-point-to-boundary`, l. 2299–2304), with `χ` from Lemma 5.3 (l. 2292–2297).

DZZ's proof (l. 2530–2578) only argues the lower bound; the upper bound
`limsup E log min_{x ∈ ∂𝕍_{u,λ}} D̄^{u,2λ}_δ(u,x) / log δ⁻¹ ≤ χ` is the immediate comparison with
one point-to-point tilde distance, which we spell out (own elementary argument, DEVIATIONS):
for `x₀ = u ± 1/40` (the sign keeping `x₀ ∈ 𝕍̄`), `x₀ ∈ ∂𝕍_{u,1/20}` and
`𝕍̃_{u,x₀} ⊆ 𝕍_{u,1/10}`, so `min_x D̄^{u,2λ}_δ(u,x) ≤ D̄^{u,2λ}_δ(u,x₀) ≤ D̃_δ(u,x₀)` (balls inside
the smaller box are admissible for the larger one: `dzzWall_anti`, `lgdDZZ_mono_measure`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The signed horizontal offset `±1/40` keeping `u ± 1/40` in `𝕍̄`. -/
def l54Off (u : ℂ) : ℝ := if u.re ≤ 1 / 2 then 1 / 40 else -(1 / 40)

/-- The comparison point `x₀ = u + l54Off u` on the vertical side of `∂𝕍_{u,1/20}`. -/
def l54Pt (u : ℂ) : ℂ := u + (l54Off u : ℂ)

lemma abs_l54Off (u : ℂ) : |l54Off u| = 1 / 40 := by
  unfold l54Off; split_ifs <;> norm_num [abs_of_pos]

lemma l54Pt_re (u : ℂ) : (l54Pt u).re = u.re + l54Off u := by simp [l54Pt]

lemma l54Pt_im (u : ℂ) : (l54Pt u).im = u.im := by simp [l54Pt]

lemma l54Pt_mem_dzzVbar {u : ℂ} (hu : u ∈ dzzVbar) : l54Pt u ∈ dzzVbar := by
  obtain ⟨h1, h2⟩ := near_of_mem_dzzVbar hu
  refine ⟨show |(l54Pt u).re - 1 / 2| ≤ 1 / 20 / 2 from ?_,
    show |(l54Pt u).im - 1 / 2| ≤ 1 / 20 / 2 from by rw [l54Pt_im]; linarith⟩
  rw [l54Pt_re]
  rw [abs_le] at h1 ⊢
  unfold l54Off; split_ifs with h <;> constructor <;> linarith

lemma l54Pt_ne {u : ℂ} : u ≠ l54Pt u := by
  intro h
  have := congrArg Complex.re h
  rw [l54Pt_re] at this
  have h0 := abs_l54Off u
  rw [show l54Off u = 0 by linarith, abs_zero] at h0
  norm_num at h0

lemma l54Pt_mem_frontier (u : ℂ) : l54Pt u ∈ frontier (sqBox u (1 / 20)) := by
  rw [frontier_sqBox (by norm_num)]
  have him : (l54Pt u).im ∈ Icc (u.im - 1 / 20 / 2) (u.im + 1 / 20 / 2) := by
    rw [l54Pt_im]; constructor <;> linarith
  by_cases h : u.re ≤ 1 / 2
  · right
    refine ⟨show (l54Pt u).re = u.re + 1 / 20 / 2 from ?_, him⟩
    rw [l54Pt_re, l54Off, if_pos h]; norm_num
  · left; left; right
    refine ⟨show (l54Pt u).re = u.re - 1 / 20 / 2 from ?_, him⟩
    rw [l54Pt_re, l54Off, if_neg h]; ring

lemma tildeBox_l54Pt_subset (u : ℂ) : tildeBox u (l54Pt u) ⊆ sqBox u (1 / 10) := by
  intro z ⟨h1, h2⟩
  have he := abs_l54Off u
  have hv : l54Pt u - u = (l54Off u : ℂ) := by simp [l54Pt]
  rw [hv, Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs, he] at h1 h2
  have hm : z - (u + l54Pt u) / 2 = z - u - (l54Off u / 2 : ℝ) := by
    simp only [l54Pt]; push_cast; ring
  rw [hm] at h1 h2
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, zero_add] at h1 h2
  rw [abs_mul, he] at h1 h2
  have h1' : |z.re - u.re - l54Off u / 2| ≤ 1 / 40 := by nlinarith [abs_nonneg (z.re - u.re - l54Off u / 2)]
  have h2' : |z.im - u.im| ≤ 1 / 40 := by nlinarith [abs_nonneg (z.im - u.im)]
  refine ⟨?_, by linarith⟩
  have := abs_sub_le (z.re - u.re) (l54Off u / 2) 0
  simp only [sub_zero, abs_div, he, abs_two] at this
  linarith

/-- Pointwise comparison: `log min_{x ∈ ∂𝕍_{u,1/20}} D̄_δ(u,x) ≤ log D̃_δ(u,x₀)` when
`D̃_δ(u,x₀) < ∞`. -/
lemma logMinLGD_bar_le_tilde (ν : Measure ℂ) (δ : ℝ) (u : ℂ)
    (hfin : lgdDZZ (dzzWall (tildeBox u (l54Pt u)) ν) δ u (l54Pt u) < ⊤) :
    logMinLGD (dzzWall (sqBox u (1 / 10)) ν) δ {u} (frontier (sqBox u (1 / 20))) ≤
      logMinLGD (dzzWall (tildeBox u (l54Pt u)) ν) δ {u} {l54Pt u} := by
  have hle : lgdMinSet (dzzWall (sqBox u (1 / 10)) ν) δ {u} (frontier (sqBox u (1 / 20))) ≤
      lgdMinSet (dzzWall (tildeBox u (l54Pt u)) ν) δ {u} {l54Pt u} := by
    rw [lgdMinSet_singleton]
    refine le_trans ?_ (lgdDZZ_mono_measure (dzzWall_anti (tildeBox_l54Pt_subset u) ν) δ u
      (l54Pt u))
    unfold lgdMinSet
    exact iInf₂_le_of_le u (mem_singleton u) (iInf₂_le (l54Pt u) (l54Pt_mem_frontier u))
  rw [← lgdMinSet_singleton] at hfin
  have h1 := one_le_lgdMinSet (dzzWall (sqBox u (1 / 10)) ν) δ {u} (frontier (sqBox u (1 / 20)))
  unfold logMinLGD
  have hm : (lgdMinSet (dzzWall (sqBox u (1 / 10)) ν) δ {u} (frontier (sqBox u (1 / 20)))).toNat
      ≤ (lgdMinSet (dzzWall (tildeBox u (l54Pt u)) ν) δ {u} {l54Pt u}).toNat :=
    ENat.toNat_le_toNat hle hfin.ne
  have hpos : (0 : ℝ) < (lgdMinSet (dzzWall (sqBox u (1 / 10)) ν) δ {u}
      (frontier (sqBox u (1 / 20)))).toNat := by
    have hne : lgdMinSet (dzzWall (sqBox u (1 / 10)) ν) δ {u} (frontier (sqBox u (1 / 20))) ≠ ⊤ :=
      (hle.trans_lt hfin).ne
    have : 1 ≤ (lgdMinSet (dzzWall (sqBox u (1 / 10)) ν) δ {u}
        (frontier (sqBox u (1 / 20)))).toNat := by
      rw [← ENat.natCast_le_natCast, ENat.natCast_toNat hne]; exact_mod_cast h1
    exact_mod_cast this
  exact Real.log_le_log hpos (by exact_mod_cast hm)

/-- **DZZ Lemma 5.4, upper half**: `limsup E log min_{x ∈ ∂𝕍_{u,1/20}} D̄^{u,1/10}_δ(u,x) /
log δ⁻¹ ≤ χ`, from Lemma 5.3, given that the tilde distances are a.s. finite and `log D̃_δ` is
integrable (both proved at `μIn` in `S5L53Side`: `ae_lgd_tilde_lt_top`, `integrable_log_tilde`). -/
theorem dzzLem54_upper {P : Measure Ω} {μ : Ω → Measure ℂ} {χ : ℝ} (hL : DZZLem53Exp P μ χ)
    (hfin : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ᵐ ω ∂P, lgdDZZ (dzzWall (tildeBox u v) (μ ω)) δ u v < ⊤)
    (hint : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Integrable (fun ω => logMinLGD (dzzWall (tildeBox u v) (μ ω)) δ {u} {v}) P)
    {u : ℂ} (hu : u ∈ dzzVbar) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∫ ω, logMinLGD (dzzWall (sqBox u (1 / 10)) (μ ω)) δ {u}
      (frontier (sqBox u (1 / 20))) ∂P) / Real.log δ⁻¹ < χ + ε := by
  have hv := l54Pt_mem_dzzVbar hu
  have hE := hL u hu (l54Pt u) hv l54Pt_ne (Iio_mem_nhds (by linarith : χ < χ + ε))
  filter_upwards [hE, hfin u hu _ hv l54Pt_ne, hint u hu _ hv l54Pt_ne,
    eventually_Ioo_nhdsGT one_pos] with δ hEδ hfδ hiδ hδ
  have hlog := log_inv_pos_of_mem hδ
  refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ hlog.le) hEδ
  refine integral_mono_of_nonneg (Eventually.of_forall fun ω => logMinLGD_nonneg _ _ _ _) hiδ ?_
  filter_upwards [hfδ] with ω hω
  exact logMinLGD_bar_le_tilde (μ ω) δ u hω

end DZZ
end LQGMetric
