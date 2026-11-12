/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Walls0 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Glue
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P317E

/-!
# The "probability → 1" glue for the walled P3.17 restricted to pairs inside `K^ξ` (P-317K-ADAPT)

Decision DEC-123 §2 (finding 1 of P2-DZZ317K): consumers of the walled DZZ Proposition 3.17
(DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, Prop 3.17 l. 1505–1517, Remark 5.2 l. 2281–2284) take
`DZZProp317In P (fun ω => dzzWall K (μ ω)) K ξ` (pairs in `kXi K ξ`), never the walled
`DZZProp317` (false for pairs touching `Kᶜ`).

* `mem_kXi_of_ball_subset`: a point whose `r`-ball lies in
  `K` (with `Kᶜ ≠ ∅`) is in `K^r`.
* **`dzz_lgd_upper_whpIn'`**, **`dzz_lgd_upper_whpIn`**: copies of
  `dzz_lgd_upper_whp'`, `dzz_lgd_upper_whp` (S5Glue, P2-DZZ56) taking
  `DZZProp317In` and the membership of the pair in `K^ξ`; the proofs are those of S5Glue
  (they use the concentration only at the given pair).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

lemma mem_kXi_of_ball_subset {K : Set ℂ} {z : ℂ} {r : ℝ} (hne : (Kᶜ).Nonempty)
    (hb : Metric.ball z r ⊆ K) : z ∈ kXi K r := by
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  by_contra hlt
  push Not at hlt
  exact hy (hb (Metric.mem_ball'.mpr hlt))

/-- `dzz_lgd_upper_whp'` (S5Glue) for `DZZProp317In`, pairs inside `K^ξ`. -/
theorem dzz_lgd_upper_whpIn' {P : Measure Ω} {μ : Ω → Measure ℂ} {K : Set ℂ} {ξ χ : ℝ}
    (h317 : DZZProp317In P μ K ξ) {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hin : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi K ξ ∧ B δ ⊆ kXi K ξ)
    (hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫ ω, logMinLGD (μ ω) δ (A δ) (B δ) ∂P) / Real.log δ⁻¹ < χ + ε)
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, lgdMinSet (μ ω) δ (A δ) (B δ) < ⊤)
    {ι : ℝ} (hι : 0 < ι) :
    Tendsto (fun δ => P {ω | ¬ ((lgdMinSet (μ ω) δ (A δ) (B δ) : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-(χ + ι)))}) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨c, hc, h⟩ := h317
  have hX := tendsto_prob_gt_of_conc' hc (fun ι hι => (h A B hAB hin).1 ι hι) hup hι
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hX
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hfin, self_mem_nhdsWithin] with δ hfδ hδ
  have hnull : P {ω | ¬ lgdMinSet (μ ω) δ (A δ) (B δ) < ⊤} = 0 := ae_iff.mp hfδ
  calc _ ≤ P ({ω | (χ + ι) * Real.log δ⁻¹ < logMinLGD (μ ω) δ (A δ) (B δ)} ∪
        {ω | ¬ lgdMinSet (μ ω) δ (A δ) (B δ) < ⊤}) := measure_mono (fun ω hω => ?_)
    _ ≤ _ + _ := measure_union_le _ _
    _ = _ := by rw [hnull, add_zero]
  by_cases htop : lgdMinSet (μ ω) δ (A δ) (B δ) < ⊤
  · left
    simp only [mem_setOf_eq] at hω ⊢
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop.ne
    have h1 := one_le_lgdMinSet (μ ω) δ (A δ) (B δ)
    rw [← hn] at h1 hω
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
    by_contra hle
    rw [not_lt] at hle
    apply hω
    have hlog : Real.log n ≤ (χ + ι) * Real.log δ⁻¹ := by
      unfold logMinLGD at hle; rw [← hn] at hle; simpa using hle
    have : (n : ℝ) ≤ δ ^ (-(χ + ι)) := by
      rw [← exp_mul_log_inv (mem_Ioi.mp hδ), ← Real.exp_log (by linarith : (0 : ℝ) < n)]
      exact Real.exp_le_exp.mpr hlog
    rw [show (((n : ℕ∞) : ℝ≥0∞)) = ENNReal.ofReal n by simp]
    exact ENNReal.ofReal_le_ofReal this
  · right; exact htop

/-- `dzz_lgd_upper_whp` (S5Glue) for `DZZProp317In`, pairs inside `K^ξ`. -/
theorem dzz_lgd_upper_whpIn {P : Measure Ω} {μ : Ω → Measure ℂ} {K : Set ℂ} {ξ χ : ℝ}
    (h317 : DZZProp317In P μ K ξ) {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hin : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi K ξ ∧ B δ ⊆ kXi K ξ)
    (hexp : Tendsto (fun δ => (∫ ω, logMinLGD (μ ω) δ (A δ) (B δ) ∂P) / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 χ))
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, lgdMinSet (μ ω) δ (A δ) (B δ) < ⊤)
    {ι : ℝ} (hι : 0 < ι) :
    Tendsto (fun δ => P {ω | ¬ ((lgdMinSet (μ ω) δ (A δ) (B δ) : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-(χ + ι)))}) (𝓝[>] 0) (𝓝 0) :=
  dzz_lgd_upper_whpIn' h317 hAB hin (fun ε hε => hexp (Iio_mem_nhds (by linarith))) hfin hι

end DZZ
end LQGMetric
