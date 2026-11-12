/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_19Fin2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19Fin
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20Ball

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.19 (ball part): Chebyshev and the change of normalization

DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 3.19,
T:2290–2298.

* `norm_change`: the last step of T:2297–2298 ("The random variables `h_𝕣(z) − h_𝕣(0)` for
  `z ∈ 𝕣K` are Gaussian with variance bounded above by a constant depending only on `K`.
  Consequently, we can apply the Gaussian tail bound"), at the cost of `ε^δ` in the threshold.
* `gauss_small`, `exp_small`: elementary limits (own elementary proofs).
* `lem3_19U_of`: **Lemma 3.19 (`eqn-ep-diam`)** from Prop 3.9 and Theorem 1.5 (`DFGPSScaling`):
  (3.31) (`moment_eps`) with `ρ = 2ε𝕣`, `r = 𝕣`, Chebyshev with `p = (ξQ − s)/ξ²` (T:2292–2296).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L319

/-- `2 e^{−κ (log ε)²} ≤ ε^A / 2` for small `ε` (own elementary proof) -/
lemma gauss_small {κ : ℝ} (hκ : 0 < κ) (A : ℝ) : ∃ ε₃ : ℝ, 0 < ε₃ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₃ →
    2 * Real.exp (-κ * Real.log ε ^ 2) ≤ ε ^ A / 2 := by
  set T₀ := max 1 ((|A| + 3) / κ)
  refine ⟨Real.exp (-T₀), Real.exp_pos _, fun ε hε hε₃ => ?_⟩
  have hl : Real.log ε < -T₀ := by
    rw [← Real.log_exp (-T₀)]; exact Real.log_lt_log hε hε₃
  set T := -Real.log ε with hT
  have hT1 : 1 ≤ T := by linarith [le_max_left 1 ((|A| + 3) / κ)]
  have hT2 : (|A| + 3) / κ ≤ T := by linarith [le_max_right 1 ((|A| + 3) / κ)]
  have hT3 : |A| + 3 ≤ κ * T := by rwa [div_le_iff₀ hκ, mul_comm] at hT2
  have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)]
  rw [Real.rpow_def_of_pos hε]
  have key : Real.log 4 + -κ * Real.log ε ^ 2 ≤ Real.log ε * A := by
    have e1 : Real.log ε ^ 2 = T * T := by rw [hT]; ring
    have e2 : Real.log ε * A = -(T * A) := by rw [hT]; ring
    rw [e1, e2]
    have hA : T * A ≤ T * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) (by linarith)
    nlinarith
  have := Real.exp_le_exp.2 key
  rw [Real.exp_add, Real.exp_log (by norm_num)] at this
  linarith

/-- `M e^{η log ε} ≤ 1/2` for small `ε` (own elementary proof) -/
lemma exp_small (M : ℝ) {η : ℝ} (hη : 0 < η) : ∃ ε₄ : ℝ, 0 < ε₄ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₄ →
    M * Real.exp (Real.log ε * η) ≤ 1 / 2 := by
  set L := Real.log (2 * |M| + 1) / η
  refine ⟨Real.exp (-L), Real.exp_pos _, fun ε hε hε₄ => ?_⟩
  have hl : Real.log ε < -L := by
    rw [← Real.log_exp (-L)]; exact Real.log_lt_log hε hε₄
  have h1 : Real.log ε * η < -Real.log (2 * |M| + 1) := by
    have : L * η = Real.log (2 * |M| + 1) := by simp only [L]; field_simp
    nlinarith
  have h2 : Real.exp (Real.log ε * η) < (2 * |M| + 1)⁻¹ := by
    rw [← Real.exp_log (show (0:ℝ) < (2 * |M| + 1)⁻¹ by positivity), Real.log_inv]
    exact Real.exp_lt_exp.2 h1
  have hM : M ≤ |M| := le_abs_self M
  have hpos : 0 < Real.exp (Real.log ε * η) := Real.exp_pos _
  have : |M| * (2 * |M| + 1)⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith [abs_nonneg M]
  calc M * Real.exp (Real.log ε * η) ≤ |M| * Real.exp (Real.log ε * η) :=
        mul_le_mul_of_nonneg_right hM hpos.le
    _ ≤ |M| * (2 * |M| + 1)⁻¹ := mul_le_mul_of_nonneg_left h2.le (abs_nonneg M)
    _ ≤ 1 / 2 := this

/-- **T:2297–2298**: replacing `h_𝕣(z)` by `h_𝕣(0)` in the normalization, at the cost of a factor
`ε^δ` and the Gaussian tail of `h_𝕣(z) − h_𝕣(0)` (variance `≤ 2 log(R+1)` for `‖z‖ ≤ R𝕣`). -/
theorem norm_change {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {ξ : ℝ} (hξ : 0 < ξ) {c : ℝ → ℝ} {𝕣 R : ℝ}
    (h𝕣 : 0 < 𝕣) (hc : 0 < c 𝕣) (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R * 𝕣) {ε s δ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (F : Ω → ℝ≥0∞) :
    P {ω | ¬ F ω ≤ ENNReal.ofReal (ε ^ s * scaleFac ξ c (h ω) 𝕣 0)} ≤
      P {ω | ENNReal.ofReal (ε ^ (s + δ)) ≤ ENNReal.ofReal (scaleFac ξ c (h ω) 𝕣 z)⁻¹ * F ω} +
        ENNReal.ofReal (2 * Real.exp (-((δ / ξ) ^ 2 / (4 * Real.log (R + 1))) *
          Real.log ε ^ 2)) := by
  have hlε : Real.log ε < 0 := Real.log_neg hε hε1
  set y := δ * (-Real.log ε) / ξ with hy_def
  have hy : 0 < y := div_pos (mul_pos hδ (by linarith)) hξ
  have htail := L34.tail_far_part hh (w := z) h𝕣 le_rfl (by linarith : (0:ℝ) ≤ R) hz hy
  have he : 2 * Real.exp (-y ^ 2 / (2 * (Real.log (𝕣 / 𝕣) + 2 * Real.log (R + 1)))) =
      2 * Real.exp (-((δ / ξ) ^ 2 / (4 * Real.log (R + 1))) * Real.log ε ^ 2) := by
    rw [div_self h𝕣.ne', Real.log_one, zero_add, hy_def]
    congr 2
    ring
  rw [he] at htail
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl htail))
  intro ω hω
  simp only [Set.mem_ofPred_eq, not_le] at hω
  by_cases hB : y ≤ |CircleAvg.cInc h 𝕣 z 𝕣 0 ω|
  · exact Or.inr hB
  left
  rw [not_le, CircleAvg.cInc] at hB
  set S := scaleFac ξ c (h ω) 𝕣 z
  have hS : 0 < S := mul_pos hc (Real.exp_pos _)
  have key : ε ^ (s + δ) * S ≤ ε ^ s * scaleFac ξ c (h ω) 𝕣 0 := by
    simp only [S, scaleFac]
    rw [Real.rpow_add hε, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hε.le _)
    rw [Real.rpow_def_of_pos hε, mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc.le
    have h1 := (abs_lt.1 hB).2
    have h2 : ξ * y = δ * (-Real.log ε) := by rw [hy_def]; field_simp
    nlinarith
  show ENNReal.ofReal (ε ^ (s + δ)) ≤ ENNReal.ofReal S⁻¹ * F ω
  calc ENNReal.ofReal (ε ^ (s + δ)) = ENNReal.ofReal S⁻¹ * ENNReal.ofReal (ε ^ (s + δ) * S) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hS.le)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal S⁻¹ * F ω := by
        gcongr
        exact (ENNReal.ofReal_le_ofReal key).trans hω.le

end L319
end LQGMetric.DFGPS
