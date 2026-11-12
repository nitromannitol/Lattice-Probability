/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18D
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105U2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.22 in `𝕊(1)` coordinates for `μ = μ_ĥ`: L3.8 discharged

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, Prop 3.22 (DG:1722–1772)
uses L3.8 (DG:1112–1150) for `μ_ĥ` on `𝕊(1)` (lower half, `min μ(B_{δ/2}) ≥ ε`, DG:1740) and,
through P3.9, on `𝕊` (upper half). At `𝕍`-scale these are `[1/6,5/6]²` and `[1/3,2/3]²`; both
are covered by the `441` balls `B̄(u, 1/30)`, `u ∈ p18Pts`, with `B̄(u, 1/15) ⊆ K₀ = [1/10,9/10]²`,
so L3.8 for `μ_ĥ` on balls (`dgL38Lower_muHat`, `dgLem3_8_muHat_of_upper`, `dgL38Upper_muHU`,
D105 P1/P2, proved) gives it on the boxes by a union bound.

* `dg_prop322_sqOne_muHat` — DG Prop 3.22 for `hc` (`𝕊(1)` coordinates) from the DG-internal
  hypotheses `DGLem311Scaled`, `DGLem311ScaledV`, `DGLem319Scaled` (for `μ_ĥ`) and L3.7 at
  `𝕍`-scale (`DGLem37V`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open WhiteNoise SupTail

variable {Ω : Type} [MeasurableSpace Ω]

lemma p18_dgL38Upper_biUnion {P : Measure Ω} {μ : Ω → Measure ℂ} {β : ℝ} {ι : Type}
    (s : Finset ι) (S : ι → Set ℂ) (h : ∀ i ∈ s, DGL38Upper P μ (S i) β) :
    DGL38Upper P μ (⋃ i ∈ s, S i) β := by
  classical
  choose! p C ε₀ hp hε₀ hb using h
  obtain ⟨p', δ', hp', hδ', hle⟩ := t18_finset_consts s p ε₀ hp hε₀
  refine ⟨p', ∑ i ∈ s, |C i|, min δ' 1, hp', lt_min hδ' one_pos, fun ε hε hεδ => ?_⟩
  have hε1 : ε < 1 := hεδ.trans_le (min_le_right _ _)
  have hsub : {ω | ¬ ∀ z ∈ ⋃ i ∈ s, S i, μ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε} ⊆
      ⋃ i ∈ s, {ω | ¬ ∀ z ∈ S i, μ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, mem_iUnion, exists_prop] at hω ⊢
    obtain ⟨z, ⟨i, hi, hz⟩, hn⟩ := hω
    exact ⟨i, hi, z, hz, hn⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ i ∈ s, P {ω | ¬ ∀ z ∈ S i, μ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε} :=
        measure_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (|C i| * ε ^ p') := by
        refine Finset.sum_le_sum fun i hi => (hb i hi ε hε
          (hεδ.trans_le ((min_le_left _ _).trans (hle i hi).2))).trans
          (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul (le_abs_self _)
          (Real.rpow_le_rpow_of_exponent_ge hε hε1.le (hle i hi).1)
          (Real.rpow_nonneg hε.le _) (abs_nonneg _)
    _ = ENNReal.ofReal ((∑ i ∈ s, |C i|) * ε ^ p') := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ =>
          mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hε.le _)]

/-- **DG L3.8, upper half, for `μ_ĥ` on `T(𝕊) = [1/3, 2/3]²`** -/
theorem p18_dgL38Upper_sq_muHat {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {β : ℝ} (hβ : 2 / (2 - γ) ^ 2 < β) :
    DGL38Upper P (muHat hW γ (by norm_num : (0 : ℝ) < 4 / 5) p18_hK0) (p39Sq p18c0 (1 / 3)) β := by
  obtain ⟨h1, h2⟩ := p18_box_cover
  obtain ⟨p, C, ε₀, hp, hε₀, hb⟩ := p18_dgL38Upper_biUnion p18Pts (fun u => closedBall u (1 / 30))
    (fun u hu => (dgLem3_8_muHat_of_upper hW hγ hγ2 (by norm_num) p18_hK0 (by norm_num)
      (p18_ball_sub_K0 hu) (fun β' hβ' => dgL38Upper_muHU hW hγ hγ2 (by norm_num) (h1 u hu)
        hβ')).2 β hβ)
  refine ⟨p, C, ε₀, hp, hε₀, fun ε hε hεε => (measure_mono fun ω hω => ?_).trans (hb ε hε hεε)⟩
  simp only [mem_ofPred_eq] at hω ⊢
  exact fun h => hω fun z hz => h z (h2 (p18_sq_sub_box hz))

end LQGMetric.DG
