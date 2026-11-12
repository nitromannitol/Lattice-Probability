/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CM4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Geom
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UClip
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32VGeo
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18

/-!
# DZZ (eq-very-crude) at `μIn`: the covering bound on `𝕍^ξ` (P2-DZZCM)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 854–857): "a simple adaption of the argument in
[DS11, Proposition 1.6] (see also [DG16, Proposition 6.2]) gives (eq-very-crude)". As in
`log_tilde_le_of_good` (P2-DZZ53, S5L53Crude; DZZ's covering l. 744–745), we cover the segment
`[u, v]` by balls `B(x, ε^β)`, `x ∈ [u, v]`, of mass `≤ δ²` on the good event of DG Lemma 3.8's
upper half (`DG.dgL38Upper_muHU`). Here `u, v ∈ 𝕍^ξ ⊆ 𝕍_{-ξ} = [ξ, 1-ξ]²` (no tilde walls), so
DG L3.8 is needed on the square `𝕍_{-ξ}`: it is covered by finitely many balls `B̄(x, ξ/3)`
(compactness), and the finite union is handled as in `DG.p18_dgL38Upper_biUnion`.

* `cm_dgL38Upper_dzzVIn`: DG L3.8 (upper half) for `M_γ` on `𝕍_{-ξ}`;
* `cm_log_min_le_of_good`: on the good event, `log min_{A×B} D_δ ≤ log 6 + β log ε⁻¹` for
  subsets `A, B ⊆ 𝕍_{-ξ}` containing points `u ≠ v`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- finite unions in DG L3.8's upper half (`DG.p18_dgL38Upper_biUnion`, for any universe) -/
lemma cm_dgL38Upper_biUnion {μ : Ω → Measure ℂ} {β : ℝ} {ι : Type}
    (s : Finset ι) (S : ι → Set ℂ) (h : ∀ i ∈ s, DG.DGL38Upper P μ (S i) β) :
    DG.DGL38Upper P μ (⋃ i ∈ s, S i) β := by
  classical
  choose! p C ε₀ hp hε₀ hb using h
  obtain ⟨p', δ', hp', hδ', hle⟩ := DG.t18_finset_consts s p ε₀ hp hε₀
  refine ⟨p', ∑ i ∈ s, |C i|, min δ' 1, hp', lt_min hδ' one_pos, fun ε hε hεδ => ?_⟩
  have hε1 : ε < 1 := hεδ.trans_le (min_le_right _ _)
  have hsub : {ω | ¬ ∀ z ∈ ⋃ i ∈ s, S i, μ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε} ⊆
      ⋃ i ∈ s, {ω | ¬ ∀ z ∈ S i, μ ω (ball z (ε ^ β)) ≤ ENNReal.ofReal ε} := by
    intro ω hω
    simp only [mem_setOf_eq, not_forall, mem_iUnion, exists_prop] at hω ⊢
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

lemma cm_isCompact_dzzVIn (r : ℝ) : IsCompact (dzzVIn r) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_dzzVIn r) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 + 2 * |r|)).subset fun z hz => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  have e1 : |z.re| ≤ 1 + |r| := abs_le.2 ⟨by linarith [neg_abs_le r, le_abs_self r],
    by linarith [neg_abs_le r, le_abs_self r]⟩
  have e2 : |z.im| ≤ 1 + |r| := abs_le.2 ⟨by linarith [neg_abs_le r, le_abs_self r],
    by linarith [neg_abs_le r, le_abs_self r]⟩
  linarith

/-- a closed ball of radius `ρ < r` around a point of `𝕍_{-r}` lies in the open square -/
lemma cm_closedBall_sub_openSquare {r ρ : ℝ} (hρ : ρ < r) {x : ℂ} (hx : x ∈ dzzVIn r) :
    closedBall x ρ ⊆ openSquare := by
  intro z hz
  rw [mem_closedBall, Complex.dist_eq] at hz
  have h1 := (Complex.abs_re_le_norm (z - x)).trans hz
  have h2 := (Complex.abs_im_le_norm (z - x)).trans hz
  simp only [Complex.sub_re, Complex.sub_im] at h1 h2
  rw [abs_le] at h1 h2
  obtain ⟨a1, a2, a3, a4⟩ := hx
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- a ball of radius `ρ ≤ r/2` around a point of `𝕍_{-r}` lies in `𝕍_{-r/2}` -/
lemma cm_ball_sub_dzzVIn {r ρ : ℝ} (hρ : ρ ≤ r / 2) {x : ℂ} (hx : x ∈ dzzVIn r) :
    ball x ρ ⊆ dzzVIn (r / 2) := by
  intro z hz
  rw [mem_ball, Complex.dist_eq] at hz
  have h1 := (Complex.abs_re_le_norm (z - x)).trans hz.le
  have h2 := (Complex.abs_im_le_norm (z - x)).trans hz.le
  simp only [Complex.sub_re, Complex.sub_im] at h1 h2
  rw [abs_le] at h1 h2
  obtain ⟨a1, a2, a3, a4⟩ := hx
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **DG L3.8 (upper half) for `M_γ` on `𝕍_{-ξ}`** -/
theorem cm_dgL38Upper_dzzVIn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ : ℝ} (hξ : 0 < ξ) {β : ℝ} (hβ : 2 / (2 - γ) ^ 2 < β) :
    DG.DGL38Upper P (fun ω => DG.muHU W γ ω) (dzzVIn ξ) β := by
  obtain ⟨t, ht⟩ := (cm_isCompact_dzzVIn ξ).elim_nhds_subcover (fun x => ball x (ξ / 3))
    (fun x _ => ball_mem_nhds x (by positivity))
  obtain ⟨p, C, ε₀, hp, hε₀, hb⟩ := cm_dgL38Upper_biUnion (P := P)
    (μ := fun ω => DG.muHU W γ ω) (β := β) t (fun x => closedBall x (ξ / 3))
    (fun x hx => DG.dgL38Upper_muHU hW hγ hγ2 (by positivity)
      (cm_closedBall_sub_openSquare (by linarith) (ht.1 x hx)) hβ)
  refine ⟨p, C, ε₀, hp, hε₀, fun ε hε hεε => (measure_mono fun ω hω => ?_).trans (hb ε hε hεε)⟩
  simp only [mem_setOf_eq] at hω ⊢
  intro hall
  apply hω
  intro z hz
  have := ht.2 hz
  simp only [mem_iUnion] at this
  obtain ⟨x, hx, hzx⟩ := this
  exact hall z (mem_biUnion hx (ball_subset_closedBall hzx))

end DZZ
end LQGMetric
