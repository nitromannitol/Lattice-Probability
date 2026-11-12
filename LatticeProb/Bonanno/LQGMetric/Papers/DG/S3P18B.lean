/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P22A4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.22 for the zero-boundary GFF at `𝕍`-scale (adapter to `dg_prop322_hat`)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.22
(`prop-lfpp-upper0`, DG:1722–1772), first paragraph DG:1729–1731: "By Lemma 3.7, it suffices to
prove an upper bound for `ε^β`-Liouville graph distances defined with `ĥ_{ε^β}` in place of
`h_{ε^β}`" (then `δ = ε^β`). The `ĥ`-form (eqn-lfpp-upper-show) at `𝕍`-scale is
`dg_prop322_hat` (P2-DG105j, Papers/DG/S3P22A4.lean).

* `p18_lfpp_compare` — `φ ≤ ψ + a` on `S` ⇒ `D_φ(·,·;S) ≤ e^{ξa} D_ψ(·,·;S)` (`ψ` continuous on
  `S`, `ξ ≥ 0`): the use of L3.7 (with `z = w`).
* `p18_dgL38Lower_biUnion`, `p18_box_cover`, `p18_dgL38Lower_box` — DG L3.8 (lower half) on
  `[1/6, 5/6]² = T(𝕊(1/2))` from the ball version (`B̄(u,R)` with `B̄(u,2R) ⊆ 𝕍`, the form of
  `dgL38Lower_qArea`) by a fixed finite cover and a union bound.
* `DGLem37V` — DG L3.7 at `𝕍`-scale on the probability space of `W` (hypothesis; the Blueprint
  `DGLem3_7` is at the scale of `𝕊(1) = [−1,2]²` for an existential coupling; transporting it to
  `𝕍` needs the white-noise scaling by `1/3`, not available, see handoff).
* `dg_prop322_V` — P3.22 for `hV` at `𝕍`-scale: `max_{z,w ∈ [1/3,2/3]²} D^δ_{hV}(z,w;[1/6,5/6]²) ≤
  δ^{λ−ζ}` w.p. `≥ 1 − Cδ^p`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DG

/-! ## Comparison of LFPP for two fields -/

lemma p18_lfppLength_le {ξ a : ℝ} (hξ : 0 ≤ ξ) {φ ψ : ℂ → ℝ} {S : Set ℂ} (hψ : ContinuousOn ψ S)
    (hφψ : ∀ x ∈ S, φ x ≤ ψ x + a) {z w : ℂ} {q : ℝ → ℂ} (hq : IsDGPath S z w q) :
    LQGDimension.lfppLength ξ φ q ≤ Real.exp (ξ * a) * LQGDimension.lfppLength ξ ψ q := by
  have hd : IntegrableOn (fun t => ‖deriv q t‖) (Ioc (0 : ℝ) 1) := by
    have h := (DFGPS.L36.dgPath_deriv_intervalIntegrable hq).norm
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  have hd' : IntegrableOn (fun t => ‖deriv q t‖) (Icc (0 : ℝ) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).2 hd
  have hc : ContinuousOn (fun t => Real.exp (ξ * a) * Real.exp (ξ * ψ (q t))) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (hψ.comp hq.continuousOn hq.mapsTo)))
  have hi := (hd'.continuousOn_mul hc isCompact_Icc).mono_set Ioc_subset_Icc_self
  unfold LQGDimension.lfppLength
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
    (hi.congr (Eventually.of_forall fun t => by simp only; ring)) ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht => ?_
  have hqt := hq.mapsTo (Ioc_subset_Icc_self ht)
  rw [← mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
  nlinarith [hφψ _ hqt]

/-- **LFPP comparison**: `φ ≤ ψ + a` on `S` ⇒ `D_φ ≤ e^{ξ a} D_ψ` -/
lemma p18_lfpp_compare {ξ a : ℝ} (hξ : 0 ≤ ξ) {φ ψ : ℂ → ℝ} {S : Set ℂ} (hψ : ContinuousOn ψ S)
    (hφψ : ∀ x ∈ S, φ x ≤ ψ x + a) (z w : ℂ) :
    dgLFPP ξ φ S z w ≤ Real.exp (ξ * a) * dgLFPP ξ ψ S z w := by
  rcases isEmpty_or_nonempty {p : ℝ → ℂ // IsDGPath S z w p} with he | hne
  · simp [dgLFPP, iInf_of_isEmpty]
  have hE := Real.exp_pos (ξ * a)
  rw [← div_le_iff₀' hE]
  refine le_ciInf fun p => ?_
  rw [div_le_iff₀' hE]
  exact (ciInf_le (bddBelow_dg ξ φ S z w) p).trans (p18_lfppLength_le hξ hψ hφψ p.2)

/-! ## L3.8 lower half on a box from balls -/

variable {Ω : Type} [MeasurableSpace Ω]

lemma p18_dgL38Lower_biUnion {P : Measure Ω} {μ : Ω → Measure ℂ} {β : ℝ} {ι : Type}
    (s : Finset ι) (S : ι → Set ℂ) (h : ∀ i ∈ s, DGL38Lower P μ (S i) β) :
    DGL38Lower P μ (⋃ i ∈ s, S i) β := by
  classical
  choose! p C ε₀ hp hε₀ hb using h
  obtain ⟨p', δ', hp', hδ', hle⟩ := t18_finset_consts s p ε₀ hp hε₀
  refine ⟨p', ∑ i ∈ s, |C i|, min δ' 1, hp', lt_min hδ' one_pos, fun ε hε hεδ => ?_⟩
  have hε1 : ε < 1 := hεδ.trans_le (min_le_right _ _)
  have hsub : {ω | ¬ ∀ z ∈ ⋃ i ∈ s, S i, ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ β))} ⊆
      ⋃ i ∈ s, {ω | ¬ ∀ z ∈ S i, ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ β))} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, mem_iUnion, exists_prop] at hω ⊢
    obtain ⟨z, ⟨i, hi, hz⟩, hn⟩ := hω
    exact ⟨i, hi, z, hz, hn⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ i ∈ s, P {ω | ¬ ∀ z ∈ S i, ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ β))} :=
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

/-- the grid points `1/6 + (i + j√-1)/30`, `0 ≤ i, j ≤ 20` -/
def p18Pts : Finset ℂ :=
  ((Finset.range 21) ×ˢ (Finset.range 21)).image fun ij =>
    ⟨1 / 6 + (ij.1 : ℝ) / 30, 1 / 6 + (ij.2 : ℝ) / 30⟩

lemma p18_coord {x : ℝ} (h0 : 1 / 6 ≤ x) (h1 : x ≤ 5 / 6) :
    ∃ i ∈ Finset.range 21, |x - (1 / 6 + (i : ℝ) / 30)| ≤ 1 / 60 := by
  set y := (x - 1 / 6) * 30
  have hy : 0 ≤ y + 1 / 2 := by simp only [y]; linarith
  refine ⟨⌊y + 1 / 2⌋₊, Finset.mem_range.2 ((Nat.floor_lt hy).2 ?_), ?_⟩
  · push_cast; simp only [y]; linarith
  · have a1 := Nat.floor_le hy
    have a2 := Nat.lt_floor_add_one (y + 1 / 2)
    rw [abs_le]; constructor <;> simp only [y] at a1 a2 <;> linarith

/-- `[1/6, 5/6]²` is covered by the balls `B̄(u, 1/30)`, `u ∈ p18Pts`, and `B̄(u, 1/15) ⊆ 𝕍` -/
lemma p18_box_cover :
    (∀ u ∈ p18Pts, closedBall u (2 * (1 / 30)) ⊆ openSquare) ∧
      p39Box ⟨1 / 3, 1 / 3⟩ (1 / 3) (1 / 6) ⊆ ⋃ u ∈ p18Pts, closedBall u (1 / 30) := by
  constructor
  · intro u hu x hx
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨hi, hj⟩ := Finset.mem_product.1 hij
    have hi' : (ij.1 : ℝ) ≤ 20 := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hj' : (ij.2 : ℝ) ≤ 20 := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hi0 : (0 : ℝ) ≤ ij.1 := Nat.cast_nonneg _
    have hj0 : (0 : ℝ) ≤ ij.2 := Nat.cast_nonneg _
    rw [mem_closedBall, dist_eq_norm] at hx
    have hr := (Complex.abs_re_le_norm _).trans hx
    have hm := (Complex.abs_im_le_norm _).trans hx
    simp only [Complex.sub_re, Complex.sub_im] at hr hm
    rw [abs_le] at hr hm
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hr.1, hr.2, hm.1, hm.2]
  · intro x hx
    simp only [p39Box, Complex.mem_reProdIm, mem_Icc] at hx
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
    obtain ⟨i, hi, hxi⟩ := p18_coord (x := x.re) (by norm_num at h1 ⊢; linarith)
      (by norm_num at h2 ⊢; linarith)
    obtain ⟨j, hj, hxj⟩ := p18_coord (x := x.im) (by norm_num at h3 ⊢; linarith)
      (by norm_num at h4 ⊢; linarith)
    refine mem_iUnion₂.2 ⟨⟨1 / 6 + (i : ℝ) / 30, 1 / 6 + (j : ℝ) / 30⟩,
      Finset.mem_image.2 ⟨(i, j), Finset.mem_product.2 ⟨hi, hj⟩, rfl⟩, ?_⟩
    rw [mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    linarith

end LQGMetric.DG
