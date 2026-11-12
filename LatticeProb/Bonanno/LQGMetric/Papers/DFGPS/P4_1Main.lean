/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepAsm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepSeg2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepArc2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Asm

/-!
# DFGPS Proposition 4.1 (`prop-line-path`)

Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*,
arXiv:1905.00380, Proposition 4.1 (T:2444–2451), proof T:2455–2582:

* Step 1 (annulus bounds, DFGPS Prop 3.1): `ann_bound_general` (`P4_1StepAnn`);
* Step 2 (crossings): `crossing_sum_le_path` (`P4_1StepCross`) and the tube geometry
  `tubeBlocks_line` (segments, `P4_1StepSeg2`), `tubeBlocks_circle` (arcs and whole circles,
  `P4_1StepArc2`);
* Step 3 (assembly, DFGPS Thm 1.5): `prop4_1_of_tube` (`P4_1StepAsm`);
* Step 4 (circle-average sums): `circSum_lower` (`P4_1Cov`), with `ξ < 1` from
  `GMXiQBound` (`xiGamma_lt_one`, `P4_1Xi`).

`dfgpsProp4_1_of` is the target `Blueprint.DFGPSProp4_1` from LM Lemma 3.1 (via DFGPS Prop 3.1),
DFGPS Theorem 1.5 and `ξQ < 1 + ξ²/2`; `dfgpsProp4_1_of_DG` plugs in the proofs of the last two
from the cited results (`dfgpsScaling_of_lem3_6`, `L36.lem3_6_of_DG`, `DG.gmXiQBound_of_dgThm1_5'`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.DFGPS.P41

open Blueprint

/-- a segment as `{a + σe : σ ∈ [0, ℓ]}` with `‖e‖ = 1` -/
lemma segment_line (a a' : ℂ) : ∃ (e : ℂ) (ℓ : ℝ), ‖e‖ = 1 ∧ 0 ≤ ℓ ∧
    ∀ x ∈ segment ℝ a a', ∃ σ ∈ Icc 0 ℓ, x = a + σ * e := by
  by_cases h : a' = a
  · refine ⟨1, 0, norm_one, le_rfl, fun x hx => ⟨0, ⟨le_rfl, le_rfl⟩, ?_⟩⟩
    rw [h, segment_same] at hx
    rw [hx]; simp
  · have hℓ : 0 < ‖a' - a‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
    refine ⟨(a' - a) / (‖a' - a‖ : ℂ), ‖a' - a‖, ?_, hℓ.le, fun x hx => ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hℓ.le, div_self hℓ.ne']
    · rw [segment_eq_image'] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      refine ⟨t * ‖a' - a‖, ⟨mul_nonneg ht.1 hℓ.le, by nlinarith [ht.2]⟩, ?_⟩
      have : ((‖a' - a‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hℓ.ne'
      show a + t • (a' - a) = _
      rw [Complex.real_smul]
      push_cast
      field_simp

/-- the tube condition for every `L` of DFGPS Prop 4.1 (segment, arc, whole circle) -/
theorem tubeBlocks_of_isSegmentOrArc {L : Set ℂ} (hL : IsSegmentOrArc L) {b : ℝ} (hb : 0 < b) :
    TubeBlocks L b := by
  rcases hL with ⟨a, a', rfl⟩ | ⟨z, ρ, θ₁, θ₂, hρ, -, -, rfl⟩ | ⟨z, ρ, hρ, rfl⟩
  · obtain ⟨e, ℓ, he, hℓ, hseg⟩ := segment_line a a'
    exact tubeBlocks_line he hℓ hseg hb
  · refine tubeBlocks_circle (z := z) hρ ?_ hb
    rintro _ ⟨θ, -, rfl⟩
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρ.le, Complex.norm_exp_ofReal_mul_I, mul_one]
  · exact tubeBlocks_circle hρ subset_rfl hb

/-- **DFGPS Proposition 4.1** (`prop-line-path`, T:2444–2451), in the corrected constants-first
form `Blueprint.DFGPSProp4_1` (D57), from LM Lemma 3.1 (1), DFGPS Theorem 1.5 and
`ξQ − 1 − ξ²/2 < 0` (used only for `ξ < 1`, T:2531). -/
theorem dfgpsProp4_1_of (h31a : LMLem3_1a) (hscal : DFGPSScaling) (hXQ : GMXiQBound) :
    DFGPSProp4_1 := by
  intro γ hγ0 hγ2 D c hD L hL b hb p hp ζ hζ
  exact prop4_1_of_tube (prop3_1 h31a) hscal hXQ hγ0 hγ2 hD
    (tubeBlocks_of_isSegmentOrArc hL hb) hp hζ

/-- **DFGPS Proposition 4.1** from the cited results: LM Lemma 3.1 (1), DG Theorem 1.5 (for
`ξQ < 1 + ξ²/2`), DG (1.5b, second half) and DG Proposition 3.21 (for DFGPS Theorem 1.5). -/
theorem dfgpsProp4_1_of_DG (h31a : LMLem3_1a) (hDG : DG.DGThm1_5) (hKU : DGThm1_5KU)
    (h321 : DGProp3_21) : DFGPSProp4_1 :=
  dfgpsProp4_1_of h31a (dfgpsScaling_of_lem3_6 h31a (L36.lem3_6_of_DG hKU h321))
    (DG.gmXiQBound_of_dgThm1_5' hDG)

end LQGMetric.DFGPS.P41
