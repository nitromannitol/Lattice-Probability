/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.BMExistence at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Existence of Brownian motion

We prove `NonVacuity.BrownianMotionExists`.

1. **Gaussian process with covariance `min s t`.** The vectors `bmVec t = 𝟙_{(0,t]}` in
   `L²(ℝ)` satisfy `⟪bmVec s, bmVec t⟫ = min s t`. The Gaussian-series construction
   `gs_process_hilbert` gives, on `(ℕ → ℝ, stdP)`, a family `X t` all of whose finite linear
   combinations are centered Gaussians with variance `‖Σ cᵢ bmVec tᵢ‖²`. By
   `IsGaussianProcess.isPreBrownianReal_of_covariance`, `X` is a pre-Brownian motion.
2. **Continuity.** The process `Z z = X (z.re⁺)` on `ℂ` satisfies the eighth-moment bound
   `E|Z z − Z w|⁸ = 105 |z.re⁺ − w.re⁺|⁴ ≤ 105 ‖z − w‖⁴`, so the dyadic Kolmogorov theorem
   `CircleCont.exists_continuous_modification` gives a modification `Y` continuous on `Hbar`.
   Restricting `Y` to the nonnegative real axis gives a modification of `X` with continuous
   paths, which is a Brownian motion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace QuantumZipper.BMExist

open QuantumZipper.GFFExist LQGDimension.ExistAsm

/-- The `L²(ℝ)` vector `𝟙_{(0,t]}`. -/
def bmVec (t : ℝ≥0) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) t))
    measure_Ioc_lt_top.ne (1 : ℝ)

theorem bmVec_inner (s t : ℝ≥0) : ⟪bmVec s, bmVec t⟫ = ((min s t : ℝ≥0) : ℝ) := by
  rw [bmVec, bmVec, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one measurableSet_Ioc
    measurableSet_Ioc measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne, Set.Ioc_inter_Ioc,
    measureReal_def, Real.volume_Ioc, sup_idem, sub_zero]
  exact (ENNReal.toReal_ofReal (le_inf s.2 t.2)).trans (NNReal.coe_min s t).symm

theorem bmVec_norm_sub_sq (s t : ℝ≥0) :
    ‖bmVec s - bmVec t‖ ^ 2 = |(s : ℝ) - t| := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    bmVec_inner, bmVec_inner, bmVec_inner]
  rcases le_total s t with h | h
  · rw [min_eq_left h, min_self, min_self,
      abs_of_nonpos (by simpa using (NNReal.coe_le_coe.2 h) : (s : ℝ) - t ≤ 0)]
    ring
  · rw [min_eq_right h, min_self, min_self,
      abs_of_nonneg (by simpa using (NNReal.coe_le_coe.2 h) : (0 : ℝ) ≤ s - t)]
    ring

section Process

variable {X : ℝ≥0 → (ℕ → ℝ) → ℝ}
  (hX : ∀ {ι : Type} [Fintype ι] (τ : ι → ℝ≥0) (c : ι → ℝ),
    HasLaw (fun ω => ∑ i, c i * X (τ i) ω)
      (gaussianReal 0 (‖∑ i, c i • bmVec (τ i)‖ ^ 2).toNNReal) stdP)
include hX

theorem bm_law_single (t : ℝ≥0) :
    HasLaw (X t) (gaussianReal 0 (‖bmVec t‖ ^ 2).toNNReal) stdP := by
  simpa using hX (fun _ : Fin 1 => t) (fun _ => 1)

theorem bm_law_add (s t : ℝ≥0) :
    HasLaw (fun ω => X s ω + X t ω)
      (gaussianReal 0 (‖bmVec s + bmVec t‖ ^ 2).toNNReal) stdP := by
  simpa [Fin.sum_univ_two] using hX ![s, t] (fun _ => 1)

theorem bm_law_sub (s t : ℝ≥0) :
    HasLaw (fun ω => X s ω - X t ω)
      (gaussianReal 0 (‖bmVec s - bmVec t‖ ^ 2).toNNReal) stdP := by
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using hX ![s, t] ![1, -1]

theorem bm_isPreBrownian (hmeas : ∀ t, Measurable (X t)) : IsPreBrownianReal X stdP := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
  · exact gs_isGaussianProcess (fun t => (hmeas t).aemeasurable)
      (fun I c => ⟨_, hX (fun i : I => (i : ℝ≥0)) c⟩)
  · rw [(bm_law_single hX t).integral_eq, integral_id_gaussianReal]
  · rw [gs_cov_eq (bm_law_single hX s) (bm_law_single hX t) (bm_law_add hX s t), bmVec_inner,
      min_eq_left hst]

theorem bm_momentBound (hmeas : ∀ t, Measurable (X t)) :
    CircleCont.MomentBound (fun z ω => X (Real.toNNReal z.re) ω) stdP (gaussianAbsMoment 8) := by
  intro z _ w _
  rw [CircleCont.lintegral_pow8_of_map_eq
    (U := fun ω => X (Real.toNNReal z.re) ω - X (Real.toNNReal w.re) ω)
    ((hmeas _).sub (hmeas _)) (bm_law_sub hX _ _).map_eq]
  apply ENNReal.ofReal_le_ofReal
  have hv : (((‖bmVec (Real.toNNReal z.re) - bmVec (Real.toNNReal w.re)‖ ^ 2).toNNReal : ℝ≥0) : ℝ)
      ≤ ‖z - w‖ := by
    rw [Real.coe_toNNReal _ (sq_nonneg _), bmVec_norm_sub_sq, Real.coe_toNNReal',
      Real.coe_toNNReal']
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have h4 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 4
  calc _ ≤ ‖z - w‖ ^ 4 * gaussianAbsMoment 8 :=
        mul_le_mul_of_nonneg_right h4 (gaussianAbsMoment_nonneg 8)
    _ = gaussianAbsMoment 8 * ‖z - w‖ ^ 4 := by ring

end Process

/-- **Existence of Brownian motion**, on the i.i.d. Gaussian sequence space. -/
theorem exists_isBrownianReal_stdP : ∃ B : ℝ≥0 → (ℕ → ℝ) → ℝ, IsBrownianReal B stdP := by
  obtain ⟨X, hmeas, hX⟩ := gs_process_hilbert ℝ≥0 bmVec
  have hpre := bm_isPreBrownian hX hmeas
  obtain ⟨Y, hc, hae, -⟩ := CircleCont.exists_continuous_modification
    (Z := fun z ω => X (Real.toNNReal z.re) ω) (fun z => (hmeas _).aemeasurable)
    (gaussianAbsMoment_nonneg 8) (bm_momentBound hX hmeas)
  have hmem : ∀ t : ℝ≥0, (((t : ℝ) : ℂ)) ∈ Hbar := fun t => by
    show 0 ≤ (((t : ℝ) : ℂ)).im
    simp
  refine ⟨fun t ω => Y ((t : ℝ) : ℂ) ω, ?_⟩
  refine { toIsPreBrownianReal := hpre.congr fun t => ?_, cont := ae_of_all _ fun ω => ?_ }
  · filter_upwards [hae _ (hmem t)] with ω hω
    rw [hω]
    simp
  · exact (hc ω).comp_continuous (by fun_prop) hmem

end QuantumZipper.BMExist

namespace QuantumZipper

end QuantumZipper
