/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L7 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Cont
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box

/-!
# DZZ Lemma 2.7, uniform Gaussian tail of `Σ_i |Δ_i|` (task P2-DZZPRE, WP-112)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`), Lemma 2.7 (`lem-tilde-h-eta`),
l. 548–576: `P(max_{v∈𝕍} max_{j≥0} |h̃_{2^{-j}}(v) − η_{2^{-j}}(v)|≥ λ) ≤ O(1)e^{−Ω(λ²)}`, proved by
bounding `Σ_i max_v |Δ_i(v)|`. Here (for continuous versions `Y_i` of `Δ_i`):

* `deltaKernel i x = K^{h̃}_x − K^η_x` on the band `bandSet i` (DZZ's `Δ_i = √π W(deltaKernel i ·)`
  a.s., `dzzDelta_ae_eq`);
* (eq-variance-truncation) `π‖deltaKernel i x‖² ≤ Kρ^i` (`dzz_variance_truncation`);
* (eq-feb25, increment half) `‖deltaKernel i x − deltaKernel i x'‖² ≤ K₁ 2^i |x − x'|`, from Lemma 2.5
  for `h̃` and `η` on the band (`dzz_lemma25_wnField`, `dzz_lemma25_etaField`; the latter assumes
  `BridgeShellBound`);
* continuous versions exist (`exists_continuous_modification_of_kernel_half`);
* `dzz_lemma27_sum`: `P(∃ v ∈ [0,1]², ∃ n, λ ≤ Σ_{i<n} |Y_i(v)|) ≤ C e^{−λ²/C}` via the probabilistic
  core `dzz_sum_sup_tail` (DZZ l. 565–576 with Lemmas 2.1, 2.3).

Not yet done: the a.s. telescoping `h̃_{2^{-j}} − η_{2^{-j}} = Σ_{i≤j} Δ_i` (see handoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-! ### Fields `√π W(F x)` -/

theorem isGaussianProcess_sqrtPi (hW : IsWhiteNoise P W) {T : Type} (F : T → WNSpace) :
    IsGaussianProcess (fun t ω => Real.sqrt Real.pi * W (F t) ω) P :=
  QuantumZipper.GFFExist.gs_isGaussianProcess
    (fun t => ((hW.measurable _).const_mul _).aemeasurable)
    fun I c => ⟨_, (hW.hasLaw (fun i : I => F i)
      (fun i => c i * Real.sqrt Real.pi)).congr (Eventually.of_forall fun ω => by
        exact Finset.sum_congr rfl fun i _ => by ring)⟩

lemma integral_sqrtPi (hW : IsWhiteNoise P W) (f : WNSpace) :
    ∫ ω, Real.sqrt Real.pi * W f ω ∂P = 0 := by
  rw [integral_const_mul, QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _),
    mul_zero]

lemma variance_sqrtPi (hW : IsWhiteNoise P W) (f : WNSpace) :
    Var[fun ω => Real.sqrt Real.pi * W f ω; P] = Real.pi * ‖f‖ ^ 2 := by
  have e : (fun ω => Real.sqrt Real.pi * W f ω) = Real.sqrt Real.pi • W f := rfl
  rw [e, variance_smul, (hW.hasLaw_single f).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (by positivity), Real.sq_sqrt Real.pi_pos.le]

lemma integral_sq_sqrtPi_sub (hW : IsWhiteNoise P W) (f g : WNSpace) :
    ∫ ω, (Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω) ^ 2 ∂P =
      Real.pi * ‖f - g‖ ^ 2 := by
  have := hW.isProbabilityMeasure
  have hm : AEMeasurable (fun ω => Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω) P :=
    (((hW.measurable _).const_mul _).sub ((hW.measurable _).const_mul _)).aemeasurable
  have hmf : MemLp (fun ω => Real.sqrt Real.pi * W f ω) 2 P :=
    ((hW.hasLaw_single _).hasGaussianLaw.memLp_two).const_mul _
  have hmg : MemLp (fun ω => Real.sqrt Real.pi * W g ω) 2 P :=
    ((hW.hasLaw_single _).hasGaussianLaw.memLp_two).const_mul _
  have h0 : ∫ ω, (Real.sqrt Real.pi * W f ω - Real.sqrt Real.pi * W g ω) ∂P = 0 := by
    rw [integral_sub (hmf.integrable one_le_two) (hmg.integrable one_le_two),
      integral_sqrtPi hW, integral_sqrtPi hW, sub_zero]
  rw [← variance_of_integral_eq_zero hm h0, variance_sqrtPi_sub hW]

/-! ### The band kernels -/

universe u

end DZZ
end LQGMetric
