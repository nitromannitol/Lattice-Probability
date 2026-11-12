/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29WN3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29WN2
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquare2
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryExt

/-!
# DDDF Proposition 29: the zero-boundary GFF on the square from a white noise (R2, part 3)

DDDF arXiv:1904.08021, `tightness.tex` DD:1514–1525 ("White noise representation"): for a
space-time white noise `W`, `h(ρ) := W(√π · zbKerFun ρ)` (`zbX`), with
`zbKerFun ρ (s, y) = 1_{s>0} 1_D(y) ∫ ρ(y') p^D_{s/2}(y', y) dy'`, is the zero-boundary GFF on
`D = (−1, 2)²` (`isZBGFFProcessExt_zbX`). Covariance: Fubini on `ℝ × ℂ`, `integral_Pk_mul_Pk`
(Chapman–Kolmogorov) and R1 `HeatSq.zeroGFFTestCov_sqOpen_eq_heat`
(`zeroGFFTestCov = π ∫_0^∞ ∫∫ ρ p^D_s σ`), as in DD:1520–1524.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Function
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq WhiteNoise

variable {a L : ℝ}

lemma memLp_zbKerFun_bdd (hL : 0 < L) (ρ : BddOn (sqOpen a L)) :
    MemLp (zbKerFun a L ρ.1) 2 (volume : Measure (ℝ × ℂ)) := by
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := ρ.2
  exact memLp_zbKerFun hL hm hC h0

/-- the kernel `zbKerFun ρ` as an element of `L²(ℝ × ℂ)` -/
def zbKerL2 (a L : ℝ) (hL : 0 < L) (ρ : BddOn (sqOpen a L)) : WNSpace :=
  (memLp_zbKerFun_bdd hL ρ).toLp

/-- `⟪zbKer ρ, zbKer σ⟫ = ∫_0^∞ ∫∫ ρ(y') p^D_s(y', y'') σ(y'')` (DD:1520–1524) -/
theorem inner_zbKerL2 (hL : 0 < L) (ρ σ : BddOn (sqOpen a L)) :
    ⟪zbKerL2 a L hL ρ, zbKerL2 a L hL σ⟫ =
      ∫ s in Ioi 0, ∫ y', ∫ y'', ρ.1 y' * sqDirKernel a L s y' y'' * σ.1 y'' := by
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := ρ.2
  obtain ⟨hm', ⟨C', hC'⟩, h0'⟩ := σ.2
  have hf := memLp_zbKerFun_bdd hL ρ
  have hg := memLp_zbKerFun_bdd hL σ
  rw [L2.inner_def]
  have h1 : ∫ q, ⟪(zbKerL2 a L hL ρ : ℝ × ℂ → ℝ) q, (zbKerL2 a L hL σ : ℝ × ℂ → ℝ) q⟫ =
      ∫ q, zbKerFun a L ρ.1 q * zbKerFun a L σ.1 q := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with q h1 h2
    simp only [zbKerL2, h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial,
      RCLike.re_to_real]
    ring
  rw [h1, Measure.volume_eq_prod, integral_prod _ (by
    rw [← Measure.volume_eq_prod]; exact hf.integrable_mul hg)]
  have h2 : ∀ s : ℝ, ∫ y, zbKerFun a L ρ.1 (s, y) * zbKerFun a L σ.1 (s, y) =
      (Ioi 0).indicator
        (fun s => ∫ y', ∫ y'', ρ.1 y' * sqDirKernel a L s y' y'' * σ.1 y'') s := by
    intro s
    by_cases hs : (0 : ℝ) < s
    · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
      have hP := integral_Pk_mul_Pk hL hm hC h0 hm' hC' h0' (half_pos hs)
      rw [add_halves] at hP
      rw [← hP, ← integral_indicator (measurableSet_sqOpen a L)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ sqOpen a L
      · have hq : ((s, y) : ℝ × ℂ) ∈ Ioi (0 : ℝ) ×ˢ sqOpen a L := ⟨hs, hy⟩
        simp only [zbKerFun, indicator_of_mem hq, indicator_of_mem hy, Pk]
      · have hq : ((s, y) : ℝ × ℂ) ∉ Ioi (0 : ℝ) ×ˢ sqOpen a L := fun h => hy h.2
        simp only [zbKerFun, indicator_of_notMem hq, indicator_of_notMem hy, zero_mul]
    · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
      have hq : ∀ y : ℂ, ((s, y) : ℝ × ℂ) ∉ Ioi (0 : ℝ) ×ˢ sqOpen a L := fun y h => hs h.1
      simp only [zbKerFun, indicator_of_notMem (hq _), zero_mul, integral_zero]
  simp_rw [h2]
  rw [integral_indicator measurableSet_Ioi]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- DDDF's white-noise zero-boundary GFF on `(−1, 2)²`:
`h(ρ) = √π ∫_0^∞ ∫_D P^D_{s/2} ρ (y) W(dy, ds)` (DD:1514) -/
def zbX (W : WNSpace → Ω → ℝ) (ρ : BddOn (sqOpen (-1) 3)) : Ω → ℝ :=
  W (Real.sqrt π • zbKerL2 (-1) 3 (by norm_num) ρ)

/-- **The white-noise representation is the zero-boundary GFF** on `(−1, 2)²` (DD:1514–1525). -/
theorem isZBGFFProcessExt_zbX (hW : IsWhiteNoise P W) :
    IsZBGFFProcessExt (sqOpens (-1) 3) (zbX W) P where
  measurable ρ := hW.measurable _
  gaussian := hW.isGaussianProcess_comp _
  centered ρ := QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _)
  covariance_eq ρ σ := by
    show cov[W (Real.sqrt π • zbKerL2 (-1) 3 _ ρ), W (Real.sqrt π • zbKerL2 (-1) 3 _ σ); P] = _
    rw [hW.cov_eq, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      Real.mul_self_sqrt Real.pi_pos.le]
    exact (congrArg (π * ·) (inner_zbKerL2 (a := -1) (L := 3) _ ρ σ)).trans
      (zeroGFFTestCov_sqOpen_eq_heat ρ σ).symm

end P29WN
end DDDF
end LQGMetric
