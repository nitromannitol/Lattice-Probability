/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29KerFn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Asm

/-!
# DDDF Proposition 29: the kernel estimates as statements about explicit functions

The white-noise kernel `p29Ker t x` of `φ_t − p_{t/2} * h` (S6P29Asm) is a.e. the function

  `dKer t x (s, y) = 1_{[0,1−t]}(s) p_{(t+s)/2}(x − y) − 1_{s>0} 1_D(y) (p_{t/2} * p^D_{s/2})(x, y)`

(DDDF arXiv:1904.08021 DD:1528, DD:1516: `coeFn_p29Ker`), so `P29KerBounds` follows from the
`L²(ℝ × ℂ)` estimates on `dKer` (`P29DKerBounds`, DD:1562–1596): `p29KerBounds_of_dKer`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq WhiteNoise Blueprint

/-- the kernel of `φ_t − p_{t/2} * h` at `x` as an explicit function (DD:1528, DD:1516) -/
def dKer (t : ℝ) (x : ℂ) (q : ℝ × ℂ) : ℝ :=
  (Icc 0 (1 - t) ×ˢ univ).indicator (fun q : ℝ × ℂ => heatKernel ((t + q.1) / 2) x q.2) q -
    (Ioi 0 ×ˢ sqOpen (-1) 3).indicator (fun q => thirdKer (-1) 3 t q.1 x q.2) q

theorem coeFn_p29Ker {t : ℝ} (ht : 0 < t) (x : ℂ) :
    (p29Ker t x : ℝ × ℂ → ℝ) =ᵐ[volume] dKer t x := by
  have h1 := coeFn_shiftL2 t (phiKernelL2 (Real.sqrt t) 1 x)
  have h2 := (measurePreserving_tShift t).quasiMeasurePreserving.ae_eq_comp
    (coeFn_phiKernelL2 (Real.sqrt t) 1 (Real.sqrt_pos.2 ht) x)
  have h3 := (memLp_zbKerFun_bdd (a := -1) (L := 3) (by norm_num)
    (heatBdd (sqOpen (-1) 3) (t / 2) x)).coeFn_toLp
  filter_upwards [Lp.coeFn_sub (shiftL2 t (phiKernelL2 (Real.sqrt t) 1 x))
    (zbKerL2 (-1) 3 (by norm_num) (heatBdd (sqOpen (-1) 3) (t / 2) x)), h1, h2, h3]
    with q hq hq1 hq2 hq3
  rw [p29Ker, hq, Pi.sub_apply, hq1, hq2, zbKerL2, hq3, zbKerFun_heatBdd ht,
    phiKernel_comp_tShift ht.le]
  rfl

lemma sq_norm_eq_integral {f : WNSpace} {g : ℝ × ℂ → ℝ} (h : (f : ℝ × ℂ → ℝ) =ᵐ[volume] g) :
    ‖f‖ ^ 2 = ∫ q, g q ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h] with q hq
  rw [hq, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [sq]

/-- **The kernel estimates on `dKer`** (DDDF DD:1562–1596): on every compact `K ⊆ (−1,2)²`,
uniformly in `t ∈ (0,1/2)`, `∫∫ (dKer t v − dKer t u)² ≤ A |u − v|` and `∫∫ dKer t v² ≤ σ²`. -/
def P29DKerBounds : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ sqOpen (-1) 3 → ∃ A σ : ℝ, 0 < A ∧ 0 < σ ∧
    ∀ t ∈ Ioo (0 : ℝ) (1 / 2), ∀ u ∈ K, ∀ v ∈ K,
      ∫⁻ q, ENNReal.ofReal ((dKer t v q - dKer t u q) ^ 2) ≤ ENNReal.ofReal (A * ‖u - v‖) ∧
      ∫⁻ q, ENNReal.ofReal (dKer t v q ^ 2) ≤ ENNReal.ofReal (σ ^ 2)

lemma integral_sq_le_of_lintegral {g : ℝ × ℂ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ q, ENNReal.ofReal (g q ^ 2) ≤ ENNReal.ofReal B) : ∫ q, g q ^ 2 ≤ B := by
  by_cases hi : Integrable (fun q => g q ^ 2) volume
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => sq_nonneg _)
      hi.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hB h
  · rw [integral_undef hi]; exact hB

theorem p29KerBounds_of_dKer (h : P29DKerBounds) : P29KerBounds := by
  intro K hK hKD
  obtain ⟨A, σ, hA, hσ, hb⟩ := h K hK hKD
  refine ⟨A, σ, hA, hσ, fun t ht u hu v hv => ⟨?_, ?_⟩⟩
  · have e : (⇑(p29Ker t v - p29Ker t u) : ℝ × ℂ → ℝ) =ᵐ[volume]
        fun q => dKer t v q - dKer t u q := by
      filter_upwards [Lp.coeFn_sub (p29Ker t v) (p29Ker t u), coeFn_p29Ker ht.1 v,
        coeFn_p29Ker ht.1 u] with q h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    rw [sq_norm_eq_integral e]
    exact integral_sq_le_of_lintegral (by positivity) (hb t ht u hu v hv).1
  · rw [sq_norm_eq_integral (coeFn_p29Ker ht.1 v)]
    exact integral_sq_le_of_lintegral (by positivity) (hb t ht u hu v hv).2

end P29WN
end DDDF
end LQGMetric
