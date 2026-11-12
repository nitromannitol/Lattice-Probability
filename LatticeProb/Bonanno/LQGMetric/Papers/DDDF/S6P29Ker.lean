/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Ker at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29WN3
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Shift
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffCV

/-!
# DDDF Proposition 29: the kernels of `p_{t/2} * h` and of `φ_t` (R2, part 4)

DDDF arXiv:1904.08021, `tightness.tex`:
* (Def:eta, DD:1516): `p_{t/2} * h(x) = η_t(x) = ∫_0^∞ ∫_D (p_{t/2} * p^D_{s/2})(x, y) W(dy, ds)`:
  the white-noise kernel of `zbX W (heatBdd D (t/2) x)` is `1_{s>0} 1_D(y) thirdKer t s x y`
  (`zbKerFun_heatBdd`, with `HeatSq.thirdKer t s x y = ∫_D p_{t/2}(x − y') p^D_{s/2}(y', y) dy'`);
* (DD:1528): `φ_t(x) = ∫_0^{1−t} ∫ p_{(t+s)/2}(x − y) W(dy, ds)`: the kernel of `φ_{√t}` of the
  shifted noise `W ∘ T_t` is `1_{[0,1−t]}(s) p_{(t+s)/2}(x − y)` (`phiKernel_comp_tShift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Real Set

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq WhiteNoise Blueprint

/-- the kernel of `p_{t/2} * h` (DD:1516) -/
theorem zbKerFun_heatBdd {a L t : ℝ} (ht : 0 < t) (x : ℂ) :
    zbKerFun a L (heatBdd (sqOpen a L) (t / 2) x).1 =
      (Ioi 0 ×ˢ sqOpen a L).indicator (fun q => thirdKer a L t q.1 x q.2) := by
  funext q
  unfold zbKerFun thirdKer
  rw [DFGPS.heatBdd_val (measurableSet_sqOpen a L) (half_pos ht)]
  congr 1
  funext q
  rw [← integral_indicator (measurableSet_sqOpen a L)]
  congr 1
  funext y'
  by_cases hy : y' ∈ sqOpen a L
  · rw [indicator_of_mem hy, indicator_of_mem hy]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]

/-- the kernel of `φ_t` (DD:1528) -/
theorem phiKernel_comp_tShift {t : ℝ} (ht : 0 ≤ t) (x : ℂ) :
    phiKernel (Real.sqrt t) 1 x ∘ tShift t =
      (Icc 0 (1 - t) ×ˢ univ).indicator (fun q : ℝ × ℂ => heatKernel ((t + q.1) / 2) x q.2) := by
  funext q
  simp only [Function.comp, phiKernel, tShift, Real.sq_sqrt ht, one_pow]
  by_cases hq : q.1 ∈ Icc 0 (1 - t)
  · have h' : ((q.1 + t, q.2) : ℝ × ℂ) ∈ Icc t 1 ×ˢ (univ : Set ℂ) :=
      ⟨⟨by linarith [hq.1], by linarith [hq.2]⟩, trivial⟩
    rw [indicator_of_mem h', indicator_of_mem (show q ∈ Icc 0 (1 - t) ×ˢ (univ : Set ℂ) from
      ⟨hq, trivial⟩), add_comm]
  · have h' : ((q.1 + t, q.2) : ℝ × ℂ) ∉ Icc t 1 ×ˢ (univ : Set ℂ) := fun h =>
      hq ⟨by linarith [h.1.1], by linarith [h.1.2]⟩
    rw [indicator_of_notMem h', indicator_of_notMem (show q ∉ Icc 0 (1 - t) ×ˢ (univ : Set ℂ)
      from fun h => hq h.1)]

end P29WN
end DDDF
end LQGMetric
