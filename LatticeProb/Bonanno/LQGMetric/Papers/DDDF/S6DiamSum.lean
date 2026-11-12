/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DiamSum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamLvl

/-!
# DDDF Prop 27, Step 1: the mean of the diameter, `eq:SumObtained` (task P2-DDDF6d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1340–1368: taking expectations in `eq:Chaining`
(`diam_chain_det`, at level `m = n − 1`), with `eq:Decouplage` (`len21_decouple`), independence of
`φ_{0,K}` and `φ_{K,n}` (`indepFun_phi_version`), the maximum bound (2.11)
(`prop2_expMoment_int`: `E e^{ξ max_{[0,1]²} |φ_{0,K}|} ≤ 4^{ξK + K₂√K}`, needs `ξ < 2`, DDDF
l. 1345 "when `ξ < 2`") and the maximum of the crossing lengths (`lintegral_Zq`):

`E Diam([0,1]², e^{ξφ_{0,n}} ds) ≤ 4·2^{-m} 4^{ξn + K₂√n}
  + 16 Σ_{K=1}^{n} 4^{ξK + K₂√K} (4^K C)^{1/q} 2^{-K} λ_{n−K}` (`s6_sumObtained`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6D

open LFPP T20E Blueprint WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- the maximum `max_{[0,1]²} |φ|` -/
def supAbs (g : ℂ → ℝ) : ℝ := ⨆ z : ferniqueBox 0 1, |g z|

lemma abs_le_supAbs {g : ℂ → ℝ} (hg : Continuous g) {x : ℂ} (hx : x ∈ closedUnitSquare) :
    |g x| ≤ supAbs g := by
  have hbdd : BddAbove (range fun z : ferniqueBox 0 1 => |g z|) := by
    have := (isCompact_ferniqueBox 0 1).bddAbove_image (continuous_abs.comp hg).continuousOn
    rwa [image_eq_range] at this
  have hx' : x ∈ ferniqueBox 0 1 := by
    obtain ⟨h1, h2, h3, h4⟩ := hx
    simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc, Complex.zero_re, Complex.zero_im,
      zero_add]
    exact ⟨⟨h1, h2⟩, h3, h4⟩
  exact le_ciSup hbdd ⟨x, hx'⟩

lemma measurable_comap_supAbs {Ω' : Type*} (F : Ω' → ℂ → ℝ) (hFc : ∀ ω, Continuous (F ω)) :
    Measurable[MeasurableSpace.comap F inferInstance] fun ω => supAbs (F ω) := by
  letI : MeasurableSpace Ω' := MeasurableSpace.comap F inferInstance
  haveI : CompactSpace (ferniqueBox 0 1) := isCompact_iff_compactSpace.1 (isCompact_ferniqueBox 0 1)
  haveI : Nonempty (ferniqueBox 0 1) := ⟨⟨0, by simp [ferniqueBox, Complex.mem_reProdIm]⟩⟩
  exact measurable_iSup_of_continuous (X := fun (x : ferniqueBox 0 1) ω => |F ω x|)
    (fun ω => continuous_abs.comp ((hFc ω).comp continuous_subtype_val))
    (fun x => continuous_abs.measurable.comp ((measurable_pi_apply (x : ℂ)).comp
      (comap_measurable F)))

end S6D
end DDDF
end LQGMetric
