/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.AffineCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.RationalMap




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

 


theorem segCost_affine_image_le {ξ δ : ℝ} (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (z w u v : ℂ)
    (hspeed : ‖v-u‖ ≤ (5/4:ℝ)*‖w-z‖)
    (hfield : ∀ t ∈ Icc (0:ℝ) 1,
      f (segPath u v t) ≤ f (segPath z w t)+δ) :
    segCost ξ f u v ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp (ξ*δ)) * segCost ξ f z w := by
  let M : ℝ := (5/4:ℝ)*Real.exp (ξ*δ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoint : ∀ t ∈ Icc (0:ℝ) 1,
      lenDens ξ f (segPath u v) t ≤
        ENNReal.ofReal M * lenDens ξ f (segPath z w) t := by
    intro t ht
    rw [lenDens_segPath, lenDens_segPath,
      ← ENNReal.ofReal_mul hM]
    apply ENNReal.ofReal_le_ofReal
    have hweight : Real.exp (ξ*f (segPath u v t)) ≤
        Real.exp (ξ*δ)*Real.exp (ξ*f (segPath z w t)) := by
      calc
        Real.exp (ξ*f (segPath u v t)) ≤
            Real.exp (ξ*(f (segPath z w t)+δ)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfield t ht) hξ)
        _ = Real.exp (ξ*δ)*Real.exp (ξ*f (segPath z w t)) := by
          rw [mul_add, Real.exp_add]
          ring
    calc
      Real.exp (ξ*f (segPath u v t))*‖v-u‖ ≤
          (Real.exp (ξ*δ)*Real.exp (ξ*f (segPath z w t)))*‖v-u‖ :=
        mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
      _ ≤ (Real.exp (ξ*δ)*Real.exp (ξ*f (segPath z w t)))*
          ((5/4:ℝ)*‖w-z‖) :=
        mul_le_mul_of_nonneg_left hspeed (by positivity)
      _ = M*(Real.exp (ξ*f (segPath z w t))*‖w-z‖) := by
        dsimp [M]
        ring
  unfold segCost
  rw [lfppLen_eq, lfppLen_eq]
  calc
    ∫⁻ t in Icc (0:ℝ) 1, lenDens ξ f (segPath u v) t ≤
        ∫⁻ t in Icc (0:ℝ) 1,
          ENNReal.ofReal M * lenDens ξ f (segPath z w) t :=
      setLIntegral_mono' measurableSet_Icc hpoint
    _ = ENNReal.ofReal M *
        ∫⁻ t in Icc (0:ℝ) 1, lenDens ξ f (segPath z w) t := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]


end SupercriticalLQGUniqueness.Exponent.InwardMap
