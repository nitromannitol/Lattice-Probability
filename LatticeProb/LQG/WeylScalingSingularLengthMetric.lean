import LatticeProb.LQG.WeylCompositionOuter2
import LatticeProb.LQG.InternalMetricSquareTail

/-!
# The Weyl scaling by a weight with a point singularity is a Euclidean length metric

Let `D` be a Euclidean length metric on `ℂ`, `ξ > 0`, and `g` a weight continuous on `ℂ ∖ {0}` (such as the log weight
`-α₀ log |·|`). Write `D_g = e^{ξ g} · D` (`weylScaling`) and `innerDist D ξ g = (D_g).toReal`. If `D_g` is finite and
`D_g(x, w) → 0` as `w → x` for every `x`, then `innerDist D ξ g` is a Euclidean length metric. The only point where the
continuity hypothesis carries content is the singular point `0`.

For the γ-LQG metric `D_h` of the field `h = h^ℂ - α₀ log |·|` (Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020,
arXiv:1905.00380, p. 9; Gwynne-Miller 2021, Remark 1.5), this reduces axiom I of the metric (finiteness, Euclidean topology,
length metric) to the almost sure finiteness of `D_h` and its continuity on the diagonal. It also reduces axiom III (Weyl
scaling `D_{h+f} = e^{ξ f} · D_h` for continuous `f`) to the finiteness of `D_h`, through the composition rule of Weyl
scalings for an inner weight continuous off the origin (`weylMetricCompositionContinuousOuter_lp`).

## Main results

* `LatticeProb.LQG.IsEuclideanLengthMetric.isEuclideanLengthMetric_innerDist`: the deterministic statement.
* `LatticeProb.LQG.IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log`: axiom I for the log-singular field, given
  almost sure finiteness and continuity on the diagonal.
* `LatticeProb.LQG.IsLQGMetric.ae_weylScaling_log_add`: axiom III for the log-singular field, given almost sure finiteness.
-/

open MeasureTheory Set Filter Topology LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

/-- **Weyl scaling by a weight continuous off the origin.** Let `D` be a Euclidean length metric and `g` continuous on
`ℂ ∖ {0}`. If `e^{ξ g} · D` is finite and `e^{ξ g} · D (x, w) → 0` as `w → x` for every `x`, then its real part
`innerDist D ξ g` is a Euclidean length metric. -/
theorem IsEuclideanLengthMetric.isEuclideanLengthMetric_innerDist {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ : ℝ} {g : ℂ → ℝ} (hg : ContinuousOn g {z | z ≠ 0}) (hfin : ∀ x y, weylScaling D ξ g x y ≠ ⊤)
    (hcont : ∀ x, Tendsto (fun w => weylScaling D ξ g x w) (𝓝 x) (𝓝 0)) :
    IsEuclideanLengthMetric (innerDist D ξ g) where
  self_eq_zero := innerDist_self hD ξ g
  eq_of_eq_zero _ _ h := hD.innerDist_eq_zero hg hfin h
  symm := innerDist_symm hD ξ g
  triangle := innerDist_triangle hD hfin
  isOpen_iff U := by
    constructor
    · intro hU z hz
      exact hD.weylScaling_nhds hg hfin z hU hz
    · intro h
      refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
      obtain ⟨ε, hε, hεU⟩ := h z hz
      have hev : ∀ᶠ w in 𝓝 z, weylScaling D ξ g z w < ENNReal.ofReal ε :=
        (hcont z).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))
      filter_upwards [hev] with w hw
      exact hεU w (ENNReal.toReal_lt_of_lt_ofReal hw)
  ofReal_eq_internalMetric z w := by
    apply le_antisymm
    · refine le_iInf fun P => le_iInf fun _ => ?_
      have h2 := two_point_le_curveLength (D := innerDist D ξ g) P.extend zero_le_one
      rw [P.extend_zero, P.extend_one, innerDist_symm hD ξ g] at h2
      exact h2
    · rw [innerDist, ENNReal.ofReal_toReal (hfin z w)]
      unfold weylScaling
      refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 => le_iInf fun hpT => ?_
      obtain ⟨P, hP⟩ := exists_path_pathLength_le_curveLength (E := innerDist D ξ g) hp.1 hp.2.1
      subst hp0 hpT
      calc internalMetric (innerDist D ξ g) univ (p 0) (p T) ≤ pathLength (innerDist D ξ g) P :=
            iInf_le_of_le P (iInf_le_of_le (fun _ => mem_univ _) le_rfl)
        _ ≤ curveLength (innerDist D ξ g) p 0 T := hP
        _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) :=
            hD.curveLength_innerDist_le_cost hfin hp le_rfl le_rfl

/-- The log weight `-α₀ log |·|` is continuous off the origin. -/
theorem continuousOn_neg_mul_log_norm (α₀ : ℝ) :
    ContinuousOn (fun x : ℂ => -α₀ * Real.log ‖x‖) {z | z ≠ 0} :=
  continuousOn_const.mul (continuous_norm.continuousOn.log fun _ hz => norm_ne_zero_iff.mpr hz)

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Axiom I for the LQG metric of a field with a log singularity, from finiteness and continuity on the diagonal.**
Let `𝔇` be a γ-LQG metric, `h^ℂ` a whole-plane GFF and `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}`. If almost surely `D_h` is
finite and `D_h(x, w) → 0` as `w → x` for every `x`, then almost surely `D_h` is finite and is a length metric inducing
the Euclidean topology. -/
theorem IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ)
    (hfin : ∀ᵐ ω ∂P, ∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞)
    (hcont : ∀ᵐ ω ∂P, ∀ x,
      Tendsto (fun w => weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) x w) (𝓝 x) (𝓝 0)) :
    ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) ∧
      IsEuclideanLengthMetric fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
  filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hfin, hcont] with ω hD hf hc
  exact ⟨hf, hD.isEuclideanLengthMetric_innerDist (continuousOn_neg_mul_log_norm α₀) (fun u v => (hf u v).ne) hc⟩

/-- **Axiom III for the LQG metric of a field with a log singularity, from finiteness.** Let `𝔇` be a γ-LQG metric with
Weyl exponent `ξ > 0`, `h^ℂ` a whole-plane GFF and `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}`. If almost surely `D_h` is finite,
then almost surely, for every continuous `f`, `e^{ξ (f - α₀ log |·|)} · D_{h^ℂ} = e^{ξ f} · D_h`. -/
theorem IsLQGMetric.ae_weylScaling_log_add (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) (hξ : 0 < ξ)
    (α₀ : ℝ) (hfin : ∀ᵐ ω ∂P, ∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v,
      weylScaling (𝔇 (hC ω)) ξ (fun x => f x - α₀ * Real.log ‖x‖) u v =
        weylScaling (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ξ f u v := by
  filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hfin] with ω hD hf f hfc u v
  rw [weylMetricCompositionContinuousOuter_lp ξ hξ (𝔇 (hC ω)) (fun x => -α₀ * Real.log ‖x‖) f hD
    (continuousOn_neg_mul_log_norm α₀) hfc (fun x y => (hf x y).ne) u v]
  congr 1
  funext z
  ring

end LatticeProb.LQG
