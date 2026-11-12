import LatticeProb.LQG.WeylScalingAnnulusCrossing
import LatticeProb.LQG.PathLengthMinComparison
import LatticeProb.LQG.WeylScalingLocality
import LatticeProb.LQG.InternalMetricSquareTail

/-!
# Weyl scalings by weights that agree outside a disc

Let `D` be a Euclidean length metric on `ℂ` and let `f, g : ℂ → ℝ` agree on `{|x| ≥ r}`. If the Weyl scalings
`e^{ξ f} · D` and `e^{ξ g} · D` are finite Euclidean length metrics and `ξ f` is bounded below on the annulus
`r < |x| < r'`, then their internal metrics agree on every set contained in `{|x| ≥ r'}`. Indeed, a path from a point
with `|x| ≥ r'` which enters the disc of radius `r` crosses the annulus, which costs at least `c = e^m D(∂B_r, ∂B_{r'})`
for either weight, while paths avoiding that disc have the same lengths for both weights. The length comparison of
paths in `{|x| ≥ r'}` for metrics that agree below the threshold `c` then gives both inequalities.

For the weight `-α₀ log |x|` and its continuous truncation `-α₀ log max(|x|, ρ)` this shows that the internal metrics on
sets contained in `{|x| ≥ 2ρ}` coincide. For the LQG metric of a whole-plane GFF, the Weyl scaling by a deterministic
continuous function is a.s. a finite Euclidean length metric, so the comparison holds a.s. for every `ρ` in a sequence
as soon as the Weyl scaling by `-α₀ log |x|` is a finite Euclidean length metric.

## Main statements

* `min_le_toReal_weylScaling_of_eq_of_le_norm`: the annulus crossing bound for the real-valued metrics.
* `IsEuclideanLengthMetric.internalMetric_weylScaling_eq_of_eq_of_le_norm`: agreement of the internal metrics.
* `IsEuclideanLengthMetric.internalMetric_weylScaling_log_eq_log_max`: the case `-α₀ log |x|` versus
  `-α₀ log max(|x|, ρ)`.
* `IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_of_continuous`: a.s. `e^{ξ f} · D_{h^ℂ}` is a finite Euclidean
  length metric for every deterministic continuous `f`.
* `IsLQGMetric.ae_internalMetric_weylScaling_log_eq_log_max`: the a.s. agreement for a sequence of truncation radii.
-/

open MeasureTheory Set
open scoped ENNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

private theorem min_le_toReal_of_min_le {a b : ℝ≥0∞} {c : ℝ} (ha : a ≠ ∞)
    (h : min (ENNReal.ofReal c) b ≤ a) : min c b.toReal ≤ a.toReal := by
  rcases le_total (ENNReal.ofReal c) b with hcb | hbc
  · rw [min_eq_left hcb] at h
    exact (min_le_left _ _).trans ((ENNReal.ofReal_le_iff_le_toReal ha).mp h)
  · rw [min_eq_right hbc] at h
    exact (min_le_right _ _).trans (ENNReal.toReal_mono ha h)

/-- **Annulus crossing bound, real-valued form.** If `f = g` on `{|x| ≥ r}`, `ξ f ≥ m` on the annulus `r < |x| < r'`,
`D ≥ c` between the circles of radii `r` and `r'`, and `e^{ξ f} · D` is finite, then for `|x| ≥ r'`,
`min(e^m c, (e^{ξ g} · D)(x, y)) ≤ (e^{ξ f} · D)(x, y)` for the real parts. -/
theorem min_le_toReal_weylScaling_of_eq_of_le_norm {D : ℂ → ℂ → ℝ} {ξ : ℝ} {f g : ℂ → ℝ} {r r' m c : ℝ}
    (hrr' : r < r') (hfg : ∀ z : ℂ, r ≤ ‖z‖ → f z = g z) (hm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < r' → m ≤ ξ * f z)
    (hc : ∀ a b : ℂ, ‖a‖ = r → ‖b‖ = r' → c ≤ D a b)
    (hf : ∀ u v, weylScaling D ξ f u v ≠ ∞) {x : ℂ} (hx : r' ≤ ‖x‖) (y : ℂ) :
    min (Real.exp m * c) (weylScaling D ξ g x y).toReal ≤ (weylScaling D ξ f x y).toReal :=
  min_le_toReal_of_min_le (hf x y)
    (min_le_weylScaling_of_eq_of_le_norm hrr' hfg hm hc hx y)

/-- **Weyl scalings by weights that agree outside a disc have the same internal metrics away from it.** Let `D` be a
Euclidean length metric, `0 ≤ r < r'`, `f = g` on `{|x| ≥ r}` and `ξ f ≥ m` on the annulus `r < |x| < r'`. If
`e^{ξ f} · D` and `e^{ξ g} · D` are finite Euclidean length metrics, then their internal metrics agree on every
`V ⊆ {|x| ≥ r'}`. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_eq_of_eq_of_le_norm {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ : ℝ} {f g : ℂ → ℝ} {r r' m : ℝ} (hr : 0 ≤ r) (hrr' : r < r')
    (hfg : ∀ z : ℂ, r ≤ ‖z‖ → f z = g z) (hm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < r' → m ≤ ξ * f z)
    (hEf : IsEuclideanLengthMetric fun u v => (weylScaling D ξ f u v).toReal)
    (hEg : IsEuclideanLengthMetric fun u v => (weylScaling D ξ g u v).toReal)
    (hf : ∀ u v, weylScaling D ξ f u v ≠ ∞) (hg : ∀ u v, weylScaling D ξ g u v ≠ ∞)
    {V : Set ℂ} (hV : V ⊆ {x | r' ≤ ‖x‖}) (x y : ℂ) :
    internalMetric (fun u v => (weylScaling D ξ f u v).toReal) V x y =
      internalMetric (fun u v => (weylScaling D ξ g u v).toReal) V x y := by
  obtain ⟨c, hc, hcD⟩ := hD.exists_pos_le_of_norm_eq hr hrr'
  have hc' : 0 < Real.exp m * c := mul_pos (Real.exp_pos m) hc
  have hgf : ∀ z : ℂ, r ≤ ‖z‖ → g z = f z := fun z hz => (hfg z hz).symm
  have hm' : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < r' → m ≤ ξ * g z := fun z h1 h2 => by
    rw [hgf z h1.le]; exact hm z h1 h2
  refine le_antisymm (internalMetric_le_of_min_le hEf hc' (W := {x | r' ≤ ‖x‖}) ?_ hV)
    (internalMetric_le_of_min_le hEg hc' (W := {x | r' ≤ ‖x‖}) ?_ hV)
  · intro u hu v _
    exact min_le_toReal_weylScaling_of_eq_of_le_norm hrr' hgf hm' hcD hg hu v
  · intro u hu v _
    exact min_le_toReal_weylScaling_of_eq_of_le_norm hrr' hfg hm hcD hf hu v

/-- The truncated logarithmic weight `x ↦ -α₀ log max(|x|, ρ)` is continuous for `ρ > 0`. -/
theorem continuous_neg_mul_log_max_norm (α₀ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous fun x : ℂ => -α₀ * Real.log (max ‖x‖ ρ) :=
  continuous_const.mul ((continuous_norm.max continuous_const).log fun _ => (lt_max_of_lt_right hρ).ne')

/-- **The logarithmic weight and its truncation.** For `ρ > 0`, if the Weyl scalings of a Euclidean length metric `D`
by `-α₀ log |x|` and by `-α₀ log max(|x|, ρ)` are finite Euclidean length metrics, their internal metrics agree on every
`V ⊆ {|x| ≥ 2ρ}`. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_log_eq_log_max {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {ξ α₀ ρ : ℝ} (hρ : 0 < ρ)
    (hEf : IsEuclideanLengthMetric fun u v => (weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal)
    (hEg : IsEuclideanLengthMetric fun u v =>
      (weylScaling D ξ (fun x => -α₀ * Real.log (max ‖x‖ ρ)) u v).toReal)
    (hf : ∀ u v, weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u v ≠ ∞)
    (hg : ∀ u v, weylScaling D ξ (fun x => -α₀ * Real.log (max ‖x‖ ρ)) u v ≠ ∞)
    {V : Set ℂ} (hV : V ⊆ {x | 2 * ρ ≤ ‖x‖}) (x y : ℂ) :
    internalMetric (fun u v => (weylScaling D ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) V x y =
      internalMetric (fun u v => (weylScaling D ξ (fun x => -α₀ * Real.log (max ‖x‖ ρ)) u v).toReal)
        V x y := by
  refine hD.internalMetric_weylScaling_eq_of_eq_of_le_norm hρ.le (by linarith)
    (m := -(|ξ * α₀| * (|Real.log ρ| + |Real.log (2 * ρ)|))) (fun z hz => ?_) (fun z h1 h2 => ?_)
    hEf hEg hf hg hV x y
  · simp only [max_eq_left hz]
  · show _ ≤ ξ * (-α₀ * Real.log ‖z‖)
    have hz0 : 0 < ‖z‖ := hρ.trans h1
    have hl1 : Real.log ρ < Real.log ‖z‖ := Real.log_lt_log hρ h1
    have hl2 : Real.log ‖z‖ < Real.log (2 * ρ) := Real.log_lt_log hz0 h2
    have habs : |Real.log ‖z‖| ≤ |Real.log ρ| + |Real.log (2 * ρ)| :=
      (abs_le_max_abs_abs hl1.le hl2.le).trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))
    have hle := le_abs_self (ξ * α₀ * Real.log ‖z‖)
    rw [abs_mul] at hle
    have e : ξ * (-α₀ * Real.log ‖z‖) = -(ξ * α₀ * Real.log ‖z‖) := by ring
    rw [e]
    have hmul := mul_le_mul_of_nonneg_left habs (abs_nonneg (ξ * α₀))
    linarith

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Weyl scaling by a deterministic continuous function is a.s. a finite Euclidean length metric.** For an LQG
metric `𝔇`, a whole-plane GFF `h^ℂ` and a continuous `f`, a.s. `e^{ξ f} · D_{h^ℂ}` is finite and its real part is a
Euclidean length metric (it is a.s. equal to `D_{h^ℂ + f}`). -/
theorem IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_of_continuous (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {f : ℂ → ℝ} (hf : Continuous f) :
    ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ f u v ≠ ∞) ∧
      IsEuclideanLengthMetric fun u v => (weylScaling (𝔇 (hC ω)) ξ f u v).toReal := by
  have h0 := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => (0 : ℝ)) hG (fun _ => continuous_const)
    (fun _ => measurable_const)
  have hS := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ => f) hG (fun _ => hf) (fun _ => measurable_const)
  filter_upwards [h0.ae_weylScaling, hS.ae_isEuclideanLengthMetric, h𝔇.ae_eq_toReal_weylScaling hG hf]
    with ω hW hE hEq
  refine ⟨fun u v => ?_, ?_⟩
  · have h := hW f hf u v
    simp only [addFunPairing_zero_fun] at h
    rw [← h]
    exact ENNReal.ofReal_ne_top
  · have hE' : IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) f)) := hE
    rwa [hEq] at hE'

/-- **A.s. agreement of the internal metrics of the logarithmic weight and its truncations.** If a.s. the Weyl scaling
of `D_{h^ℂ}` by `-α₀ log |x|` is a finite Euclidean length metric, then for every sequence of radii `ρ_n > 0`, a.s.
for every `n` its internal metric agrees with that of the Weyl scaling by `-α₀ log max(|x|, ρ_n)` on every
`V ⊆ {|x| ≥ 2 ρ_n}`. -/
theorem IsLQGMetric.ae_internalMetric_weylScaling_log_eq_log_max (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {α₀ : ℝ} {ρ : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    (hI : ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) ∧
      IsEuclideanLengthMetric fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) :
    ∀ᵐ ω ∂P, ∀ n, ∀ V ⊆ {x : ℂ | 2 * ρ n ≤ ‖x‖}, ∀ x y,
      internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) V x y =
        internalMetric
          (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log (max ‖x‖ (ρ n))) u v).toReal) V x y := by
  have hn : ∀ᵐ ω ∂P, ∀ n, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log (max ‖x‖ (ρ n))) u v ≠ ∞) ∧
      IsEuclideanLengthMetric fun u v =>
        (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log (max ‖x‖ (ρ n))) u v).toReal :=
    ae_all_iff.2 fun n =>
      h𝔇.ae_isEuclideanLengthMetric_weylScaling_of_continuous hG (continuous_neg_mul_log_max_norm α₀ (hρ n))
  filter_upwards [hI, hn, h𝔇.ae_isEuclideanLengthMetric_self hG] with ω hω hωn hD
  intro n V hV x y
  exact hD.internalMetric_weylScaling_log_eq_log_max (hρ n) hω.2 (hωn n).2 (fun u v => (hω.1 u v).ne) (hωn n).1
    hV x y

end LatticeProb.LQG
