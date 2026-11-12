import LatticeProb.LQG.LQGMetric
import LatticeProb.LQG.LengthMetricDerived
import LatticeProb.Gauss.GFFAffineInvariance

/-! # Scaling of the γ-LQG metric about a point

Let `𝔇` be a γ-LQG metric with Weyl exponent `ξ` (`IsLQGMetric`), let `h` be a whole-plane GFF with pairings `hC` and
circle averages `hcirc`, and let `r > 0` and `z ∈ ℂ`. The recentred and dilated field
  `h' = h(r · + z) - h_r(z)`
is again a whole-plane GFF, and almost surely, for all `u, v ∈ ℂ`,
  `D_h(r u + z, r v + z) = e^{ξ (h_r(z) + Q log r)} · D_{h'}(u, v) = r^{ξ Q} e^{ξ h_r(z)} · D_{h'}(u, v)`,
where `Q = 2/γ + γ/2` (Gwynne-Miller 2021, Section 1.2: coordinate change (Axiom IV) followed by Weyl scaling
(Axiom III) by the constant `h_r(z) + Q log r`). This is the exact scaling relation behind the multiscale estimates for
the LQG metric of Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020 (Section 3), in which the distances at Euclidean scale `r`
around `z` are compared with `r^{ξ Q} e^{ξ h_r(z)}`.

Main results:
* `recentredPairing`: the pairings of `h(r · + z) - h_r(z)`.
* `isWholePlaneGFF_recentredPairing`: the recentred and dilated field is a whole-plane GFF.
* `IsEuclideanLengthMetric.weylScaling_const`: Weyl scaling by a constant `c` multiplies a length metric by `e^{ξ c}`.
* `IsLQGMetric.ae_scaling`: the scaling relation above.
-/

namespace LatticeProb.LQG

open MeasureTheory LatticeProb.Gauss
open scoped ENNReal

/-- The pairings of the recentred and dilated field `h(r · + z) - h_r(z)`:
`(h(r · + z) - h_r(z), φ) = r⁻² (h, φ((· - z) / r)) - h_r(z) ∫ φ`. -/
noncomputable def recentredPairing {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) :
    Ω → (ℂ → ℝ) → ℝ :=
  fun ω φ => (r ^ 2)⁻¹ * hC ω (fun y => φ ((y - z) / r)) - hcirc ω r z * ∫ x, φ x

/-- The recentred and dilated field `h(r · + z) - h_r(z)` of a whole-plane GFF `h` is a whole-plane GFF, with circle
averages `(s, w) ↦ h_{r s}(r w + z) - h_r(z)`. -/
theorem isWholePlaneGFF_recentredPairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r)
    (z : ℂ) :
    IsWholePlaneGFF P (recentredPairing hC hcirc r z)
      (fun ω s w => hcirc ω (r * s) (r * w + z) - hcirc ω r z) := by
  have h := AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hG (r : ℂ)
    (Complex.ofReal_ne_zero.2 hr.ne') z
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [hnr] at h
  exact h

/-- Weyl scaling of a Euclidean length metric by a constant function `c` multiplies it by `e^{ξ c}`. -/
theorem IsEuclideanLengthMetric.weylScaling_const {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ c : ℝ)
    (x y : ℂ) :
    weylScaling D ξ (fun _ => c) x y = ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (D x y) := by
  refine le_antisymm (hD.weylScaling_le_exp_mul (fun _ => le_rfl) x y) ?_
  have h := hD.exp_mul_le_weylScaling (K := -(ξ * c)) (f := fun _ => c) (fun _ => (neg_neg _).le) x y
  rwa [neg_neg] at h

/-- **Scaling of the γ-LQG metric about a point.** For a γ-LQG metric `𝔇`, a whole-plane GFF `h`, `r > 0` and
`z ∈ ℂ`, almost surely, for all `u, v ∈ ℂ`,
`D_h(r u + z, r v + z) = e^{ξ (h_r(z) + Q log r)} · D_{h'}(u, v)` with `h' = h(r · + z) - h_r(z)`
(`recentredPairing`), itself a whole-plane GFF (`isWholePlaneGFF_recentredPairing`). Route: the coordinate change
(Axiom IV) for `h` gives `D_h(r · + z, r · + z) = D_{h(r · + z) + Q log r} = D_{h' + c}` with the random constant
`c = h_r(z) + Q log r`, and Weyl scaling (Axiom III) for `h'` by the constant `c` gives `e^{ξ c} D_{h'}`. -/
theorem IsLQGMetric.ae_scaling {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, 𝔇 (hC ω) (r * u + z) (r * v + z) =
      Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r)) * 𝔇 (recentredPairing hC hcirc r z ω) u v := by
  have hG' := isWholePlaneGFF_recentredPairing hG hr z
  have hzero : ∀ T : (ℂ → ℝ) → ℝ, addFunPairing T (fun (_ : ℂ) => (0 : ℝ)) = T := by
    intro T
    funext φ
    simp [addFunPairing]
  have hA := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) hG (fun _ => continuous_const)
    (fun _ => measurable_const)
  have hA' := h𝔇.satisfiesLQGMetricAxioms Ω P (recentredPairing hC hcirc r z) _ (fun _ _ => 0) hG'
    (fun _ => continuous_const) (fun _ => measurable_const)
  have e : (fun ω => addFunPairing (hC ω) ((fun (_ : Ω) (_ : ℂ) => (0 : ℝ)) ω)) = hC := by
    funext ω
    exact hzero _
  have e' : (fun ω => addFunPairing (recentredPairing hC hcirc r z ω) ((fun (_ : Ω) (_ : ℂ) => (0 : ℝ)) ω)) =
      recentredPairing hC hcirc r z := by
    funext ω
    exact hzero _
  rw [e] at hA
  rw [e'] at hA'
  filter_upwards [hA.coordChange r hr z, hA'.ae_weylScaling, hA'.ae_isEuclideanLengthMetric,
    hA.ae_isEuclideanLengthMetric] with ω hIV hIII hI' hI u v
  set c := hcirc ω r z + lqgQ γ * Real.log r with hc
  have hpair : addFunPairing (affinePullbackPairing (hC ω) r z) (fun _ => lqgQ γ * Real.log r) =
      addFunPairing (recentredPairing hC hcirc r z ω) (fun _ => c) := by
    funext φ
    simp only [addFunPairing, affinePullbackPairing, recentredPairing, integral_const_mul, hc]
    ring
  have hW := hIII (fun _ => c) continuous_const u v
  rw [← hpair, ← hIV u v, hI'.weylScaling_const, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hW
  have hnn : ∀ {E : ℂ → ℂ → ℝ}, IsEuclideanLengthMetric E → ∀ x y, 0 ≤ E x y := by
    intro E hE x y
    have h1 := hE.triangle x y x
    have h2 := hE.symm y x
    have h3 := hE.self_eq_zero x
    linarith
  exact (ENNReal.ofReal_eq_ofReal_iff (hnn hI _ _) (mul_nonneg (Real.exp_pos _).le (hnn hI' _ _))).mp hW

end LatticeProb.LQG
