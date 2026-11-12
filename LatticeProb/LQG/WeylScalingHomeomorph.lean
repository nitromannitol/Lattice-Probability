import LatticeProb.LQG.LQGMetric

/-!
# Weyl scaling under a change of coordinates, and the coordinate change for a log-singular field

The length-parametrized path formula for the Weyl scaling `e^{ξ f} · D` is invariant under pulling the metric `D` and
the weight `f` back by a homeomorphism of `ℂ`; no regularity of the weight is needed.

As a consequence, Axiom IV (coordinate change for scaling and translation) of a γ-LQG metric `𝔇` passes to the metric
`D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` of the field `h = h^ℂ - α₀ log |·|` with a log singularity at the origin
(Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020, *Weak LQG metrics and Liouville first passage percolation*, arXiv:1905.00380,
p. 9; Gwynne-Miller 2021, Remark 1.5): for `r > 0` and `z ∈ ℂ`, almost surely, for all `u, v`,
`D_h(r u + z, r v + z) = e^{-ξ α₀ log |r · + z|} · D_{h^ℂ(r · + z) + Q log r}(u, v)`.
This is clause IV of `LQGMetricFieldAxioms`.

## Main results

* `LatticeProb.LQG.IsLengthParametrized.comp_homeomorph_symm`: length parametrization is preserved by a homeomorphism.
* `LatticeProb.LQG.weylScaling_comp_homeomorph`: `e^{ξ (f ∘ e)} · (D ∘ e)(u, v) = e^{ξ f} · D(e u, e v)`.
* `LatticeProb.LQG.IsLQGMetric.ae_weylScaling_log_coordChange`: the coordinate change for the log-singular field.
-/

open MeasureTheory Set LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

/-- Length parametrization is preserved when a curve and the metric are pulled back by a homeomorphism `e`: if `p` is
parametrized by `D`-length on `[0, T]`, then `e⁻¹ ∘ p` is parametrized by `(D ∘ e)`-length on `[0, T]`. -/
theorem IsLengthParametrized.comp_homeomorph_symm {D : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {T : ℝ}
    (hp : IsLengthParametrized D p T) (e : ℂ ≃ₜ ℂ) :
    IsLengthParametrized (fun x y => D (e x) (e y)) (e.symm ∘ p) T := by
  refine ⟨hp.1, e.symm.continuous.comp_continuousOn hp.2.1, ?_⟩
  intro s t hs hst ht
  have heq : curveLength (fun x y => D (e x) (e y)) (e.symm ∘ p) s t = curveLength D p s t := by
    simp only [curveLength, Function.comp_apply, e.apply_symm_apply]
  rw [heq]
  exact hp.2.2 s t hs hst ht

/-- **Weyl scaling commutes with a change of coordinates.** For a homeomorphism `e` of `ℂ`, the Weyl scaling of the
pulled-back metric `(x, y) ↦ D(e x, e y)` by the pulled-back weight `f ∘ e` is the pull-back of the Weyl scaling of `D`
by `f`: `e^{ξ (f ∘ e)} · (D ∘ e)(u, v) = e^{ξ f} · D(e u, e v)`. -/
theorem weylScaling_comp_homeomorph (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) (e : ℂ ≃ₜ ℂ) (u v : ℂ) :
    weylScaling (fun x y => D (e x) (e y)) ξ (f ∘ e) u v = weylScaling D ξ f (e u) (e v) := by
  apply le_antisymm
  · unfold weylScaling
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hu => le_iInf fun hv => ?_
    refine iInf_le_of_le T (iInf_le_of_le (e.symm ∘ p) ?_)
    refine iInf_le_of_le (hp.comp_homeomorph_symm e) ?_
    have hpu : (e.symm ∘ p) 0 = u := by simp [hu]
    have hpv : (e.symm ∘ p) T = v := by simp [hv]
    refine iInf_le_of_le hpu (iInf_le_of_le hpv ?_)
    simp only [Function.comp_apply, e.apply_symm_apply, le_refl]
  · unfold weylScaling
    refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hu => le_iInf fun hv => ?_
    have hp' : IsLengthParametrized D (e ∘ p) T := by
      have h := hp.comp_homeomorph_symm e.symm
      simpa only [e.symm_symm, e.apply_symm_apply] using h
    refine iInf_le_of_le T (iInf_le_of_le (e ∘ p) ?_)
    refine iInf_le_of_le hp' ?_
    have hpu : (e ∘ p) 0 = e u := by simp [hu]
    have hpv : (e ∘ p) T = e v := by simp [hv]
    exact iInf_le_of_le hpu (iInf_le_of_le hpv (by simp only [Function.comp_apply, le_refl]))

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Coordinate change for the LQG metric of a field with a log singularity** (Axiom IV for `h = h^ℂ - α₀ log |·|`).
Let `𝔇` be a γ-LQG metric with Weyl exponent `ξ`, `h^ℂ` a whole-plane GFF, and `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}`.
For `r > 0` and `z ∈ ℂ`, almost surely, for all `u, v`,
`D_h(r u + z, r v + z) = e^{-ξ α₀ log |r · + z|} · D_{h^ℂ(r · + z) + Q log r}(u, v)`.
Proof: Axiom IV for `h^ℂ` identifies `D_{h^ℂ}(r · + z, r · + z)` with `D_{h^ℂ(r · + z) + Q log r}`, and the Weyl scaling
commutes with the change of coordinates `x ↦ r x + z` (`weylScaling_comp_homeomorph`). -/
theorem IsLQGMetric.ae_weylScaling_log_coordChange (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    (α₀ : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) (r * u + z) (r * v + z) =
        weylScaling (𝔇 (addFunPairing (affinePullbackPairing (hC ω) r z) fun _ => lqgQ γ * Real.log r)) ξ
          (fun x => -α₀ * Real.log ‖(r : ℂ) * x + z‖) u v := by
  have hA := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) hG (fun _ => continuous_const)
    (fun _ => measurable_const)
  have h0 : ∀ ω, addFunPairing (hC ω) (fun _ => (0 : ℝ)) = hC ω := fun ω => by
    funext φ
    simp [addFunPairing]
  filter_upwards [hA.coordChange r hr z] with ω hω u v
  simp only [h0] at hω
  let e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')).trans (Homeomorph.addRight z)
  have he : ∀ x, e x = (r : ℂ) * x + z := fun _ => rfl
  have hfun : (fun x y => 𝔇 (hC ω) (e x) (e y)) =
      𝔇 (addFunPairing (affinePullbackPairing (hC ω) r z) fun _ => lqgQ γ * Real.log r) :=
    funext fun x => funext fun y => by rw [he, he]; exact hω x y
  rw [← hfun, ← he u, ← he v, ← weylScaling_comp_homeomorph (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) e u v]
  rfl

end LatticeProb.LQG
