import LatticeProb.LQG.LQGMetricPointScaling

/-! # Scaling of internal metrics of the γ-LQG metric about a point

If two functions `D, D' : ℂ → ℂ → ℝ` satisfy `D(e x, e y) = K · D'(x, y)` for a homeomorphism `e` of `ℂ` and a constant
`K > 0`, then lengths of curves, lengths of paths and internal metrics are related by the same factor:
  `D(e u, e v; e(U)) = K · D'(u, v; U)`.
The factor must be positive: for `K = 0` the right-hand side is `0` when no path in `U` joins `u` to `v`, while the
left-hand side is `∞`.

Combined with the scaling relation of the γ-LQG metric about a point (`IsLQGMetric.ae_scaling`), this gives, almost surely
and simultaneously for every set `U` and all `u, v`,
  `D_h(r u + z, r v + z; r U + z) = e^{ξ (h_r(z) + Q log r)} · D_{h'}(u, v; U)`,
with `h' = h(r · + z) - h_r(z)` a whole-plane GFF. Internal distances in a set at Euclidean scale `r` around `z` are thus
`r^{ξ Q} e^{ξ h_r(z)}` times internal distances of a unit-scale whole-plane GFF metric, as used throughout the multiscale
arguments for the LQG metric (Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020, Section 3).

Main results:
* `curveLength_comp_of_eq_mul`, `pathLength_map_of_eq_mul`: lengths of image curves and paths.
* `internalMetric_image_of_eq_mul`: internal metrics of an image set under a homeomorphism.
* `internalMetric_affine_image_of_eq_mul`: the case of the affine map `x ↦ r x + z`, `r ≠ 0` real.
* `IsLQGMetric.ae_internalMetric_scaling`: the scaling relation of internal metrics of the γ-LQG metric about a point.
-/

namespace LatticeProb.LQG

open MeasureTheory LatticeProb.Gauss Set
open scoped ENNReal

section General

variable {D D' : ℂ → ℂ → ℝ} {e : ℂ → ℂ} {K : ℝ}

/-- If `D(e x, e y) = K · D'(x, y)` with `K ≥ 0`, the `D`-length of the curve `e ∘ p` is `K` times the `D'`-length of
`p`. -/
theorem curveLength_comp_of_eq_mul (hK : 0 ≤ K) (hDe : ∀ x y, D (e x) (e y) = K * D' x y) (p : ℝ → ℂ) (a b : ℝ) :
    curveLength D (e ∘ p) a b = ENNReal.ofReal K * curveLength D' p a b := by
  unfold curveLength
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun q => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, hDe, ENNReal.ofReal_mul hK]

/-- If `D(e x, e y) = K · D'(x, y)` with `K ≥ 0` and `e` continuous, the `D`-length of the image path `e ∘ P` is `K`
times the `D'`-length of `P`. -/
theorem pathLength_map_of_eq_mul (hK : 0 ≤ K) (hDe : ∀ x y, D (e x) (e y) = K * D' x y) (he : Continuous e)
    {x y : ℂ} (P : Path x y) :
    pathLength D (P.map he) = ENNReal.ofReal K * pathLength D' P := by
  unfold pathLength
  exact curveLength_comp_of_eq_mul hK hDe P.extend 0 1

/-- **Internal metrics of an image set.** If `e` is a homeomorphism of `ℂ` and `D(e x, e y) = K · D'(x, y)` with
`K > 0`, then `D(e u, e v; e(U)) = K · D'(u, v; U)` for every set `U` and all `u, v`. -/
theorem internalMetric_image_of_eq_mul (e : ℂ ≃ₜ ℂ) (hK : 0 < K) (hDe : ∀ x y, D (e x) (e y) = K * D' x y)
    (U : Set ℂ) (u v : ℂ) :
    internalMetric D (e '' U) (e u) (e v) = ENNReal.ofReal K * internalMetric D' U u v := by
  have h0 : ENNReal.ofReal K ≠ 0 := by simpa using hK
  unfold internalMetric
  simp_rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun P hP => ?_
    refine iInf₂_le_of_le (P.map e.continuous) (fun t => ⟨P t, hP t, rfl⟩) ?_
    exact (pathLength_map_of_eq_mul hK.le hDe e.continuous P).le
  · refine le_iInf₂ fun P hP => ?_
    let Q : Path u v :=
      (P.map e.symm.continuous).cast (e.symm_apply_apply u).symm (e.symm_apply_apply v).symm
    have hQ : ∀ t, Q t ∈ U := by
      intro t
      obtain ⟨w, hw, hwt⟩ := hP t
      show e.symm (P t) ∈ U
      rw [← hwt, e.symm_apply_apply]
      exact hw
    have hPQ : Q.map e.continuous = P := by
      ext t
      show e (e.symm (P t)) = P t
      exact e.apply_symm_apply _
    refine iInf₂_le_of_le Q hQ ?_
    rw [← pathLength_map_of_eq_mul hK.le hDe e.continuous Q, hPQ]

/-- **Internal metrics under an affine map.** For real `r ≠ 0` and `z ∈ ℂ`, if `D(r x + z, r y + z) = K · D'(x, y)`
with `K > 0`, then `D(r u + z, r v + z; r U + z) = K · D'(u, v; U)` for every set `U` and all `u, v`. -/
theorem internalMetric_affine_image_of_eq_mul {r : ℝ} (hr : r ≠ 0) (z : ℂ) (hK : 0 < K)
    (hDe : ∀ x y : ℂ, D (r * x + z) (r * y + z) = K * D' x y) (U : Set ℂ) (u v : ℂ) :
    internalMetric D ((fun x : ℂ => (r : ℂ) * x + z) '' U) (r * u + z) (r * v + z) =
      ENNReal.ofReal K * internalMetric D' U u v := by
  let e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (r : ℂ) (Complex.ofReal_ne_zero.mpr hr)).trans (Homeomorph.addRight z)
  have he : ∀ x, e x = (r : ℂ) * x + z := fun _ => rfl
  have hU : (fun x : ℂ => (r : ℂ) * x + z) '' U = e '' U := by
    simp only [he]
  rw [hU, ← he u, ← he v]
  exact internalMetric_image_of_eq_mul e hK (fun x y => by rw [he, he]; exact hDe x y) U u v

end General

/-- **Scaling of internal metrics of the γ-LQG metric about a point.** For a γ-LQG metric `𝔇`, a whole-plane GFF `h`,
`r > 0` and `z ∈ ℂ`, almost surely, simultaneously for every set `U ⊆ ℂ` and all `u, v ∈ ℂ`,
`D_h(r u + z, r v + z; r U + z) = e^{ξ (h_r(z) + Q log r)} · D_{h'}(u, v; U)`, where `h' = h(r · + z) - h_r(z)`
(`recentredPairing`) is a whole-plane GFF (`isWholePlaneGFF_recentredPairing`). -/
theorem IsLQGMetric.ae_internalMetric_scaling {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ (U : Set ℂ) (u v : ℂ),
      internalMetric (𝔇 (hC ω)) ((fun x : ℂ => (r : ℂ) * x + z) '' U) (r * u + z) (r * v + z) =
        ENNReal.ofReal (Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r))) *
          internalMetric (𝔇 (recentredPairing hC hcirc r z ω)) U u v := by
  filter_upwards [h𝔇.ae_scaling hG hr z] with ω hω U u v
  exact internalMetric_affine_image_of_eq_mul hr.ne' z (Real.exp_pos _) hω U u v

end LatticeProb.LQG
