import LatticeProb.LQG.InternalMetricDyadicSmallCells
import LatticeProb.LQG.HalfCrossingScaling
import LatticeProb.LQG.LQGMetricInternalScaling

/-!
# Weyl-scaled internal distances near a point and dyadic subsquares of corner squares

Let `E = e^{ξ f} · D_h` be a Weyl scaling (Gwynne-Miller, arXiv:1905.00383, (1.8)) of a γ-LQG metric `D_h` by a
deterministic weight `f`, and let `r > 0`, `z ∈ ℂ`. If `ξ f ≤ B` on `r U + z`, then almost surely, simultaneously for all
such `U` and all `u, v`,
  `E(r u + z, r v + z; r U + z) ≤ e^{B + ξ (h_r(z) + Q log r)} · D_{h'}(u, v; U)`,
where `h' = h(r · + z) - h_r(z)` is the recentred and dilated field (`recentredPairing`). This combines the comparison
of a Weyl scaling with the metric it scales (`internalMetric_le_of_weylScaling`) and the scaling of internal metrics of
the LQG metric about a point (`IsLQGMetric.ae_internalMetric_scaling`). It is the form in which the distances of a
Weyl scaling by `-α log |·|` at Euclidean scale `r` around `0` are compared with `r^{ξ (Q - α)} e^{ξ h_r(0)}` (the
multiscale argument of Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020, Section 3).

For a square `S = [a, a + s] × [b, b + s]` with a corner at `0` (`a, b ∈ {0, -s}`), the dilation by `2^{-k}` maps the
closed dyadic subsquare of `S` of level `n` with indices `(i, j)` onto the closed dyadic subsquare of `S` of level
`n + k` with indices `(i', j')`, where `i' = i` if `a = 0` and `i' = i + 2^{n+k} - 2^n` if `a = -s`
(`closedDyadicSubsquare_image_two_pow_inv_mul`).

## Main statements

* `LatticeProb.LQG.affine_image_reProdIm`: the image of a closed rectangle under `x ↦ r x + z`, `r > 0`.
* `LatticeProb.LQG.closedDyadicSubsquare_image_two_pow_inv_mul`.
* `LatticeProb.LQG.IsLQGMetric.ae_internalMetric_weylScaling_affine_image_le`.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

/-- The image of the closed rectangle `[x₀, x₁] × [y₀, y₁]` under the affine map `x ↦ r x + z` with `r > 0` real is the
closed rectangle `[r x₀ + Re z, r x₁ + Re z] × [r y₀ + Im z, r y₁ + Im z]`. -/
theorem affine_image_reProdIm {r : ℝ} (hr : 0 < r) (z : ℂ) (x₀ x₁ y₀ y₁ : ℝ) :
    (fun x : ℂ => (r : ℂ) * x + z) '' (Icc x₀ x₁ ×ℂ Icc y₀ y₁) =
      Icc (r * x₀ + z.re) (r * x₁ + z.re) ×ℂ Icc (r * y₀ + z.im) (r * y₁ + z.im) := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact affine_mem_reProdIm hr z hw
  · intro w hw
    refine ⟨(w - z) / r, ?_, ?_⟩
    · rw [Complex.mem_reProdIm] at hw ⊢
      obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := hw
      simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im, mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [le_div_iff₀ hr]; linarith
      · rw [div_le_iff₀ hr]; linarith
      · rw [le_div_iff₀ hr]; linarith
      · rw [div_le_iff₀ hr]; linarith
    · have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      show (r : ℂ) * ((w - z) / r) + z = w
      field_simp
      ring

/-- **Dilation of the closed dyadic subsquares of a square with a corner at `0`.** Let `s > 0` and
`S = [a, a + s] × [b, b + s]` with `a, b ∈ {0, -s}`. The dilation `x ↦ 2^{-k} x` maps the closed dyadic subsquare of `S`
of level `n` with indices `(i, j)` onto the closed dyadic subsquare of `S` of level `n + k` with indices `(i', j')`, where
`i' = i` if `a = 0` and `i' = i + (2^{n+k} - 2^n)` if `a = -s` (and likewise for `j'`). -/
theorem closedDyadicSubsquare_image_two_pow_inv_mul {a b s : ℝ} (k n : ℕ) {i j i' j' : ℕ}
    (hi : a = 0 ∧ i' = i ∨ a = -s ∧ i' = i + (2 ^ (n + k) - 2 ^ n))
    (hj : b = 0 ∧ j' = j ∨ b = -s ∧ j' = j + (2 ^ (n + k) - 2 ^ n)) :
    (fun x : ℂ => ((((2 : ℝ) ^ k)⁻¹ : ℝ) : ℂ) * x) '' closedDyadicSubsquare a b s n i j =
      closedDyadicSubsquare a b s (n + k) i' j' := by
  have hcoord : ∀ (c : ℝ) (i i' : ℕ), (c = 0 ∧ i' = i ∨ c = -s ∧ i' = i + (2 ^ (n + k) - 2 ^ n)) →
      ((2 : ℝ) ^ k)⁻¹ * (c + i * (s / 2 ^ n)) = c + i' * (s / 2 ^ (n + k)) ∧
      ((2 : ℝ) ^ k)⁻¹ * (c + (i + 1) * (s / 2 ^ n)) = c + (i' + 1) * (s / 2 ^ (n + k)) := by
    rintro c i i' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [pow_add]
      constructor <;> field_simp <;> ring
    · have hle : 2 ^ n ≤ 2 ^ (n + k) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right n k)
      push_cast [hle]
      rw [pow_add]
      constructor <;> field_simp <;> ring
  have himg := affine_image_reProdIm (r := ((2 : ℝ) ^ k)⁻¹) (by positivity) 0
  simp only [add_zero, Complex.zero_re, Complex.zero_im] at himg
  unfold closedDyadicSubsquare
  rw [himg]
  obtain ⟨h1, h2⟩ := hcoord a i i' hi
  obtain ⟨h3, h4⟩ := hcoord b j j' hj
  rw [h1, h2, h3, h4]

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Weyl-scaled internal distances near a point.** Let `𝔇` be a γ-LQG metric, `h` a whole-plane GFF, `r > 0`,
`z ∈ ℂ`, and let `E` be a random function which is almost surely the Weyl scaling `e^{ξ f} · D_h` of `D_h` by a
deterministic weight `f`. Then almost surely, simultaneously for every set `U`, every `B` with `ξ f ≤ B` on `r U + z`,
and all `u, v ∈ ℂ`,
`E(r u + z, r v + z; r U + z) ≤ e^{B + ξ (h_r(z) + Q log r)} · D_{h'}(u, v; U)`, where `h' = h(r · + z) - h_r(z)`
(`recentredPairing`) is again a whole-plane GFF (`isWholePlaneGFF_recentredPairing`). -/
theorem IsLQGMetric.ae_internalMetric_weylScaling_affine_image_le (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) {E : Ω → ℂ → ℂ → ℝ} {f : ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (𝔇 (hC ω)) ξ f x y) :
    ∀ᵐ ω ∂P, ∀ (U : Set ℂ) (B : ℝ), (∀ x ∈ U, ξ * f ((r : ℂ) * x + z) ≤ B) → ∀ u v : ℂ,
      internalMetric (E ω) ((fun x : ℂ => (r : ℂ) * x + z) '' U) (r * u + z) (r * v + z) ≤
        ENNReal.ofReal (Real.exp (B + ξ * (hcirc ω r z + lqgQ γ * Real.log r))) *
          internalMetric (𝔇 (recentredPairing hC hcirc r z ω)) U u v := by
  filter_upwards [h𝔇.ae_isEuclideanLengthMetric_self hG, hE, h𝔇.ae_internalMetric_scaling hG hr z]
    with ω hD hEω hsc U B hB u v
  calc internalMetric (E ω) ((fun x : ℂ => (r : ℂ) * x + z) '' U) (r * u + z) (r * v + z)
      ≤ ENNReal.ofReal (Real.exp B) *
          internalMetric (𝔇 (hC ω)) ((fun x : ℂ => (r : ℂ) * x + z) '' U) (r * u + z) (r * v + z) :=
        internalMetric_le_of_weylScaling hD hEω (by rintro _ ⟨x, hx, rfl⟩; exact hB x hx) _ _
    _ = _ := by
        rw [hsc U u v, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

end LatticeProb.LQG
