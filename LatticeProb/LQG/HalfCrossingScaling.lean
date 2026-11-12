import LatticeProb.LQG.LQGMetricInternalScaling
import LatticeProb.LQG.InternalMetricHalfCrossings

/-!
# Scaling of short half crossings of rectangles

If `D(r x + z, r y + z) = K · D'(x, y)` for real `r > 0`, `z ∈ ℂ` and `K ≥ 0`, the affine map `x ↦ r x + z` carries a
left-right (top-bottom) crossing of a closed rectangle to a left-right (top-bottom) crossing of the image rectangle, and
it multiplies lengths by `K`. Hence half crossings of a rectangle of `D'`-length at most `L` (`HasShortHalfCrossings`)
give half crossings of the image rectangle of `D`-length at most `K L`.

For a γ-LQG metric and a whole-plane GFF `h`, the scaling relation about a point (`IsLQGMetric.ae_scaling`) gives, for
each `r > 0` and `z ∈ ℂ`, almost surely: half crossings of a rectangle of length at most `L` for the metric of the
recentred field `h' = h(r · + z) - h_r(z)` give half crossings of the image rectangle of `D_h`-length at most
`e^{ξ (h_r(z) + Q log r)} L`. Consequently the probability that the image rectangle has no half crossings of
`D_h`-length at most `l` is at most the probability that the original rectangle has no half crossings of `D_{h'}`-length
at most `A`, plus the probability that `e^{ξ (h_r(z) + Q log r)} A > l` (the reduction to unit scale in
Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020, proof of Proposition 3.10, Step 1). These are outer measures: no measurability
of the crossing events is needed.

Main results:
* `IsLeftRightCrossing.map_affine`, `IsTopBottomCrossing.map_affine`: crossings under `x ↦ r x + z`.
* `HasShortHalfCrossings.of_affine`: short half crossings under `x ↦ r x + z`.
* `IsLQGMetric.ae_hasShortHalfCrossings_scaling`: the almost sure transfer for the γ-LQG metric.
* `IsLQGMetric.measure_not_hasShortHalfCrossings_le`: the tail bound for the image of a rectangle.
* `IsLQGMetric.measure_not_hasShortHalfCrossings_dyadic_le`: the tail bound for a closed dyadic subsquare of a square,
  in terms of the unit square `[0, 1]²` for the recentred field.
-/

namespace LatticeProb.LQG

open MeasureTheory LatticeProb.Gauss Set
open scoped ENNReal

section General

variable {D D' : ℂ → ℂ → ℝ} {K r : ℝ}

/-- The affine map `x ↦ r x + z` with `r > 0` real maps the closed rectangle `[x₀, x₁] × [y₀, y₁]` into the closed
rectangle `[r x₀ + Re z, r x₁ + Re z] × [r y₀ + Im z, r y₁ + Im z]`. -/
theorem affine_mem_reProdIm (hr : 0 < r) (z : ℂ) {x₀ x₁ y₀ y₁ : ℝ} {w : ℂ}
    (hw : w ∈ Icc x₀ x₁ ×ℂ Icc y₀ y₁) :
    (r : ℂ) * w + z ∈ Icc (r * x₀ + z.re) (r * x₁ + z.re) ×ℂ Icc (r * y₀ + z.im) (r * y₁ + z.im) := by
  rw [Complex.mem_reProdIm] at hw ⊢
  obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := hw
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  exact ⟨⟨by gcongr, by gcongr⟩, ⟨by gcongr, by gcongr⟩⟩

/-- The image of a left-right crossing of `[x₀, x₁] × [y₀, y₁]` under `x ↦ r x + z` (`r > 0` real) is a left-right
crossing of the image rectangle. -/
theorem IsLeftRightCrossing.map_affine (hr : 0 < r) (z : ℂ) (hc : Continuous fun x : ℂ => (r : ℂ) * x + z)
    {x₀ x₁ y₀ y₁ : ℝ} {a b : ℂ} {P : Path a b} (hP : IsLeftRightCrossing x₀ x₁ y₀ y₁ P) :
    IsLeftRightCrossing (r * x₀ + z.re) (r * x₁ + z.re) (r * y₀ + z.im) (r * y₁ + z.im) (P.map hc) := by
  obtain ⟨hP, ha, hb⟩ := hP
  refine ⟨fun t => affine_mem_reProdIm hr z (hP t), ?_, ?_⟩
  · simp [ha]
  · simp [hb]

/-- The image of a top-bottom crossing of `[x₀, x₁] × [y₀, y₁]` under `x ↦ r x + z` (`r > 0` real) is a top-bottom
crossing of the image rectangle. -/
theorem IsTopBottomCrossing.map_affine (hr : 0 < r) (z : ℂ) (hc : Continuous fun x : ℂ => (r : ℂ) * x + z)
    {x₀ x₁ y₀ y₁ : ℝ} {a b : ℂ} {P : Path a b} (hP : IsTopBottomCrossing x₀ x₁ y₀ y₁ P) :
    IsTopBottomCrossing (r * x₀ + z.re) (r * x₁ + z.re) (r * y₀ + z.im) (r * y₁ + z.im) (P.map hc) := by
  obtain ⟨hP, ha, hb⟩ := hP
  refine ⟨fun t => affine_mem_reProdIm hr z (hP t), ?_, ?_⟩
  · simp [ha]
  · simp [hb]

/-- **Short half crossings under an affine map.** If `D(r x + z, r y + z) = K · D'(x, y)` with `r > 0` real and
`K ≥ 0`, and the rectangle `[x₀, x₁] × [y₀, y₁]` has half crossings of `D'`-length at most `L`, then its image
`[X₀, X₁] × [Y₀, Y₁]` under `x ↦ r x + z` has half crossings of `D`-length at most `K L`. -/
theorem HasShortHalfCrossings.of_affine (hr : 0 < r) (z : ℂ) (hK : 0 ≤ K)
    (hDe : ∀ x y : ℂ, D (r * x + z) (r * y + z) = K * D' x y) {x₀ x₁ y₀ y₁ X₀ X₁ Y₀ Y₁ : ℝ}
    (hX₀ : X₀ = r * x₀ + z.re) (hX₁ : X₁ = r * x₁ + z.re) (hY₀ : Y₀ = r * y₀ + z.im)
    (hY₁ : Y₁ = r * y₁ + z.im) {L : ℝ≥0∞} (h : HasShortHalfCrossings D' x₀ x₁ y₀ y₁ L) :
    HasShortHalfCrossings D X₀ X₁ Y₀ Y₁ (ENNReal.ofReal K * L) := by
  subst hX₀ hX₁ hY₀ hY₁
  have hc : Continuous fun x : ℂ => (r : ℂ) * x + z := by fun_prop
  have hlen : ∀ {u v : ℂ} (Q : Path u v), pathLength D' Q ≤ L →
      pathLength D (Q.map hc) ≤ ENNReal.ofReal K * L := fun Q hQ => by
    rw [pathLength_map_of_eq_mul (e := fun x : ℂ => (r : ℂ) * x + z) hK hDe hc Q]
    gcongr
  have hmy : r * ((y₀ + y₁) / 2) + z.im = (r * y₀ + z.im + (r * y₁ + z.im)) / 2 := by ring
  have hmx : r * ((x₀ + x₁) / 2) + z.re = (r * x₀ + z.re + (r * x₁ + z.re)) / 2 := by ring
  obtain ⟨⟨u₁, v₁, P₁, h₁, l₁⟩, ⟨u₂, v₂, P₂, h₂, l₂⟩, ⟨u₃, v₃, P₃, h₃, l₃⟩, ⟨u₄, v₄, P₄, h₄, l₄⟩⟩ := h
  refine ⟨⟨_, _, P₁.map hc, ?_, hlen P₁ l₁⟩, ⟨_, _, P₂.map hc, ?_, hlen P₂ l₂⟩,
    ⟨_, _, P₃.map hc, ?_, hlen P₃ l₃⟩, ⟨_, _, P₄.map hc, ?_, hlen P₄ l₄⟩⟩
  · rw [← hmy]; exact h₁.map_affine hr z hc
  · rw [← hmy]; exact h₂.map_affine hr z hc
  · rw [← hmx]; exact h₃.map_affine hr z hc
  · rw [← hmx]; exact h₄.map_affine hr z hc

end General

section LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Scaling of short half crossings for the γ-LQG metric.** For a γ-LQG metric `𝔇`, a whole-plane GFF `h`, `r > 0`
and `z ∈ ℂ`, almost surely, for every rectangle `[x₀, x₁] × [y₀, y₁]` and every `L`: if the rectangle has half crossings
of length at most `L` for the metric of `h' = h(r · + z) - h_r(z)` (`recentredPairing`), then its image under
`x ↦ r x + z` has half crossings of `D_h`-length at most `e^{ξ (h_r(z) + Q log r)} L`. -/
theorem IsLQGMetric.ae_hasShortHalfCrossings_scaling (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ (x₀ x₁ y₀ y₁ : ℝ) (L : ℝ≥0∞),
      HasShortHalfCrossings (𝔇 (recentredPairing hC hcirc r z ω)) x₀ x₁ y₀ y₁ L →
        HasShortHalfCrossings (𝔇 (hC ω)) (r * x₀ + z.re) (r * x₁ + z.re) (r * y₀ + z.im) (r * y₁ + z.im)
          (ENNReal.ofReal (Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r))) * L) := by
  filter_upwards [h𝔇.ae_scaling hG hr z] with ω hω x₀ x₁ y₀ y₁ L h
  exact h.of_affine hr z (Real.exp_pos _).le hω rfl rfl rfl rfl

/-- **Tail of the half-crossing lengths of a rectangle at scale `r` around `z`.** For a γ-LQG metric `𝔇`, a whole-plane
GFF `h`, `r > 0` and `z ∈ ℂ`, let `[X₀, X₁] × [Y₀, Y₁]` be the image of `[x₀, x₁] × [y₀, y₁]` under `x ↦ r x + z`. For
all `A, l`, the probability that the image has no half crossings of `D_h`-length at most `l` is at most the probability
that `[x₀, x₁] × [y₀, y₁]` has no half crossings of length at most `A` for the metric of `h' = h(r · + z) - h_r(z)`, plus
the probability that `e^{ξ (h_r(z) + Q log r)} A > l`. -/
theorem IsLQGMetric.measure_not_hasShortHalfCrossings_le (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) {x₀ x₁ y₀ y₁ X₀ X₁ Y₀ Y₁ : ℝ}
    (hX₀ : X₀ = r * x₀ + z.re) (hX₁ : X₁ = r * x₁ + z.re) (hY₀ : Y₀ = r * y₀ + z.im)
    (hY₁ : Y₁ = r * y₁ + z.im) (A l : ℝ≥0∞) :
    P {ω | ¬ HasShortHalfCrossings (𝔇 (hC ω)) X₀ X₁ Y₀ Y₁ l} ≤
      P {ω | ¬ HasShortHalfCrossings (𝔇 (recentredPairing hC hcirc r z ω)) x₀ x₁ y₀ y₁ A} +
        P {ω | l < ENNReal.ofReal (Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r))) * A} := by
  subst hX₀ hX₁ hY₀ hY₁
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | ¬ HasShortHalfCrossings (𝔇 (hC ω)) (r * x₀ + z.re) (r * x₁ + z.re)
      (r * y₀ + z.im) (r * y₁ + z.im) l} →
      ω ∈ {ω | ¬ HasShortHalfCrossings (𝔇 (recentredPairing hC hcirc r z ω)) x₀ x₁ y₀ y₁ A} ∪
        {ω | l < ENNReal.ofReal (Real.exp (ξ * (hcirc ω r z + lqgQ γ * Real.log r))) * A} := by
    filter_upwards [h𝔇.ae_hasShortHalfCrossings_scaling hG hr z] with ω hω hl
    by_contra hmem
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_lt] at hmem hl
    exact hl ((hω x₀ x₁ y₀ y₁ A hmem.1).mono hmem.2)
  exact (measure_mono_ae hsub).trans (measure_union_le _ _)

/-- **Tail of the half-crossing lengths of a closed dyadic subsquare.** For a γ-LQG metric `𝔇`, a whole-plane GFF `h`,
a square `[a, a + s] × [b, b + s]` with `s > 0` and its closed dyadic subsquare of level `n` and index `(i, j)`, of side
`r = s / 2ⁿ` and bottom-left corner `z = (a + i r, b + j r)`: for all `A, l`, the probability that the subsquare has no
half crossings of `D_h`-length at most `l` is at most the probability that the unit square `[0, 1]²` has no half
crossings of length at most `A` for the metric of `h' = h(r · + z) - h_r(z)`, plus the probability that
`e^{ξ (h_r(z) + Q log r)} A > l`. -/
theorem IsLQGMetric.measure_not_hasShortHalfCrossings_dyadic_le (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (n i j : ℕ) (A l : ℝ≥0∞) :
    P {ω | ¬ HasShortHalfCrossings (𝔇 (hC ω)) (a + i * (s / 2 ^ n)) (a + (i + 1) * (s / 2 ^ n))
        (b + j * (s / 2 ^ n)) (b + (j + 1) * (s / 2 ^ n)) l} ≤
      P {ω | ¬ HasShortHalfCrossings
          (𝔇 (recentredPairing hC hcirc (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ ω)) 0 1 0 1 A} +
        P {ω | l < ENNReal.ofReal (Real.exp (ξ * (hcirc ω (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ +
          lqgQ γ * Real.log (s / 2 ^ n)))) * A} :=
  h𝔇.measure_not_hasShortHalfCrossings_le hG (by positivity) _
    (show _ = s / 2 ^ n * 0 + (a + i * (s / 2 ^ n)) by ring)
    (show _ = s / 2 ^ n * 1 + (a + i * (s / 2 ^ n)) by ring)
    (show _ = s / 2 ^ n * 0 + (b + j * (s / 2 ^ n)) by ring)
    (show _ = s / 2 ^ n * 1 + (b + j * (s / 2 ^ n)) by ring) A l

end LQG

end LatticeProb.LQG
