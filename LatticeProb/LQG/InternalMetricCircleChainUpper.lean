import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_1Up
import LatticeProb.LQG.LQGMetricMeasurable

/-! # Chaining along a path through good circles: the upper bound for the internal distance of two sets

Let `D` be a Euclidean length metric on `ℂ`, `g` a field with circle averages `h_r(w)`, and `good w r` a predicate on
circles `∂B_r(w)` which implies that the internal diameter of the circle in the annulus `A_{r/2, 2r}(w)` is at most
`C 𝔠_r e^{ξ h_r(w)}`. Suppose that a path in `𝕣 U₀` joining `𝕣 K₁` to `𝕣 K₂` lies in the union of the good circles
`∂B_r(w)`, `w` in the lattice `(ε² 𝕣 / 4) ℤ²` near `𝕣 U₀`, `r ∈ [ε² 𝕣, ε 𝕣] ∩ {2^{-k} 𝕣}`, with `B̄_{2r}(w) ⊆ 𝕣 U₀`, and
that the circle averages of `g` at these circles are controlled by those at `∂B_𝕣(0)` (`TailOK`). Then the internal
distance of `𝕣 K₁` and `𝕣 K₂` in `𝕣 U₀` is at most
`B ε^{-6} · C · Λ ε^{-(2Λ + ξ q)} 𝔠_𝕣 e^{ξ h_𝕣(0)}`
(the number of circles needed times the bound for one of them, by the triangle inequality for the internal metric).

Main result:
* `IsEuclideanLengthMetric.iInf_internalMetric_scaleSet_le_of_goodCircles`.
-/

namespace LatticeProb.LQG

open Set Metric LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS LQGMetric.DFGPS.P31 LQGDimension.LFPPRecords
open scoped ENNReal

/-- The image of an open set under `w ↦ 𝕣 w + 0`, `𝕣 > 0`, is open. -/
theorem isOpen_scaleSet_zero {𝕣 : ℝ} (h𝕣 : 0 < 𝕣) {K : Set ℂ} (hK : IsOpen K) : IsOpen (scaleSet 𝕣 0 K) := by
  have hne : ((𝕣 : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 h𝕣.ne'
  have h := (Homeomorph.mulLeft₀ (𝕣 : ℂ) hne).isOpenMap K hK
  convert h using 1
  ext x
  simp [scaleSet]

/-- **Upper bound of the internal distance by chaining through good circles.** See the module docstring. -/
theorem IsEuclideanLengthMetric.iInf_internalMetric_scaleSet_le_of_goodCircles {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {g : DistC} {c : ℝ → ℝ} {ξ Λ q ε 𝕣 C R₀ : ℝ} (hξ : 0 < ξ) (hΛ : 1 < Λ)
    (hc : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ))
    (hcpos : ∀ r, 0 < r → 0 < c r) (hε0 : 0 < ε) (hε1 : ε < 1) (h𝕣 : 0 < 𝕣) (hC : 1 < C)
    (hR₀ : 0 < R₀) {U₀ K₁ K₂ : Set ℂ} (hU₀ : U₀ ⊆ ball 0 R₀) (hU₀o : IsOpen U₀) {good : ℂ → ℝ → Prop}
    (hgd : ∀ w r, good w r → ∀ p ∈ sphere w r, ∀ p' ∈ sphere w r,
      internalMetric D {z : ℂ | r / 2 < ‖z - w‖ ∧ ‖z - w‖ < 2 * r} p p' ≤
        ENNReal.ofReal (C * scaleFac ξ c g r w))
    (h35 : ∃ x ∈ scaleSet 𝕣 0 K₁, ∃ y ∈ scaleSet 𝕣 0 K₂, ∃ γ : Path x y, ∀ t,
        γ t ∈ scaleSet 𝕣 0 U₀ ∧ ∃ w : ℂ, ∃ r : ℝ, w ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 U₀) ∧
          w ∈ gridPts (ε ^ 2 * 𝕣 / 4) ∧ (∃ k : ℕ, r = ((2 : ℝ) ^ k)⁻¹ * 𝕣) ∧
          ε ^ 2 * 𝕣 ≤ r ∧ r ≤ ε * 𝕣 ∧ good w r ∧ γ t ∈ sphere w r ∧
          closedBall w (2 * r) ⊆ scaleSet 𝕣 0 U₀)
    (htail : TailOK g q ε 𝕣 (R₀ + 1)) :
    (⨅ u ∈ scaleSet 𝕣 0 K₁, ⨅ v ∈ scaleSet 𝕣 0 K₂, internalMetric D (scaleSet 𝕣 0 U₀) u v) ≤
      ENNReal.ofReal ((2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) / ε ^ 6 *
        (C * (Λ * ε ^ (-(2 * Λ + ξ * q)) * scaleFac ξ c g 𝕣 0))) := by
  classical
  have hnn : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    have h2 := hD.symm y x
    have h3 := hD.self_eq_zero x
    linarith
  obtain ⟨x, hx, y, hy, γ, hγ⟩ := h35
  set m := ε ^ 2 * 𝕣 / 4 with hm_def
  have hm : 0 < m := by positivity
  set R := R₀ + 1
  set V := scaleSet 𝕣 0 U₀
  set L := C * (Λ * ε ^ (-(2 * Λ + ξ * q)) * scaleFac ξ c g 𝕣 0)
  set I0 := gridBox m 0 (R * 𝕣) ×ˢ Finset.range (⌊(ε ^ 2)⁻¹⌋₊ + 1)
  set Cs : (ℤ × ℤ) × ℕ → Set ℂ := fun i => sphere (gridPt m i.1) (((2 : ℝ) ^ i.2)⁻¹ * 𝕣)
  set Q : (ℤ × ℤ) × ℕ → Prop := fun i =>
    good (gridPt m i.1) (((2 : ℝ) ^ i.2)⁻¹ * 𝕣) ∧
      closedBall (gridPt m i.1) (2 * (((2 : ℝ) ^ i.2)⁻¹ * 𝕣)) ⊆ V ∧
      ε ^ 2 ≤ ((2 : ℝ) ^ i.2)⁻¹ ∧ ((2 : ℝ) ^ i.2)⁻¹ ≤ ε ∧ ‖gridPt m i.1‖ < R * 𝕣
  set I := I0.filter Q
  have hS : IsPreconnected (range γ) := isPreconnected_range γ.continuous
  have hxS : x ∈ range γ := ⟨0, γ.source⟩
  have hyS : y ∈ range γ := ⟨1, γ.target⟩
  have hxV : x ∈ V := by simpa using (hγ 0).1
  have hcov : ∀ p ∈ range γ, ∃ i ∈ I, p ∈ Cs i := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨_, w, r, hwth, ⟨a, b, rfl⟩, ⟨k, rfl⟩, hr1, hr2, hgoodw, hsph, hball⟩ := hγ t
    have hpt : gridPt m (a, b) = ⟨a * m, b * m⟩ := rfl
    have hwn : ‖(⟨a * m, b * m⟩ : ℂ)‖ < R * 𝕣 := by
      obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.1 hwth
      have hzn := norm_of_mem_scaleSet h𝕣 hU₀ hz
      have : ‖(⟨a * m, b * m⟩ : ℂ)‖ ≤ ‖z‖ + dist (⟨a * m, b * m⟩ : ℂ) z := by
        rw [dist_eq_norm]
        calc _ = ‖z + ((⟨a * m, b * m⟩ : ℂ) - z)‖ := by rw [add_sub_cancel]
          _ ≤ _ := norm_add_le _ _
      have : ε * 𝕣 ≤ 𝕣 := by nlinarith
      simp only [R]; nlinarith
    have hδ1 : ε ^ 2 ≤ ((2 : ℝ) ^ k)⁻¹ := le_of_mul_le_mul_right hr1 h𝕣
    have hδ2 : ((2 : ℝ) ^ k)⁻¹ ≤ ε := le_of_mul_le_mul_right hr2 h𝕣
    refine ⟨((a, b), k), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_gridBox hm ?_,
      Finset.mem_range.2 (Nat.lt_succ_of_le (le_floor_of_dyadic hε0 hδ1))⟩, ?_⟩, ?_⟩
    · rw [sub_zero, hpt]; exact hwn.le
    · exact ⟨by rw [hpt]; exact hgoodw, by rw [hpt]; exact hball, hδ1, hδ2, by rw [hpt]; exact hwn⟩
    · show γ t ∈ sphere (gridPt m (a, b)) _
      rw [hpt]; exact hsph
  have hdiam : ∀ i ∈ I, ∀ p ∈ Cs i ∩ range γ, ∀ p' ∈ Cs i ∩ range γ,
      internalMetric D V p p' ≤ ENNReal.ofReal L := by
    intro i hi p hp p' hp'
    obtain ⟨-, hgoodi, hball, hδ1, hδ2, hwn⟩ := Finset.mem_filter.1 hi
    set w := gridPt m i.1
    set r := ((2 : ℝ) ^ i.2)⁻¹ * 𝕣
    have hwg : w ∈ gridPts (ε ^ 2 * 𝕣 / 4) := ⟨i.1.1, i.1.2, rfl⟩
    obtain ⟨-, hb2⟩ := scaleFac_bounds hξ hΛ hc hcpos hε0 hε1 h𝕣 hδ1 hδ2
      (htail w hwn hwg i.2 hδ1 hδ2)
    have hann : {z : ℂ | r / 2 < ‖z - w‖ ∧ ‖z - w‖ < 2 * r} ⊆ V := fun z hz =>
      hball (mem_closedBall.2 (by rw [dist_eq_norm]; exact hz.2.le))
    calc internalMetric D V p p' ≤ internalMetric D {z : ℂ | r / 2 < ‖z - w‖ ∧ ‖z - w‖ < 2 * r} p p' :=
          internalMetric_anti D hann p p'
      _ ≤ ENNReal.ofReal (C * scaleFac ξ c g r w) := hgd w r hgoodi p hp.1 p' hp'.1
      _ ≤ ENNReal.ofReal L :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hb2 (by linarith))
  have hchain := chain_bound I hS Cs (fun _ => isClosed_sphere) (internalMetric D V)
    (fun a b c => hD.internalMetric_triangle V a b c) (ENNReal.ofReal L) hcov hdiam hxS hyS
    (hD.internalMetric_self_of_mem_open hnn (isOpen_scaleSet_zero h𝕣 hU₀o) hxV)
  have hcard : ((I.card : ℝ≥0∞) + 1) ≤
      ENNReal.ofReal ((2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) / ε ^ 6) := by
    have h1 : (I.card : ℝ) + 1 ≤ (I0.card : ℝ) + 1 := by
      have := Finset.card_filter_le I0 Q
      exact_mod_cast Nat.add_le_add_right this 1
    have h2 := card_circles_le hε0 hε1 h𝕣 (by positivity : (0 : ℝ) ≤ R)
    rw [show ((I.card : ℝ≥0∞) + 1) = ENNReal.ofReal ((I.card : ℝ) + 1) by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]]
    exact ENNReal.ofReal_le_ofReal (h1.trans h2)
  have hL : 0 ≤ (2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) / ε ^ 6 := by positivity
  calc (⨅ u ∈ scaleSet 𝕣 0 K₁, ⨅ v ∈ scaleSet 𝕣 0 K₂, internalMetric D V u v) ≤ internalMetric D V x y :=
        iInf₂_le_of_le x hx (iInf₂_le_of_le y hy le_rfl)
    _ ≤ ((I.card : ℝ≥0∞) + 1) * ENNReal.ofReal L := hchain
    _ ≤ ENNReal.ofReal ((2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) / ε ^ 6) * ENNReal.ofReal L := by
        gcongr
    _ = _ := (ENNReal.ofReal_mul hL).symm

end LatticeProb.LQG
