import LatticeProb.LQG.InternalMetricSquareScalingWeyl

/-!
# Internal diameters of a sequence of squares, by the Borel-Cantelli lemma

Let `𝔇` be a γ-LQG metric and `h` a whole-plane GFF. Consider squares `Sₖ = [Re cₖ, Re cₖ + tₖ] × [Im cₖ, Im cₖ + tₖ]`
with `tₖ > 0`. By LQG coordinate change, the internal metric of `D_h` on `Sₖ` is `e^{ξ (h_{tₖ}(cₖ) + Q log tₖ)}` times the
internal metric of `D_{h'}` on the closed unit square, where `h' = h(tₖ · + cₖ) - h_{tₖ}(cₖ)` is again a whole-plane GFF
(`IsLQGMetric.ae_internalMetric_scaling`).

* If the unit-square internal diameter of every whole-plane GFF exceeds `e^{εk}` with probability at most `ψₖ`,
  `∑ ψₖ < ∞`, and the events `{ξ (h_{tₖ}(cₖ) + Q log tₖ) > aₖ}` have summable probabilities, then almost surely the
  internal diameter of `Sₖ` for `D_h` is at most `e^{aₖ + εk}` for all large `k`
  (`IsLQGMetric.ae_eventually_internalMetric_square_le`).
* Under the same tail bound, almost surely every `Sₖ` has finite internal diameter for `D_h`
  (`IsLQGMetric.ae_forall_exists_internalMetric_square_le`).

These are the probabilistic estimates over the dyadic shells around a point in the proof that the LQG metric with a
logarithmic singularity has finite internal diameters (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380,
Proposition 3.17, last paragraph of the proof).
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Eventual internal-diameter bound over a sequence of squares.** Let `𝔇` be a γ-LQG metric and `h` a whole-plane
GFF. Suppose that for every whole-plane GFF the internal diameter of the closed unit square exceeds `e^{εk}` with
probability at most `ψₖ`, where `∑ ψₖ < ∞`. Let `Sₖ = [Re cₖ, Re cₖ + tₖ] × [Im cₖ, Im cₖ + tₖ]` with `tₖ > 0`, and let
`aₖ` be such that `∑ₖ P[ξ (h_{tₖ}(cₖ) + Q log tₖ) > aₖ] < ∞`. Then almost surely, for all large `k`,
`D_h(u, v; Sₖ) ≤ e^{aₖ + εk}` for all `u, v ∈ Sₖ`. -/
theorem IsLQGMetric.ae_eventually_internalMetric_square_le (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {ε : ℝ} {ψ : ℕ → ℝ≥0∞} (hψ : ∑' k, ψ k ≠ ⊤)
    (htail : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' → ∀ k : ℕ,
      P {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
        internalMetric (𝔇 (hC' ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
          ENNReal.ofReal (Real.exp (ε * k))} ≤ ψ k)
    {t : ℕ → ℝ} (ht : ∀ k, 0 < t k) {c : ℕ → ℂ} {a : ℕ → ℝ}
    (ha : ∑' k, P {ω | a k < ξ * (hcirc ω (t k) (c k) + lqgQ γ * Real.log (t k))} ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      ∀ u ∈ Icc (c k).re ((c k).re + t k) ×ℂ Icc (c k).im ((c k).im + t k),
      ∀ v ∈ Icc (c k).re ((c k).re + t k) ×ℂ Icc (c k).im ((c k).im + t k),
        internalMetric (𝔇 (hC ω)) (Icc (c k).re ((c k).re + t k) ×ℂ Icc (c k).im ((c k).im + t k)) u v ≤
          ENNReal.ofReal (Real.exp (a k + ε * k)) := by
  -- the bad events at scale `k`: a large unit-square diameter for the recentred field, or a large scale factor
  let bad1 : ℕ → Set Ω := fun k => {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
    internalMetric (𝔇 (recentredPairing hC hcirc (t k) (c k) ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
      ENNReal.ofReal (Real.exp (ε * k))}
  let bad2 : ℕ → Set Ω := fun k => {ω | a k < ξ * (hcirc ω (t k) (c k) + lqgQ γ * Real.log (t k))}
  have h1 : ∀ k, P (bad1 k) ≤ ψ k := fun k =>
    htail _ _ (isWholePlaneGFF_recentredPairing hG (ht k) (c k)) k
  have hsum : ∑' k, P (bad1 k ∪ bad2 k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hψ, ha⟩) ?_
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun k => (measure_union_le _ _).trans (add_le_add (h1 k) le_rfl)
  have hsc : ∀ᵐ ω ∂P, ∀ k, ∀ (U : Set ℂ) (u v : ℂ),
      internalMetric (𝔇 (hC ω)) ((fun x : ℂ => (t k : ℂ) * x + c k) '' U) (t k * u + c k) (t k * v + c k) =
        ENNReal.ofReal (Real.exp (ξ * (hcirc ω (t k) (c k) + lqgQ γ * Real.log (t k)))) *
          internalMetric (𝔇 (recentredPairing hC hcirc (t k) (c k) ω)) U u v :=
    ae_all_iff.2 fun k => h𝔇.ae_internalMetric_scaling hG (ht k) (c k)
  filter_upwards [ae_eventually_notMem hsum, hsc] with ω hω hscω
  filter_upwards [hω] with k hk
  rw [Set.mem_union, not_or] at hk
  have hunit : ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      internalMetric (𝔇 (recentredPairing hC hcirc (t k) (c k) ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
        ENNReal.ofReal (Real.exp (ε * k)) := by
    by_contra hcon
    exact hk.1 hcon
  have hfac : ξ * (hcirc ω (t k) (c k) + lqgQ γ * Real.log (t k)) ≤ a k := not_lt.1 hk.2
  intro u hu v hv
  rw [← affine_image_unitSquare (ht k) (c k)] at hu hv ⊢
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  refine (hscω k _ u' v').le.trans ?_
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr ?_ * ?_
  · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hfac)
  · exact hunit u' hu' v' hv'

/-- **Finite internal diameters of a sequence of squares.** Let `𝔇` be a γ-LQG metric and `h` a whole-plane GFF.
Suppose that for every whole-plane GFF the internal diameter of the closed unit square exceeds `e^{εk}` with probability
at most `ψₖ`, where `∑ ψₖ < ∞`. Then for squares `Sₖ = [Re cₖ, Re cₖ + tₖ] × [Im cₖ, Im cₖ + tₖ]` with `tₖ > 0`, almost
surely every `Sₖ` has finite internal diameter for `D_h`. -/
theorem IsLQGMetric.ae_forall_exists_internalMetric_square_le (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {ε : ℝ} {ψ : ℕ → ℝ≥0∞} (hψ : ∑' k, ψ k ≠ ⊤)
    (htail : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' → ∀ k : ℕ,
      P {ω | ¬ ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
        internalMetric (𝔇 (hC' ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
          ENNReal.ofReal (Real.exp (ε * k))} ≤ ψ k)
    {t : ℕ → ℝ} (ht : ∀ k, 0 < t k) (c : ℕ → ℂ) :
    ∀ᵐ ω ∂P, ∀ k, ∃ A : ℝ,
      ∀ u ∈ Icc (c k).re ((c k).re + t k) ×ℂ Icc (c k).im ((c k).im + t k),
      ∀ v ∈ Icc (c k).re ((c k).re + t k) ×ℂ Icc (c k).im ((c k).im + t k),
        internalMetric (𝔇 (hC ω)) (Icc (c k).re ((c k).re + t k) ×ℂ Icc (c k).im ((c k).im + t k)) u v ≤
          ENNReal.ofReal A := by
  have hψ0 : Tendsto ψ atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hψ
  refine ae_all_iff.2 fun k => ?_
  -- almost surely the unit-square diameter of the recentred field is at most `e^{εj}` for some `j`
  have hfin : ∀ᵐ ω ∂P, ∃ j : ℕ, ∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
      internalMetric (𝔇 (recentredPairing hC hcirc (t k) (c k) ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤
        ENNReal.ofReal (Real.exp (ε * j)) := by
    rw [ae_iff]
    refine le_antisymm (ge_of_tendsto' hψ0 fun j => ?_) zero_le
    refine (measure_mono fun ω hω => ?_).trans
      (htail _ _ (isWholePlaneGFF_recentredPairing hG (ht k) (c k)) j)
    exact fun hj => hω ⟨j, hj⟩
  filter_upwards [hfin, h𝔇.ae_internalMetric_scaling hG (ht k) (c k)] with ω hω hscω
  obtain ⟨j, hj⟩ := hω
  refine ⟨Real.exp (ξ * (hcirc ω (t k) (c k) + lqgQ γ * Real.log (t k))) * Real.exp (ε * j), ?_⟩
  intro u hu v hv
  rw [← affine_image_unitSquare (ht k) (c k)] at hu hv ⊢
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  refine (hscω _ u' v').le.trans ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr
  exact hj u' hu' v' hv'

end LatticeProb.LQG
