import LatticeProb.LQG.InternalMetricGoodCircle
import LatticeProb.LQG.AnnulusIterateNoGood
import LatticeProb.LQG.InternalMetricCircleChainUpper
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_4
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6

/-!
# Upper tail of the internal distance of two sets: one scale parameter

Let `𝔇` be a γ-LQG metric with Weyl exponent `ξ > 0`, `h` a whole-plane GFF with circle averages `h_r(z)`, and `U₀` a
bounded open connected set containing two compact connected non-singletons `K₁, K₂`. For `ε` small and `𝕣 > 0`, with
probability at least `1 - K ε^M - C₄ ε^{q²/8 - 4}`, the internal distance of `𝕣K₁` and `𝕣K₂` in `𝕣U₀` is at most
`A ε^{-(6 + 2Λ + ξ q)} 𝕣^{ξ Q} e^{ξ h_𝕣(0)}`, where `Q = 2/γ + γ/2` and `Λ ≥ max(1, ξ Q)` (upper bound of Proposition 3.1
of Ding-Dubédat-Gwynne-Pfeffer-Sheffield, one-parameter version of the proof).

The proof combines the following ingredients:
* the good-circle events (`goodCircleEvent`): for a probability `pt` close to one the diameter event of the circle of
  radius `r` about `w` in the annulus `A_{r/2,2r}(w)` holds with probability `≥ pt` and is almost surely local on
  the annulus (`IsLQGMetric.exists_le_measure_goodCircleEvent`, `IsLQGMetric.aeAnnulusEvent_goodCircleEvent`);
* the annulus iteration lemma: with probability `≥ 1 - K ε^M` the good circles cover the ball `B_{𝕣 ε^{-M}}(0)`
  (`exists_prob_not_goodCover_le_of_aeAnnulusEvent`);
* the circle average tail: with probability `≥ 1 - C₄ ε^{q²/8 - 4}`, `|h_r(w) - h_𝕣(0)| ≤ q log ε⁻¹` for all dyadic
  `r ∈ [ε²𝕣, ε𝕣]` and `w` in the grid `(ε²𝕣/4)ℤ²` of `B_{(R₀+1)𝕣}(0)` (`LQGMetric.DFGPS.lem3_4`);
* on the intersection of these events, a path from `𝕣K₁` to `𝕣K₂` in `𝕣U₀` through good circles (`lem3_5`), and the
  chaining estimate `IsEuclideanLengthMetric.iInf_internalMetric_scaleSet_le_of_goodCircles`.
-/

namespace LatticeProb.LQG

open MeasureTheory Set Metric LatticeProb.Gauss LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS LQGMetric.DFGPS.P31
open scoped ENNReal

/-- **One-parameter upper tail of the internal distance of two sets.** See the module docstring. The constants `A > 0, K, C₄,
ε₁` depend on the parameters and on the realization of the field only through `C₄`; the bound holds for every scale
`𝕣 > 0` and `ε ∈ (0, ε₁)`. -/
theorem IsLQGMetric.exists_measure_internalDist_gt_le {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hξ : 0 < ξ) (hγ : 0 < γ) {U₀ K₁ K₂ : Set ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hU₀b : U₀ ⊆ ball (0 : ℂ) R₀) (hU₀ : IsOpen U₀) (hU₀c : IsConnected U₀) (hK₁ : IsCompact K₁)
    (hK₁c : IsConnected K₁) (hK₁n : K₁.Nontrivial) (hK₂ : IsCompact K₂) (hK₂c : IsConnected K₂)
    (hK₂n : K₂.Nontrivial) (h₁U : K₁ ⊆ U₀) (h₂U : K₂ ⊆ U₀) {M q Λ : ℝ} (hM : 0 < M) (hq : 0 < q) (hΛ : 1 < Λ)
    (hΛξ : ξ * lqgQ γ ≤ Λ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {H : Ω → DistC}
    (hH : LQGMetric.IsWholePlaneGFF H P) (hHC : ∀ ψ : TestC, (fun ω => H ω ψ) =ᵐ[P] fun ω => hC ω ψ)
    (hHcirc : ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, hcirc ω r z = circleAvg (H ω) r z) :
    ∃ A K C₄ ε₁ : ℝ, 0 < A ∧ 0 < ε₁ ∧ ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₁,
      P {ω | ENNReal.ofReal (A * ε ^ (-(6 + 2 * Λ + ξ * q)) * (𝕣 ^ (ξ * lqgQ γ) * Real.exp (ξ * hcirc ω 𝕣 0))) <
          ⨅ u ∈ scaleSet 𝕣 0 K₁, ⨅ v ∈ scaleSet 𝕣 0 K₂,
            internalMetric (𝔇 (hC ω)) (scaleSet 𝕣 0 U₀) u v} ≤
        ENNReal.ofReal (K * ε ^ M) + ENNReal.ofReal (C₄ * ε ^ (q ^ 2 / 8 - 4)) := by
  classical
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hξQ : 0 ≤ ξ * lqgQ γ := mul_nonneg hξ.le hQ.le
  -- the scale function `c r = r ^ (ξ Q)`
  have hcpos : ∀ r : ℝ, 0 < r → 0 < r ^ (ξ * lqgQ γ) := fun r hr => Real.rpow_pos_of_pos hr _
  have hc : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      Λ⁻¹ * δ ^ Λ ≤ (δ * r) ^ (ξ * lqgQ γ) / r ^ (ξ * lqgQ γ) ∧
        (δ * r) ^ (ξ * lqgQ γ) / r ^ (ξ * lqgQ γ) ≤ Λ * δ ^ (-Λ) := by
    intro δ hδ r hr
    have e : (δ * r) ^ (ξ * lqgQ γ) / r ^ (ξ * lqgQ γ) = δ ^ (ξ * lqgQ γ) := by
      rw [Real.mul_rpow hδ.1.le hr.le]
      field_simp [(Real.rpow_pos_of_pos hr (ξ * lqgQ γ)).ne']
    rw [e]
    refine ⟨?_, ?_⟩
    · calc Λ⁻¹ * δ ^ Λ ≤ 1 * δ ^ (ξ * lqgQ γ) :=
            mul_le_mul (inv_le_one_of_one_le₀ hΛ.le) (Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ.2.le hΛξ)
              (Real.rpow_nonneg hδ.1.le _) zero_le_one
        _ = δ ^ (ξ * lqgQ γ) := one_mul _
    · calc δ ^ (ξ * lqgQ γ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2.le hξQ
        _ = 1 * 1 := by ring
        _ ≤ Λ * δ ^ (-Λ) :=
            mul_le_mul hΛ.le (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ.1 hδ.2.le (neg_nonpos.2 (by linarith)))
              zero_le_one (by linarith)
  -- constants from the three probabilistic ingredients
  obtain ⟨pt, hpt0, hpt1, K, ε₀, hε₀, Hcov⟩ :=
    exists_prob_not_goodCover_le_of_aeAnnulusEvent LQGMetric.LM.lmLem3_1a (ν := 1) one_pos hM
  obtain ⟨C, hC1, hCprob⟩ := h𝔇.exists_le_measure_goodCircleEvent hpt1
  obtain ⟨C₄, hC₄⟩ := lem3_4 hH (ν := 1) (q := q) (R := R₀ + 1) zero_le_one hq (by linarith)
  obtain ⟨ε₀', hε₀', H35⟩ := lem3_5 hU₀ hU₀c hK₁ hK₁c hK₁n hK₂ hK₂c hK₂n h₁U h₂U hM
  have hCpos : 0 < C := by linarith
  have hΛpos : 0 < Λ := by linarith
  refine ⟨(2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) * C * Λ, K, C₄, min (min ε₀ ε₀') 1, by positivity,
    lt_min (lt_min hε₀ hε₀') one_pos, ?_⟩
  intro 𝕣 h𝕣 ε hε
  obtain ⟨hε0, hεlt⟩ := hε
  simp only [lt_min_iff] at hεlt
  obtain ⟨⟨hεε₀, hεε₀'⟩, hε1⟩ := hεlt
  -- the good circle events
  have hGp : ∀ r w, 0 < r → ENNReal.ofReal pt ≤ P (goodCircleEvent γ ξ 𝔇 hC hcirc H C r w) :=
    fun r w hr => hCprob Ω P hC hcirc hG H hHcirc r hr w
  have hGl : ∀ r w, 0 < r → AeAnnulusEvent P H w r (goodCircleEvent γ ξ 𝔇 hC hcirc H C r w) :=
    fun r w hr => h𝔇.aeAnnulusEvent_goodCircleEvent hG hH hHC hHcirc hr w C
  have hB1 := Hcov P H hH 𝕣 h𝕣 ε ⟨hε0, hεε₀⟩ (goodCircleEvent γ ξ 𝔇 hC hcirc H C) hGp hGl
  -- the circle average tail
  set S : Set ℝ := {r | ∃ k : ℕ, r = ((2 : ℝ) ^ k)⁻¹ * 𝕣 ∧ ε ^ 2 * 𝕣 ≤ r ∧ r ≤ ε * 𝕣} with hS
  have hSc : S.Countable := (Set.countable_range (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹ * 𝕣)).mono
    (fun r hr => by obtain ⟨k, hk, _⟩ := hr; exact ⟨k, hk.symm⟩)
  have hSI : S ⊆ Icc (ε ^ ((1 : ℝ) + 1) * 𝕣) (ε * 𝕣) := by
    rintro r ⟨k, _, h1, h2⟩
    rw [P31.rpow_one_add_one]
    exact ⟨h1, h2⟩
  have hB2 := hC₄ 𝕣 h𝕣 ε ⟨hε0, hε1⟩ S hSc hSI
  have hexp : q ^ 2 / (2 * (1 + Real.sqrt 1) ^ 2) - 2 - 2 * 1 = q ^ 2 / 8 - 4 := by
    rw [Real.sqrt_one]; ring
  rw [hexp] at hB2
  -- almost sure facts
  have hae : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) ∧ hcirc ω 𝕣 0 = circleAvg (H ω) 𝕣 0 :=
    (h𝔇.ae_isEuclideanLengthMetric_self hG).and (hHcirc 𝕣 h𝕣 0)
  have hnull := ae_iff.1 hae
  -- the deterministic inclusion
  refine le_trans (measure_mono (t := {ω | ¬ GoodCover (fun w r => ω ∈ goodCircleEvent γ ξ 𝔇 hC hcirc H C r w) 1 M ε 𝕣} ∪
    {ω | ∃ w ∈ Metric.ball (0 : ℂ) ((R₀ + 1) * 𝕣) ∩ Blueprint.gridPts (ε ^ ((1 : ℝ) + 1) * 𝕣 / 4), ∃ r ∈ S,
      q * Real.log ε⁻¹ < |circleAvg (H ω) r w - circleAvg (H ω) 𝕣 0|} ∪
    {ω | ¬ (IsEuclideanLengthMetric (𝔇 (hC ω)) ∧ hcirc ω 𝕣 0 = circleAvg (H ω) 𝕣 0)}) ?_) ?_
  · intro ω hω
    by_contra hnot
    have hA : GoodCover (fun w r => ω ∈ goodCircleEvent γ ξ 𝔇 hC hcirc H C r w) 1 M ε 𝕣 := by
      by_contra h
      exact hnot (Or.inl (Or.inl h))
    have hB2' : ∀ w ∈ Metric.ball (0 : ℂ) ((R₀ + 1) * 𝕣) ∩ Blueprint.gridPts (ε ^ ((1 : ℝ) + 1) * 𝕣 / 4),
        ∀ r ∈ S, |circleAvg (H ω) r w - circleAvg (H ω) 𝕣 0| ≤ q * Real.log ε⁻¹ := by
      intro w hw r hr
      by_contra hlt
      exact hnot (Or.inl (Or.inr ⟨w, hw, r, hr, not_le.1 hlt⟩))
    have hPQ : IsEuclideanLengthMetric (𝔇 (hC ω)) ∧ hcirc ω 𝕣 0 = circleAvg (H ω) 𝕣 0 := by
      by_contra h
      exact hnot (Or.inr h)
    obtain ⟨hEuc, hcircω⟩ := hPQ
    have hcover := hA
    -- good circles with positive radius
    have hcov' : GoodCover (fun w r => 0 < r ∧ ω ∈ goodCircleEvent γ ξ 𝔇 hC hcirc H C r w) 1 M ε 𝕣 := by
      intro z hz
      obtain ⟨w, hw, r, ⟨k, hk⟩, h1, h2, hg, hzw⟩ := hcover z hz
      exact ⟨w, hw, r, ⟨k, hk⟩, h1, h2, ⟨by rw [hk]; positivity, hg⟩, hzw⟩
    have h35 := H35 ε ⟨hε0, hεε₀'⟩ 𝕣 h𝕣 (fun w r => 0 < r ∧ ω ∈ goodCircleEvent γ ξ 𝔇 hC hcirc H C r w) hcov'
    have htail : TailOK (H ω) q ε 𝕣 (R₀ + 1) := by
      intro w hw hwg k hk1 hk2
      have hmem : w ∈ Metric.ball (0 : ℂ) ((R₀ + 1) * 𝕣) ∩ Blueprint.gridPts (ε ^ ((1 : ℝ) + 1) * 𝕣 / 4) := by
        refine ⟨mem_ball_zero_iff.2 hw, ?_⟩
        rw [P31.rpow_one_add_one]
        exact hwg
      refine hB2' w hmem (((2 : ℝ) ^ k)⁻¹ * 𝕣) ⟨k, rfl, ?_, ?_⟩
      · exact mul_le_mul_of_nonneg_right hk1 h𝕣.le
      · exact mul_le_mul_of_nonneg_right hk2 h𝕣.le
    have hgd : ∀ w r, (0 < r ∧ ω ∈ goodCircleEvent γ ξ 𝔇 hC hcirc H C r w) → ∀ p ∈ sphere w r, ∀ p' ∈ sphere w r,
        internalMetric (𝔇 (hC ω)) {z : ℂ | r / 2 < ‖z - w‖ ∧ ‖z - w‖ < 2 * r} p p' ≤
          ENNReal.ofReal (C * scaleFac ξ (fun r => r ^ (ξ * lqgQ γ)) (H ω) r w) := by
      intro w r ⟨hr, hgood⟩ p hp p' hp'
      obtain ⟨hg1, hg2⟩ := hgood
      have hg2' : hcirc ω r w = circleAvg (H ω) r w := hg2
      refine (internalMetric_sphere_le_of_mem_scaledInternalSupEvent hr hg1 hp hp').trans (le_of_eq ?_)
      congr 1
      rw [hg2']
      have e : Real.exp (ξ * (circleAvg (H ω) r w + lqgQ γ * Real.log r)) =
          r ^ (ξ * lqgQ γ) * Real.exp (ξ * circleAvg (H ω) r w) := by
        rw [Real.rpow_def_of_pos hr, ← Real.exp_add]; congr 1; ring
      simp only [scaleFac, e]
    have key := IsEuclideanLengthMetric.iInf_internalMetric_scaleSet_le_of_goodCircles hEuc
      (c := fun r => r ^ (ξ * lqgQ γ)) (g := H ω) hξ hΛ hc hcpos hε0 hε1 h𝕣 hC1 hR₀ hU₀b hU₀
      (good := fun w r => 0 < r ∧ ω ∈ goodCircleEvent γ ξ 𝔇 hC hcirc H C r w) hgd h35 htail
    have hal : ε ^ (-(6 + 2 * Λ + ξ * q)) = (ε ^ 6)⁻¹ * ε ^ (-(2 * Λ + ξ * q)) := by
      rw [show -(6 + 2 * Λ + ξ * q) = -(6 : ℝ) + -(2 * Λ + ξ * q) by ring, Real.rpow_add hε0,
        Real.rpow_neg hε0.le]
      norm_num
    have hX : (2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) * C * Λ * ε ^ (-(6 + 2 * Λ + ξ * q)) *
          (𝕣 ^ (ξ * lqgQ γ) * Real.exp (ξ * hcirc ω 𝕣 0)) =
        (2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) / ε ^ 6 *
          (C * (Λ * ε ^ (-(2 * Λ + ξ * q)) * scaleFac ξ (fun r => r ^ (ξ * lqgQ γ)) (H ω) 𝕣 0)) := by
      rw [hal, hcircω]
      simp only [scaleFac]
      ring
    have hωT : ENNReal.ofReal ((2 * (8 * (R₀ + 1) + 1) ^ 2 + 1) * C * Λ * ε ^ (-(6 + 2 * Λ + ξ * q)) *
          (𝕣 ^ (ξ * lqgQ γ) * Real.exp (ξ * hcirc ω 𝕣 0))) < _ := hω
    rw [hX] at hωT
    exact absurd key (not_le.2 hωT)
  · refine (measure_union_le _ _).trans ?_
    rw [hnull, add_zero]
    exact (measure_union_le _ _).trans (add_le_add hB1 hB2)

end LatticeProb.LQG
