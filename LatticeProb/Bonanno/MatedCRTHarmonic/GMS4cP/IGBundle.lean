/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.IGBundle at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.IGNorm
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionMeasurable

/-!
# One S7 locality map for every affine pullback of the IG input

Source: [18] Lemma 2.4 (the frozen `igMap` clause (S7)) and the
coordinate change of imaginary geometry (IG1; `igMap`'s coordinate clause and its v4 positive-radius
clause (A)).

The frozen (S7) clause gives, for a bounded open `U'` and `δ' > 0`, a Borel map `g` reading the excursion
segments of `η_L` into `U'` from `restrictCircles (thickening δ' U')` of the IG input. Such a map is only
characterized almost surely under the law of the bundle's input. `ae_excursionSegment_of_l43pNorm` shows that
the **same** `g`, applied to the renormalized pullback `l43pNorm r (igPullback γ z s 0 H)` (`IGNorm.lean`),
returns the excursion segments of the re-rooted curve `affineReroot z s 0 η_L`, for **every** `z` and `s > 0`:
The renormalized pullback has the law of the input (`map_l43pNorm_igPullback`), and the curve read from it is
`affineReroot z s 0 η_L` by the coordinate clause and the `2πχ`-periodicity of the curve map
(IGCO's `ae_periodic_of_ccPos`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw

namespace MatedCRTHarmonic.GMS4cP

theorem posIn_addIn_posIn (c : ℝ) (K : ℝ → ℂ → ℝ) :
    posIn (addIn c (posIn K)) = posIn (addIn c K) := by
  funext ρ v
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [posIn_apply_of_nonpos hρ, posIn_apply_of_nonpos hρ]
  · rw [posIn_apply_of_pos hρ, posIn_apply_of_pos hρ]
    simp only [addIn]
    rw [posIn_apply_of_pos hρ]

theorem posIn_eq_of_pos (K : ℝ → ℂ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) : posIn K ρ = K ρ :=
  funext fun v => posIn_apply_of_pos hρ v K

theorem posIn_posIn (K : ℝ → ℂ → ℝ) : posIn (posIn K) = posIn K := by
  funext ρ v
  rcases le_or_gt ρ 0 with hρ | hρ
  · rw [posIn_apply_of_nonpos hρ, posIn_apply_of_nonpos hρ]
  · rw [posIn_apply_of_pos hρ, posIn_apply_of_pos hρ]

theorem restrictCircles_posIn (W : Set ℂ) (K : ℝ → ℂ → ℝ) :
    restrictCircles W (posIn K) = restrictCircles W K := by
  funext ρ v
  unfold restrictCircles
  split_ifs with h
  · exact posIn_apply_of_pos h.1 v K
  · rfl

theorem measurable_restrictCircles (W : Set ℂ) :
    Measurable (restrictCircles W) := by
  classical
  refine measurable_pi_iff.2 fun ρ => measurable_pi_iff.2 fun v => ?_
  by_cases h : 0 < ρ ∧ closedBall v ρ ⊆ W
  · have e : (fun K : ℝ → ℂ → ℝ => restrictCircles W K ρ v) = fun K => K ρ v := by
      funext K
      simp [restrictCircles, h]
    rw [e]
    exact (measurable_pi_apply v).comp (measurable_pi_apply ρ)
  · have e : (fun K : ℝ → ℂ → ℝ => restrictCircles W K ρ v) = fun _ => 0 := by
      funext K
      simp [restrictCircles, h]
    rw [e]
    exact measurable_const

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : NNReal → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The IG period `2πχ` is positive. -/
theorem igPeriod_pos
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm) :
    0 < 2 * Real.pi * igChi γ := by
  have := D.isProbabilityMeasure
  exact period_pos_of_uniform D.igField.2.1

/-- **One S7 map for all affine pullbacks.** -/
theorem ae_excursionSegment_of_l43pNorm
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    {U' : Set ℂ} (hU'o : IsOpen U') (hU'b : Bornology.IsBounded U') {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ g : (ℝ → ℂ → ℝ) → (ℚ × ℚ → ℝ → ℂ), Measurable g ∧
      ∀ (z : ℂ) (s : ℝ), 0 < s →
        haveI : Fact (0 < 2 * Real.pi * igChi γ) := ⟨igPeriod_pos D⟩
        ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, GMS4c.ratPt q ∈ U' → ∀ t : ℚ,
          g (restrictCircles (thickening δ' U') (l43pNorm (2 * Real.pi * igChi γ)
            (igPullback γ z s 0 (igCircleAvgInput (hIG₀ ω, T ω))))) q t =
          excursionSegment (affineReroot z s 0 (ηL ω)) U' (GMS4c.ratPt q) t := by
  have hP := D.isProbabilityMeasure
  set r : ℝ := 2 * Real.pi * igChi γ with hr
  have : Fact (0 < r) := ⟨igPeriod_pos D⟩
  obtain ⟨Φ, hΦ, hign, hroot, hcc, hS7⟩ := D.igMap
  obtain ⟨g, hg, hgS⟩ := hS7 U' hU'o hU'b δ' hδ'
  refine ⟨g, hg, fun z s hs => ?_⟩
  set K : Ω → ℝ → ℂ → ℝ := fun ω => igCircleAvgInput (hIG₀ ω, T ω) with hKdef
  have hroot' : ∀ᵐ ω ∂P, ηL ω = Φ (posIn (K ω)) := by
    filter_upwards [hroot] with ω hω
    rw [hω]
    exact hign _ _ fun ρ hρ => (posIn_eq_of_pos (K ω) hρ).symm
  have hcc' : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (posIn (igPullback γ z₀ s φ (K ω))) = affineReroot z₀ s φ (ηL ω) := by
    intro z₀ s φ hs
    filter_upwards [hcc z₀ s φ hs] with ω hω
    rw [← hω]
    exact hign _ _ fun ρ hρ => posIn_eq_of_pos (igPullback γ z₀ s φ (K ω)) hρ
  have htr : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) := by
    filter_upwards [D.spaceFilling] with ω hω
    exact hω.2.1
  have hτ := ae_firstHit_zero_of_ccPos hroot' hcc' htr
  have hper := ae_periodic_of_ccPos hroot' hcc' hτ
  -- the property transported through the law identity
  have hz : (U'ᶜ).Nonempty := by
    obtain ⟨R, hR⟩ := hU'b.subset_ball (0 : ℂ)
    refine ⟨((|R| + 1 : ℝ) : ℂ), fun h => ?_⟩
    have h' := hR h
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at h'
    linarith [le_abs_self R]
  let Q : Set (ℝ → ℂ → ℝ) :=
    (⋂ q : ℚ × ℚ, ⋂ (_ : GMS4c.ratPt q ∈ U'), ⋂ t : ℚ,
      {L | g (restrictCircles (thickening δ' U') L) q t =
        excursionSegment (Φ L) U' (GMS4c.ratPt q) t}) ∩
    ⋂ k : ℤ, {L | Φ (posIn (addIn (r * k) L)) = Φ (posIn L)}
  have hQm : MeasurableSet Q := by
    refine MeasurableSet.inter (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq =>
      MeasurableSet.iInter fun t => measurableSet_eq_fun ?_ ?_) (MeasurableSet.iInter fun k =>
        measurableSet_eq_curve (hΦ.comp (measurable_posIn.comp (measurable_addIn _)))
          (hΦ.comp measurable_posIn))
    · exact (measurable_pi_apply (t : ℝ)).comp ((measurable_pi_apply q).comp
        (hg.comp (measurable_restrictCircles _)))
    · exact (measurable_pi_apply (t : ℝ)).comp
        ((GMS4c.measurable_excursionSegment ⟨U', hU'o⟩ (GMS4c.ratPt q) hz).comp hΦ)
  have hQ0 : ∀ᵐ ω ∂P, posIn (K ω) ∈ Q := by
    filter_upwards [hroot', hgS, hper] with ω hrω hgω hpω
    simp only [Q, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    refine ⟨fun q hq t => ?_, fun k => ?_⟩
    · rw [restrictCircles_posIn, ← hrω]
      exact congrFun (hgω q hq).symm (t : ℝ)
    · rw [posIn_addIn_posIn, posIn_posIn]
      exact hpω k
  have hlaw := map_l43pNorm_igPullback (γ := γ) D.igField.1 D.igField.2.1 D.igField.2.2 z hs
  have hYm : AEMeasurable (fun ω => l43pNorm r (igPullback γ z s 0 (K ω))) P := by
    have hUm : AEMeasurable T P :=
      MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif Fact.out D.igField.2.1
    exact ((measurable_l43pNorm r).comp ((measurable_igPullback γ z s 0).comp
      measurable_igCircleAvgInput)).comp_aemeasurable
      (D.igField.1.1.measurable.aemeasurable.prodMk hUm)
  have hXm : AEMeasurable (fun ω => posIn (K ω)) P := by
    have hUm : AEMeasurable T P :=
      MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif Fact.out D.igField.2.1
    exact (measurable_posIn.comp measurable_igCircleAvgInput).comp_aemeasurable
      (D.igField.1.1.measurable.aemeasurable.prodMk hUm)
  have hQ1 : ∀ᵐ ω ∂P, l43pNorm r (igPullback γ z s 0 (K ω)) ∈ Q := by
    have h1 : ∀ᵐ L ∂(P.map fun ω => posIn (K ω)), L ∈ Q := (ae_map_iff hXm hQm).2 hQ0
    rw [← hlaw] at h1
    exact (ae_map_iff hYm hQm).1 h1
  filter_upwards [hQ1, hcc' z s 0 hs] with ω hQω hccω q hq t
  simp only [Q, mem_inter_iff, mem_iInter, mem_ofPred_eq] at hQω
  obtain ⟨k, hk⟩ := exists_l43pNorm_eq r (igPullback γ z s 0 (K ω))
  have hcurve : Φ (l43pNorm r (igPullback γ z s 0 (K ω))) = affineReroot z s 0 (ηL ω) := by
    have hp := hQω.2 (-k)
    rw [hk, posIn_addIn_posIn, posIn_posIn] at hp
    have e : addIn (r * ((-k : ℤ) : ℝ)) (addIn (r * k) (igPullback γ z s 0 (K ω))) =
        igPullback γ z s 0 (K ω) := by
      funext ρ v
      simp only [addIn]
      push_cast
      ring
    rw [e] at hp
    rw [hk, ← hccω, hp]
  rw [← hcurve]
  exact hQω.1 q hq t

end MatedCRTHarmonic.GMS4cP
