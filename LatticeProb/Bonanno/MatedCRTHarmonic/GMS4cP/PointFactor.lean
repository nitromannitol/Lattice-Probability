/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.PointFactor at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: Measurable.ite no longer unifies with the point factor (time-out); its measurability goes through Set.indicator (Measurable.indicator). -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.PointBorel

/-!
# The local all-visit point factor of (4.22)

Source: [18] (4.22) and the proof of Lemma 4.9, with the
all-visit observables (`GMS4c.areaRatioPrime`, `degreeInPrime`, `degreeOutPrime`).

`truePointFactor c z ε r₀ ζ` is the part of the masked all-visit density `1_F u′_*(z)` read near `z`: the window
test at every visit (`diam ≤ r₀`) and the degree cap `deg′_in + deg′_out ≤ ε^{-ζ}`, times
`DA′ (deg′_in + deg′_out)`. (The two circle-average conditions of (4.22) are separate observables.)
`locPointFactor` is the same expression in the local segment data; `locPointFactor_eq` identifies them when
`B̄_{4 r₀}(z) ⊆ U`, and `nullMeasurable_locPointFactor` makes it null measurable for every finite law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c
open LQGMetric (UMeasurableSet)

attribute [local instance] Classical.propDecidable

/-- The local part of the masked all-visit density at `z`, for the curve `c`. -/
def truePointFactor (c : ℝ → ℂ) (z : ℂ) (ε r₀ ζ : ℝ) : ℝ :=
  if (∀ t, c t = z → diam (locWindow ε c t) ≤ r₀) ∧
      (((degreeInPrime ε c z + degreeOutPrime ε c z : ℕ∞)) : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ (-ζ))
  then (areaRatioPrime ε c z).toReal *
    (((degreeInPrime ε c z).toNat + (degreeOutPrime ε c z).toNat : ℕ) : ℝ)
  else 0

/-- The same expression in the local segment data. -/
def locPointFactor (L : Set (ℚ × ℚ)) (z : ℂ) (ε r₀ ζ : ℝ) (σ : SegSpace) : ℝ :=
  if locWinOK L z ε r₀ σ ∧
      (((locDegInPrime L z ε σ + locDegOutPrime L z ε σ : ℕ∞)) : ℝ≥0∞) ≤
        ENNReal.ofReal (ε ^ (-ζ))
  then (locDAPrime L z ε σ).toReal *
    (((locDegInPrime L z ε σ).toNat + (locDegOutPrime L z ε σ).toNat : ℕ) : ℝ)
  else 0

/-- **The local point factor equals the true one.** -/
theorem locPointFactor_eq {c : ℝ → ℂ} {U : Set ℂ} {L : Set (ℚ × ℚ)} {e x : ℚ × ℚ → ℝ}
    (hc : Continuous c) {ε : ℝ} (hε : 0 ≤ ε) (hD : IsExcursionFamily c U L e x) {μ : Measure ℂ}
    (hμ : ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {z : ℂ} {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hz4 : closedBall z (4 * r₀) ⊆ U) (ζ : ℝ) :
    locPointFactor L z ε r₀ ζ σ = truePointFactor c z ε r₀ ζ := by
  have hz1 : closedBall z r₀ ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hz4
  have hzU : z ∈ U := hz1 (mem_closedBall_self hr₀)
  have hwin := winOK_iff hc hε hD hσ hzU hz1
  unfold locPointFactor truePointFactor
  by_cases hw : ∀ t, c t = z → diam (locWindow ε c t) ≤ r₀
  · obtain ⟨hDA, hIn, hOut⟩ := prime_identities hc hε hD hμ hσ hr₀ hz4 hw
    rw [hDA, hIn, hOut]
    by_cases hd : (((degreeInPrime ε c z + degreeOutPrime ε c z : ℕ∞)) : ℝ≥0∞) ≤
        ENNReal.ofReal (ε ^ (-ζ))
    · rw [ite_eq_left ⟨hwin.1 hw, hd⟩, ite_eq_left ⟨hw, hd⟩]
    · rw [ite_eq_right fun h => hd h.2, ite_eq_right fun h => hd h.2]
  · have hw' : ¬ locWinOK L z ε r₀ σ := fun h => hw (hwin.2 h)
    rw [ite_eq_right fun h => hw' h.1, ite_eq_right fun h => hw h.1]

/-- **The local point factor is null measurable for every finite law.** -/
theorem nullMeasurable_locPointFactor (L : Set (ℚ × ℚ)) (z : ℂ) (ε r₀ ζ : ℝ)
    (ν : Measure SegSpace) [IsFiniteMeasure ν] :
    NullMeasurable (locPointFactor L z ε r₀ ζ) ν := by
  -- work in the null-measurable σ-algebra
  have hset : ∀ {S : Set SegSpace}, UMeasurableSet S →
      @MeasurableSet (NullMeasurableSpace SegSpace ν) _ S := fun hS => hS ν inferInstance
  have hW : @MeasurableSet (NullMeasurableSpace SegSpace ν) _ {σ | locWinOK L z ε r₀ σ} := by
    have := (um_not_locWinOK L z ε r₀).compl
    simp only [compl_ofPred, not_not] at this
    exact hset this
  have hDA : Measurable fun σ : NullMeasurableSpace SegSpace ν => locDAPrime L z ε σ :=
    measurable_of_Ioi fun a => hset (um_lt_locDAPrime L z ε a)
  have hIn : Measurable fun σ : NullMeasurableSpace SegSpace ν => locDegInPrime L z ε σ := by
    refine measurable_of_le_enat fun k => ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [Nat.cast_zero, zero_le, ofPred_true]
      exact MeasurableSet.univ
    · exact hset (um_le_locDegInPrime L z ε k hk)
  have hOut : Measurable fun σ : NullMeasurableSpace SegSpace ν => locDegOutPrime L z ε σ := by
    refine measurable_of_le_enat fun k => ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [Nat.cast_zero, zero_le, ofPred_true]
      exact MeasurableSet.univ
    · exact hset (um_le_locDegOutPrime L z ε k hk)
  have hpair : Measurable fun σ : NullMeasurableSpace SegSpace ν =>
      (locDegInPrime L z ε σ, locDegOutPrime L z ε σ) := hIn.prodMk hOut
  have hsum : Measurable fun σ : NullMeasurableSpace SegSpace ν =>
      (((locDegInPrime L z ε σ + locDegOutPrime L z ε σ : ℕ∞)) : ℝ≥0∞) :=
    (measurable_of_countable (fun p : ℕ∞ × ℕ∞ => (((p.1 + p.2 : ℕ∞)) : ℝ≥0∞))).comp hpair
  have hcnt : Measurable fun σ : NullMeasurableSpace SegSpace ν =>
      (((locDegInPrime L z ε σ).toNat + (locDegOutPrime L z ε σ).toNat : ℕ) : ℝ) :=
    (measurable_of_countable (fun p : ℕ∞ × ℕ∞ => ((p.1.toNat + p.2.toNat : ℕ) : ℝ))).comp hpair
  have hcond : @MeasurableSet (NullMeasurableSpace SegSpace ν) _ {σ | locWinOK L z ε r₀ σ ∧
      (((locDegInPrime L z ε σ + locDegOutPrime L z ε σ : ℕ∞)) : ℝ≥0∞) ≤
        ENNReal.ofReal (ε ^ (-ζ))} :=
    hW.inter (measurableSet_le hsum measurable_const)
  have hval : Measurable fun σ : NullMeasurableSpace SegSpace ν =>
      (locDAPrime L z ε σ).toReal *
        (((locDegInPrime L z ε σ).toNat + (locDegOutPrime L z ε σ).toNat : ℕ) : ℝ) :=
    (ENNReal.measurable_toReal.comp hDA).mul hcnt
  have e : (fun σ : NullMeasurableSpace SegSpace ν => locPointFactor L z ε r₀ ζ σ) =
      {σ | locWinOK L z ε r₀ σ ∧ (((locDegInPrime L z ε σ + locDegOutPrime L z ε σ : ℕ∞)) : ℝ≥0∞) ≤ ENNReal.ofReal (ε ^ (-ζ))}.indicator fun σ =>
        (locDAPrime L z ε σ).toReal * (((locDegInPrime L z ε σ).toNat + (locDegOutPrime L z ε σ).toNat : ℕ) : ℝ) := by
    funext σ; exact if_congr Iff.rfl rfl rfl
  have hfin : Measurable fun σ : NullMeasurableSpace SegSpace ν =>
      locPointFactor L z ε r₀ ζ σ := by
    rw [e]; exact hval.indicator hcond
  exact hfin

end MatedCRTHarmonic.GMS4cP
