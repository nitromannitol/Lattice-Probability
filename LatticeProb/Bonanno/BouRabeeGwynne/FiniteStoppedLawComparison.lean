/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.FiniteStoppedLawComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkCanonicalStopping
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteStoppedCurveComparison
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianActiveTransfer

/-! The finite rich-sequence coupling controls the two reconstructed stopped
laws. Its exceptional mass consists of first failure, the Brownian active
tail, and the measurable finite Brownian boundary-oscillation event. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal NNReal

namespace BouRabeeGwynne

theorem levyProkhorov_reconstructed_stopped_laws_le {d n : ℕ} {V : Type*}
    (pos : V → Euc d) (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (a : ℝ) (P : TimePartition n) {U : Set (Euc d)} (hU : IsOpen U)
    (ρ : Measure ((ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d))))
    {ε mesh δ η : ℝ} (hε : 0 < ε) (hmesh : 0 ≤ mesh) (hbuffer : ε + mesh < δ)
    (r : ℝ≥0) (hsmall : ENNReal.ofReal (ε + η) < (r : ℝ≥0∞))
    (hwalk : ∀ᵐ e ∂ρ.fst, (e n).1 = false ∨ e ∈ canonicalWalkStoppingSupport U mesh P)
    (hendpoint : ∀ᵐ γ ∂ρ.snd, (γ n).1 = true →
      P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (γ k).2)) 1 ∉
        Metric.thickening δ U)
    (hclose : ∀ᵐ p ∂ρ, (∀ i ≤ n, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a) →
      ∀ t, dist (pastedWalkCurve P p.1 t)
        (P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (p.2 k).2)) t) ≤ ε)
    {b c o : ℝ≥0∞}
    (hfailure : ρ {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤ b)
    (htail : ρ.snd (sequenceActive n) ≤ c)
    (hosc : ρ.snd {γ | P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (γ k).2)) ∈
      unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η} ≤ o)
    (hbudget : b + c + o ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist (ρ.fst.map (reconstructedVertexStoppedCurve U n))
      (ρ.snd.map (reconstructedBrownianStoppedCurve U P)) ≤ r := by
  let G := fun γ : ℕ → Bool × C(unitInterval, Euc d) =>
    P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (γ k).2))
  have hG : Measurable G := P.measurable_concatenate.comp
    ((ExcursionTrajectory.measurable_prefixChain n d).comp
      (Measurable.of_eval fun k => (measurable_pi_apply k).snd))
  let Fbad := {p : (ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d)) |
      ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a}
  let Obad := {γ | G γ ∈
    unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η}
  have hObad : MeasurableSet Obad :=
    (measurableSet_unitCurveExitOscillationBad (isOpen_innerDomain U ε)
      Metric.isOpen_thickening η).preimage hG
  let Bad := (Fbad ∪ (Prod.snd ⁻¹' sequenceActive n)) ∪ (Prod.snd ⁻¹' Obad)
  have hbad : ρ Bad ≤ (r : ℝ≥0∞) := by
    apply le_trans (measure_union_le _ _)
    apply le_trans (add_le_add_left (measure_union_le _ _) _)
    rw [← Measure.snd_apply (measurableSet_sequenceActive n), ← Measure.snd_apply hObad]
    exact (add_le_add (add_le_add hfailure htail) hosc).trans hbudget
  have hwalk' : ∀ᵐ p ∂ρ, (p.1 n).1 = false ∨
      p.1 ∈ canonicalWalkStoppingSupport U mesh P :=
    ae_of_ae_map measurable_fst.aemeasurable hwalk
  have hend' : ∀ᵐ p ∂ρ, (p.2 n).1 = true → G p.2 1 ∉ Metric.thickening δ U :=
    ae_of_ae_map measurable_snd.aemeasurable hendpoint
  change levyProkhorovEDist
    ((ρ.map Prod.fst).map (reconstructedVertexStoppedCurve U n))
    ((ρ.map Prod.snd).map (reconstructedBrownianStoppedCurve U P)) ≤ _
  rw [Measure.map_map (measurable_reconstructedVertexStoppedCurve hU.measurableSet n) measurable_fst,
    Measure.map_map (measurable_reconstructedBrownianStoppedCurve hU P) measurable_snd]
  apply levyProkhorov_curveLaws_le_of_ae_good ρ _ _
    ((measurable_reconstructedVertexStoppedCurve hU.measurableSet n).comp measurable_fst).aemeasurable
    ((measurable_reconstructedBrownianStoppedCurve hU P).comp measurable_snd).aemeasurable
    Bad r hbad
  filter_upwards [hwalk', hend', hclose] with p hw he hc
  intro hp
  have hgood : ∀ i ≤ n, (p.1 i, p.2 i) ∈ goodExcursionPair pos (E i) a := by
    intro i hi
    by_contra hfail
    exact hp (Or.inl (Or.inl ⟨i, hi, hfail⟩))
  have hbtrue : (p.2 n).1 = true := Bool.eq_true_of_not_eq_false
    (fun hb => hp (Or.inl (Or.inr hb)))
  have hwtrue : (p.1 n).1 = true :=
    (goodExcursionPair_flags pos (E n) a (hgood n le_rfl)).trans hbtrue
  have hsupport : p.1 ∈ canonicalWalkStoppingSupport U mesh P :=
    hw.resolve_left (by rw [hwtrue]; decide)
  have hgoodOsc : G p.2 ∉
      unitCurveExitOscillationBad (innerDomain U ε) (Metric.thickening δ U) η :=
    fun h => hp (Or.inr h)
  have hd := curveSpace_edist_prefix_unitExit_le_of_endpoint_outside hU
    (pastedWalkCurve P p.1) (G p.2)
    (ClockedWalkExcursion.pastedVertexExitParameter U P p.1)
    hε hmesh hbuffer (hc hgood) (canonicalWalkStoppingSupport_pre hsupport)
    hsupport.2.1 (he hbtrue) hgoodOsc
  rw [hsupport.1] at hd
  exact hd.trans_lt hsmall

end BouRabeeGwynne
