import LatticeProb.Prob.Cadlag.HalfLine.Laws

/-!
# Ethier–Kurtz: weak convergence and relative compactness in `D_E[0,∞)`

S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
(1986), Chapter 3, on the half-line càdlàg space `D_E[0,∞)` with the metric (5.2):
Theorem 7.8(b) (a relatively compact sequence of laws whose finite-dimensional laws converge
on a dense set of times converges weakly; `E` separable) and Theorem 8.6, (b) ⇒ (a) (Kurtz's
criterion for relative compactness from conditional increment bounds with respect to the raw
natural filtration, under the marginal compactness condition 7.2(a) at rational times; `E`
complete and separable). The propositions are stated so that a formalization citing them can
carry them as explicit hypotheses; they are not proved here.
-/

namespace LatticeProb.External

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open LatticeProb.Cadlag.HalfLine

/-- **Ethier–Kurtz, Chapter 3, Theorem 7.8(b).** -/
def EthierKurtzConvergenceFromFdd : Prop :=
  ∀ (E : Type) [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (mu : ℕ → ProbabilityMeasure (D E)) (nu : ProbabilityMeasure (D E)),
    IsCompact (closure (Set.range mu)) →
    (∃ S : Set Time, Dense S ∧
      ∀ (k : ℕ) (ts : Fin k → Time), (∀ i, ts i ∈ S) →
        Tendsto (fun n => jointLaw (mu n) ts) atTop (𝓝 (jointLaw nu ts))) →
    Tendsto mu atTop (𝓝 nu)

/-- **Ethier–Kurtz, Chapter 3, Theorem 8.6, (b) ⇒ (a).** -/
def EthierKurtzRelativeCompactness : Prop :=
  ∀ (E : Type) [MetricSpace E] [CompleteSpace E] [SeparableSpace E] [MeasurableSpace E]
    [BorelSpace E] (A : Type) (Ω : A → Type) (m : ∀ a, MeasurableSpace (Ω a))
    (P : ∀ a, @ProbabilityMeasure (Ω a) (m a)) (Y : ∀ a, Ω a → D E)
    (hY : ∀ a, @Measurable (Ω a) (D E) (m a) inferInstance (Y a)),
    (∀ a t, @Measurable (Ω a) E (m a) inferInstance (fun w => (Y a w).1 t)) →
    (∀ eta : ℝ, 0 < eta → ∀ t : ℚ, 0 ≤ t → ∃ K : Set E, IsCompact K ∧
      ∀ a, ENNReal.ofReal (1 - eta) ≤
        (P a : @Measure (Ω a) (m a)) {w | (Y a w).1 (t : ℝ).toNNReal ∈ K}) →
    (∀ T : ℝ, 0 < T → ∃ beta : ℝ, 0 < beta ∧
      ∃ gam : ∀ a, ℝ → Ω a → ℝ≥0,
        (∀ a delta, 0 < delta → delta < 1 →
          @Measurable (Ω a) ℝ≥0 (m a) inferInstance (gam a delta)) ∧
        (∀ a delta, 0 < delta → delta < 1 → ∀ t u v : Time,
          (t : ℝ) ≤ T → (u : ℝ) ≤ delta → (v : ℝ) ≤ min delta t →
          ∀ᵐ w ∂(P a : @Measure (Ω a) (m a)),
            (@condLExp (Ω a) (m a) (naturalSigma (Y a) t)
              (P a : @Measure (Ω a) (m a))
              (incrementPower (Y a) beta (t + u) t) w) *
                incrementPower (Y a) beta t (t - v) w ≤
            @condLExp (Ω a) (m a) (naturalSigma (Y a) t)
              (P a : @Measure (Ω a) (m a)) (fun w => gam a delta w) w) ∧
        Tendsto (fun delta : ℝ => ⨆ a, ∫⁻ w, (gam a delta w : ℝ≥0∞)
          ∂(P a : @Measure (Ω a) (m a))) (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun delta : ℝ => ⨆ a,
          ∫⁻ w, incrementPower (Y a) beta delta.toNNReal 0 w
            ∂(P a : @Measure (Ω a) (m a))) (𝓝[>] 0) (𝓝 0)) →
    IsCompact (closure (Set.range (fun a =>
      (P a).map (@Measurable.aemeasurable (Ω a) (D E) (m a) inferInstance
        (Y a) (P a) (hY a)))))

/-- Theorem 7.8(b) applies to a constant sequence of Dirac laws on `ℝ`-valued paths. -/
theorem ethierKurtzConvergenceFromFdd_const (h : EthierKurtzConvergenceFromFdd) (a : ℝ) :
    Tendsto (fun _ : ℕ => constantLaw a) atTop (𝓝 (constantLaw a)) := by
  apply h ℝ
  · simpa only [Set.range_const, isClosed_singleton.closure_eq] using
      (isCompact_singleton : IsCompact ({constantLaw a} : Set (ProbabilityMeasure (D ℝ))))
  · exact ⟨univ, dense_univ, fun _ _ _ => tendsto_const_nhds⟩

/-- Theorem 8.6 applies to a constant real process on the one-point space, with `β = 1`
and `γ = 0`. -/
theorem ethierKurtzRelativeCompactness_const (h : EthierKurtzRelativeCompactness) (a : ℝ) :
    IsCompact (closure (Set.range (fun _ : Unit => constantProcessLaw a))) := by
  refine h ℝ Unit (fun _ => Unit) (fun _ => inferInstance) (fun _ => unitLaw)
    (fun _ _ => const a) (fun _ => measurable_const) (fun _ _ => measurable_const) ?_ ?_
  · intro eta heta t ht
    refine ⟨{a}, isCompact_singleton, ?_⟩
    intro index
    simp only [const, mem_singleton_iff, setOf_true, measure_univ]
    exact (ENNReal.ofReal_le_ofReal (sub_le_self 1 heta.le)).trans_eq
      ENNReal.ofReal_one
  · intro T hT
    refine ⟨1, zero_lt_one, (fun _ _ _ => 0), (fun _ _ _ _ => measurable_const),
      ?_, ?_, ?_⟩
    · intro index delta hd hd1 t u v ht hu hv
      have hz (s t : Time) : incrementPower (fun _ : Unit => const a) 1 s t = 0 := by
        funext w
        simp [incrementPower, const]
      simp only [hz, ENNReal.coe_zero, condLExp_zero, Pi.zero_apply, mul_zero]
      exact Filter.Eventually.of_forall fun _ => zero_le
    · simp only [ENNReal.coe_zero, lintegral_zero, ENNReal.iSup_zero]
      exact tendsto_const_nhds
    · simp only [incrementPower, const, dist_self, min_eq_left zero_le_one,
        Real.rpow_one, ENNReal.ofReal_zero, lintegral_zero, ENNReal.iSup_zero]
      exact tendsto_const_nhds

end LatticeProb.External
