/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ExponentFromProb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan

/-!
# Node `EX`: from probability bounds to exponent bounds

Proves `Blueprint.Draft.ExponentFromProb`: convergence in probability along the full filter
`𝓝[>] 0` implies convergence in probability along any sequence `u j → 0⁺`, and consequently
that an `IsLFPPExponent` value `lam` is squeezed between any probabilistic upper/lower bound
`Λ` for the ratio `log D^ξ_ε / log ε` along such sequences.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped Classical

namespace LQGDimension

/-- Common engine for both halves of `ExponentFromProb`.  If `X ε → lam` in `P`-measure along
the full filter `𝓝[>] 0`, `u j → 0⁺`, and `Ac ⊆ ℝ` is a "bad" set staying at distance `≥ θ`
from `lam` outside itself (`x ∉ Ac → θ ≤ |x - lam|`), then `P {ω | X (u j) ω ∈ Ac}` cannot
tend to `0`: outside `Ac`, `X (u j) ω` is far from `lam`, and convergence in measure along `u`
(via `TendstoInMeasure.comp`) forces that event to also have vanishing probability, so the
whole space would have measure `< 1` in the limit, a contradiction. -/
private theorem exponentFromProb_aux {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ → Ω → ℝ) (lam : ℝ) (u : ℕ → ℝ)
    (hexp : TendstoInMeasure P X (𝓝[>] (0 : ℝ)) (fun _ => lam))
    (hu : Tendsto u atTop (𝓝[>] (0 : ℝ))) (θ : ℝ) (hθ : 0 < θ)
    (Ac : Set ℝ) (hAc : ∀ x : ℝ, x ∉ Ac → θ ≤ |x - lam|)
    (hAmeas : Tendsto (fun j => P {ω | X (u j) ω ∈ Ac}) atTop (𝓝 0)) : False := by
  have hcomp : TendstoInMeasure P (X ∘ u) atTop (fun _ => lam) := hexp.comp hu
  have hcomp' := hcomp (ENNReal.ofReal θ) (by positivity)
  simp only [Function.comp_apply] at hcomp'
  have hsum : Tendsto
      (fun j => P {ω | X (u j) ω ∈ Ac} + P {ω | ENNReal.ofReal θ ≤ edist (X (u j) ω) lam})
      atTop (𝓝 0) := by
    have := hAmeas.add hcomp'
    simpa using this
  have hone : ∀ j : ℕ, (1 : ENNReal) ≤
      P {ω | X (u j) ω ∈ Ac} + P {ω | ENNReal.ofReal θ ≤ edist (X (u j) ω) lam} := by
    intro j
    calc (1 : ENNReal) = P (Set.univ : Set Ω) := (measure_univ).symm
      _ ≤ P ({ω | X (u j) ω ∈ Ac} ∪ {ω | ENNReal.ofReal θ ≤ edist (X (u j) ω) lam}) := by
          apply measure_mono
          intro ω _
          by_cases hωA : X (u j) ω ∈ Ac
          · exact Or.inl hωA
          · right
            rw [Set.mem_ofPred_eq, edist_dist, Real.dist_eq]
            rw [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
            exact hAc _ hωA
      _ ≤ P {ω | X (u j) ω ∈ Ac} + P {ω | ENNReal.ofReal θ ≤ edist (X (u j) ω) lam} :=
          measure_union_le _ _
  exact absurd (ge_of_tendsto' hsum hone) (by norm_num)

/-- **Node `EX`.** -/
theorem exponentFromProb : Blueprint.Draft.ExponentFromProb := by
  intro Ω _ P h ξ lam Λ hP hexp
  have hexp' : TendstoInMeasure P
      (fun ε ω => Real.log (lfppDistance ξ (fun z => h ε z ω)) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (fun _ => lam) := hexp
  set X : ℝ → Ω → ℝ := fun ε ω =>
    Real.log (lfppDistance ξ (fun z => h ε z ω)) / Real.log ε with hX_def
  constructor
  · -- lam ≤ Λ
    intro hyp
    by_contra hlt
    push Not at hlt
    set θ := (lam - Λ) / 3 with hθ_def
    have hθpos : 0 < θ := by rw [hθ_def]; linarith
    obtain ⟨u, hu_tendsto, hu_meas⟩ := hyp θ hθpos
    exact exponentFromProb_aux P X lam u hexp' hu_tendsto θ hθpos
      {x : ℝ | Λ + θ < x}
      (fun x hx => by
        simp only [Set.mem_ofPred_eq, not_lt] at hx
        rw [abs_of_nonpos (by linarith)]
        linarith)
      hu_meas
  · -- Λ ≤ lam
    intro hyp
    by_contra hlt
    push Not at hlt
    set θ := (Λ - lam) / 3 with hθ_def
    have hθpos : 0 < θ := by rw [hθ_def]; linarith
    obtain ⟨u, hu_tendsto, hu_meas⟩ := hyp θ hθpos
    exact exponentFromProb_aux P X lam u hexp' hu_tendsto θ hθpos
      {x : ℝ | x < Λ - θ}
      (fun x hx => by
        simp only [Set.mem_ofPred_eq, not_lt] at hx
        rw [abs_of_nonneg (by linarith)]
        linarith)
      hu_meas

end LQGDimension
