import LatticeProb.Prob.UpcrossGluePrefix
import LatticeProb.Prob.UpcrossGlueMeasure
import LatticeProb.Prob.EventuallyCoupledPathLaw

/-!
# Uniqueness of gluing laws under a common coupling

Two stationary laws of glued continuous paths coincide when their initial paths are coupled and
hit every negative integer level, and their continuation paths have a common starting value.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- Gluing laws with a common first path and equally initialized continuations coincide if they
are independent of the positive integer gluing level. -/
theorem glueC_law_unique_of_common_coupling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Y Z W : Ω → C(ℝ≥0, ℝ))
    (μ ν : Measure C(ℝ≥0, ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    (hhit : ∀ᵐ ω ∂P, ∀ n : ℕ, hitFrom (-(n : ℝ)) 0 (Y ω : ℝ≥0 → ℝ) ≠ ⊤)
    (hzero : ∀ᵐ ω ∂P, Z ω 0 = W ω 0)
    (hμ : ∀ n : ℕ, 0 < n → P.map (fun ω => glueC (n : ℝ) (Y ω) (Z ω)) = μ)
    (hν : ∀ n : ℕ, 0 < n → P.map (fun ω => glueC (n : ℝ) (Y ω) (W ω)) = ν) : μ = ν := by
  let U : ℕ → Ω → C(ℝ≥0, ℝ) := fun n ω => glueC ((n + 1 : ℕ) : ℝ) (Y ω) (Z ω)
  let V : ℕ → Ω → C(ℝ≥0, ℝ) := fun n ω => glueC ((n + 1 : ℕ) : ℝ) (Y ω) (W ω)
  have hU : ∀ n, Measurable (U n) := by
    intro n
    change Measurable ((fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      glueC ((n + 1 : ℕ) : ℝ) p.1 p.2) ∘ fun ω => (Y ω, Z ω))
    exact (measurable_glueC ((n + 1 : ℕ) : ℝ)).comp (hY.prodMk hZ)
  have hV : ∀ n, Measurable (V n) := by
    intro n
    change Measurable ((fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      glueC ((n + 1 : ℕ) : ℝ) p.1 p.2) ∘ fun ω => (Y ω, W ω))
    exact (measurable_glueC ((n + 1 : ℕ) : ℝ)).comp (hY.prodMk hW)
  have hUlaw : ∀ n, P.map (U n) = μ := fun n => hμ (n + 1) (Nat.zero_lt_succ n)
  have hVlaw : ∀ n, P.map (V n) = ν := fun n => hν (n + 1) (Nat.zero_lt_succ n)
  apply continuousMap_law_eq_of_ae_eventually_restrict_eq P U V μ ν hU hV hUlaw hVlaw
  intro I
  filter_upwards [hhit, hzero] with ω hω h0
  have heq : ∀ t ∈ I, ∀ᶠ n : ℕ in atTop, U n ω t = V n ω t := by
    intro t ht
    have h := eventually_glueC_eqOn (Y ω) (Z ω) (W ω) hω h0 t
    have h' : ∀ᶠ n : ℕ in atTop, n + 1 ∈ {m : ℕ |
        Set.EqOn (glueC (m : ℝ) (Y ω) (Z ω))
          (glueC (m : ℝ) (Y ω) (W ω)) (Set.Iic t)} :=
      (tendsto_add_atTop_nat 1).eventually h
    filter_upwards [h'] with n hn
    exact hn (le_refl t)
  filter_upwards [(eventually_all_finset I).2 heq] with n hn
  ext t
  exact hn t.1 t.2

end LatticeProb
