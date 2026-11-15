/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianContinuityCells at commit fdb5cad; local imports and linter settings are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitReference
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuityCells

set_option linter.style.haveILetI false

/-!
# One continuity partition for a finite family of actual Brownian exit laws

The reference is the finite sum of the actual Gaussian-start exit references.
Every interior-start exit law for every member of the family is dominated by
this same measure, so each stage may use one common spatial cell labelling.
-/

open MeasureTheory ProbabilityTheory Set
namespace BouRabeeGwynne

theorem exists_common_brownian_exit_continuity_cells {d : ℕ} (hd : 1 ≤ d)
    {ι : Type*} [Fintype ι] {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (U : ι → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (hUb : ∀ j, Bornology.IsBounded (U j))
    {K : Set (Euc d)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (E : Fin n → Set (Euc d)),
      Pairwise (fun i j ↦ Disjoint (E i) (E j)) ∧ K ⊆ ⋃ i, E i ∧
      (∀ i, MeasurableSet (E i)) ∧ (∀ i, Bornology.IsBounded (E i)) ∧
      (∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist x y < ε) ∧
      ∀ j z, z ∈ U j → ∀ i,
        ((stoppedBrownianLaw (U j) z μ).map CurveSpace.endPoint) (frontier (E i)) = 0 := by
  classical
  letI : IsProbabilityMeasure μ := hμ.1
  let γ : Measure (Euc d) := ∑ j, brownianExitReferenceLaw (U j) μ
  haveI : IsFiniteMeasure γ := by
    dsimp [γ, brownianExitReferenceLaw]
    infer_instance
  obtain ⟨n, E, hdisj, hcover, hmeas, hbounded, hnull, hdiam⟩ :=
    exists_finite_small_nullFrontier_cells γ hK hε
  refine ⟨n, E, hdisj, hcover, hmeas, hbounded, hdiam, ?_⟩
  intro j z hz i
  have hle : brownianExitReferenceLaw (U j) μ ≤ γ :=
    Finset.single_le_sum (f := fun k ↦ brownianExitReferenceLaw (U k) μ)
      (fun k hk ↦ bot_le) (Finset.mem_univ j)
  exact ((standardBrownianLaw_exit_absolutelyContinuous_reference hd hμ (hU j) (hUb j) hz).trans
    hle.absolutelyContinuous) (hnull i)

end BouRabeeGwynne
