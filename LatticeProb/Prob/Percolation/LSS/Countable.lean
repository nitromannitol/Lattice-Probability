import LatticeProb.Prob.Percolation.LSS.Cylinder
import LatticeProb.Prob.Percolation.LSS.DependencyGraph
import LatticeProb.Prob.Percolation.LSS.DominationCouple
import LatticeProb.Prob.Percolation.LSS.DominationFinite
import LatticeProb.Prob.Percolation.LSS.General
import LatticeProb.Prob.Percolation.LSS.UpHull

/-!
# Domination by product measures: from finitely many coordinates to all events

Ported from the Exploding-Sandpiles formalization, `Support/ExtLSSCountable.lean`.

A closed increasing set is the intersection of its cylinder hulls over the finite coordinate
sets. Each hull is an increasing set determined by finitely many coordinates, so the
finite-coordinate estimate dominates it, and continuity from above passes the domination to
the closed set. A measurable increasing set is approximated from inside by closed sets, whose
increasing hulls are closed increasing subsets of it.

This discharges the finite-to-countable estimate `xlss_finite_to_countable`, and with it the
two domination statements `LiggettSchonmannStaceyBoundedDegree` and `LiggettSchonmannStacey`
of `LatticeProb.Percolation.LSS.Defs`.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace LatticeProb.Percolation.LSS

variable {S : Type}

/-- Domination of a closed increasing set.  The set is the intersection of its cylinder
hulls over the finite coordinate sets, each dominated by the finite-coordinate estimate. -/
theorem xlse_dom_isClosed [Countable S] [DecidableEq S] (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ] (ρ γ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hthin : ∀ T : Finset S, ∃ w, XlssThin μ ρ γ T w)
    {F : Set (S → Bool)} (hF : IsClosed F) (hinc : IsIncreasingSet F) :
    bernoulliProduct S ρ F ≤ μ F := by
  have := xlsd_isProbabilityMeasure (S := S) ρ hρ0 hρ1
  have hiInf : ∀ ν : Measure (S → Bool), IsProbabilityMeasure ν →
      ν F = ⨅ T : Finset S, ν (xlsb_cylHull T F) := by
    intro ν hν
    conv_lhs => rw [← xlsb_iInter_cylHull hF]
    rw [measure_iInter_eq_iInf_measure_iInter_le
      (fun T => (xlsb_measurableSet_cylHull T F).nullMeasurableSet) ⟨∅, measure_ne_top _ _⟩]
    exact iInf_congr fun T => by rw [xlsb_biInter_le_eq]
  rw [hiInf (bernoulliProduct S ρ) inferInstance, hiInf μ inferInstance]
  refine iInf_mono fun T => ?_
  obtain ⟨w, hw⟩ := hthin T
  exact xlss7_dom_fin μ ρ γ hρ0 hρ1 T w hw _ (xlsb_measurableSet_cylHull T F)
    (xlsb_cylHull_increasing T hinc) (fun x y hxy => xlsb_cylHull_det T F x y hxy)

/-- Domination of every measurable increasing set, by inner approximation with closed sets
and their increasing hulls. -/
theorem xlse_dom_increasing [Countable S] [DecidableEq S] (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ] (ρ γ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hthin : ∀ T : Finset S, ∃ w, XlssThin μ ρ γ T w)
    {A : Set (S → Bool)} (hA : MeasurableSet A) (hinc : IsIncreasingSet A) :
    bernoulliProduct S ρ A ≤ μ A := by
  rw [xlsd_measure_eq_iSup_isClosed ρ hρ0 hρ1 hA]
  refine iSup_le fun F => iSup_le fun hFA => iSup_le fun hF => ?_
  calc bernoulliProduct S ρ F
      ≤ bernoulliProduct S ρ (xlsc_upHull F) := measure_mono (xlsc_subset_upHull F)
    _ ≤ μ (xlsc_upHull F) :=
        xlse_dom_isClosed μ ρ γ hρ0 hρ1 hthin (xlsc_isClosed_upHull hF)
          (xlsc_upHull_increasing F)
    _ ≤ μ A := measure_mono (xlsc_upHull_subset hinc hFA)

/-- The thinning on a single site forces the product density into `[0, 1]`: its marginal
law at that site is `ρ`, and the weights lie in `[0, 1]`. -/
theorem xlse_density_bounds [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) (s : S) (w : S → Bool → Finset S → ℝ) (hw : XlssThin μ ρ γ {s} w) :
    0 ≤ ρ ∧ ρ ≤ 1 := by
  have hmarg := hw.marg {s} (Finset.Subset.refl _)
  simp only [Finset.card_singleton, pow_one, Nat.sub_self, pow_zero, mul_one] at hmarg
  have hbd : ∀ x : S → Bool, 0 ≤ ∏ l ∈ ({s} : Finset S), w l (x l) {s} ∧
      ∏ l ∈ ({s} : Finset S), w l (x l) {s} ≤ 1 := by
    intro x
    rw [Finset.prod_singleton]
    exact hw.bd s (Finset.mem_singleton_self s) {s} (Finset.Subset.refl _) (x s)
  have hint : Integrable (fun x : S → Bool => ∏ l ∈ ({s} : Finset S), w l (x l) {s}) μ :=
    xlss_integrable_prod μ {s} (fun l b => w l b {s})
      (fun l hl b => hw.bd l hl {s} (Finset.Subset.refl _) b)
  constructor
  · rw [← hmarg]
    exact integral_nonneg fun x => (hbd x).1
  · rw [← hmarg]
    calc ∫ x, ∏ l ∈ ({s} : Finset S), w l (x l) {s} ∂μ
        ≤ ∫ _x, (1 : ℝ) ∂μ := integral_mono hint (integrable_const 1) fun x => (hbd x).2
      _ = 1 := by simp

/-- On an empty index set every configuration coincides, so an increasing measurable set is
empty or everything, and both laws are probability measures. -/
theorem xlse_dom_of_isEmpty [IsEmpty S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ : ℝ) {A : Set (S → Bool)} : bernoulliProduct S ρ A ≤ μ A := by
  have : ∀ i : S, IsProbabilityMeasure (bitLaw ρ) := fun i => isEmptyElim i
  have : IsProbabilityMeasure (bernoulliProduct S ρ) := by
    unfold bernoulliProduct
    infer_instance
  rcases Set.eq_empty_or_nonempty A with hAe | hAne
  · simp [hAe]
  · rw [hAne.eq_univ, measure_univ, measure_univ]

/-- **The finite-to-countable estimate.**  On a nonempty index set the thinning on one site
bounds the density, and the two domination steps apply; on an empty index set the claim is
the comparison of two probability measures on a one-point space. -/
theorem xlse_finite_to_countable : xlss_finite_to_countable := by
  intro S _ _ μ _ ρ γ hthin A hA hinc
  rcases isEmpty_or_nonempty S with hS | hS
  · exact xlse_dom_of_isEmpty μ ρ
  · obtain ⟨s⟩ := hS
    obtain ⟨w, hw⟩ := hthin {s}
    obtain ⟨hρ0, hρ1⟩ := xlse_density_bounds μ ρ γ s w hw
    exact xlse_dom_increasing μ ρ γ hρ0 hρ1 hthin hA hinc

/-- **Corollary 1.4 of Liggett, Schonmann and Stacey**, the bounded-degree domination of a
dependent field of bits by a product measure, with no remaining hypothesis. -/
theorem xlse_lss_bounded_degree : LiggettSchonmannStaceyBoundedDegree :=
  xlss_proved xlse_finite_to_countable

/-- **Theorem 0.0 of Liggett, Schonmann and Stacey**, the domination of a finitely dependent
field of bits on `ℤ^d` by a product measure, with no remaining hypothesis. -/
theorem xlse_lss_general : LiggettSchonmannStacey :=
  xlssg_of_bd xlse_lss_bounded_degree

end LatticeProb.Percolation.LSS
