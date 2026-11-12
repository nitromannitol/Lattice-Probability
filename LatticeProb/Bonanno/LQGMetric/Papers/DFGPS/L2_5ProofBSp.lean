/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofBSp at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofLim
import LatticeProb.Bonanno.LQGMetric.LFPP.Dyadic
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 B: the state space `DyProd` and tightness of the joint laws

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:1014–1016: "we first apply
Lemma 2.9 and the Prokhorov theorem to get that the joint law of the metrics on the left side of
(eqn-lfpp-dyadic) is tight". The class `𝒲` of dyadic domains is countable
(`dyadicDomains_countable`), each `C(W̄ × W̄, ℝ)` is Polish (`W̄` compact), so `DyProd` is Polish;
a family of laws on `DyProd` whose marginals are tight is tight (countable union bound with
summable errors, Tychonoff).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

instance : Countable dyadicDomainsC :=
  (dyadicDomains_countable.mono fun _ hW => hW.1).to_subtype

theorem isCompact_closure_dyadicDomainsC (W : dyadicDomainsC) : IsCompact (closure (W : Set ℂ)) :=
  W.2.1.isBounded.isCompact_closure

instance (W : dyadicDomainsC) : CompactSpace (closure (W : Set ℂ)) :=
  isCompact_iff_compactSpace.1 (isCompact_closure_dyadicDomainsC W)

instance : PolishSpace DyProd := inferInstanceAs (PolishSpace (C(ℂ × ℂ, ℝ) × DyFam))

theorem continuous_dyProd_fst : Continuous (fun x : DyProd => x.1) := continuous_fst

theorem continuous_dyProd_snd (W : dyadicDomainsC) : Continuous (fun x : DyProd => x.2 W) :=
  (continuous_apply W).comp continuous_snd

/-- **tightness from tight marginals** on `DyProd` (countable product) -/
theorem isTightMeasureSet_dyProd {S : Set (Measure DyProd)}
    (h0 : IsTightMeasureSet ((fun μ : Measure DyProd => μ.map fun x : DyProd => x.1) '' S))
    (hW : ∀ W : dyadicDomainsC,
      IsTightMeasureSet ((fun μ : Measure DyProd => μ.map fun x : DyProd => x.2 W) '' S)) :
    IsTightMeasureSet S := by
  have hW := fun W => isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 (hW W)
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h0 ⊢
  intro e he
  have he2 : (e / 2 : ℝ≥0∞) ≠ 0 := (ENNReal.half_pos he.ne').ne'
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable he2 dyadicDomainsC
  obtain ⟨K0, hK0, hK0m⟩ := h0 (e / 2) (ENNReal.half_pos he.ne')
  choose KW hKW hKWm using fun W => hW W (ε' W) (by simpa using hε'pos W)
  refine ⟨K0 ×ˢ (univ.pi KW), hK0.prod (isCompact_univ_pi hKW), fun μ hμ => ?_⟩
  have hsub : (K0 ×ˢ (univ.pi KW) : Set DyProd)ᶜ ⊆
      ((fun x : DyProd => x.1) ⁻¹' K0ᶜ) ∪ ⋃ W, (fun x : DyProd => x.2 W) ⁻¹' (KW W)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_prod, mem_univ_pi, not_and_or, not_forall] at hx
    rcases hx with h | ⟨W, hW⟩
    · exact Or.inl h
    · exact Or.inr (mem_iUnion.2 ⟨W, hW⟩)
  have hm0 : μ ((fun x : DyProd => x.1) ⁻¹' K0ᶜ) ≤ e / 2 := by
    have := hK0m _ ⟨μ, hμ, rfl⟩
    rwa [Measure.map_apply continuous_dyProd_fst.measurable hK0.isClosed.isOpen_compl.measurableSet]
      at this
  have hmW : ∀ W, μ ((fun x : DyProd => x.2 W) ⁻¹' (KW W)ᶜ) ≤ ε' W := by
    intro W
    have := hKWm W _ ⟨μ, hμ, rfl⟩
    rwa [Measure.map_apply (continuous_dyProd_snd W).measurable
      (hKW W).isClosed.isOpen_compl.measurableSet] at this
  calc μ (K0 ×ˢ (univ.pi KW) : Set DyProd)ᶜ
      ≤ μ ((fun x : DyProd => x.1) ⁻¹' K0ᶜ) + μ (⋃ W, (fun x : DyProd => x.2 W) ⁻¹' (KW W)ᶜ) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ e / 2 + ∑' W, (ε' W : ℝ≥0∞) :=
        add_le_add hm0 ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hmW))
    _ ≤ e / 2 + e / 2 := add_le_add le_rfl hε'sum.le
    _ = e := ENNReal.add_halves e

end LQGMetric.DFGPS
