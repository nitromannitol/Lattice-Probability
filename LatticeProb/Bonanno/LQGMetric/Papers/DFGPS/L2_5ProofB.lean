/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofBDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 B (T:1014–1019)

"To get the joint convergence (eqn-lfpp-dyadic), we first apply Lemma 2.9 and the Prokhorov
theorem to get that the joint law of the metrics on the left side of (eqn-lfpp-dyadic) is tight.
Moreover any subsequential limit of these joint laws is a coupling of a continuous length metric
`D_h` on `ℂ` and a length metric `D_{h,W}` on `W̄` for each `W ∈ 𝒲` which induces the Euclidean
topology on `W̄`. We then apply Lemma 2.11 to say that `D_{h,W}(·,·;W) = D_h(·,·;W)`."

Tightness: `isTightMeasureSet_dyProd` with `lem2_5_tight` and Lemma 2.9; Prokhorov:
`isCompact_closure_of_isTightMeasureSet`; marginals: `lem2_5_lim` and Lemma 2.9; Lemma 2.11:
its two steps via the closed conditions `dyC1`, `dyC2` (portmanteau) and
`isDyadicLimit_of` (see `L2_5ProofBDet.lean`; this replaces the Skorokhod coupling under which
DFGPS apply Lemma 2.11 to the a.s. convergent metrics, proposed DEVIATIONS entry DF-L25-B).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

section closureW

variable {ξ ε : ℝ} {g : DistC} {W : Set ℂ} (hW : IsDyadicDomain W) (hWc : IsConnected (closure W))
include hW hWc

theorem lfppDOn_closure_ne_top {φ : ℂ → ℝ} (hφ : Continuous φ) :
    ∀ x ∈ closure W, ∀ y ∈ closure W, lfppDOn ξ φ (closure W) x y ≠ ⊤ := by
  obtain ⟨𝒮, h𝒮, rfl⟩ := id hW
  have he := closure_dyadicDomain_eq h𝒮
  rw [he] at hWc ⊢
  exact lfppDOn_union_ne_top hφ 𝒮 (dyadic_squares_closedSq h𝒮) hWc.isPreconnected

theorem lfppSqC_closure_apply (hc : Continuous (heatMollify ε g)) (p : closure W × closure W) :
    lfppSqC ξ ε g (closure W) p =
      (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε g) (closure W) p.1 p.2).toReal := by
  have hcont : Continuous fun p : closure W × closure W =>
      (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε g) (closure W) p.1 p.2).toReal := by
    obtain ⟨𝒮, h𝒮, rfl⟩ := id hW
    have he := closure_dyadicDomain_eq h𝒮
    rw [he] at hWc ⊢
    exact continuous_lfppDOn_union_toReal hc 𝒮 (dyadic_squares_closedSq h𝒮) hWc.isPreconnected _
  exact toCMap_apply_of_continuous hcont p

theorem aemeasurable_lfppSqC_closure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hm : Measurable h) (hc : ∀ᵐ ω ∂P, Continuous (heatMollify ε (h ω))) :
    AEMeasurable (fun ω => lfppSqC ξ ε (h ω) (closure W)) P := by
  obtain ⟨𝒮, h𝒮, rfl⟩ := id hW
  have he := closure_dyadicDomain_eq h𝒮
  rw [he] at hWc ⊢
  exact aemeasurable_lfppSqC_union hm hc 𝒮 (dyadic_squares_closedSq h𝒮) hWc.isPreconnected

end closureW

/-- the joint metric `(𝔞_ε⁻¹ D_h^ε, {𝔞_ε⁻¹ D_h^ε(·,·;W̄)}_W)` -/
def lfppJoint (ξ ε : ℝ) (g : DistC) : DyProd :=
  ((lfppC ξ ε g, fun W : dyadicDomainsC => lfppSqC ξ ε g (closure W)) : DyProd)

theorem lfppJoint_mem_dyC1 {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    (W : dyadicDomainsC) : lfppJoint ξ ε g ∈ dyC1 W := by
  intro u v
  show lfppC ξ ε g (u.1, v.1) ≤ lfppSqC ξ ε g (closure W) (u, v)
  rw [lfppC_apply_of_continuous hc, lfppSqC_closure_apply W.2.1 W.2.2 hc]
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
    (lfppDOn_closure_ne_top W.2.1 W.2.2 hc _ u.2 _ v.2) (lfppDistE_le_lfppDOn _ _ _ _ _ _))
    (inv_nonneg.2 (aEpsDF_nonneg_sq _ _))

theorem lfppJoint_mem_dyC2 {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    (W : dyadicDomainsC) : lfppJoint ξ ε g ∈ dyC2 W := by
  intro u v hw
  change ∀ w : closure (W : Set ℂ), w.1 ∈ frontier (closure (W : Set ℂ)) →
    lfppC ξ ε g (u.1, v.1) < lfppC ξ ε g (u.1, w.1) at hw
  show lfppSqC ξ ε g (closure W) (u, v) ≤ lfppC ξ ε g (u.1, v.1)
  have hKc : IsCompact (closure (W : Set ℂ)) := isCompact_closure_dyadicDomainsC W
  have hc0 : 0 ≤ (aEpsDF ξ ε)⁻¹ := inv_nonneg.2 (aEpsDF_nonneg_sq _ _)
  have hlt : lfppDistE ξ ε g u.1 v.1 <
      ⨅ w ∈ frontier (closure (W : Set ℂ)), lfppDistE ξ ε g u.1 w := by
    rcases (frontier (closure (W : Set ℂ))).eq_empty_or_nonempty with he | hne
    · rw [he]; simpa using (lfppDistE_ne_top' hc u.1 v.1).lt_top
    have hFc : IsCompact (frontier (closure (W : Set ℂ))) :=
      hKc.of_isClosed_subset isClosed_frontier isClosed_closure.frontier_subset
    have hcont : Continuous fun w => (lfppDistE ξ ε g u.1 w).toReal := by
      have := (continuous_lfppDReal (ξ := ξ) hc).comp
        (Continuous.prodMk (continuous_const (y := (u.1 : ℂ))) continuous_id)
      convert this using 2 with w
      simp only [Function.comp_apply, lfppDReal, lfppDistE_eq_lfppDOn]; rfl
    obtain ⟨w0, hw0, hmin⟩ := hFc.exists_isMinOn hne hcont.continuousOn
    have hw0' := hw ⟨w0, isClosed_closure.frontier_subset hw0⟩ hw0
    simp only [lfppC_apply_of_continuous hc] at hw0'
    rcases hc0.eq_or_lt with h0 | h0
    · rw [← h0] at hw0'; simp at hw0'
    have hr : (lfppDistE ξ ε g u.1 v.1).toReal < (lfppDistE ξ ε g u.1 w0).toReal :=
      lt_of_mul_lt_mul_left hw0' hc0
    refine lt_of_lt_of_le ((ENNReal.toReal_lt_toReal (lfppDistE_ne_top' hc _ _)
      (lfppDistE_ne_top' hc _ _)).1 hr) (le_iInf₂ fun w hw' => ?_)
    have := hmin hw'
    simp only [mem_ofPred_eq] at this
    exact (ENNReal.toReal_le_toReal (lfppDistE_ne_top' hc _ _) (lfppDistE_ne_top' hc _ _)).1 this
  have heq := lfppDistE_eq_lfppDOn_of_lt isClosed_closure u.2 hlt
  rw [lfppC_apply_of_continuous hc, lfppSqC_closure_apply W.2.1 W.2.2 hc, ← heq]

theorem aemeasurable_lfppJoint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P) {ξ ε : ℝ} (hε : ε ≠ 0) :
    AEMeasurable (fun ω => lfppJoint ξ ε (h ω)) P := by
  have hc : ∀ᵐ ω ∂P, Continuous (heatMollify ε (h ω)) :=
    (hh.ae_tendstoLocallyUniformly_heatMollify ε hε).mono fun ω hω => hω.2
  have key : AEMeasurable (β := C(ℂ × ℂ, ℝ) × DyFam) (fun ω => lfppJoint ξ ε (h ω)) P :=
    (aemeasurable_lfppC hh hε).prodMk (AEMeasurable.of_eval fun W =>
      aemeasurable_lfppSqC_closure W.2.1 W.2.2 hh.1 hc)
  have hid : @Measurable (C(ℂ × ℂ, ℝ) × DyFam) DyProd _ _ (fun x => x) := by
    intro t ht
    rw [BorelSpace.measurable_eq (α := C(ℂ × ℂ, ℝ) × DyFam)]
    exact ht
  exact hid.comp_aemeasurable key

end LQGMetric.DFGPS
