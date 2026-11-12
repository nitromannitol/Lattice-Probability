/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea4 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Vague
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Fact
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability

/-!
For an open bounded `U ⊆ ℍ` and a sequence of measures `μs`, `AreaGood U μs` says that `μs` has a
vague limit on `U` and is eventually finite on every compact subset of `U`; `AreaCert U μs` is a
countable certificate for it: convergence of the test integrals of `openBump U n · g` (QZ's
cut-offs, `g` in LM's fixed countable dense family `GMCIdent3.denseF`) and eventual finiteness on
the compacts `cutSet U n = {1 ≤ n · d(·, Uᶜ)}`.

* `areaGood_of_cert`, `cert_of_areaGood`: the two are equivalent (QZ
  `VagueOpen.exists_isVagueLimitOn_of_cutoff`, the Riesz–Markov step of Duplantier–Sheffield
  arXiv:0808.1560 Prop. 1.1, and the definition of vague convergence);
* `measurableSet_areaCert`: for the whole-plane approximations `areaApproxC γ x`, the certificate
  is a measurable event in the field sample `x`.

This is LM `GMCIdent3.VagueGood` / `measurableSet_vagueGood` (Dimension/GMCIdent3Vague.lean),
copied and adapted from the square `𝕍` with `sqCut` to an arbitrary open bounded `U ⊆ ℍ` with
`openBump`, and from QZ's `areaApprox` to `areaApproxC`. It is the measurable event used for the
law transfer in `ConeArea4C` (LM decision D85 route).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea4

open QuantumZipper QuantumZipper.LQGMeas LQGMetric

/-- the compacts exhausting `U` -/
def cutSet (U : Set ℂ) (n : ℕ) : Set ℂ := {z | 1 ≤ (n : ℝ) * infDist z Uᶜ}

lemma cutSet_subset (U : Set ℂ) (n : ℕ) : cutSet U n ⊆ U := setOf_one_le_infDist_subset U n

lemma isClosed_cutSet (U : Set ℂ) (n : ℕ) : IsClosed (cutSet U n) :=
  isClosed_le continuous_const (continuous_const.mul (continuous_infDist_pt _))

lemma isCompact_cutSet {U : Set ℂ} (hU : Bornology.IsBounded U) (n : ℕ) :
    IsCompact (cutSet U n) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_cutSet U n) (hU.subset (cutSet_subset U n))

/-- a compact subset of `U` lies in some `cutSet U n`, on which `openBump U n = 1` -/
lemma exists_cutSet {U : Set ℂ} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ n : ℕ, K ⊆ cutSet U n ∧ ∀ z ∈ K, openBump U n z = 1 := by
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ z ∈ K, δ ≤ infDist z Uᶜ := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact absurd hz (notMem_empty z)⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne (continuous_infDist_pt _).continuousOn
    exact ⟨_, (hU.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h => h (hKU hz₀)),
      fun z hz => hmin hz⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ)
  have h2 : ∀ z ∈ K, 2 ≤ (n : ℝ) * infDist z Uᶜ := fun z hz => by
    rw [div_lt_iff₀ hδ] at hn
    nlinarith [hδK z hz]
  refine ⟨n, fun z hz => ?_, fun z hz => ?_⟩
  · exact le_trans (by norm_num) (h2 z hz)
  · rw [openBump, max_eq_right (by linarith [h2 z hz]), min_eq_left (by linarith [h2 z hz])]

/-- local vague limit on `U` together with eventual finiteness on compacts of `U` -/
def AreaGood (U : Set ℂ) (μs : ℕ → Measure ℂ) : Prop :=
  (∃ μ, IsVagueLimitOn U μs μ) ∧ ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, μs k K < ⊤

/-- the countable certificate of `AreaGood` -/
def AreaCert (U : Set ℂ) (μs : ℕ → Measure ℂ) : Prop :=
  (∀ n : ℕ, ∀ g ∈ GMCIdent3.denseF, ∃ l,
    Tendsto (fun k => ∫ z, openBump U n z * g z ∂(μs k)) atTop (𝓝 l)) ∧
  ∀ n : ℕ, ∀ᶠ k in atTop, μs k (cutSet U n) < ⊤

theorem areaGood_of_cert {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) (hUc : Uᶜ.Nonempty)
    {μs : ℕ → Measure ℂ} (h : AreaCert U μs) : AreaGood U μs := by
  have hfin : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, μs k K < ⊤ := by
    intro K hK hKU
    obtain ⟨n, hn, -⟩ := exists_cutSet hU hUc hK hKU
    filter_upwards [h.2 n] with k hk using (measure_mono hn).trans_lt hk
  refine ⟨VagueOpen.exists_isVagueLimitOn_of_cutoff hU hUH (continuous_openBump U)
    (openBump_nonneg U) (openBump_le_one U) (tsupport_openBump_subset U) ?_
    GMCIdent3.denseF_dense hfin h.1, hfin⟩
  intro K hK hKU
  obtain ⟨n, -, hn⟩ := exists_cutSet hU hUc hK hKU
  exact ⟨n, hn⟩

theorem cert_of_areaGood {U : Set ℂ} (hUb : Bornology.IsBounded U) {μs : ℕ → Measure ℂ}
    (h : AreaGood U μs) : AreaCert U μs := by
  obtain ⟨⟨μ, hμ⟩, hfin⟩ := h
  refine ⟨fun n g hg => ⟨_, hμ.2.2 _ ?_ ?_ ?_⟩, fun n =>
    hfin _ (isCompact_cutSet hUb n) (cutSet_subset U n)⟩
  · exact (continuous_openBump U n).mul (GMCIdent3.denseF_dense.1 g hg).1
  · exact (GMCIdent3.denseF_dense.1 g hg).2.1.mul_left
  · exact tsupport_mul_subset_left.trans (tsupport_openBump_subset U n)

/-- the density of `areaApproxC` is jointly measurable in the point and the field sample -/
lemma measurable_densC (γ : ℝ) (k : ℕ) :
    Measurable fun p : ℂ × Field => radius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * circleAvg p.2 (radius k) p.1) := by
  have h1 : Measurable fun p : ℂ × Field => circleAvg p.2 (radius k) p.1 :=
    measurable_circleAvg.comp (f := fun p : ℂ × Field => (p.2, radius k, p.1))
      (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))
  exact (Real.measurable_exp.comp (h1.const_mul γ)).const_mul _

/-- test integrals of the approximations are measurable in the field sample -/
lemma measurable_integral_areaApproxC (γ : ℝ) (k : ℕ) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable fun x : Field => ∫ z, f z ∂(areaApproxC γ x k) := by
  have e : (fun x : Field => ∫ z, f z ∂(areaApproxC γ x k)) = fun x => ∫ z,
      (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg x (radius k) z)) * f z := by
    funext x
    exact GMCIdent4.integral_withDensity_ofReal
      ((measurable_densC γ k).comp (measurable_id.prodMk measurable_const))
      (fun z => mul_nonneg (by have := QuantumZipper.radius_pos k; positivity) (Real.exp_pos _).le) f
  rw [e]
  exact (((measurable_densC γ k).mul (hf.comp measurable_fst)).stronglyMeasurable
    |>.integral_prod_left).measurable

theorem measurableSet_areaCert (γ : ℝ) (U : Set ℂ) :
    MeasurableSet {x : Field | AreaCert U (areaApproxC γ x)} := by
  unfold AreaCert
  simp only [ofPred_and, ofPred_forall, eventually_atTop]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => MeasurableSet.biInter
    GMCIdent3.denseF_countable fun g hg => ?_) (MeasurableSet.iInter fun n => ?_)
  · exact StronglyMeasurable.measurableSet_exists_tendsto fun k =>
      (measurable_integral_areaApproxC γ k ((continuous_openBump U n).mul
        (GMCIdent3.denseF_dense.1 g hg).1).measurable).stronglyMeasurable
  · simp only [ofPred_exists, ofPred_forall]
    refine MeasurableSet.iUnion fun (N : ℕ) => MeasurableSet.iInter fun (k : ℕ) =>
      MeasurableSet.iInter fun (_ : N ≤ k) => ?_
    exact measurableSet_lt ((Measure.measurable_coe (isClosed_cutSet U n).measurableSet).comp
      (ConeArea.measurable_areaApproxC γ k)) measurable_const

end ConeArea4
end MatedCRTHarmonic.MoTPort
