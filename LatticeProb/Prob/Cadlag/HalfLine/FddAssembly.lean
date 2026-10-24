import LatticeProb.External.EthierKurtzSkorokhod
import LatticeProb.Prob.ProductTests
import LatticeProb.Topology.EpsFilter
import Mathlib.Data.Finset.Sort

/-!
# Assembly of path-law convergence from positive-time product tests

Marginal tightness supplies tightness of finite evaluation families. Ordered distinct
positive-time product tests then determine all positive-time joint laws by reindexing.
The cited Ethier–Kurtz implication and the sequential epsilon criterion finish the assembly.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace BoundedContinuousFunction
open scoped Topology ENNReal

noncomputable section

variable {E : Type} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Finite evaluation laws are tight whenever each of their time marginals is tight.
The compactness assumption records the intended path-law application; marginal tightness
is supplied explicitly because evaluation is not continuous on the Skorokhod space. -/
theorem jointLaw_tight_of_relativelyCompact {I : Type*}
    (μ : I → ProbabilityMeasure (D E))
    (_hcompact : IsCompact (closure (range μ)))
    (hmarg : ∀ t : Time,
      IsTightMeasureSet {Measure.map (fun w : D E => w.1 t) (μ i : Measure (D E)) | i})
    {k : ℕ} (ts : Fin k → Time) :
    IsTightMeasureSet {(jointLaw (μ i) ts : Measure (Fin k → E)) | i} := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hδ : 0 < ε / (k + 1 : ℝ≥0∞) := ENNReal.div_pos hε.ne' (by simp)
  have hK := fun j : Fin k =>
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp (hmarg (ts j))) _ hδ
  choose K hKcompact hKbound using hK
  refine ⟨Set.pi univ K, isCompact_univ_pi hKcompact, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hpre : (Set.pi univ K)ᶜ = ⋃ j, {x : Fin k → E | x j ∉ K j} := by
    ext x
    simp
  rw [hpre]
  calc
    _ ≤ ∑ j : Fin k, (jointLaw (μ i) ts : Measure (Fin k → E))
        {x | x j ∉ K j} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin k, ε / (k + 1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro j _
      have hj := hKbound j _ ⟨i, rfl⟩
      rw [Measure.map_apply (measurable_eval (ts j)) (hKcompact j).isClosed.measurableSet.compl]
        at hj
      change (Measure.map (fun w : D E => fun l : Fin k => w.1 (ts l))
        (μ i : Measure (D E))) ((fun x : Fin k → E => x j) ⁻¹' (K j)ᶜ) ≤ _
      rw [Measure.map_apply (measurable_pi_lambda _ (fun l => measurable_eval (ts l)))
        ((hKcompact j).isClosed.measurableSet.compl.preimage (measurable_pi_apply j))]
      exact hj
    _ ≤ ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (k : ℝ≥0∞) * (ε / (k + 1 : ℝ≥0∞)) ≤
            (k + 1 : ℝ≥0∞) * (ε / (k + 1 : ℝ≥0∞)) := by gcongr; simp
        _ = ε := ENNReal.mul_div_cancel (by simp) (by simp)

/-- Joint-law product integrals are the product expectations of the path evaluations. -/
theorem integral_jointLaw_productTest [SecondCountableTopology E]
    (μ : ProbabilityMeasure (D E)) {k : ℕ}
    (ts : Fin k → Time) (φ : Fin k → E →ᵇ ℝ) :
    (∫ x, ∏ j, φ j (x j) ∂(jointLaw μ ts : Measure (Fin k → E))) =
      ∫ w : D E, ∏ j, φ j (w.1 (ts j)) ∂(μ : Measure (D E)) := by
  simpa only [jointLaw, ProbabilityMeasure.toMeasure_map, LatticeProb.productTest_apply]
    using (integral_map (μ := (μ : Measure (D E)))
      (measurable_pi_lambda _ (fun j : Fin k => measurable_eval (ts j))).aemeasurable
      (LatticeProb.productTest φ).continuous.aestronglyMeasurable)

/-- Repeating or reordering an evaluation family is a continuous pushforward of its law. -/
theorem jointLaw_reindex (μ : ProbabilityMeasure (D E)) {k m : ℕ}
    (ts : Fin m → Time) (r : Fin k → Fin m) :
    jointLaw μ (ts ∘ r) = (jointLaw μ ts).map
      (measurable_pi_lambda _ (fun i => measurable_pi_apply (r i))).aemeasurable := by
  apply Subtype.ext
  change Measure.map _ (μ : Measure (D E)) = Measure.map _ (Measure.map _ (μ : Measure (D E)))
  rw [Measure.map_map (measurable_pi_lambda _ (fun i => measurable_pi_apply (r i)))
    (measurable_pi_lambda _ (fun i => measurable_eval (ts i)))]
  rfl

/-- Product tests at strictly increasing positive times determine every positive-time joint law. -/
theorem tendsto_jointLaw_of_productTests [PolishSpace E]
    {μ : ℕ → ProbabilityMeasure (D E)} {ν : ProbabilityMeasure (D E)}
    (htight : ∀ {k : ℕ} (ts : Fin k → Time),
      IsTightMeasureSet {(jointLaw (μ n) ts : Measure (Fin k → E)) | n})
    (hprod : ∀ {m : ℕ} (ss : Fin m → Time), StrictMono ss → (∀ j, 0 < ss j) →
      ∀ φ : Fin m → E →ᵇ ℝ,
      Tendsto (fun n => ∫ x, ∏ j, φ j (x j)
        ∂(jointLaw (μ n) ss : Measure (Fin m → E))) atTop
        (𝓝 (∫ x, ∏ j, φ j (x j) ∂(jointLaw ν ss : Measure (Fin m → E)))))
    {k : ℕ} (ts : Fin k → Time) (hpos : ∀ i, 0 < ts i) :
    Tendsto (fun n => jointLaw (μ n) ts) atTop (𝓝 (jointLaw ν ts)) := by
  classical
  let s := Finset.univ.image ts
  let e := s.orderIsoOfFin rfl
  let ss : Fin s.card → Time := s.orderEmbOfFin rfl
  let r : Fin k → Fin s.card := fun i => e.symm ⟨ts i, Finset.mem_image.mpr ⟨i,
    Finset.mem_univ i, rfl⟩⟩
  have hts : ss ∘ r = ts := by
    funext i
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hspos : ∀ j, 0 < ss j := by
    intro j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem rfl j)
    change 0 < s.orderEmbOfFin rfl j
    rw [← hi]
    exact hpos i
  have hconv := LatticeProb.tendsto_of_product_tests (htight ss)
    (hprod ss (s.orderEmbOfFin rfl).strictMono hspos)
  have hc : Continuous (fun x : Fin s.card → E => x ∘ r) :=
    continuous_pi fun i => continuous_apply (r i)
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv hc
  have heq (ρ : ProbabilityMeasure (D E)) :
      jointLaw ρ (ss ∘ r) = (jointLaw ρ ss).map hc.measurable.aemeasurable := by
    exact jointLaw_reindex ρ ss r
  have hmap' : Tendsto (fun n => jointLaw (μ n) (ss ∘ r)) atTop
      (𝓝 (jointLaw ν (ss ∘ r))) := by
    simp only [heq]
    exact hmap
  simpa only [hts] using hmap'

/-- The positive times are dense in the half-line, including at its endpoint. -/
theorem dense_positive_times : Dense {t : Time | 0 < t} := by
  rw [dense_iff_closure_eq, show {t : Time | 0 < t} = Ioi 0 from rfl, closure_Ioi]
  apply Set.eq_univ_of_forall
  intro t
  change (0 : Time) ≤ t
  exact zero_le

/-- Relative compactness and positive-time product tests imply weak path-law convergence,
using the explicit cited Ethier–Kurtz finite-dimensional convergence implication. -/
theorem tendsto_of_relativelyCompact_productTests [SeparableSpace E] [PolishSpace E]
    (hFdd : LatticeProb.External.EthierKurtzConvergenceFromFdd)
    {μ : ℕ → ProbabilityMeasure (D E)} {ν : ProbabilityMeasure (D E)}
    (hcompact : IsCompact (closure (range μ)))
    (hmarg : ∀ t : Time,
      IsTightMeasureSet {Measure.map (fun w : D E => w.1 t) (μ n : Measure (D E)) | n})
    (hprod : ∀ {m : ℕ} (ss : Fin m → Time), StrictMono ss → (∀ j, 0 < ss j) →
      ∀ φ : Fin m → E →ᵇ ℝ,
      Tendsto (fun n => ∫ x, ∏ j, φ j (x j)
        ∂(jointLaw (μ n) ss : Measure (Fin m → E))) atTop
        (𝓝 (∫ x, ∏ j, φ j (x j) ∂(jointLaw ν ss : Measure (Fin m → E))))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply hFdd E μ ν hcompact
  refine ⟨{t : Time | 0 < t}, dense_positive_times, ?_⟩
  intro k ts hpos
  exact tendsto_jointLaw_of_productTests
    (jointLaw_tight_of_relativelyCompact μ hcompact hmarg) hprod ts hpos

/-- The assembly applies to the genuine Dirac law of a constant real path. -/
theorem tendsto_of_relativelyCompact_productTests_const
    (hFdd : LatticeProb.External.EthierKurtzConvergenceFromFdd) (a : ℝ) :
    Tendsto (fun _ : ℕ => constantLaw a) atTop (𝓝 (constantLaw a)) := by
  apply tendsto_of_relativelyCompact_productTests hFdd
  · simpa only [Set.range_const, isClosed_singleton.closure_eq] using
      (isCompact_singleton : IsCompact ({constantLaw a} : Set (ProbabilityMeasure (D ℝ))))
  · intro t
    simpa only [exists_const, Set.setOf_eq_eq_singleton'] using
      (isTightMeasureSet_singleton (μ :=
        Measure.map (fun w : D ℝ => w.1 t) (constantLaw a : Measure (D ℝ))))
  · intro m ss hmono hpos φ
    exact tendsto_const_nhds

omit [MeasurableSpace E] [BorelSpace E] in
/-- The sequential criterion transfers path-law convergence to the epsilon filter. -/
theorem tendsto_epsFilter_of_sequences {μ : LatticeProb.Eps → ProbabilityMeasure (D E)}
    {ν : ProbabilityMeasure (D E)}
    (hseq : ∀ ε : ℕ → LatticeProb.Eps,
      Tendsto (fun n => (ε n).val) atTop (𝓝 0) →
      Tendsto (μ ∘ ε) atTop (𝓝 ν)) :
    Tendsto μ LatticeProb.epsFilter (𝓝 ν) :=
  LatticeProb.tendsto_epsFilter_iff_seq.mpr hseq

end

end LatticeProb.Cadlag.HalfLine
