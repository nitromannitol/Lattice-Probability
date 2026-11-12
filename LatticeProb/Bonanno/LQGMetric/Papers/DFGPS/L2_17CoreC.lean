/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreC at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreD
import Mathlib.MeasureTheory.Measure.Prokhorov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the limit coupling and its independence (packets P-C/P-D)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3 (T:1236–1264): "By possibly passing to a further deterministic subsequence … we have the
convergence of joint laws (eqn-internal-joint-law-conv) … Since independence is preserved under
convergence in law, we obtain from (eqn-internal-metric-ind) and (eqn-internal-joint-law-conv)
that …". Decision D80, packets P-C (i) and P-D, abstract form.

* `exists_limit_coupling` — if the laws of `Yₙ` are tight, then along a subsequence the laws of
  `(X, Yₙ)` converge (Prokhorov, mathlib `isCompact_closure_of_isTightMeasureSet`) to a
  probability measure `ρ` on `S × T` whose first marginal is the law of `X`.
* `indep_of_tendsto_coupling` — if `(X, Aₙ, Bₙ)` converge in law to `ρ` (first marginal the law
  of `X`) and `σ(𝒢(X)) ∨ σ(Aₙ) ⫫ σ(ℋ(X)) ∨ σ(Bₙ)` for all `n`, then under `ρ` the coordinates
  satisfy `σ(𝒢(x)) ∨ σ(a) ⫫ σ(ℋ(x)) ∨ σ(b)` (`indep_sup_of_tendsto`). The sub-σ-algebras
  `𝒢, ℋ` of the Borel σ-algebra of `S` are passed as elements of a subtype, so that they are not
  local instances.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {S : Type*} [TopologicalSpace S] [mS : MeasurableSpace S] [BorelSpace S] [PolishSpace S]
  {T₁ T₂ : Type*} [TopologicalSpace T₁] [mT₁ : MeasurableSpace T₁] [BorelSpace T₁]
  [SecondCountableTopology T₁] [PseudoMetrizableSpace T₁] [T2Space T₁]
  [TopologicalSpace T₂] [mT₂ : MeasurableSpace T₂] [BorelSpace T₂]
  [SecondCountableTopology T₂] [PseudoMetrizableSpace T₂] [T2Space T₂]

/-- **the limit coupling** (T:1240–1256): if the laws of `Yₙ` are tight, then along a subsequence
the laws of `(X, Yₙ)` converge to a probability measure whose first marginal is the law of `X`
(Prokhorov). -/
theorem exists_limit_coupling {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    [SecondCountableTopology T] [PseudoMetrizableSpace T] [T2Space T] {X : Ω → S} (hX : Measurable X) {Yn : ℕ → Ω → T}
    (hYn : ∀ n, Measurable (Yn n)) (hYt : IsTightMeasureSet (range fun n => P.map (Yn n))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ ρ : ProbabilityMeasure (S × T),
      Tendsto (β := ProbabilityMeasure (S × T))
        (fun n => (⟨P.map fun ω => (X ω, Yn (ψ n) ω),
          (Measure.isProbabilityMeasure_map_iff (hX.prodMk (hYn (ψ n))).aemeasurable).2
            inferInstance⟩ : ProbabilityMeasure (S × T))) atTop (𝓝 ρ) ∧
      (ρ : Measure (S × T)).map Prod.fst = P.map X := by
  have hJ : ∀ n, Measurable fun ω => (X ω, Yn n ω) := fun n => hX.prodMk (hYn n)
  let law : ℕ → ProbabilityMeasure (S × T) := fun n =>
    ⟨P.map fun ω => (X ω, Yn n ω),
      (Measure.isProbabilityMeasure_map_iff (hJ n).aemeasurable).2 inferInstance⟩
  have hT : IsTightMeasureSet
      {((μ : ProbabilityMeasure (S × T)) : Measure (S × T)) | μ ∈ range law} := by
    refine IsTightMeasureSet.prodMk ?_ (hYt.subset ?_)
    · refine (isTightMeasureSet_singleton (μ := P.map X)).subset ?_
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact Measure.fst_map_prodMk hX (hYn n)
    · rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact ⟨n, (Measure.snd_map_prodMk hX (hYn n)).symm⟩
  obtain ⟨ρ, -, ψ, hψ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
    (x := law) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨ψ, hψ, ρ, hlim, ?_⟩
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  have key := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim)
    (g.compContinuous ⟨Prod.fst, continuous_fst⟩)
  have hgm : Measurable fun x => g x := g.continuous.measurable
  have e : ∀ n, ∫ p, (g.compContinuous ⟨Prod.fst, continuous_fst⟩) p
      ∂((law (ψ n) : Measure (S × T))) = ∫ x, g x ∂(P.map X) := fun n => by
    show ∫ p, g p.1 ∂(P.map fun ω => (X ω, Yn (ψ n) ω)) = _
    rw [integral_map (hJ _).aemeasurable (f := fun p : S × T => g p.1)
        (hgm.comp measurable_fst).aestronglyMeasurable,
      integral_map hX.aemeasurable hgm.aestronglyMeasurable]
  simp only [Function.comp_apply, e] at key
  rw [integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable]
  exact tendsto_nhds_unique key tendsto_const_nhds

omit [T2Space T₁] [T2Space T₂] in
/-- a coupling limit of `(X, Aₙ, Bₙ)` inherits the independence
`σ(𝒢(X)) ∨ σ(Aₙ) ⫫ σ(ℋ(X)) ∨ σ(Bₙ)` (`indep_sup_of_tendsto`) -/
theorem indep_of_tendsto_coupling {X : Ω → S} (hX : Measurable X) {An : ℕ → Ω → T₁}
    {Bn : ℕ → Ω → T₂} (hAn : ∀ n, Measurable (An n)) (hBn : ∀ n, Measurable (Bn n))
    {ρ : ProbabilityMeasure (S × (T₁ × T₂))}
    (hlim : Tendsto (β := ProbabilityMeasure (S × (T₁ × T₂)))
        (fun n => (⟨P.map fun ω => (X ω, (An n ω, Bn n ω)),
        (Measure.isProbabilityMeasure_map_iff
          (hX.prodMk ((hAn n).prodMk (hBn n))).aemeasurable).2 inferInstance⟩ :
          ProbabilityMeasure (S × (T₁ × T₂)))) atTop (𝓝 ρ))
    (hmarg : (ρ : Measure (S × (T₁ × T₂))).map Prod.fst = P.map X)
    (𝒢 ℋ : {m : MeasurableSpace S // m ≤ mS})
    (hind : ∀ n, Indep (𝒢.1.comap X ⊔ mT₁.comap (An n)) (ℋ.1.comap X ⊔ mT₂.comap (Bn n)) P) :
    Indep (𝒢.1.comap Prod.fst ⊔ mT₁.comap fun p : S × (T₁ × T₂) => p.2.1)
      (ℋ.1.comap Prod.fst ⊔ mT₂.comap fun p : S × (T₁ × T₂) => p.2.2) (ρ : Measure _) := by
  have hJ : ∀ n, Measurable fun ω => (X ω, (An n ω, Bn n ω)) := fun n =>
    hX.prodMk ((hAn n).prodMk (hBn n))
  refine indep_sup_of_tendsto hX measurable_fst hmarg.symm hAn hBn
    (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd) ?_ 𝒢.1 ℋ.1 𝒢.2 ℋ.2 hind
  intro φ hφ ⟨C, hC⟩
  let F : (S × (T₁ × T₂)) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨φ, hφ⟩ (2 * C)
    fun x y => by
      rw [Real.dist_eq]
      have h1 := abs_le.1 (hC x); have h2 := abs_le.1 (hC y)
      show |φ x - φ y| ≤ 2 * C
      rw [abs_le]; constructor <;> linarith
  have key := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) F
  have hFm : Measurable fun p => F p := F.continuous.measurable
  have e : ∀ n, ∫ p, F p ∂(P.map fun ω => (X ω, (An n ω, Bn n ω))) =
      ∫ ω, φ (X ω, (An n ω, Bn n ω)) ∂P := fun n => by
    rw [integral_map (hJ _).aemeasurable hFm.aestronglyMeasurable]
    rfl
  exact key.congr e

end LQGMetric.DFGPS.L217
