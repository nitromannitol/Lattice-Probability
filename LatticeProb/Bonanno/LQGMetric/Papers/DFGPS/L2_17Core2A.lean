/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core2A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreC
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5Final
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the coupling of the two LFPP sequences (step C2)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3 (T:1236–1256): "By Lemma 2.5, … after possibly passing to a further deterministic
subsequence we can arrange that … (eqn-internal-joint-law-conv)". Decision D80, packet P-C (i),(ii).

* `isTight_lfppJoint` — the laws of `(𝔞_ε⁻¹ D^ε_h, {𝔞_ε⁻¹ D^ε_h(·,·;W̄)}_W)`, `ε ∈ (0,1)`, are
  tight on `DyProd` (Lemma 2.5 A tightness and Lemma 2.9; as in `lem2_5B_proof`).
* `ae_isDyadicLimit_of_tendsto` — every weak limit of these laws along `ε_k → 0` is carried by
  `IsDyadicLimit` (Lemma 2.5 B along a further subsequence and uniqueness of weak limits).
* `exists_lfpp_coupling` — for a measurable `X : Ω → S` (`S` Polish) and two fields
  `h₁, h₂` (GFF plus bounded continuous function), a subsequence along which
  `(X, lfppJoint h₁, lfppJoint h₂)` converge in law to `ρ` with first marginal the law of `X` and
  `ρ`-a.s. both `DyProd` coordinates `IsDyadicLimit`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

open Blueprint

/-- tightness of the joint LFPP laws on `DyProd` (as in `lem2_5B_proof`, T:1014–1016) -/
theorem isTight_lfppJoint (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P) :
    IsTightMeasureSet
      {μ | ∃ ε ∈ Ioo (0 : ℝ) 1, μ = P.map fun ω => lfppJoint (xiGamma γ) ε (h ω)} := by
  apply isTightMeasureSet_dyProd
  · refine (lem2_5_tight h28 hγ hγ2 P h hh).subset ?_
    rintro _ ⟨_, ⟨ε, hε, rfl⟩, rfl⟩
    exact ⟨ε, hε, AEMeasurable.map_map_of_aemeasurable continuous_dyProd_fst.aemeasurable
      (aemeasurable_lfppJoint hh hε.1.ne')⟩
  · intro W
    refine ((lem2_9 h28 γ hγ hγ2 W.1 W.2.1 W.2.2 P h hh).2.1).subset ?_
    rintro _ ⟨_, ⟨ε, hε, rfl⟩, rfl⟩
    exact ⟨ε, hε, AEMeasurable.map_map_of_aemeasurable (continuous_dyProd_snd W).aemeasurable
      (aemeasurable_lfppJoint hh hε.1.ne')⟩

/-- every weak limit of the joint LFPP laws along `ε_k → 0` is a.s. a dyadic limit
(Lemma 2.5 B along a further subsequence; uniqueness of weak limits) -/
theorem ae_isDyadicLimit_of_tendsto (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P) {εk : ℕ → ℝ} (hεk : ∀ k, 0 < εk k)
    (hεk0 : Tendsto εk atTop (𝓝 0)) {μ : ProbabilityMeasure DyProd}
    (hlim : Tendsto (β := ProbabilityMeasure DyProd) (fun n => (⟨P.map fun ω => lfppJoint (xiGamma γ) (εk n) (h ω),
      (Measure.isProbabilityMeasure_map_iff (aemeasurable_lfppJoint hh (hεk n).ne')).2
        inferInstance⟩ : ProbabilityMeasure DyProd)) atTop (𝓝 μ)) :
    ∀ᵐ x ∂(μ : Measure DyProd), IsDyadicLimit x := by
  obtain ⟨φ, hφ, μ', hconv, hae⟩ := lem2_5B_proof h28 γ hγ hγ2 P h hh εk hεk hεk0
  have h1 := hconv (fun n => (⟨P.map fun ω => lfppJoint (xiGamma γ) (εk (φ n)) (h ω),
      (Measure.isProbabilityMeasure_map_iff (aemeasurable_lfppJoint hh (hεk (φ n)).ne')).2
        inferInstance⟩ : ProbabilityMeasure DyProd)) fun n => rfl
  have h2 := hlim.comp hφ.tendsto_atTop
  have e : μ = μ' := tendsto_nhds_unique h2 h1
  rw [e]
  exact hae

/-- **the coupling of the two LFPP sequences** (T:1240–1256; D80 P-C (i),(ii)) -/
theorem exists_lfpp_coupling (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [PolishSpace S]
    {X : Ω → S} (hX : Measurable X) {h₁ h₂ : Ω → DistC} (hh₁ : IsGFFPlusBddCont h₁ P)
    (hh₂ : IsGFFPlusBddCont h₂ P) {εk : ℕ → ℝ} (hεk : ∀ k, 0 < εk k)
    (hεk0 : Tendsto εk atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ ρ : ProbabilityMeasure (S × (DyProd × DyProd)),
      (∀ f : S × (DyProd × DyProd) →ᵇ ℝ, Tendsto (fun n => ∫ ω, f (X ω,
          (lfppJoint (xiGamma γ) (εk (ψ n)) (h₁ ω), lfppJoint (xiGamma γ) (εk (ψ n)) (h₂ ω))) ∂P)
        atTop (𝓝 (∫ p, f p ∂(ρ : Measure (S × (DyProd × DyProd)))))) ∧
      (ρ : Measure (S × (DyProd × DyProd))).map Prod.fst = P.map X ∧
      ∀ᵐ p ∂(ρ : Measure (S × (DyProd × DyProd))), IsDyadicLimit p.2.1 ∧ IsDyadicLimit p.2.2 := by
  set ξ := xiGamma γ
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hεk0.eventually (gt_mem_nhds one_pos))
  have hεI : ∀ n, εk (n + N0) ∈ Ioo (0 : ℝ) 1 := fun n => ⟨hεk _, hN0 _ (by omega)⟩
  have hA₁ : ∀ n, AEMeasurable (fun ω => lfppJoint ξ (εk (n + N0)) (h₁ ω)) P := fun n =>
    aemeasurable_lfppJoint hh₁ (hεk _).ne'
  have hA₂ : ∀ n, AEMeasurable (fun ω => lfppJoint ξ (εk (n + N0)) (h₂ ω)) P := fun n =>
    aemeasurable_lfppJoint hh₂ (hεk _).ne'
  set Y : ℕ → Ω → DyProd × DyProd := fun n ω => ((hA₁ n).mk _ ω, (hA₂ n).mk _ ω) with hYdef
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    (hA₁ n).measurable_mk.prodMk (hA₂ n).measurable_mk
  have hYe : ∀ n, (fun ω => (lfppJoint ξ (εk (n + N0)) (h₁ ω),
      lfppJoint ξ (εk (n + N0)) (h₂ ω))) =ᵐ[P] Y n := fun n => by
    filter_upwards [(hA₁ n).ae_eq_mk, (hA₂ n).ae_eq_mk] with ω e1 e2
    simp only [hYdef, ← e1, ← e2]
  have hT : IsTightMeasureSet (range fun n => P.map (Y n)) := by
    refine IsTightMeasureSet.prodMk ((isTight_lfppJoint h28 hγ hγ2 P hh₁).subset ?_)
      ((isTight_lfppJoint h28 hγ hγ2 P hh₂).subset ?_)
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      refine ⟨_, hεI n, ?_⟩
      rw [Measure.fst_map_prodMk (hA₁ n).measurable_mk (hA₂ n).measurable_mk]
      exact Measure.map_congr (hA₁ n).ae_eq_mk.symm
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      refine ⟨_, hεI n, ?_⟩
      rw [Measure.snd_map_prodMk (hA₁ n).measurable_mk (hA₂ n).measurable_mk]
      exact Measure.map_congr (hA₂ n).ae_eq_mk.symm
  obtain ⟨ψ, hψ, ρ, hlim, hmarg⟩ := exists_limit_coupling hX hYm hT
  refine ⟨fun n => ψ n + N0, fun a b hab => by simpa using hψ hab, ρ, ?_, hmarg, ?_⟩
  · intro f
    refine ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) f).congr fun n => ?_
    show ∫ p, f p ∂(P.map fun ω => (X ω, Y (ψ n) ω)) = _
    rw [integral_map (hX.prodMk (hYm _)).aemeasurable f.continuous.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hYe (ψ n)] with ω hω
    simp only [← hω]
  -- identification of the two `DyProd` marginals
  have key : ∀ (i : DyProd × DyProd → DyProd), Continuous i → ∀ g : Ω → DistC,
      ∀ hg : IsGFFPlusBddCont g P,
      (∀ n, (fun ω => i (Y n ω)) =ᵐ[P] fun ω => lfppJoint ξ (εk (n + N0)) (g ω)) →
      ∀ᵐ p ∂(ρ : Measure (S × (DyProd × DyProd))), IsDyadicLimit (i p.2) := by
    intro i hi g hg hiY
    have hc : Continuous fun p : S × (DyProd × DyProd) => i p.2 := hi.comp continuous_snd
    have hl := ((ProbabilityMeasure.continuous_map hc).tendsto ρ).comp hlim
    have hae := ae_isDyadicLimit_of_tendsto h28 hγ hγ2 hg (εk := fun n => εk (ψ n + N0))
      (fun n => hεk _) (hεk0.comp ((tendsto_add_atTop_nat N0).comp hψ.tendsto_atTop))
      (μ := ρ.map fun p : S × (DyProd × DyProd) => i p.2) (hl.congr fun n => Subtype.ext ?_)
    · rw [ProbabilityMeasure.toMeasure_map] at hae
      exact ae_of_ae_map hc.measurable.aemeasurable hae
    · show (P.map fun ω => (X ω, Y (ψ n) ω)).map (fun p : S × (DyProd × DyProd) => i p.2) = _
      rw [Measure.map_map hc.measurable (hX.prodMk (hYm _))]
      exact Measure.map_congr (hiY (ψ n))
  filter_upwards [key Prod.fst continuous_fst h₁ hh₁ fun n => by
      filter_upwards [hYe n] with ω hω; simp only [← hω],
    key Prod.snd continuous_snd h₂ hh₂ fun n => by
      filter_upwards [hYe n] with ω hω; simp only [← hω]] with p h1 h2
  exact ⟨h1, h2⟩

end L217

end LQGMetric.DFGPS
