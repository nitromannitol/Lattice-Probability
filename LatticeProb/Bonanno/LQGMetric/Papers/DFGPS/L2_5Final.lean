/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5ProofB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 (`lem-lfpp-tight`, T:817–830, proof T:993–1019), from Lemma 2.8

* A, tightness: `lem2_5_tight` (`L2_5ProofTightA.lean`);
* A, limits are continuous length metrics: `lem2_5_lim` (`L2_5ProofLim.lean`);
* B: `lem2_5B_proof` (below): tightness of the joint laws (Lemma 2.9 and `lem2_5_tight`,
  `isTightMeasureSet_dyProd`), Prokhorov, identification of the marginals (`lem2_5_lim`,
  Lemma 2.9) and of the internal metrics (`isDyadicLimit_of`, the two steps of Lemma 2.11).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- **DFGPS Lemma 2.5 B** (T:1014–1019), from Lemma 2.8. -/
theorem lem2_5B_proof (h28 : Lem2_8) : Lem2_5B := by
  intro γ hγ hγ2 Ω _ P _ h hh εk hεk hεk0
  set ξ := xiGamma γ
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hεk0.eventually (gt_mem_nhds one_pos))
  have hεI : ∀ n, εk (n + N0) ∈ Ioo (0 : ℝ) 1 := fun n => ⟨hεk _, hN0 _ (by omega)⟩
  have hJm : ∀ n, AEMeasurable (fun ω => lfppJoint ξ (εk (n + N0)) (h ω)) P := fun n =>
    aemeasurable_lfppJoint hh (hεk _).ne'
  have hcS : ∀ n, ∀ᵐ ω ∂P, Continuous (heatMollify (εk (n + N0)) (h ω)) := fun n =>
    (hh.ae_tendstoLocallyUniformly_heatMollify _ (hεk _).ne').mono fun ω hω => hω.2
  let law : ℕ → ProbabilityMeasure DyProd := fun n =>
    ⟨P.map fun ω => lfppJoint ξ (εk (n + N0)) (h ω),
      (Measure.isProbabilityMeasure_map_iff (hJm n)).2 inferInstance⟩
  have hm1 : ∀ n, ((law n : Measure DyProd).map fun x : DyProd => x.1) =
      P.map fun ω => lfppC ξ (εk (n + N0)) (h ω) := fun n =>
    AEMeasurable.map_map_of_aemeasurable continuous_dyProd_fst.aemeasurable (hJm n)
  have hmW : ∀ (W : dyadicDomainsC) n, ((law n : Measure DyProd).map fun x : DyProd => x.2 W) =
      P.map fun ω => lfppSqC ξ (εk (n + N0)) (h ω) (closure W) := fun W n =>
    AEMeasurable.map_map_of_aemeasurable (continuous_dyProd_snd W).aemeasurable (hJm n)
  have hT : IsTightMeasureSet
      {((μ : ProbabilityMeasure DyProd) : Measure DyProd) | μ ∈ range law} := by
    apply isTightMeasureSet_dyProd
    · refine (lem2_5_tight h28 hγ hγ2 P h hh).subset ?_
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, hεI n, hm1 n⟩
    · intro W
      refine ((lem2_9 h28 γ hγ hγ2 W.1 W.2.1 W.2.2 P h hh).2.1).subset ?_
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, hεI n, hmW W n⟩
  obtain ⟨μ, -, ψ, hψ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
    (x := law) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨fun n => ψ n + N0, fun a b hab => by simpa using hψ hab, μ, ?_, ?_⟩
  · intro ν hν
    have : ν = law ∘ ψ := funext fun n => Subtype.ext (hν n)
    rw [this]; exact hlim
  have hψ' : Tendsto (fun n => ψ n + N0) atTop atTop :=
    (tendsto_add_atTop_nat N0).comp hψ.tendsto_atTop
  have hεψ : Tendsto (fun n => εk (ψ n + N0)) atTop (𝓝 0) := hεk0.comp hψ'
  have hA : ∀ᵐ x ∂(μ : Measure DyProd), IsContLengthMetric x.1 := by
    have hl1 : Tendsto (fun n => (law (ψ n)).map fun x : DyProd => x.1) atTop
        (𝓝 (μ.map fun x : DyProd => x.1)) :=
      ((ProbabilityMeasure.continuous_map continuous_dyProd_fst).tendsto μ).comp hlim
    have := lem2_5_lim h28 hγ hγ2 P h hh (fun n => εk (ψ n + N0)) _ _
      (fun n => ⟨hεI (ψ n), by rw [ProbabilityMeasure.toMeasure_map]; exact hm1 (ψ n)⟩) hεψ hl1
    rw [ProbabilityMeasure.toMeasure_map] at this
    exact ae_of_ae_map continuous_dyProd_fst.aemeasurable this
  have hB : ∀ᵐ x ∂(μ : Measure DyProd), ∀ W, IsSqLengthMetric (x.2 W) := by
    refine ae_all_iff.2 fun W => ?_
    have hlW : Tendsto (fun n => (law (ψ n)).map fun x : DyProd => x.2 W) atTop
        (𝓝 (μ.map fun x : DyProd => x.2 W)) :=
      ((ProbabilityMeasure.continuous_map (continuous_dyProd_snd W)).tendsto μ).comp hlim
    have := (lem2_9 h28 γ hγ hγ2 W.1 W.2.1 W.2.2 P h hh).2.2 (fun n => εk (ψ n + N0)) _ _
      (fun n => ⟨hεI (ψ n), by rw [ProbabilityMeasure.toMeasure_map]; exact hmW W (ψ n)⟩)
      hεψ hlW
    rw [ProbabilityMeasure.toMeasure_map] at this
    exact ae_of_ae_map (continuous_dyProd_snd W).aemeasurable this
  have hfull : ∀ F : Set DyProd, IsClosed F →
      (∀ (g : DistC) (ε : ℝ), Continuous (heatMollify ε g) → lfppJoint ξ ε g ∈ F) →
      ∀ᵐ x ∂(μ : Measure DyProd), x ∈ F := by
    intro F hF hg
    refine ae_mem_of_isClosed_of_forall hlim hF fun n => ?_
    show (P.map fun ω => lfppJoint ξ (εk (ψ n + N0)) (h ω)) F = 1
    rw [Measure.map_apply_of_aemeasurable (hJm _) hF.measurableSet]
    have hae : ∀ᵐ ω ∂P, ω ∈ (fun ω => lfppJoint ξ (εk (ψ n + N0)) (h ω)) ⁻¹' F :=
      (hcS (ψ n)).mono fun ω hω => hg _ _ hω
    exact (measure_congr (eventuallyEqSet_univ.2 hae)).trans measure_univ
  have hC : ∀ᵐ x ∂(μ : Measure DyProd), ∀ W, x ∈ dyC1 W ∧ x ∈ dyC2 W := by
    refine ae_all_iff.2 fun W => ?_
    filter_upwards [hfull _ (isClosed_dyC1 W) fun g ε hc => lfppJoint_mem_dyC1 hc W,
      hfull _ (isClosed_dyC2 W) fun g ε hc => lfppJoint_mem_dyC2 hc W] with x h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hA, hB, hC] with x h1 h2 h3
  exact isDyadicLimit_of h1 h2 (fun W => (h3 W).1) (fun W => (h3 W).2)

/-- **DFGPS Lemma 2.5** (`lem-lfpp-tight`, T:817–830), from Lemma 2.8. -/
theorem lem2_5 (h28 : Lem2_8) : Lem2_5 :=
  ⟨fun _ hγ hγ2 _ _ P _ h hh =>
    ⟨lem2_5_tight h28 hγ hγ2 P h hh, lem2_5_lim h28 hγ hγ2 P h hh⟩, lem2_5B_proof h28⟩

end LQGMetric.DFGPS
