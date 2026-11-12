/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3A
import LatticeProb.Bonanno.LQGMetric.Prob.Skorokhod

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: fibre properties through a Skorokhod representation

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3–4 (T:1248–1273). The Weyl relation `D_h = e^{ξφ𝔥}·D_{h−φ𝔥}` (T:1271) is obtained on a
Skorokhod space (a.s. convergence), where the relevant event is not known to be measurable (it
involves the Weyl infimum over uncountably many paths). What Step 4 needs from it is only the
"measurable function" statement `σ(D_h(·,·;W')) ⊆ σ(𝔥, D_{h−φ𝔥}(·,·;W'))` (mod null sets), which
only involves measurable maps of the law. Tools:

* `exists_skorokhod_representation_sb` — Skorokhod's representation theorem (Billingsley,
  *Convergence of Probability Measures*, 2nd ed., Thm 6.7; proof copied from
  `exists_skorokhod_representation_of_pseudoMetric`, Prob/Skorokhod.lean) with in addition a
  **standard Borel** underlying space (the product space of Billingsley's construction).
* `comap_le_aeClosure_of_rep` — if on a standard Borel space a measurable `Z` a.s. takes values
  in a set `Good` on which `G` is constant along the fibres of `R`, then `σ(G) ⊆ σ(R)` mod null
  sets under the law of `Z` (Lusin separation on the representation space,
  `comap_le_aeClosure_of_fiber`).
* `comap_comp_le_aeClosure` — pulling such a statement back along a measurable map.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal unitInterval

namespace LQGMetric.DFGPS.L217

open GM.Bilip

universe u

/-- **Skorokhod's representation theorem** on a Polish space (Billingsley Thm 6.7), with a
standard Borel representation space. -/
theorem exists_skorokhod_representation_sb {S : Type u} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S]
    {μ : ProbabilityMeasure S} {μs : ℕ → ProbabilityMeasure S} (h : Tendsto μs atTop (𝓝 μ)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (Pr : Measure Ω),
      IsProbabilityMeasure Pr ∧
      ∃ (Y : ℕ → Ω → S) (Ylim : Ω → S), (∀ n, Measurable (Y n)) ∧ Measurable Ylim ∧
        (∀ n, Pr.map (Y n) = (μs n : Measure S)) ∧ Pr.map Ylim = (μ : Measure S) ∧
        ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)) := by
  classical
  have hsb : StandardBorelSpace (SkΩ S) := inferInstance
  let := TopologicalSpace.upgradeIsCompletelyMetrizable S
  obtain ⟨D⟩ := exists_skData h
  have hE : D.prob (D.good ∩ D.badᶜ)ᶜ = 0 := by
    rw [compl_inter, compl_compl]
    exact measure_union_null D.prob_good_compl D.prob_bad
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null hE
  have hX : Measurable fun ω : SkΩ S => ω.1 none := (measurable_pi_apply _).comp measurable_fst
  refine ⟨SkΩ S, inferInstance, hsb, D.prob, inferInstance,
    fun n ω => if ω ∈ N then ω.1 none else D.X' n ω, fun ω => ω.1 none,
    fun n => Measurable.ite hNm hX (D.measurable_X' n), hX, fun n => ?_, ?_, fun ω => ?_⟩
  · rw [← D.map_X' n]
    refine Measure.map_congr ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    simp [hω]
  · ext A hA
    rw [Measure.map_apply hX hA]
    exact D.prob_coord none hA
  · by_cases hω : ω ∈ N
    · simp only [hω]; exact tendsto_const_nhds
    · have hω' : ω ∈ D.good ∩ D.badᶜ := by
        by_contra h'; exact hω (hN h')
      simp only [hω]
      exact D.tendsto_X' hω'.1 hω'.2

/-- **fibre property on a representation space ⇒ `σ(G) ⊆ σ(R)` mod null under the law** -/
theorem comap_le_aeClosure_of_rep {Ω' E Y β : Type*} [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    {P' : Measure Ω'} [MeasurableSpace E] {Z : Ω' → E} (hZ : Measurable Z) [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] [T2Space Y]
    [mβ : MeasurableSpace β] {G : E → β} (hG : Measurable G) {R : E → Y} (hR : Measurable R)
    {Good : E → Prop} (hgood : ∀ᵐ ω ∂P', Good (Z ω))
    (hfib : ∀ e, Good e → ∀ e', Good e' → R e = R e' → G e = G e') :
    MeasurableSpace.comap G mβ ≤ aeClosure (P'.map Z) (MeasurableSpace.comap R inferInstance) := by
  obtain ⟨M, hMsup, hMm, hM0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have H := comap_le_aeClosure_of_fiber (μ := P') (hG.comp hZ) (hR.comp hZ) hMm.compl
    (by rwa [compl_compl]) fun x hx x' hx' he => by
      have k : ∀ y ∈ Mᶜ, Good (Z y) := fun y hy => by by_contra hn; exact hy (hMsup hn)
      exact hfib _ (k x hx) _ (k x' hx') he
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨_, ⟨C, hC, rfl⟩, heq⟩ := H _ ⟨B, hB, rfl⟩
  refine ⟨R ⁻¹' C, ⟨C, hC, rfl⟩, ?_⟩
  rw [ae_eq_set] at heq ⊢
  rw [Measure.map_apply hZ ((hG hB).diff (hR hC)), Measure.map_apply hZ ((hR hC).diff (hG hB))]
  exact heq

/-- pulling `σ(G) ⊆ σ(R)` (mod null) back along a measurable map -/
theorem comap_comp_le_aeClosure {Ω E Y β : Type*} [MeasurableSpace Ω] {ρ : Measure Ω}
    [MeasurableSpace E] {ι : Ω → E} (hι : Measurable ι) [mY : MeasurableSpace Y]
    [mβ : MeasurableSpace β] {G : E → β} {R : E → Y}
    (h : MeasurableSpace.comap G mβ ≤ aeClosure (ρ.map ι) (MeasurableSpace.comap R mY)) :
    MeasurableSpace.comap (G ∘ ι) mβ ≤ aeClosure ρ (MeasurableSpace.comap (R ∘ ι) mY) := by
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨_, ⟨C, hC, rfl⟩, heq⟩ := h _ ⟨B, hB, rfl⟩
  exact ⟨(R ∘ ι) ⁻¹' C, ⟨C, hC, rfl⟩, ae_of_ae_map hι.aemeasurable heq⟩

end L217

end LQGMetric.DFGPS
