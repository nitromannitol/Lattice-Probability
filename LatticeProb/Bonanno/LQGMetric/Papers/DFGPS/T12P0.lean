/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P0 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P1A
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12Nodes
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreC
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_5Final
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2, Step 0: the coupling `(h, D_h)` (packet P-0 of D90)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1342: "Lemma 2.5 implies that for any sequence of `ε`'s tending to zero, there is a subsequence
`εₙ → 0` along which `(h, D^{εₙ}_h) → (h, D_h)` in law". Decision D90 (decisions/DEC-90.md, Q1, P-0).

Proof (as D90 prescribes): the laws of `(pairJ ⊤ h₀, 𝔞_ε⁻¹ D^ε_{h₀})` on the Polish space
`(CoordJ → ℝ) × C(ℂ × ℂ, ℝ)` have a fixed first marginal and tight second marginals (Lemma 2.5 A,
`lem2_5_tight`), so Prokhorov (`L217.exists_limit_coupling`) gives a limit `ρ` along a
subsequence. The coupling is `Ω := (CoordJ → ℝ) × C(ℂ × ℂ, ℝ)`, `P := ρ`,
`h := pairJInv ⊤ ∘ fst`, `D_h := toContMetric ∘ snd`. The field is a normalized GFF because its law
is that of `h₀` (`isNormalizedWPGFF_of_map_eq`); `ρ`-a.s. the second coordinate is a continuous
metric by Lemma 2.5 A (the support statement of `Lem2_5A`).

* `isNormalizedWPGFF_of_map_eq` — a measurable field with the law of a normalized whole-plane GFF
  is one (own elementary argument: all defining properties are properties of the law).
* `t12Coupling : Lem2_8 → T12Coupling`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BoundedContinuousFunction

namespace LQGMetric.DFGPS.T12

open Blueprint

/-- a measurable field with the law of a normalized whole-plane GFF is a normalized whole-plane
GFF -/
theorem isNormalizedWPGFF_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistC} {h' : Ω' → DistC} (hm : Measurable h)
    (hh' : IsNormalizedWPGFF h' P') (e : P.map h = P'.map h') : IsNormalizedWPGFF h P := by
  have hid : IsWholePlaneGFF id (P.map h) := by rw [e]; exact GM.isWholePlaneGFF_id_map hh'.1
  refine ⟨⟨hm, ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩, ?_⟩
  · have hF : Measurable fun g : DistC => I.restrict fun φ : TestC0 => g φ.1 :=
      measurable_pi_iff.2 fun _ => GFFInv.measurable_pair _
    refine ⟨(hF.comp hm).aemeasurable, ?_⟩
    have h1 : IsGaussian ((P.map h).map fun g : DistC => I.restrict fun φ : TestC0 => g φ.1) :=
      (hid.gaussian.hasGaussianLaw I).isGaussian_map
    rw [Measure.map_map hF hm] at h1
    exact h1
  · have h1 : ∫ g, g φ.1 ∂(P.map h) = 0 := hid.centered φ
    rw [integral_map hm.aemeasurable (GFFInv.measurable_pair _).aestronglyMeasurable] at h1
    exact h1
  · have h1 : cov[fun g : DistC => g φ.1, fun g : DistC => g ψ.1; P.map h] = logCov φ.1 ψ.1 :=
      hid.covariance_eq φ ψ
    rw [covariance_map (GFFInv.measurable_pair _).aestronglyMeasurable
      (GFFInv.measurable_pair _).aestronglyMeasurable hm.aemeasurable] at h1
    exact h1
  · have hs : MeasurableSet {g : DistC | circleAvg g 1 0 = 0} :=
      measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const
    have h1 : ∀ᵐ g ∂(P.map h), circleAvg g 1 0 = 0 := by
      rw [e]; exact (ae_map_iff hh'.1.measurable.aemeasurable hs).2 hh'.2
    exact (ae_map_iff hm.aemeasurable hs).1 h1

theorem isGFFPlusBddCont_of_wp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) : IsGFFPlusBddCont h P :=
  ⟨hh.measurable, fun _ => 0, measurable_const, fun _ => ⟨0, fun z => by simp⟩, by
    simpa [GM.ofCont_zero_eq] using hh⟩

/-- **DFGPS T:1342** (Step 0 of the proof of Theorem 1.2), from Lemma 2.5 (via Lemma 2.8). -/
theorem t12Coupling (h28 : Lem2_8) : T12Coupling := by
  intro γ hγ hγ2 ε hε hε0
  set ξ := xiGamma γ
  obtain ⟨Ω₀, _, P₀, _, g₀, hg₀⟩ := GFFExist.exists_normalizedWPGFF
  -- the base field `id` under `μ := law(g₀)`
  set μ : Measure DistC := P₀.map g₀ with hμ
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hg₀.1.measurable.aemeasurable).2 inferInstance
  have hgμ : IsNormalizedWPGFF (id : DistC → DistC) μ :=
    isNormalizedWPGFF_of_map_eq measurable_id hg₀ (by rw [Measure.map_id])
  have hgb : IsGFFPlusBddCont (id : DistC → DistC) μ := isGFFPlusBddCont_of_wp hgμ.1
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hε0.eventually (gt_mem_nhds one_pos))
  have hεI : ∀ n, ε (n + N0) ∈ Ioo (0 : ℝ) 1 := fun n => ⟨hε _, hN0 _ (by omega)⟩
  have hA : ∀ n, AEMeasurable (fun g => lfppC ξ (ε (n + N0)) (id g)) μ := fun n =>
    aemeasurable_lfppC hgb (hε _).ne'
  set Y : ℕ → DistC → C(ℂ × ℂ, ℝ) := fun n => (hA n).mk _ with hYdef
  have hYm : ∀ n, Measurable (Y n) := fun n => (hA n).measurable_mk
  have hYe : ∀ n, (fun g => lfppC ξ (ε (n + N0)) (id g)) =ᵐ[μ] Y n := fun n => (hA n).ae_eq_mk
  have hT : IsTightMeasureSet (range fun n => μ.map (Y n)) := by
    refine (lem2_5_tight h28 hγ hγ2 μ id hgb).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨_, hεI n, (Measure.map_congr (hYe n)).symm⟩
  set X : DistC → (CoordJ → ℝ) := pairJ ⊤ with hX
  have hXm : Measurable X := measurable_pairJ ⊤
  obtain ⟨ψ, hψ, ρ, hlim, hmarg⟩ := L217.exists_limit_coupling (P := μ) hXm hYm hT
  set S := (CoordJ → ℝ) × C(ℂ × ℂ, ℝ)
  set H : S → DistC := fun q => pairJInv ⊤ q.1 with hH
  have hHm : Measurable H := (measurable_pairJInv ⊤).comp measurable_fst
  have hlawH : (ρ : Measure S).map H = μ := by
    rw [show H = pairJInv ⊤ ∘ Prod.fst from rfl, ← Measure.map_map (measurable_pairJInv ⊤)
      measurable_fst, hmarg, Measure.map_map (measurable_pairJInv ⊤) hXm]
    have : (pairJInv ⊤ ∘ X) = id := funext fun g => pairJInv_pairJ ⊤ g
    rw [this, Measure.map_id]
  -- a.s. the first coordinate is in the range of `pairJ`
  have hran : ∀ᵐ q ∂(ρ : Measure S), pairJ ⊤ (H q) = q.1 := by
    have hrs : MeasurableSet (range (pairJ (⊤ : TopologicalSpace.Opens ℂ))) := by
      rw [range_pairJ_eq]; exact measurableSet_rangeSet ⊤
    have h1 : ∀ᵐ s ∂((ρ : Measure S).map Prod.fst), s ∈ range (pairJ (⊤ : TopologicalSpace.Opens ℂ)) := by
      rw [hmarg]
      exact (ae_map_iff hXm.aemeasurable hrs).2 (Eventually.of_forall fun g => ⟨g, rfl⟩)
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable h1] with q hq
    obtain ⟨T, hT⟩ := hq
    simp only [hH, ← hT, pairJInv_pairJ]
  -- a.s. the second coordinate is a continuous (length) metric: Lemma 2.5 A
  have hmet : ∀ᵐ q ∂(ρ : Measure S), IsContLengthMetric q.2 := by
    have hc : Continuous fun q : S => q.2 := continuous_snd
    have hl := ((ProbabilityMeasure.continuous_map hc).tendsto ρ).comp hlim
    have hae := ((lem2_5 h28).1 γ hγ hγ2 μ id hgb).2 (fun n => ε (ψ n + N0))
      (fun n => ⟨μ.map fun g => lfppC ξ (ε (ψ n + N0)) (id g),
        (Measure.isProbabilityMeasure_map_iff (hA (ψ n))).2 inferInstance⟩)
      (ρ.map fun q : S => q.2) (fun n => ⟨hεI _, rfl⟩)
      (hε0.comp ((tendsto_add_atTop_nat N0).comp hψ.tendsto_atTop))
      (hl.congr fun n => Subtype.ext ?_)
    · rw [ProbabilityMeasure.toMeasure_map] at hae
      exact ae_of_ae_map hc.measurable.aemeasurable hae
    · show (μ.map fun g => (X g, Y (ψ n) g)).map (fun q : S => q.2) = _
      rw [Measure.map_map hc.measurable (hXm.prodMk (hYm _))]
      exact Measure.map_congr (hYe (ψ n)).symm
  refine ⟨fun n => ψ n + N0, fun a b hab => by simpa using hψ hab, S, inferInstance,
    (ρ : Measure S), inferInstance, H, fun q => toContMetric q.2,
    isNormalizedWPGFF_of_map_eq hHm hgμ (by rw [hlawH, Measure.map_id]),
    measurable_toContMetric.comp measurable_snd, ?_⟩
  intro φ hφ ⟨C, hC⟩
  let f : S →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨φ, hφ⟩ (2 * C) fun x y => by
    rw [Real.dist_eq]
    have := abs_sub (φ x) (φ y)
    have := hC x; have := hC y
    show |φ x - φ y| ≤ 2 * C
    linarith
  have hconv := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) f
  have eR : ∫ q, φ (pairJ ⊤ (H q), (toContMetric q.2).1) ∂(ρ : Measure S) =
      ∫ q, f q ∂(ρ : Measure S) := by
    refine integral_congr_ae ?_
    filter_upwards [hran, hmet] with q h1 h2
    rw [h1, toContMetric_val_of h2.1]
    rfl
  have eL : ∀ n, ∫ q, φ (pairJ ⊤ (H q), lfppC ξ (ε (ψ n + N0)) (H q)) ∂(ρ : Measure S) =
      ∫ p, f p ∂(μ.map fun g => (X g, Y (ψ n) g)) := by
    intro n
    rw [integral_map (hXm.prodMk (hYm _)).aemeasurable f.continuous.aestronglyMeasurable]
    have hΨ : AEStronglyMeasurable (fun g => φ (pairJ ⊤ g, lfppC ξ (ε (ψ n + N0)) g))
        ((ρ : Measure S).map H) := by
      rw [hlawH]
      exact (hφ.measurable.comp_aemeasurable (hXm.aemeasurable.prodMk (hA (ψ n)))).aestronglyMeasurable
    have e2 := integral_map hHm.aemeasurable hΨ
    rw [hlawH] at e2
    rw [← e2]
    refine integral_congr_ae ?_
    filter_upwards [hYe (ψ n)] with g hg
    simp only [← hg, id]
    rfl
  rw [eR]
  exact hconv.congr fun n => (eL n).symm

end LQGMetric.DFGPS.T12
