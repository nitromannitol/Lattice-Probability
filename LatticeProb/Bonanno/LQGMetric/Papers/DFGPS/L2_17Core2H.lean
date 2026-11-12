/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core2H at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2G
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the field on the coordinate space (input of step C5 (iii))

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3 (T:1248–1256, Skorokhod coupling and "the analog of Lemma 2.12"). On a Skorokhod space only
the coordinates `x̃ₙ` of the field (law of `J h`, `J = pairJ ⊤`) are available; the field is
recovered as `pairJInv ⊤ x̃ₙ`. Being a whole-plane GFF only depends on the law
(`isWholePlaneGFF_of_map_eq`), so `pairJInv ⊤` is a normalized whole-plane GFF under the law of
`J h` (`isNormalizedWPGFF_pairJInv`), and `normField (pairJInv ⊤) z r` is a GFF plus a bounded
continuous function there (`isGFFPlusBddCont_normField_pairJInv`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric.DFGPS.L217

open Blueprint

/-- **being a whole-plane GFF only depends on the law** -/
theorem isWholePlaneGFF_of_map_eq {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    {ν : Measure T} {P : Measure Ω} {Y : T → DistC} (hY : Measurable Y) {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (hlaw : ν.map Y = P.map h) : IsWholePlaneGFF Y ν := by
  have hev : ∀ ψ : TestC, Measurable fun g : DistC => g ψ := fun ψ =>
    (measurable_pi_apply ψ).comp (show Measurable fun (g : DistC) (φ : TestC) => g φ from
      fun _ hs => ⟨_, hs, rfl⟩)
  refine ⟨hY, ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · have hF : Measurable fun g : DistC => I.restrict (fun φ : TestC0 => g φ.1) :=
      measurable_pi_iff.2 fun i => hev _
    refine ⟨(hF.comp hY).aemeasurable, ?_⟩
    change IsGaussian (ν.map ((fun g : DistC => I.restrict fun φ : TestC0 => g φ.1) ∘ Y))
    rw [← Measure.map_map hF hY, hlaw, Measure.map_map hF hh.measurable]
    exact (hh.gaussian.hasGaussianLaw I).isGaussian_map
  · calc ∫ t, Y t φ.1 ∂ν = ∫ g, (fun g : DistC => g φ.1) g ∂(ν.map Y) :=
          (integral_map hY.aemeasurable (hev _).aestronglyMeasurable).symm
      _ = ∫ g, (fun g : DistC => g φ.1) g ∂(P.map h) := by rw [hlaw]
      _ = ∫ ω, h ω φ.1 ∂P := integral_map hh.measurable.aemeasurable (hev _).aestronglyMeasurable
      _ = 0 := hh.centered φ
  · have e1 := covariance_map (μ := ν) (X := fun g : DistC => g φ.1) (Y := fun g : DistC => g ψ.1)
      (hev _).aestronglyMeasurable (hev _).aestronglyMeasurable hY.aemeasurable
    have e2 := covariance_map (μ := P) (X := fun g : DistC => g φ.1) (Y := fun g : DistC => g ψ.1)
      (hev _).aestronglyMeasurable (hev _).aestronglyMeasurable hh.measurable.aemeasurable
    have k := e1.symm.trans ((congrArg (fun μ => cov[fun g : DistC => g φ.1,
      fun g : DistC => g ψ.1; μ]) hlaw).trans e2)
    exact k.trans (hh.covariance_eq φ ψ)

/-- the field `pairJInv ⊤` under the law of `J h` is a normalized whole-plane GFF -/
theorem isNormalizedWPGFF_pairJInv {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) :
    IsNormalizedWPGFF (pairJInv ⊤) (P.map fun ω => pairJ ⊤ (h ω)) := by
  have hX : Measurable fun ω => pairJ ⊤ (h ω) := (measurable_pairJ ⊤).comp hh.1.measurable
  have hlaw : (P.map fun ω => pairJ ⊤ (h ω)).map (pairJInv ⊤) = P.map h := by
    rw [Measure.map_map (measurable_pairJInv ⊤) hX]
    congr 1
    funext ω
    exact pairJInv_pairJ ⊤ (h ω)
  refine ⟨isWholePlaneGFF_of_map_eq (measurable_pairJInv ⊤) hh.1 hlaw, ?_⟩
  have hm : MeasurableSet {x : CoordJ → ℝ | circleAvg (pairJInv ⊤ x) 1 0 = 0} :=
    measurableSet_eq_fun ((measurable_circleAvg_left 1 0).comp (measurable_pairJInv ⊤))
      measurable_const
  refine (ae_map_iff hX.aemeasurable hm).2 ?_
  filter_upwards [hh.2] with ω hω
  simp only [pairJInv_pairJ]
  exact hω

/-- **`h − h_r(z)` on the coordinate space** is a GFF plus a bounded continuous function -/
theorem isGFFPlusBddCont_normField_pairJInv {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IsGFFPlusBddCont (normField (pairJInv ⊤) z r) (P.map fun ω => pairJ ⊤ (h ω)) :=
  isGFFPlusBddCont_normField (isNormalizedWPGFF_pairJInv hh) hr z

theorem normField_pairJInv_pairJ {Ω : Type} {h : Ω → DistC} (z : ℂ) (r : ℝ) (ω : Ω) :
    normField (pairJInv ⊤) z r (pairJ ⊤ (h ω)) = normField h z r ω := by
  simp only [normField, pairJInv_pairJ]

end L217

end LQGMetric.DFGPS
