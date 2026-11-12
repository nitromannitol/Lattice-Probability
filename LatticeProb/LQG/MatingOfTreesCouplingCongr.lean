import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Null modifications of a mating-of-trees coupling

Every field of `IsMatingOfTreesCoupling` is a statement about laws, independence, almost sure
properties of the sample, outer measures of events or moments. Each of them is therefore unchanged
when every coordinate of the coupling is replaced by an almost surely equal one (the Brownian
coordinates almost surely equal as paths), provided the new field and curve coordinates are
measurable.

## Main results

* `LQGMetric.IsWholePlaneGFF.congr_ae`: a measurable field which is almost surely equal to a
  whole-plane Gaussian free field is a whole-plane Gaussian free field.
* `isBrownianReal_congr_ae`: a process whose paths almost surely agree
  with those of a standard Brownian motion is a standard Brownian motion.
* `IsMatingOfTreesCoupling.congr_ae`: the coupling property passes to
  almost surely equal data.
* `IsMatingOfTreesCoupling.congr_bm`: the special case in which only the
  boundary-length pair is modified.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The covariance of two real random variables only depends on their almost sure classes. -/
theorem covariance_congr_ae {f f' g g' : Ω → ℝ} (hf : f =ᵐ[P] f') (hg : g =ᵐ[P] g') :
    cov[f, g; P] = cov[f', g'; P] := by
  simp only [covariance]
  rw [integral_congr_ae hf, integral_congr_ae hg]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with ω h1 h2
  rw [h1, h2]

/-- A measurable field which is almost surely equal to a whole-plane GFF is a whole-plane GFF. -/
theorem IsWholePlaneGFF.congr_ae {h h' : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hm : Measurable h') (he : ∀ᵐ ω ∂P, h' ω = h ω) : IsWholePlaneGFF h' P where
  measurable := hm
  gaussian := hh.gaussian.congr fun φ => by
    filter_upwards [he] with ω hω
    simp only [hω]
  centered φ := by
    refine (integral_congr_ae ?_).trans (hh.centered φ)
    filter_upwards [he] with ω hω
    simp only [hω]
  covariance_eq φ ψ := by
    refine (covariance_congr_ae ?_ ?_).trans (hh.covariance_eq φ ψ) <;>
    · filter_upwards [he] with ω hω
      simp only [hω]

/-- A measurable field which is almost surely equal to a normalized whole-plane GFF is a
normalized whole-plane GFF. -/
theorem IsNormalizedWPGFF.congr_ae {h h' : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    (hm : Measurable h') (he : ∀ᵐ ω ∂P, h' ω = h ω) : IsNormalizedWPGFF h' P := by
  refine And.intro (hh.1.congr_ae hm he) ?_
  filter_upwards [hh.2, he] with ω h1 h2
  rw [h2]
  exact h1

end LQGMetric

namespace MatedCRTHarmonic

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- A process whose paths almost surely agree with those of a standard Brownian motion is a
standard Brownian motion. -/
theorem isBrownianReal_congr_ae {B C : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (he : ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) : IsBrownianReal C P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.congr fun t => by
    filter_upwards [he] with ω hω using (hω t).symm
  cont := by
    filter_upwards [hB.cont, he] with ω hc hω
    simpa only [hω] using hc

/-- The outer measure of an event defined through a random element only depends on the almost
sure class of that element. -/
theorem measure_setOf_congr_ae {α : Type*} {f g : Ω → α} (p : α → Prop)
    (h : ∀ᵐ ω ∂P, f ω = g ω) : P {ω | p (f ω)} = P {ω | p (g ω)} :=
  measure_congr (Filter.eventuallyEqSet_iff.2 (h.mono fun _ hω => Iff.of_eq (congrArg p hω)))

/-- **Null modifications of a mating-of-trees coupling.** If every coordinate of a
mating-of-trees coupling is replaced by an almost surely equal one (the four Brownian motions
almost surely equal as paths), and the new field and curve coordinates are measurable, the new data
form a mating-of-trees coupling. -/
theorem IsMatingOfTreesCoupling.congr_ae {γ : ℝ}
    {X X₀ hIG₀ Xn X₀n hIGn : Ω → Field} {B B' B₀ B₀' Bn Bn' B₀n B₀n' : ℝ≥0 → Ω → ℝ}
    {U Un : Ω → ℝ} {ηL η η₀ ηLn ηn η₀n : Ω → C(ℝ, ℂ)} {bm bmn : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hXm : Measurable Xn) (hX₀m : Measurable X₀n) (hIGm : Measurable hIGn)
    (hηLm : Measurable ηLn) (hηm : Measurable ηn) (hη₀m : Measurable η₀n)
    (hbmm : Measurable bmn)
    (hX : ∀ᵐ ω ∂P, Xn ω = X ω) (hX₀ : ∀ᵐ ω ∂P, X₀n ω = X₀ ω)
    (hIG : ∀ᵐ ω ∂P, hIGn ω = hIG₀ ω)
    (hB : ∀ᵐ ω ∂P, ∀ t, Bn t ω = B t ω) (hB' : ∀ᵐ ω ∂P, ∀ t, Bn' t ω = B' t ω)
    (hB₀ : ∀ᵐ ω ∂P, ∀ t, B₀n t ω = B₀ t ω) (hB₀' : ∀ᵐ ω ∂P, ∀ t, B₀n' t ω = B₀' t ω)
    (hU : ∀ᵐ ω ∂P, Un ω = U ω) (hηL : ∀ᵐ ω ∂P, ηLn ω = ηL ω) (hη : ∀ᵐ ω ∂P, ηn ω = η ω)
    (hη₀ : ∀ᵐ ω ∂P, η₀n ω = η₀ ω) (hbm : ∀ᵐ ω ∂P, bmn ω = bm ω) :
    IsMatingOfTreesCoupling γ P Xn X₀n hIGn Bn Bn' B₀n B₀n' Un ηLn ηn η₀n bmn where
  isProbabilityMeasure := hC.isProbabilityMeasure
  gff := hC.gff.congr_ae hXm hX
  gff₀ := hC.gff₀.congr_ae hX₀m hX₀
  bm_B := isBrownianReal_congr_ae hC.bm_B hB
  bm_B' := isBrownianReal_congr_ae hC.bm_B' hB'
  bm_B₀ := isBrownianReal_congr_ae hC.bm_B₀ hB₀
  bm_B₀' := isBrownianReal_congr_ae hC.bm_B₀' hB₀'
  indep_cone := by
    refine ⟨hC.indep_cone.1.congr ?_ ?_, hC.indep_cone.2.congr ?_ ?_⟩
    · filter_upwards [hX] with ω e
      rw [e]
    · filter_upwards [hB, hB'] with ω e1 e2
      simp only [e1, e2]
    · filter_upwards [hB] with ω e
      simp only [e]
    · filter_upwards [hB'] with ω e
      simp only [e]
  indep_cone₀ := by
    refine ⟨hC.indep_cone₀.1.congr ?_ ?_, hC.indep_cone₀.2.congr ?_ ?_⟩
    · filter_upwards [hX₀] with ω e
      rw [e]
    · filter_upwards [hB₀, hB₀'] with ω e1 e2
      simp only [e1, e2]
    · filter_upwards [hB₀] with ω e
      simp only [e]
    · filter_upwards [hB₀'] with ω e
      simp only [e]
  igField := by
    refine ⟨hC.igField.1.congr_ae hIGm hIG, (Measure.map_congr hU).trans hC.igField.2.1,
      hC.igField.2.2.congr ?_ ?_⟩
    · filter_upwards [hIG] with ω e
      rw [e]
    · filter_upwards [hU] with ω e
      rw [e]
  indep_curve := by
    refine hC.indep_curve.congr ?_ ?_
    · filter_upwards [hIG, hU] with ω e1 e2
      simp only [e1, e2]
    · filter_upwards [hX, hB, hB', hX₀, hB₀, hB₀'] with ω e1 e2 e3 e4 e5 e6
      simp only [e1, e2, e3, e4, e5, e6]
  measurable_curves := ⟨hηLm, hηm, hη₀m, hbmm⟩
  igMap := by
    obtain ⟨Φ, hΦm, hΦpos, hrep, hcc, hloc⟩ := hC.igMap
    refine ⟨Φ, hΦm, hΦpos, ?_, fun z₀ s φ hs => ?_, fun V hV hVb δ hδ => ?_⟩
    · filter_upwards [hrep, hηL, hIG, hU] with ω e1 e2 e3 e4
      simpa only [e2, e3, e4] using e1
    · filter_upwards [hcc z₀ s φ hs, hηL, hIG, hU] with ω e1 e2 e3 e4
      simpa only [e2, e3, e4] using e1
    · obtain ⟨g, hg, hgae⟩ := hloc V hV hVb δ hδ
      refine ⟨g, hg, ?_⟩
      filter_upwards [hgae, hηL, hIG, hU] with ω e1 e2 e3 e4
      simpa only [e2, e3, e4] using e1
  spaceFilling := by
    filter_upwards [hC.spaceFilling, hηL] with ω e1 e2
    simpa only [e2] using e1
  areaParam := by
    filter_upwards [hC.areaParam, hη, hηL, hX, hB, hB'] with ω e1 e2 e3 e4 e5 e6
    simpa only [e2, e3, e4, e5, e6] using e1
  areaParam₀ := by
    filter_upwards [hC.areaParam₀, hη₀, hηL, hX₀, hB₀, hB₀'] with ω e1 e2 e3 e4 e5 e6
    simpa only [e2, e3, e4, e5, e6] using e1
  segmentsContainBalls := by
    intro R hR r hr N
    obtain ⟨C, hCb⟩ := hC.segmentsContainBalls R hR r hr N
    exact ⟨C, fun ε hε =>
      (measure_setOf_congr_ae (fun c => ¬ SegmentsContainBalls c R r ε) hηL).trans_le (hCb ε hε)⟩
  coverage := by
    obtain ⟨c, hc, C, hCb⟩ := hC.coverage
    exact ⟨c, hc, C, fun M hM =>
      (measure_setOf_congr_ae (fun e : C(ℝ, ℂ) => ¬ ball (0 : ℂ) 1 ⊆ e '' Icc (-M) M) hη).trans_le
        (hCb M hM)⟩
  cellMoments := by
    obtain ⟨h1, h2, h3⟩ := hC.cellMoments
    refine ⟨fun p hp => ?_, fun p hp hp' => ?_, fun p hp => ?_⟩
    · refine (lintegral_congr_ae ?_).trans_lt (h1 p hp)
      filter_upwards [hη₀] with ω e
      simp only [e]
    · refine (lintegral_congr_ae ?_).trans_lt (h2 p hp hp')
      filter_upwards [hη₀] with ω e
      simp only [e]
    · refine (lintegral_congr_ae ?_).trans_lt (h3 p hp)
      filter_upwards [hη₀] with ω e
      simp only [e]
  boundaryLawBM := by
    rw [Measure.map_congr hbm]
    exact hC.boundaryLawBM
  boundaryLength := by
    obtain ⟨BL, hBLm, h1, h2⟩ := hC.boundaryLength
    refine ⟨BL, hBLm, ?_, fun b₀ hb₀ => ?_⟩
    · filter_upwards [h1, hbm, hX, hB, hB', hη] with ω e1 e2 e3 e4 e5 e6
      simpa only [e2, e3, e4, e5, e6] using e1
    · filter_upwards [h2 b₀ hb₀, hbm, hX, hB, hB', hη] with ω e1 e2 e3 e4 e5 e6
      simpa only [e2, e3, e4, e5, e6] using e1
  merge := by
    filter_upwards [hC.merge, hη, hbm] with ω e1 e2 e3
    simpa only [e2, e3] using e1
  onlyMerge := by
    filter_upwards [hC.onlyMerge, hη, hbm] with ω e1 e2 e3
    simpa only [e2, e3] using e1
  visitBound := by
    obtain ⟨k, hk⟩ := hC.visitBound
    refine ⟨k, ?_⟩
    filter_upwards [hk, hηL] with ω e1 e2
    simpa only [e2] using e1

/-- **Modifying the boundary-length pair on a null set.** A measurable pair which almost surely
equals the boundary-length pair of a mating-of-trees coupling can replace it. -/
theorem IsMatingOfTreesCoupling.congr_bm {γ : ℝ} {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm bmn : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hbmm : Measurable bmn) (hbm : ∀ᵐ ω ∂P, bmn ω = bm ω) :
    IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bmn :=
  hC.congr_ae hC.gff.measurable hC.gff₀.measurable hC.igField.1.1.measurable
    hC.measurable_curves.1 hC.measurable_curves.2.1 hC.measurable_curves.2.2.1 hbmm
    (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl)
    (ae_of_all _ fun _ _ => rfl) (ae_of_all _ fun _ _ => rfl) (ae_of_all _ fun _ _ => rfl)
    (ae_of_all _ fun _ _ => rfl) (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl)
    (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl) hbm

end MatedCRT

end MatedCRTHarmonic
