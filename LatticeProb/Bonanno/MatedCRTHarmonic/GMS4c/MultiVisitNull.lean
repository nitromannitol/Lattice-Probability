/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.MultiVisitNull at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionCoverage
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OG4Adapter

/-! Spatially almost every point of an area-parametrized curve is visited once. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.IGLaw

/-- Points visited at two distinct times. -/
def multiVisitPoints (c : ℝ → ℂ) : Set ℂ :=
  {z | ∃ s t : ℝ, s < t ∧ c s = z ∧ c t = z}

/-- Joint curve/point measurability of the multiple-visit relation. -/
theorem measurableSet_multiVisitRelation :
    MeasurableSet {p : C(ℝ, ℂ) × ℂ | p.2 ∈ multiVisitPoints p.1} := by
  let R (a b e d : ℚ) : Set (C(ℝ, ℂ) × ℂ) :=
    if (a : ℝ) ≤ b ∧ (b : ℝ) < e ∧ (e : ℝ) ≤ d then
      {p | ∃ s ∈ Icc (a : ℝ) b, p.1 s = p.2} ∩
        {p | ∃ t ∈ Icc (e : ℝ) d, p.1 t = p.2}
    else ∅
  have hR : ∀ a b e d : ℚ, MeasurableSet (R a b e d) := by
    intro a b e d
    dsimp [R]
    split_ifs
    · exact (GMS4b.isClosed_hitIn isCompact_Icc).measurableSet.inter
        (GMS4b.isClosed_hitIn isCompact_Icc).measurableSet
    · exact MeasurableSet.empty
  have heq : {p : C(ℝ, ℂ) × ℂ | p.2 ∈ multiVisitPoints p.1} =
      ⋃ a : ℚ, ⋃ b : ℚ, ⋃ e : ℚ, ⋃ d : ℚ, R a b e d := by
    ext p
    constructor
    · rintro ⟨s, t, hst, hsz, htz⟩
      obtain ⟨a, ha⟩ := exists_rat_lt s
      obtain ⟨d, hd⟩ := exists_rat_gt t
      obtain ⟨b, hsb, hbmid⟩ := exists_rat_btwn (show s < (s + t) / 2 by linarith)
      obtain ⟨e, hmid, het⟩ := exists_rat_btwn (show (s + t) / 2 < t by linarith)
      have hchain : (a : ℝ) ≤ b ∧ (b : ℝ) < e ∧ (e : ℝ) ≤ d :=
        ⟨(ha.trans hsb).le, hbmid.trans hmid, (het.trans hd).le⟩
      refine mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨b,
        mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨d, ?_⟩⟩⟩⟩
      simp only [R, if_pos hchain, mem_inter_iff, mem_setOf_eq]
      exact ⟨⟨s, ⟨ha.le, hsb.le⟩, hsz⟩, ⟨t, ⟨het.le, hd.le⟩, htz⟩⟩
    · simp only [mem_iUnion]
      rintro ⟨a, b, e, d, hp⟩
      have hchain : (a : ℝ) ≤ b ∧ (b : ℝ) < e ∧ (e : ℝ) ≤ d := by
        by_cases h : (a : ℝ) ≤ b ∧ (b : ℝ) < e ∧ (e : ℝ) ≤ d
        · exact h
        · simp [R] at hp
          exact_mod_cast hp.1
      rcases (show p ∈ R a b e d from hp) with hp
      simp only [R, if_pos hchain, mem_inter_iff, mem_setOf_eq] at hp
      obtain ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩ := hp
      exact ⟨s, t, hs.2.trans_lt (hchain.2.1.trans_le ht.1), hsz, htz⟩
  rw [heq]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
    MeasurableSet.iUnion fun e => MeasurableSet.iUnion fun d => hR a b e d

private theorem volume_separated_images_inter_zero {c : C(ℝ, ℂ)}
    (hvol : ∀ s t : ℝ, s ≤ t → volume (c '' Icc s t) = ENNReal.ofReal (t - s))
    {a b e d : ℝ} (hab : a ≤ b) (hbe : b ≤ e) (hed : e ≤ d) :
    volume ((c '' Icc a b) ∩ (c '' Icc e d)) = 0 := by
  refine measure_mono_null (μ := volume) ?_
    (volume_adjacent_images_inter_zero hvol hab (hbe.trans hed))
  rintro z ⟨hz₁, ⟨t, ht, htz⟩⟩
  exact ⟨hz₁, ⟨t, ⟨hbe.trans ht.1, ht.2⟩, htz⟩⟩

/-- The Lebesgue area clock implies that the spatial set of multiple visits is null.
The countable cover separates two visit times by rational intervals. -/
theorem volume_multiVisitPoints_eq_zero {c : C(ℝ, ℂ)}
    (hvol : ∀ s t : ℝ, s ≤ t → volume (c '' Icc s t) = ENNReal.ofReal (t - s)) :
    volume (multiVisitPoints c) = 0 := by
  let cover (a b e d : ℚ) : Set ℂ :=
    if (a : ℝ) ≤ b ∧ (b : ℝ) ≤ e ∧ (e : ℝ) ≤ d then
      (c '' Icc (a : ℝ) b) ∩ (c '' Icc (e : ℝ) d) else ∅
  have hnull (a b e d : ℚ) : volume (cover a b e d) = 0 := by
    dsimp [cover]
    split_ifs with h
    · exact volume_separated_images_inter_zero hvol h.1 h.2.1 h.2.2
    · exact measure_empty
  have hcover : multiVisitPoints c ⊆ ⋃ a : ℚ, ⋃ b : ℚ, ⋃ e : ℚ, ⋃ d : ℚ,
      cover a b e d := by
    rintro z ⟨s, t, hst, hsz, htz⟩
    obtain ⟨a, ha⟩ := exists_rat_lt s
    obtain ⟨d, hd⟩ := exists_rat_gt t
    obtain ⟨b, hsb, hbmid⟩ := exists_rat_btwn (show s < (s + t) / 2 by linarith)
    obtain ⟨e, hmid, het⟩ := exists_rat_btwn (show (s + t) / 2 < t by linarith)
    refine mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨b,
      mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨d, ?_⟩⟩⟩⟩
    have hchain : (a : ℝ) ≤ b ∧ (b : ℝ) ≤ e ∧ (e : ℝ) ≤ d := by
      constructor
      · exact (ha.trans hsb).le
      constructor
      · exact (hbmid.trans hmid).le
      · exact (het.trans hd).le
    simp only [cover, if_pos hchain, mem_inter_iff]
    exact ⟨⟨s, ⟨ha.le, hsb.le⟩, hsz⟩, ⟨t, ⟨het.le, hd.le⟩, htz⟩⟩
  apply nonpos_iff_eq_zero.mp
  calc
    volume (multiVisitPoints c) ≤
        volume (⋃ a : ℚ, ⋃ b : ℚ, ⋃ e : ℚ, ⋃ d : ℚ, cover a b e d) :=
      measure_mono hcover
    _ = 0 := by
      simp only [measure_iUnion_null_iff]
      exact fun a => fun b => fun e => fun d => hnull a b e d

/-- The null multiple-visit conclusion holds for the bundle's Lebesgue-time
space-filling curve on one common probability-one event. -/
theorem ae_bundle_volume_multiVisitPoints_eq_zero
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, volume (multiVisitPoints (ηL ω)) = 0 := by
  filter_upwards [D.spaceFilling] with ω hω
  exact volume_multiVisitPoints_eq_zero hω.2.2.2

private theorem multiVisit_affineReroot_one (c : C(ℝ, ℂ)) (z : ℂ) :
    (0 : ℂ) ∈ multiVisitPoints (MatedCRTHarmonic.MatedCRT.affineReroot z 1 0 c) ↔
      z ∈ multiVisitPoints c := by
  have heval (u : ℝ) :
      MatedCRTHarmonic.MatedCRT.affineReroot z 1 0 c u =
        c (MatedCRTHarmonic.MatedCRT.firstHit c z + u) - z := by
    simp [MatedCRTHarmonic.MatedCRT.affineReroot]
  constructor
  · rintro ⟨s, t, hst, hs, ht⟩
    refine ⟨MatedCRTHarmonic.MatedCRT.firstHit c z + s,
      MatedCRTHarmonic.MatedCRT.firstHit c z + t, by linarith, ?_, ?_⟩
    · exact sub_eq_zero.mp ((heval s).symm.trans hs)
    · exact sub_eq_zero.mp ((heval t).symm.trans ht)
  · rintro ⟨s, t, hst, hs, ht⟩
    refine ⟨s - MatedCRTHarmonic.MatedCRT.firstHit c z,
      t - MatedCRTHarmonic.MatedCRT.firstHit c z, by linarith, ?_, ?_⟩
    · rw [heval, show MatedCRTHarmonic.MatedCRT.firstHit c z +
        (s - MatedCRTHarmonic.MatedCRT.firstHit c z) = s by ring, hs, sub_self]
    · rw [heval, show MatedCRTHarmonic.MatedCRT.firstHit c z +
        (t - MatedCRTHarmonic.MatedCRT.firstHit c z) = t by ring, ht, sub_self]

/-- Every fixed spatial point is visited at most once almost surely by the
bundle's Lebesgue-time curve. -/
theorem ae_bundle_uniqueVisit_fixed
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (D : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm) (z : ℂ) :
    ∀ᵐ ω ∂P, z ∉ multiVisitPoints (ηL ω) := by
  haveI : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hE : MeasurableSet {p : Ω × ℂ | p.2 ∈ multiVisitPoints (ηL p.1)} :=
    measurableSet_multiVisitRelation.preimage
      ((D.measurable_curves.1.comp measurable_fst).prodMk measurable_snd)
  have hFubini : ∀ᵐ w ∂(volume : Measure ℂ),
      ∀ᵐ ω ∂P, w ∉ multiVisitPoints (ηL ω) := by
    apply (Measure.ae_ae_comm (μ := P) (ν := (volume : Measure ℂ)) hE.compl).1
    filter_upwards [ae_bundle_volume_multiVisitPoints_eq_zero D] with ω hω
    exact compl_mem_ae_iff.mpr hω
  have hzero_ae : ∀ᵐ w ∂(volume : Measure ℂ),
      P {ω | w ∈ multiVisitPoints (ηL ω)} = 0 := by
    filter_upwards [hFubini] with w hw
    exact compl_mem_ae_iff.mp hw
  have hconst (w : ℂ) :
      P {ω | w ∈ multiVisitPoints (ηL ω)} =
        P {ω | (0 : ℂ) ∈ multiVisitPoints (ηL ω)} := by
    let A : Set C(ℝ, ℂ) := {c | (0 : ℂ) ∈ multiVisitPoints c}
    have hA : MeasurableSet A :=
      measurableSet_multiVisitRelation.preimage (measurable_id.prodMk measurable_const)
    let f : Ω → C(ℝ, ℂ) := fun ω =>
      MatedCRTHarmonic.MatedCRT.affineReroot w 1 0 (ηL ω)
    have hf : AEMeasurable f P :=
      IGLaw.IsMatingOfTreesCoupling.aemeasurable_affineReroot_of_igMapPositiveRadii
        D (IGLaw.IsMatingOfTreesCoupling.igMapPositiveRadii D) w one_pos 0
    calc
      P {ω | w ∈ multiVisitPoints (ηL ω)} = P (f ⁻¹' A) := by
        congr 1
        ext ω
        exact (multiVisit_affineReroot_one (ηL ω) w).symm
      _ = (P.map f) A := (Measure.map_apply_of_aemeasurable hf hA).symm
      _ = (P.map ηL) A :=
        congrArg (fun μ : Measure C(ℝ, ℂ) => μ A)
          (IGLaw.IsMatingOfTreesCoupling.map_affineReroot_ηL D w one_pos 0)
      _ = P {ω | (0 : ℂ) ∈ multiVisitPoints (ηL ω)} :=
        Measure.map_apply D.measurable_curves.1 hA
  obtain ⟨w, hw⟩ := hzero_ae.exists
  have hzero0 : P {ω | (0 : ℂ) ∈ multiVisitPoints (ηL ω)} = 0 :=
    (hconst w).symm.trans hw
  exact compl_mem_ae_iff.mpr ((hconst z).trans hzero0)

end MatedCRTHarmonic.GMS4c

