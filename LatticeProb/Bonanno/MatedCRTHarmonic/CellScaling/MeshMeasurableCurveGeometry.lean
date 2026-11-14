/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.MeshMeasurableCurve at commit fdb5cad;
   selected declarations and their proof closure, with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model

set_option autoImplicit false
set_option linter.unnecessarySimpa false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.CellScaling

private def meshCellMinNorm (a b : ℝ) (η : C(ℝ, ℂ)) : ℝ :=
  sInf ((fun t : ℝ => ‖η t‖) '' Icc a b)

private theorem meshCellMinNorm_continuous (a b : ℝ) :
    Continuous (fun η : C(ℝ, ℂ) => meshCellMinNorm a b η) := by
  have hI : IsCompact (Icc a b) := isCompact_Icc
  have heval : Continuous (fun p : C(ℝ, ℂ) × ℝ => ‖p.1 p.2‖) :=
    continuous_norm.comp continuous_eval
  simpa [meshCellMinNorm] using hI.continuous_sInf heval

private theorem meshCell_meets_openBall_iff_minNorm_lt {a b ρ : ℝ}
    (hab : a ≤ b) (η : C(ℝ, ℂ)) :
    ((η '' Icc a b) ∩ ball (0 : ℂ) ρ).Nonempty ↔ meshCellMinNorm a b η < ρ := by
  let R : Set ℝ := (fun t : ℝ => ‖η t‖) '' Icc a b
  have hI : (Icc a b).Nonempty := ⟨a, ⟨le_rfl, hab⟩⟩
  have hR : R.Nonempty := hI.image (fun t : ℝ => ‖η t‖)
  have hcompact : IsCompact R := by
    exact isCompact_Icc.image (continuous_norm.comp η.continuous)
  have hmin : meshCellMinNorm a b η ∈ R := hcompact.sInf_mem hR
  constructor
  · rintro ⟨z, ⟨t, ht, rfl⟩, hz⟩
    have hnorm : ‖η t‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact (csInf_le hcompact.bddBelow ⟨t, ht, rfl⟩).trans_lt hnorm
  · intro hρ
    rcases hmin with ⟨t, ht, hnorm⟩
    refine ⟨η t, ⟨t, ht, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [meshCellMinNorm, hnorm] using hρ

/-- A curve-image mesh cell meets an open ball on a measurable event. -/
theorem measurable_meshCell_meets_openBall {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η) {ε : ℝ} (hε : 0 ≤ ε)
    (x : ℤ) (ρ : ℝ) :
    MeasurableSet {ω | (meshCells ε (η ω) x ∩ ball (0 : ℂ) ρ).Nonempty} := by
  let a := ε * ((x : ℝ) - 1)
  let b := ε * x
  have hab : a ≤ b := by
    have hx : ((x : ℝ) - 1) ≤ x := by linarith
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_left hx hε
  have hmeas : Measurable (fun ω => meshCellMinNorm a b (η ω)) :=
    (meshCellMinNorm_continuous a b).measurable.comp hη
  have hEq : {ω | (meshCells ε (η ω) x ∩ ball (0 : ℂ) ρ).Nonempty} =
      {ω | meshCellMinNorm a b (η ω) < ρ} := by
    ext ω
    exact meshCell_meets_openBall_iff_minNorm_lt hab (η ω)
  rw [hEq]
  exact measurableSet_lt hmeas measurable_const

private def meshCellSphereDeviation (a b : ℝ) (z : ℂ) (r : ℝ)
    (η : C(ℝ, ℂ)) : ℝ :=
  sInf ((fun t : ℝ => |dist (η t) z - r|) '' Icc a b)

private theorem meshCellSphereDeviation_continuous (a b : ℝ) (z : ℂ) (r : ℝ) :
    Continuous (fun η : C(ℝ, ℂ) => meshCellSphereDeviation a b z r η) := by
  have hI : IsCompact (Icc a b) := isCompact_Icc
  let ev : C(ℝ, ℂ) × ℝ → ℂ := fun p => p.1 p.2
  have hev : Continuous ev := continuous_eval
  have heval : Continuous (fun p : C(ℝ, ℂ) × ℝ => |dist (p.1 p.2) z - r|) := by
    change Continuous (fun p => |dist (ev p) z - r|)
    have hdist : Continuous (fun p : C(ℝ, ℂ) × ℝ => dist (ev p) z) := by
      exact continuous_dist.comp (hev.prodMk continuous_const)
    have hsub : Continuous (fun p : C(ℝ, ℂ) × ℝ => dist (ev p) z - r) := by
      exact hdist.sub continuous_const
    exact continuous_abs.comp hsub
  simpa [meshCellSphereDeviation] using hI.continuous_sInf heval

private theorem meshCell_meets_sphere_iff_deviation_eq_zero {a b : ℝ} (hab : a ≤ b)
    (z : ℂ) (r : ℝ) (η : C(ℝ, ℂ)) :
    ((η '' Icc a b) ∩ sphere z r).Nonempty ↔ meshCellSphereDeviation a b z r η = 0 := by
  let R : Set ℝ := (fun t : ℝ => |dist (η t) z - r|) '' Icc a b
  have hI : (Icc a b).Nonempty := ⟨a, ⟨le_rfl, hab⟩⟩
  have hR : R.Nonempty := hI.image (fun t : ℝ => |dist (η t) z - r|)
  have hcompact : IsCompact R := by
    exact isCompact_Icc.image (by fun_prop)
  have hmin : meshCellSphereDeviation a b z r η ∈ R := hcompact.sInf_mem hR
  constructor
  · rintro ⟨w, ⟨t, ht, rfl⟩, hw⟩
    have heq : dist (η t) z = r := by
      simpa only [Metric.mem_sphere] using hw
    have habs : |dist (η t) z - r| = 0 := by rw [heq, sub_self, abs_zero]
    have hnonneg : 0 ≤ sInf R := by
      apply le_csInf hR
      rintro y ⟨u, hu, rfl⟩
      exact abs_nonneg _
    change sInf R = 0
    apply le_antisymm
    · exact csInf_le hcompact.bddBelow ⟨t, ht, habs⟩
    · exact hnonneg
  · intro hzero
    rcases hmin with ⟨t, ht, hdev⟩
    have hdev0 : |dist (η t) z - r| = 0 := by
      calc
        |dist (η t) z - r| = meshCellSphereDeviation a b z r η := hdev
        _ = 0 := hzero
    have hdist : dist (η t) z = r := by
      exact sub_eq_zero.mp (abs_eq_zero.mp hdev0)
    refine ⟨η t, ⟨t, ht, rfl⟩, ?_⟩
    change dist (η t) z = r
    exact hdist

/-- A curve-image mesh cell meets a fixed sphere on a measurable event. -/
theorem measurable_meshCell_meets_sphere {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η) {ε : ℝ} (hε : 0 ≤ ε)
    (x : ℤ) (z : ℂ) (r : ℝ) :
    MeasurableSet {ω | (meshCells ε (η ω) x ∩ sphere z r).Nonempty} := by
  let a := ε * ((x : ℝ) - 1)
  let b := ε * x
  have hab : a ≤ b := by
    have hx : ((x : ℝ) - 1) ≤ x := by linarith
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_left hx hε
  have hmeas : Measurable (fun ω => meshCellSphereDeviation a b z r (η ω)) :=
    (meshCellSphereDeviation_continuous a b z r).measurable.comp hη
  have hEq : {ω | (meshCells ε (η ω) x ∩ sphere z r).Nonempty} =
      {ω | meshCellSphereDeviation a b z r (η ω) = 0} := by
    ext ω
    exact meshCell_meets_sphere_iff_deviation_eq_zero hab z r (η ω)
  rw [hEq]
  exact measurableSet_eq_fun hmeas measurable_const

private def meshCellMinDist (a b : ℝ) (z : ℂ) (η : C(ℝ, ℂ)) : ℝ :=
  sInf ((fun t : ℝ => dist (η t) z) '' Icc a b)

private def meshCellMaxDist (a b : ℝ) (z : ℂ) (η : C(ℝ, ℂ)) : ℝ :=
  sSup ((fun t : ℝ => dist (η t) z) '' Icc a b)

private theorem meshCellMinDist_continuous (a b : ℝ) (z : ℂ) :
    Continuous (fun η : C(ℝ, ℂ) => meshCellMinDist a b z η) := by
  have hI : IsCompact (Icc a b) := isCompact_Icc
  have heval : Continuous (fun p : C(ℝ, ℂ) × ℝ => dist (p.1 p.2) z) := by
    exact continuous_dist.comp (continuous_eval.prodMk continuous_const)
  simpa [meshCellMinDist] using hI.continuous_sInf heval

private theorem meshCellMaxDist_continuous (a b : ℝ) (z : ℂ) :
    Continuous (fun η : C(ℝ, ℂ) => meshCellMaxDist a b z η) := by
  have hI : IsCompact (Icc a b) := isCompact_Icc
  have heval : Continuous (fun p : C(ℝ, ℂ) × ℝ => dist (p.1 p.2) z) := by
    exact continuous_dist.comp (continuous_eval.prodMk continuous_const)
  simpa [meshCellMaxDist] using hI.continuous_sSup heval

private theorem meshCell_meets_annulus_iff_extrema {a b inner outer : ℝ}
    (hab : a ≤ b) (z : ℂ) (η : C(ℝ, ℂ)) :
    ((η '' Icc a b) ∩ annulus z inner outer).Nonempty ↔
      inner < outer ∧ meshCellMinDist a b z η < outer ∧
        inner ≤ meshCellMaxDist a b z η := by
  let f : ℝ → ℝ := fun t => dist (η t) z
  have hf : ContinuousOn f (Icc a b) := (continuous_dist.comp
    (η.continuous.prodMk continuous_const)).continuousOn
  have himage : f '' Icc a b =
      Icc (meshCellMinDist a b z η) (meshCellMaxDist a b z η) := by
    exact hf.image_Icc hab
  constructor
  · rintro ⟨w, ⟨t, ht, rfl⟩, hw⟩
    have hfw : f t ∈ Icc (meshCellMinDist a b z η) (meshCellMaxDist a b z η) := by
      rw [← himage]
      exact ⟨t, ht, rfl⟩
    have hout : f t < outer := hw.1
    have hin : inner ≤ f t := not_lt.mp hw.2
    exact ⟨hin.trans_lt hout, hfw.1.trans_lt hout, hin.trans hfw.2⟩
  · rintro ⟨hio, hmin, hmax⟩
    let d : ℝ := max inner (meshCellMinDist a b z η)
    have hdlo : meshCellMinDist a b z η ≤ d := le_max_right _ _
    have hdhi : d ≤ meshCellMaxDist a b z η := by
      apply max_le
      · exact hmax
      · have hne : (Icc a b).Nonempty := ⟨a, ⟨le_rfl, hab⟩⟩
        have hcompact : IsCompact (f '' Icc a b) := isCompact_Icc.image
          (continuous_dist.comp (η.continuous.prodMk continuous_const))
        exact csInf_le_csSup (hne.image f) hcompact.bddBelow hcompact.bddAbove
    have hdout : d < outer := max_lt hio hmin
    obtain ⟨t, ht, htd⟩ : d ∈ f '' Icc a b := by
      rw [himage]
      exact ⟨hdlo, hdhi⟩
    refine ⟨η t, ⟨t, ht, rfl⟩, ?_⟩
    constructor
    · simpa only [Metric.mem_ball, ← htd] using hdout
    · have hdin : inner ≤ d := le_max_left _ _
      simpa only [Metric.mem_ball, ← htd] using (not_lt.mpr hdin)

/-- A curve-image mesh cell meets a fixed half-open annulus on a Borel event. -/
theorem measurable_meshCell_meets_annulus {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η) {ε : ℝ} (hε : 0 ≤ ε)
    (x : ℤ) (z : ℂ) (inner outer : ℝ) :
    MeasurableSet {ω | (meshCells ε (η ω) x ∩ annulus z inner outer).Nonempty} := by
  let a := ε * ((x : ℝ) - 1)
  let b := ε * x
  have hab : a ≤ b := by
    have hx : ((x : ℝ) - 1) ≤ x := by linarith
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_left hx hε
  have hmin : Measurable (fun ω => meshCellMinDist a b z (η ω)) :=
    (meshCellMinDist_continuous a b z).measurable.comp hη
  have hmax : Measurable (fun ω => meshCellMaxDist a b z (η ω)) :=
    (meshCellMaxDist_continuous a b z).measurable.comp hη
  have hEq : {ω | (meshCells ε (η ω) x ∩ annulus z inner outer).Nonempty} =
      {ω | inner < outer ∧ meshCellMinDist a b z (η ω) < outer ∧
        inner ≤ meshCellMaxDist a b z (η ω)} := by
    ext ω
    exact meshCell_meets_annulus_iff_extrema hab z (η ω)
  rw [hEq]
  exact (show MeasurableSet {ω : Ω | inner < outer} from
    if hio : inner < outer then by simpa [hio] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
    else by simpa [hio] using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))).inter
      ((measurableSet_lt hmin measurable_const).inter
        (measurableSet_le measurable_const hmax))

private theorem meshCell_subset_annulus_iff_extrema {a b inner outer : ℝ}
    (hab : a ≤ b) (z : ℂ) (η : C(ℝ, ℂ)) :
    η '' Icc a b ⊆ annulus z inner outer ↔
      inner ≤ meshCellMinDist a b z η ∧ meshCellMaxDist a b z η < outer := by
  let R : Set ℝ := (fun t : ℝ => dist (η t) z) '' Icc a b
  have hI : (Icc a b).Nonempty := ⟨a, ⟨le_rfl, hab⟩⟩
  have hR : R.Nonempty := hI.image (fun t : ℝ => dist (η t) z)
  have hcompact : IsCompact R := isCompact_Icc.image (by fun_prop)
  have hmin : meshCellMinDist a b z η ∈ R := hcompact.sInf_mem hR
  have hmax : meshCellMaxDist a b z η ∈ R := hcompact.sSup_mem hR
  constructor
  · intro hsub
    have hinner : ∀ y ∈ R, inner ≤ y := by
      rintro y ⟨t, ht, rfl⟩
      have hmem := hsub ⟨t, ht, rfl⟩
      have hnot : ¬ dist (η t) z < inner := by
        simpa only [Metric.mem_ball] using hmem.2
      exact not_lt.mp hnot
    have houterMax : meshCellMaxDist a b z η < outer := by
      rcases hmax with ⟨t, ht, hdist⟩
      have hmem := hsub ⟨t, ht, rfl⟩
      simpa [meshCellMaxDist, hdist] using hmem.1
    exact ⟨le_csInf hR hinner, houterMax⟩
  · rintro ⟨hinner, houter⟩ w ⟨t, ht, rfl⟩
    constructor
    · have hle : dist (η t) z ≤ meshCellMaxDist a b z η := by
        apply le_csSup (hcompact.bddAbove)
        exact ⟨t, ht, rfl⟩
      exact hle.trans_lt houter
    · have hle : meshCellMinDist a b z η ≤ dist (η t) z := by
        exact csInf_le hcompact.bddBelow ⟨t, ht, rfl⟩
      exact not_lt.mpr (hinner.trans hle)

/-- A curve-image mesh cell lies in a fixed annulus on a measurable event. -/
theorem measurable_meshCell_subset_annulus {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η) {ε : ℝ} (hε : 0 ≤ ε)
    (x : ℤ) (z : ℂ) (inner outer : ℝ) :
    MeasurableSet {ω | meshCells ε (η ω) x ⊆ annulus z inner outer} := by
  let a := ε * ((x : ℝ) - 1)
  let b := ε * x
  have hab : a ≤ b := by
    have hx : ((x : ℝ) - 1) ≤ x := by linarith
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_left hx hε
  have hmin : Measurable (fun ω => meshCellMinDist a b z (η ω)) :=
    (meshCellMinDist_continuous a b z).measurable.comp hη
  have hmax : Measurable (fun ω => meshCellMaxDist a b z (η ω)) :=
    (meshCellMaxDist_continuous a b z).measurable.comp hη
  have hEq : {ω | meshCells ε (η ω) x ⊆ annulus z inner outer} =
      {ω | inner ≤ meshCellMinDist a b z (η ω) ∧
        meshCellMaxDist a b z (η ω) < outer} := by
    ext ω
    exact meshCell_subset_annulus_iff_extrema hab z (η ω)
  rw [hEq]
  exact (measurableSet_le measurable_const hmin).inter (measurableSet_lt hmax measurable_const)

end MatedCRTHarmonic.CellScaling
