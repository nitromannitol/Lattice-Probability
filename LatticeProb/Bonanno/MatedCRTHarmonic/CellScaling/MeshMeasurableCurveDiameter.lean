/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source modules MatedCRTHarmonic.CellFamily.MeasurableCurve and
   MatedCRTHarmonic.CellScaling.MeshMeasurableCurve at commit fdb5cad;
   selected declarations and their proof closure, with local imports adapted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableCurveGeometry

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.CellFamily

/-- The curve-image cell associated to a continuous-map representative. -/
def curveCell {Ω : Type*} (η : Ω → C(ℝ, ℂ)) (ε : ℝ) (ω : Ω) (x : ℤ) : Set ℂ :=
  η ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x)

private def curveCellDiameterSup (a b : ℝ) (η : C(ℝ, ℂ)) : ℝ :=
  sSup ((fun p : ℝ × ℝ => dist (η p.1) (η p.2)) '' (Icc a b ×ˢ Icc a b))

private theorem curveCellDiameterSup_eq_diam {a b : ℝ} (hab : a ≤ b)
    (η : C(ℝ, ℂ)) :
    curveCellDiameterSup a b η = Metric.diam (η '' Icc a b) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc a b
  let d : ℝ × ℝ → ℝ := fun p => dist (η p.1) (η p.2)
  have hK : K.Nonempty := ⟨(a, a), ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hab⟩⟩⟩
  have hbd : BddAbove (d '' K) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.image η.continuous).isBounded.exists_norm_le
    refine ⟨2 * C, ?_⟩
    rintro r ⟨p, hp, rfl⟩
    rcases hp with ⟨hp1, hp2⟩
    have h1 : ‖η p.1‖ ≤ C := hC _ ⟨p.1, hp1, rfl⟩
    have h2 : ‖η p.2‖ ≤ C := hC _ ⟨p.2, hp2, rfl⟩
    calc dist (η p.1) (η p.2) ≤ ‖η p.1‖ + ‖η p.2‖ := by
          rw [dist_eq_norm]
          exact norm_sub_le _ _
      _ ≤ 2 * C := by linarith
  have hnonempty : (η '' Icc a b).Nonempty := (nonempty_Icc.mpr hab).image η
  have hsNonempty : (d '' K).Nonempty := hK.image d
  have hsup_nonneg : 0 ≤ sSup (d '' K) := by
    apply le_csSup hbd
    exact ⟨(a, a), ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hab⟩⟩, by simp [d]⟩
  apply le_antisymm
  · apply csSup_le hsNonempty
    rintro r ⟨p, hp, rfl⟩
    rcases hp with ⟨hp1, hp2⟩
    exact Metric.dist_le_diam_of_mem (isCompact_Icc.image η.continuous).isBounded
      ⟨p.1, hp1, rfl⟩ ⟨p.2, hp2, rfl⟩
  · apply Metric.diam_le_of_forall_dist_le (s := η '' Icc a b) hsup_nonneg
    rintro u ⟨t, ht, rfl⟩ v ⟨s, hs, rfl⟩
    apply le_csSup hbd
    exact ⟨(t, s), ⟨ht, hs⟩, rfl⟩

private theorem continuous_curveCellDiameterSup (a b : ℝ) :
    Continuous (fun η : C(ℝ, ℂ) => curveCellDiameterSup a b η) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc a b
  have hI : IsCompact (Icc a b) := isCompact_Icc
  have hK : IsCompact K := hI.prod hI
  have heval : Continuous (fun p : C(ℝ, ℂ) × (ℝ × ℝ) => p.1 p.2.1) := by
    exact continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have heval₂ : Continuous (fun p : C(ℝ, ℂ) × (ℝ × ℝ) => p.1 p.2.2) := by
    exact continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hd : Continuous (fun p : C(ℝ, ℂ) × (ℝ × ℝ) =>
      dist (p.1 p.2.1) (p.1 p.2.2)) :=
    continuous_dist.comp (heval.prodMk heval₂)
  simpa [curveCellDiameterSup, K] using hK.continuous_sSup hd

/-- Diameter of a curve-image cell is a continuous, hence measurable, functional of the random
continuous curve in the compact-open topology. -/
theorem measurable_curveCell_diam {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → C(ℝ, ℂ)) (hη : Measurable η) {ε : ℝ} (hε : 0 ≤ ε) (x : ℤ) :
    Measurable (fun ω => Metric.diam (curveCell η ε ω x)) := by
  let a := ε * ((x : ℝ) - 1)
  let b := ε * x
  have hab : a ≤ b := by
    have hx : ((x : ℝ) - 1) ≤ x := by linarith
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_left hx hε
  have hcont := continuous_curveCellDiameterSup a b
  have hEq : (fun ω => Metric.diam (curveCell η ε ω x)) =
      (fun ω => curveCellDiameterSup a b (η ω)) := by
    funext ω
    exact (curveCellDiameterSup_eq_diam hab (η ω)).symm
  rw [hEq]
  exact hcont.measurable.comp hη

end MatedCRTHarmonic.CellFamily

namespace MatedCRTHarmonic.CellScaling

/-- The diameter clause of `meshGridGood` is a Borel event in the curve coordinate. -/
theorem measurable_meshGridDiameterPart (k : ℕ) (q ρ : ℝ) :
    MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) | ∀ x : ℤ,
      (meshCells (CellFamily.mesh k) d.2 x ∩ ball (0 : ℂ) ρ).Nonempty →
        Metric.diam (meshCells (CellFamily.mesh k) d.2 x) ≤ CellFamily.mesh k ^ q} := by
  classical
  rw [show {d : MatedCRT.Path2 × C(ℝ, ℂ) | ∀ x : ℤ,
      (meshCells (CellFamily.mesh k) d.2 x ∩ ball (0 : ℂ) ρ).Nonempty →
        Metric.diam (meshCells (CellFamily.mesh k) d.2 x) ≤ CellFamily.mesh k ^ q} =
      ⋂ x : ℤ, {d : MatedCRT.Path2 × C(ℝ, ℂ) |
        (meshCells (CellFamily.mesh k) d.2 x ∩ ball (0 : ℂ) ρ).Nonempty →
          Metric.diam (meshCells (CellFamily.mesh k) d.2 x) ≤ CellFamily.mesh k ^ q} by
        ext d
        simp]
  apply MeasurableSet.iInter
  intro x
  have hε : 0 ≤ CellFamily.mesh k := by
    dsimp [CellFamily.mesh]
    positivity
  have hhit : MeasurableSet {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      (meshCells (CellFamily.mesh k) d.2 x ∩ ball (0 : ℂ) ρ).Nonempty} :=
    measurable_meshCell_meets_openBall Prod.snd measurable_snd hε x ρ
  have hdiam : Measurable (fun d : MatedCRT.Path2 × C(ℝ, ℂ) =>
      Metric.diam (meshCells (CellFamily.mesh k) d.2 x)) := by
    let η : MatedCRT.Path2 × C(ℝ, ℂ) → C(ℝ, ℂ) := fun d => d.2
    have hcurve := CellFamily.measurable_curveCell_diam η measurable_snd hε x
    simpa [CellFamily.curveCell, meshCells] using hcurve
  rw [show {d : MatedCRT.Path2 × C(ℝ, ℂ) |
      (meshCells (CellFamily.mesh k) d.2 x ∩ ball (0 : ℂ) ρ).Nonempty →
        Metric.diam (meshCells (CellFamily.mesh k) d.2 x) ≤ CellFamily.mesh k ^ q} =
      {d | d ∉ {d : MatedCRT.Path2 × C(ℝ, ℂ) |
        (meshCells (CellFamily.mesh k) d.2 x ∩ ball (0 : ℂ) ρ).Nonempty} ∨
        Metric.diam (meshCells (CellFamily.mesh k) d.2 x) ≤ CellFamily.mesh k ^ q} by
        ext d
        simp [imp_iff_not_or]]
  exact hhit.compl.union (measurableSet_le hdiam measurable_const)

end MatedCRTHarmonic.CellScaling
