/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46TZeroInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TTransfer
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TModel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.ZeroConeMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedArea
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.UStarMoments
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Packing
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Transform
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FinalAdapters

/-!
# Lemma 2.7 area input for the zero-cone model

The zero-cone GMC agrees inside every disk of radius below one with the GMC
of a normalized whole-plane GFF on the same sample space. A countable disk
exhaustion gives the pathwise area domination required by Lemma 2.7.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.MatedCRT

private def l46tExhaustRadius (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)

private theorem l46tExhaustRadius_mem (n : ℕ) :
    l46tExhaustRadius (n + 1) ∈ Ioo (0 : ℝ) 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (n : ℝ) + 2 := by linarith
  have hfrac : 0 < 1 / ((n : ℝ) + 2) := one_div_pos.mpr hden
  have hfrac1 : 1 / ((n : ℝ) + 2) < 1 :=
    (div_lt_iff₀ hden).2 (by linarith)
  have hdeneq : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
  change 0 < 1 - 1 / (((n + 1 : ℕ) : ℝ) + 1) ∧
    1 - 1 / (((n + 1 : ℕ) : ℝ) + 1) < 1
  rw [hdeneq]
  constructor <;> linarith

private theorem l46tExhaust_ball_iUnion :
    (⋃ n : ℕ, ball (0 : ℂ) (l46tExhaustRadius n)) = ball (0 : ℂ) 1 := by
  ext z
  constructor
  · intro hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨n, hn⟩ := hz
    have hr : l46tExhaustRadius n ≤ 1 := by
      dsimp [l46tExhaustRadius]
      have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith
    exact (ball_subset_ball hr) hn
  · intro hz
    have hgap : 0 < 1 - dist z (0 : ℂ) := by
      have := Metric.mem_ball.mp hz
      linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgap
    simp only [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    rw [Metric.mem_ball]
    dsimp [l46tExhaustRadius]
    linarith

/-- The zero-cone area dominates the area of a normalized whole-plane GFF
on the unit disk; in fact the restrictions agree almost surely. -/
theorem l46t_zeroCone_areaDominates
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    GMSLemma27.AreaDominatesWholePlaneGFF (l46tZeroConeCellModel D hγ) := by
  let M := l46tZeroConeCellModel D hγ
  let _ : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Xt, hXt, hlocal⟩ := GMCUpper.exists_zeroConeArea_local_wholePlane hγ D
  obtain ⟨H, hH, _, _, hμ⟩ := GMCFacts.exists_isLQGAreaOf hXt hγ.1 hγ.2
  refine ⟨H, fun ω => MoTPort.qAreaC γ (Xt ω), hH, hμ, ?_⟩
  have hEq : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (GMCUpper.zeroConeArea γ X₀ B₀ B₀' ω).restrict
        (ball (0 : ℂ) (l46tExhaustRadius n)) =
      (GMCUpper.wholePlaneArea γ Xt ω).restrict
        (ball (0 : ℂ) (l46tExhaustRadius n)) := by
    rw [ae_all_iff]
    intro n
    cases n with
    | zero =>
        simp [l46tExhaustRadius]
    | succ n =>
        exact hlocal (l46tExhaustRadius (n + 1)) (l46tExhaustRadius_mem n)
  filter_upwards [hEq] with ω hω
  have hdisc : (GMCUpper.zeroConeArea γ X₀ B₀ B₀' ω).restrict (ball (0 : ℂ) 1) =
      (GMCUpper.wholePlaneArea γ Xt ω).restrict (ball (0 : ℂ) 1) := by
    rw [← l46tExhaust_ball_iUnion]
    exact Measure.restrict_iUnion_congr.mpr hω
  intro A hA hsub
  have hAint : A ∩ ball (0 : ℂ) 1 = A := Set.inter_eq_left.mpr hsub
  have harea : GMCUpper.zeroConeArea γ X₀ B₀ B₀' ω A =
      GMCUpper.wholePlaneArea γ Xt ω A := by
    have hval := congrArg (fun μ : Measure ℂ => μ A) hdisc
    simpa only [Measure.restrict_apply hA, hAint] using hval
  rw [← LQGCone.lqgArea_eq_qAreaC]
  change CellScaling.lqgArea γ (Xt ω) A ≤
    GMCUpper.zeroConeArea γ X₀ B₀ B₀' ω A
  simpa only [GMCUpper.wholePlaneArea] using harea.symm.le

private theorem l46t_orderIso_tendsto_cocompact (φ : ℝ ≃o ℝ) :
    Tendsto φ (cocompact ℝ) (cocompact ℝ) := by
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨K, hK, hKU⟩ := Filter.mem_cocompact.mp hs
  refine Filter.mem_cocompact.mpr ⟨φ.symm '' K, hK.image φ.symm.continuous, ?_⟩
  intro x hx
  apply hKU
  intro hφxK
  apply hx
  exact ⟨φ x, hφxK, by simp⟩

/-- The frozen space-filling curve geometry also holds for its zero-cone
area parametrization. -/
theorem l46t_zeroCone_spaceFillingGeometry
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    SpaceFillingGeometry (l46tZeroConeCellModel D hγ) := by
  filter_upwards [D.spaceFilling, D.areaParam₀] with ω hspace harea
  rcases harea.1 with ⟨φ, _, hηeq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z
    obtain ⟨t, ht⟩ := hspace.1 z
    refine ⟨φ.symm t, ?_⟩
    change η₀ ω (φ.symm t) = z
    rw [hηeq, φ.apply_symm_apply, ht]
  · change Tendsto (η₀ ω) (cocompact ℝ) (cocompact ℂ)
    have hcurve : η₀ ω = ηL ω ∘ φ := by
      funext t
      exact hηeq t
    rw [hcurve]
    exact hspace.2.1.comp (l46t_orderIso_tendsto_cocompact φ)
  · change NullOverlaps (η₀ ω)
    have hcurve : η₀ ω = ηL ω ∘ φ := by
      funext t
      exact hηeq t
    rw [hcurve]
    exact nullOverlaps_of_reparam φ.monotone hspace.2.2.2

/-- The bundle's segment-ball estimate passes through the zero-cone area
time change, using the existing generic reparametrization adapter. -/
theorem l46t_zeroCone_segmentsContainBalls
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    GMSLemma27.SegmentsContainBalls (l46tZeroConeCellModel D hγ) := by
  refine MesoModel.final_segmentsContainBalls_of_reparam
    (l46tZeroConeCellModel D hγ) ηL ?_ D.segmentsContainBalls
  filter_upwards [D.areaParam₀] with ω harea
  rcases harea.1 with ⟨φ, _, hηeq⟩
  exact ⟨φ, hηeq⟩

end MatedCRTHarmonic.GMS4b
