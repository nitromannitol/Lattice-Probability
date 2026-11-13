/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.FrozenIdentities at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge

/-!
# Cone-field area and circle-average facts

Two SLE-free facts establish that the coupling's field data describe the intended γ-cone and
0-cone:
* `ae_exists_isVagueLimitC_cone` and `ae_exists_isVagueLimitC_cone₀`: almost surely the dyadic area
  approximations of both cone fields of a mating-of-trees coupling have a vague limit, so the quantification over every
  vague limit in the fields `areaParam`, `areaParam₀` (the area-parametrization premise) is not empty;
* `ae_circleAvg_cone_exp` and `ae_circleAvg_cone₀_exp`: for every `t`, almost surely the circle average of the
  cone field about `0` at radius `e^{−t}` is the radial process at `t`.

Both hold for every coupling satisfying the bundle's SLE-free data fields (`gff`, `bm_B`, `bm_B'`, `indep_cone` and
their `₀` versions), with `γ ∈ (0, 2)` for the area limit. The corresponding results for `CellScaling.*` are definitionally equal
(`LQGCone.ae_isVagueLimitC_coneField`, `LQGCone.ae_circleAvg_coneField_exp`); this file restates them on the frozen v3
definitions. LC's area theorem assumes the independence of the field from the cone radial process (`hXA`); the bundle
states the independence of the field from the pair of Brownian paths (`indep_cone`). The bridge
`indepFun_motConeRadial_of_indep` derives the former from the latter: the Brownian paths are replaced by versions that
are continuous for every sample (QuantumZipper `WedgeMeas.exists_good_version`), on which the cone radial process is a
measurable function of the pair of paths (QuantumZipper `WedgeMeas.measurable_lastZero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel.FrozenIdentities

open MatedCRTHarmonic

/-! ### The frozen v3 field layer is the landed `CellScaling` copy (definitionally) -/

theorem coneRadial_eq_cellScaling : MatedCRT.coneRadial = CellScaling.coneRadial := rfl

theorem coneField_eq_cellScaling : MatedCRT.coneField = CellScaling.coneField := rfl

/-- `γ < Q` for `γ ∈ (0, 2)` (the γ-cone is subcritical: `Q − γ = 2/γ − γ/2 > 0`). -/
theorem lt_lqgQ {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) : γ < MatedCRT.lqgQ γ := by
  obtain ⟨h0, h2⟩ := hγ
  have h : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ two_pos h0]
    nlinarith
  simp only [MatedCRT.lqgQ]
  linarith

/-- `0 < Q` for `γ > 0`. -/
theorem lqgQ_pos {γ : ℝ} (hγ : 0 < γ) : 0 < MatedCRT.lqgQ γ := by
  simp only [MatedCRT.lqgQ]
  positivity

/-! ### Independence of the field from the cone radial process -/

/-- Pairs of paths that are both continuous (the subtype carries the subspace σ-algebra of the product σ-algebra). -/
abbrev ContPair : Type := {p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) // Continuous p.1 ∧ Continuous p.2}

/-- The radial process `motConeRadial` (LC's MoT convention `A_t − Qt`) of a pair of continuous paths is a measurable
function of the pair: on continuous paths the last zero is measurable (QuantumZipper `WedgeMeas.measurable_lastZero`)
and the evaluation at a measurable time is jointly measurable. -/
theorem measurable_motConeRadial_contPair (γ α : ℝ) :
    Measurable fun q : ContPair => fun t : ℝ => LQGCone.motConeRadial γ α q.1.1 q.1.2 t := by
  have hev : ∀ s : ℝ≥0, Measurable fun q : ContPair => q.1.1 s := fun s =>
    (measurable_pi_apply s).comp (measurable_fst.comp measurable_subtype_coe)
  have hev' : ∀ s : ℝ≥0, Measurable fun q : ContPair => q.1.2 s := fun s =>
    (measurable_pi_apply s).comp (measurable_snd.comp measurable_subtype_coe)
  refine measurable_pi_iff.2 fun t => ?_
  by_cases ht : 0 ≤ t
  · have e : (fun q : ContPair => LQGCone.motConeRadial γ α q.1.1 q.1.2 t) =
        fun q => q.1.1 t.toNNReal + α * t - CellScaling.lqgQ γ * t := by
      funext q
      simp only [LQGCone.motConeRadial, CellScaling.coneRadial, ite_eq_left ht]
    rw [e]
    exact ((hev _).add_const _).sub_const _
  · set c : ContPair → ℝ → ℝ := fun q u => q.1.2 u.toNNReal + (CellScaling.lqgQ γ - α) * u with hc
    have hcc : ∀ q, Continuous (c q) := fun q =>
      (q.2.2.comp continuous_real_toNNReal).add (continuous_const.mul continuous_id)
    have hcm : ∀ u, Measurable fun q => c q u := fun u => (hev' _).add_const _
    have hL : Measurable fun q => QuantumZipper.lastZero (c q) :=
      QuantumZipper.WedgeMeas.measurable_lastZero hcc hcm
    have hJ : Measurable fun p : ℝ × ContPair => c p.2 p.1 :=
      measurable_uncurry_of_continuous_of_measurable (u := fun r q => c q r) hcc hcm
    have e : (fun q : ContPair => LQGCone.motConeRadial γ α q.1.1 q.1.2 t) =
        fun q => c q (QuantumZipper.lastZero (c q) - t) + CellScaling.lqgQ γ * t - CellScaling.lqgQ γ * t := by
      funext q
      simp only [LQGCone.motConeRadial, CellScaling.coneRadial, ite_eq_right ht, hc]
      rfl
    rw [e]
    exact ((hJ.comp ((hL.sub_const t).prodMk measurable_id)).add_const _).sub_const _

/-- **Independence bridge.** The independence of `X` from the pair of Brownian paths (the bundle's field
`indep_cone.1`) implies the independence of `X` from the cone radial process `motConeRadial` of that pair (LC's
hypothesis `hXA`). The paths are replaced by versions continuous for every sample, equal to them on a conull set. -/
theorem indepFun_motConeRadial_of_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {β : Type*} [MeasurableSpace β] {X : Ω → β} {B B' : ℝ≥0 → Ω → ℝ} (γ α : ℝ)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P) :
    IndepFun X (fun ω t => LQGCone.motConeRadial γ α (fun s => B s ω) (fun s => B' s ω) t) P := by
  obtain ⟨G, -, hG0, hGc, -⟩ :=
    QuantumZipper.WedgeMeas.exists_good_version (fun t => hB.aemeasurable t) hB.cont
  obtain ⟨G', -, hG'0, hG'c, -⟩ :=
    QuantumZipper.WedgeMeas.exists_good_version (fun t => hB'.aemeasurable t) hB'.cont
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := measure_eq_zero_iff_ae_notMem.1 hG0 |>.mono fun ω h => not_not.1 h
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := measure_eq_zero_iff_ae_notMem.1 hG'0 |>.mono fun ω h => not_not.1 h
  -- the versions: continuous for every sample
  set C : ℝ≥0 → Ω → ℝ := fun t => G.indicator (B t) with hC
  set C' : ℝ≥0 → Ω → ℝ := fun t => G'.indicator (B' t) with hC'
  have hCc : ∀ ω, Continuous fun t => C t ω := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [hC, Set.indicator_of_mem hω] using hGc ω hω
    · simpa only [hC, Set.indicator_of_notMem hω] using continuous_const
  have hC'c : ∀ ω, Continuous fun t => C' t ω := by
    intro ω
    by_cases hω : ω ∈ G'
    · simpa only [hC', Set.indicator_of_mem hω] using hG'c ω hω
    · simpa only [hC', Set.indicator_of_notMem hω] using continuous_const
  let Y : Ω → ContPair := fun ω => ⟨((fun t => C t ω), (fun t => C' t ω)), hCc ω, hC'c ω⟩
  -- `X` is independent of the versions
  have hYae : (fun ω => ((fun t => B t ω), (fun t => B' t ω))) =ᵐ[P] fun ω => (Y ω).1 := by
    filter_upwards [hGae, hG'ae] with ω h1 h2
    simp only [Y, hC, hC', Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  have hindY : IndepFun X Y P := by
    have h := hind.congr (ae_eq_refl _) hYae
    rw [IndepFun_iff_Indep] at h ⊢
    have hσ : MeasurableSpace.comap Y (inferInstance : MeasurableSpace ContPair) =
        MeasurableSpace.comap (fun ω => (Y ω).1) (inferInstance : MeasurableSpace ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))) := by
      rw [show (inferInstance : MeasurableSpace ContPair) =
          MeasurableSpace.comap Subtype.val inferInstance from rfl, MeasurableSpace.comap_comp]
      rfl
    rw [hσ]
    exact h
  -- the radial process of the versions is a measurable function of the versions
  have hindZ := hindY.comp measurable_id (measurable_motConeRadial_contPair γ α)
  refine hindZ.congr (ae_eq_refl _) ?_
  filter_upwards [hGae, hG'ae] with ω h1 h2
  have e1 : (fun s => C s ω) = fun s => B s ω := funext fun s => by
    simp only [hC, Set.indicator_of_mem h1]
  have e2 : (fun s => C' s ω) = fun s => B' s ω := funext fun s => by
    simp only [hC', Set.indicator_of_mem h2]
  simp only [Function.comp_apply, Y]
  rw [e1, e2]

/-! ### NJ1, NJ2 on the frozen names, from the bundle's SLE-free data fields -/

/-- **NJ1, general form.** For `0 < γ < 2` and `α < Q`, a whole-plane GFF `X` and Brownian motions `B, B'` with the
independence structure of the bundle's field `indep_cone`: almost surely the dyadic area approximations of the frozen
cone field `coneField X (coneRadial γ α B B')` have a vague limit. -/
theorem ae_exists_isVagueLimitC_coneField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} {X : Ω → MatedCRT.Field} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < MatedCRT.lqgQ γ)
    (hX : LQGMetric.IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℂ, MatedCRT.IsVagueLimitC
      (MatedCRT.lqgAreaApprox γ (MatedCRT.coneField (X ω)
        (MatedCRT.coneRadial γ α (fun t => B t ω) (fun t => B' t ω)))) μ :=
  LQGCone.ae_isVagueLimitC_coneField hγ hγ2 hα hX hB hB' hind.2
    (indepFun_motConeRadial_of_indep γ α hB hB' hind.1)

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **NJ1 for the γ-cone of a mating-of-trees coupling** (closure anchor R4): almost surely the area approximations
of `h = coneField X (coneRadial γ γ B B')` have a vague limit. -/
theorem ae_exists_isVagueLimitC_cone
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℂ, MatedCRT.IsVagueLimitC
      (MatedCRT.lqgAreaApprox γ (MatedCRT.coneField (X ω)
        (MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))) μ := by
  have := D.isProbabilityMeasure
  exact ae_exists_isVagueLimitC_coneField hγ.1 hγ.2 (lt_lqgQ hγ) D.gff D.bm_B D.bm_B' D.indep_cone

/-- **NJ1 for the 0-cone of a mating-of-trees coupling** (closure anchor R4): almost surely the area approximations
of `h₀ = coneField X₀ (coneRadial γ 0 B₀ B₀')` have a vague limit. -/
theorem ae_exists_isVagueLimitC_cone₀
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℂ, MatedCRT.IsVagueLimitC
      (MatedCRT.lqgAreaApprox γ (MatedCRT.coneField (X₀ ω)
        (MatedCRT.coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω)))) μ := by
  have := D.isProbabilityMeasure
  exact ae_exists_isVagueLimitC_coneField hγ.1 hγ.2 (lqgQ_pos hγ.1) D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀

end MatedCRTHarmonic.MesoModel.FrozenIdentities
