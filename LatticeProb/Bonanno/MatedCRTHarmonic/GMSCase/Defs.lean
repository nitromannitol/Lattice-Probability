/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase.Defs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTAffineReroot
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_19

/-!
# The Case 3 and Case 4 objects of [18] Proposition 4.10

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*,
 (`[18]:N`), proof of Proposition 4.10, Cases 2–4,
`[18]`; (the Case 4 inverse coordinate is `2(w − z₀)`) and.

For a field `h` (a whole-plane GFF normalized by `h_1(0) = 0`), a root `z₀` and a Lebesgue-time
curve `c` (the whole-plane space-filling SLE `η_L`):

* `halfAvg h z₀ = h_{1/2}(z₀)`. With `h² = h − γ log|· − z₀|` (the Case 2 field), the Case 2
  index of [18] is `h²_{1/2}(z₀) = h_{1/2}(z₀) + γ log 2`;
* `case4Normalized h z₀ = h(·/2 + z₀) − h_{1/2}(z₀)`. The Case 4 field of [18]
  is `h⁴ = h³(·/2 + z₀)` with `h³ = h² − h²_{1/2}(z₀)`; on the whole plane
  `h⁴ = case4Normalized h z₀ − γ log|·|`;
* `case4Curve z₀ c = affineReroot z₀ (1/2) 0 c = 2(c(τ_{z₀} + ·/4) − z₀)`: the image of `c` under
  `w ↦ 2(w − z₀)`, re-rooted at its first visit to `z₀` and reparametrized by Lebesgue measure.

The file proves the joint Borel measurability of these maps in `(field, root)` and
`(root, curve)`; the first needs the continuity of the translation family of a test function in
`𝓓(ℂ)` (the same Carathéodory argument as LQGMetric's `measurable_apply_bumpTest`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open scoped Distributions

namespace MatedCRTHarmonic.GMSCase

open LQGMetric

/-! ## Definitions -/

/-! ## General radius

The repaired Case 3 argument  renormalizes at a radius `r ∈ (3/4, 1)` (not `1/2`),
matching the γ-cone's Markov decomposition at the same radius. -/

/-- `h_r(z₀)`. -/
def radAvg (r : ℝ) (h : DistC) (z₀ : ℂ) : ℝ := circleAvg h r z₀

/-- `h(r · + z₀) − h_r(z₀)`. -/
def caseNormalized (r : ℝ) (h : DistC) (z₀ : ℂ) : DistC :=
  addConst (affineComp r z₀ h) (-circleAvg h r z₀)

/-- `t ↦ r⁻¹ (c(τ_{z₀} + r² t) − z₀)`: the curve under `w ↦ (w − z₀)/r`, re-rooted at `z₀`. -/
def caseCurve (r : ℝ) (z₀ : ℂ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) := MatedCRT.affineReroot z₀ r 0 c

theorem caseCurve_apply (r : ℝ) (z₀ : ℂ) (c : C(ℝ, ℂ)) (t : ℝ) :
    caseCurve r z₀ c t = (r⁻¹ : ℂ) * (c (MatedCRT.firstHit c z₀ + r ^ 2 * t) - z₀) := by
  simp only [caseCurve, MatedCRT.affineReroot, ContinuousMap.coe_mk]
  have h1 : ((r : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I))⁻¹ = (r⁻¹ : ℂ) := by
    simp
  rw [h1]

/-! ## Joint measurability in the root -/

/-- The translation family `z ↦ φ((· − z)/r)` is continuous into `𝓓(ℂ)`. -/
theorem continuous_testAffinePull_center {r : ℝ} (hr : r ≠ 0) (φ : TestC) :
    Continuous fun z : ℂ => testAffinePull r z φ := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let S := closedBall x₀ 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let g : TestC := testAffinePull r 0 φ
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y : ℂ, R < ‖y‖ → g y = 0 := by
    obtain ⟨R, hR⟩ := g.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun y hy => ?_⟩
    by_contra hne
    have hmem : y ∈ tsupport (g : ℂ → ℝ) := subset_tsupport _ hne
    have := hR hmem
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  let K : Compacts ℂ := ⟨closedBall 0 (|R| + ‖x₀‖ + 1), isCompact_closedBall _ _⟩
  have hs : ∀ x : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => g (y + -(x : ℂ)) :=
    fun x => g.contDiff.comp (contDiff_id.add contDiff_const)
  have hK : ∀ x : S, ∀ y ∉ (K : Set ℂ), g (y + -(x : ℂ)) = 0 := by
    intro x y hy
    apply hR
    have hx : ‖(x : ℂ) - x₀‖ ≤ 1 := by rw [← dist_eq_norm]; exact mem_closedBall.1 x.2
    have hy' : |R| + ‖x₀‖ + 1 < ‖y‖ := by
      have : y ∉ closedBall (0 : ℂ) (|R| + ‖x₀‖ + 1) := hy
      rw [mem_closedBall, dist_zero_right, not_le] at this
      exact this
    have h1 : ‖y‖ ≤ ‖y + -(x : ℂ)‖ + ‖(x : ℂ) - x₀‖ + ‖x₀‖ := by
      calc ‖y‖ = ‖(y + -(x : ℂ)) + ((x : ℂ) - x₀) + x₀‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    have hRle : R ≤ |R| := le_abs_self R
    linarith
  have hD : ∀ i : ℕ, Continuous fun p : S × ℂ =>
      iteratedFDeriv ℝ i (fun y => g (y + -(p.1 : ℂ))) p.2 := by
    intro i
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (g.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_subtype_val.comp continuous_fst).neg)
  have hc := continuous_testFamK K (fun (x : S) y => g (y + -(x : ℂ))) hs hK hD
  have e : (fun x : S => testAffinePull r x φ) = ofSuppC K ∘ testFamK K _ hs hK := by
    funext x
    ext y
    show testAffinePull r x φ y = testAffinePull r 0 φ (y + -(x : ℂ))
    rw [testAffinePull_apply r _ hr, testAffinePull_apply r _ hr]
    congr 1
    ring
  have h2 : Continuous fun x : S => testAffinePull r x φ := by
    rw [e]; exact (ofSuppC K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 h2).continuousAt
    (closedBall_mem_nhds _ one_pos)

/-- **The affine pullback is jointly measurable in the field and the centre.** -/
theorem measurable_affineComp_center (r : ℝ) :
    Measurable fun p : DistC × ℂ => affineComp r p.2 p.1 := by
  by_cases hr : r = 0
  · subst hr
    have e : (fun p : DistC × ℂ => affineComp 0 p.2 p.1) = fun _ => 0 := by
      funext p
      refine DFunLike.ext _ _ fun φ => ?_
      simp [affineComp, testAffinePull]
      rfl
    rw [e]
    exact measurable_const
  refine measurable_distOn_iff.2 fun φ => ?_
  show Measurable fun p : DistC × ℂ => (r ^ 2)⁻¹ * p.1 (testAffinePull r p.2 φ)
  refine Measurable.const_mul ?_ _
  have := measurable_uncurry_of_continuous_of_measurable (u := fun (x : ℂ) (h : DistC) =>
      h (testAffinePull r x φ)) (fun h => (map_continuous h).comp
        (continuous_testAffinePull_center hr φ))
    (fun x => measurable_distOn_apply _)
  exact this.comp measurable_swap

/-- `(h, z₀) ↦ h_r(z₀)` is measurable. -/
theorem measurable_radAvg (r : ℝ) : Measurable fun p : DistC × ℂ => radAvg r p.1 p.2 := by
  have : (fun p : DistC × ℂ => radAvg r p.1 p.2) =
      (fun q : DistC × ℝ × ℂ => circleAvg q.1 q.2.1 q.2.2) ∘
        fun p : DistC × ℂ => (p.1, (r, p.2)) := rfl
  rw [this]
  exact measurable_circleAvg.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

/-- `(h, z₀) ↦ h(r · + z₀) − h_r(z₀)` is measurable. -/
theorem measurable_caseNormalized (r : ℝ) :
    Measurable fun p : DistC × ℂ => caseNormalized r p.1 p.2 :=
  DFGPS.L219.measurable_addConst_of (measurable_affineComp_center r) (measurable_radAvg r).neg

/-- The general-radius curve map is measurable in `(z₀, c)`. -/
theorem measurable_caseCurve (r : ℝ) :
    Measurable fun p : ℂ × C(ℝ, ℂ) => caseCurve r p.1 p.2 := by
  let Ψ : C(ℝ, ℂ) × ℂ → C(ℝ, ℂ) := fun q =>
    ⟨fun t => (r⁻¹ : ℂ) * (q.1 (r ^ 2 * t) - q.2), by fun_prop⟩
  have hΨ : Continuous Ψ := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have hev : Continuous fun x : (C(ℝ, ℂ) × ℂ) × ℝ => x.1.1 (r ^ 2 * x.2) :=
      continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
        (continuous_const.mul continuous_snd))
    exact continuous_const.mul (hev.sub (continuous_snd.comp continuous_fst))
  have e : (fun p : ℂ × C(ℝ, ℂ) => caseCurve r p.1 p.2) =
      Ψ ∘ (fun q : C(ℝ, ℂ) × ℂ => (GMS4b.curveShift q.1 (GMS4b.hitTime q.1 q.2), q.2)) ∘
        Prod.swap := by
    funext p
    ext t
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, Ψ, ContinuousMap.coe_mk,
      caseCurve_apply r, GMS4b.curveShift, ContinuousMap.comp_apply]
    rfl
  rw [e]
  exact hΨ.measurable.comp ((GMS4b.measurable_shiftAtHit.prodMk
    (measurable_snd)).comp measurable_swap)

end MatedCRTHarmonic.GMSCase
