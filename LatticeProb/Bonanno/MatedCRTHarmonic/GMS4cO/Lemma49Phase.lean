/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.Lemma49Phase at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.IGRecentrePhase
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OPhase

/-!
# [18] Lemma 4.9 with the IG phase among the conditioning variables

The frozen IG field is `hIG₀ + U`, and the far-pair argument conditions on the *physical* circle averages
`(h₀,r(z), hIG₀,r(z) + U)`. This file proves (4.24)–(4.25) conditionally on the finer triple
`(h₀,r(z), (hIG₀,r(z), U))`, which implies the bound for every coarser observation (in particular the physical pair).

Given the conditioning triple, the recentred excursion data is `F(h''|_{V^δ}, U')` with `U' = (hIG₀,r(z) + U) mod 2πχ`
and `h''|_{V^δ}` an independent copy of the local IG field (`IGRecentrePhase`). Freezing the triple therefore leaves
The expectation `Ψ(s, u) = E[G(s, (h₀|_W, F(hIG₀|_{V^δ}, u)))]` at a *fixed* phase `u`. This is bounded for almost
every `u` because the 0-cone root observable is independent of `U` (the
`GMS4O.p48o_indepFun_rotInvariant_zeroConeCurve_phase`: the observable is invariant under rotations of the curve, and
The phase rotates the curve), so the conditional expectation of `obs_s(η₀)` given `U` is its mean, at most the
`ε`-uniform moment of [18] Theorem 4.4.

Main results: `L43O.phase_slice_ae_le` (the fixed-phase slice bound), `L43O.lemma49_core_phase`,
`L43O.lemma49_zeroCone_uStar_phase` ((4.25)), `L43O.lemma49_zeroCone_DA_phase` ((4.24)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.L43O

attribute [local instance] Classical.propDecidable

/-! ## The masked observables are Borel and rotation invariant -/

/-- In `ℂ`, `B̄_ρ(x) ⊆ B̄_θ(0)` iff `ρ + |x| ≤ θ` (for `ρ ≥ 0`). -/
theorem closedBall_subset_closedBall_zero_iff {x : ℂ} {ρ θ : ℝ} (hρ : 0 ≤ ρ) :
    closedBall x ρ ⊆ closedBall (0 : ℂ) θ ↔ ρ + ‖x‖ ≤ θ := by
  constructor
  · intro h
    by_cases hx : x = 0
    · have hmem : ((ρ : ℝ) : ℂ) ∈ closedBall x ρ := by
        rw [hx, mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hρ]
      have := h hmem
      rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hρ] at this
      rw [hx, norm_zero, add_zero]
      exact this
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
      set w : ℂ := x + ((ρ / ‖x‖ : ℝ) : ℂ) * x with hw
      have hwx : ‖w - x‖ = ρ := by
        rw [hw, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hρ hxn.le), div_mul_cancel₀ _ hxn.ne']
      have hwn : ‖w‖ = ρ + ‖x‖ := by
        have : w = ((1 + ρ / ‖x‖ : ℝ) : ℂ) * x := by
          rw [hw]
          push_cast
          ring
        rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), add_mul, one_mul, div_mul_cancel₀ _ hxn.ne', add_comm]
      have hmem : w ∈ closedBall x ρ := by
        rw [mem_closedBall, dist_eq_norm, hwx]
      have := h hmem
      rw [mem_closedBall, dist_zero_right, hwn] at this
      exact this
  · intro h
    refine closedBall_subset_closedBall' ?_
    rwa [dist_zero_right]

theorem locBall_subset_closedBall_iff (s θ : ℝ) (c : ℝ → ℂ) :
    GMS4b.locBall s c 0 ⊆ closedBall (0 : ℂ) θ ↔
      4 * diam (GMS4b.locWindow s c 0) + ‖c 0‖ ≤ θ := by
  rw [GMS4b.locBall, closedBall_subset_closedBall_zero_iff (by positivity)]

theorem measurableSet_locBall_subset (s θ : ℝ) :
    MeasurableSet {c : C(ℝ, ℂ) | GMS4b.locBall s c 0 ⊆ closedBall (0 : ℂ) θ} := by
  simp_rw [locBall_subset_closedBall_iff]
  refine measurableSet_le ?_ measurable_const
  exact ((GMS4b.continuous_diam_window s 0).measurable.const_mul 4).add
    ((continuous_norm.comp (continuous_eval_const 0)).measurable)

theorem measurable_maskedLocUStar (θ : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Measurable fun c : C(ℝ, ℂ) => maskedLocUStar θ s c := by
  unfold maskedLocUStar
  exact Measurable.ite (measurableSet_locBall_subset s θ) (GMS4b.measurable_locUStar hs 0)
    measurable_const

theorem measurable_maskedLocDA (θ s : ℝ) :
    Measurable fun c : C(ℝ, ℂ) => maskedLocDA θ s c := by
  unfold maskedLocDA
  exact Measurable.ite (measurableSet_locBall_subset s θ) (GMS4b.measurable_locDA s 0)
    measurable_const

theorem rotCurve_eq_simC (θ : ℝ) (c : C(ℝ, ℂ)) :
    (IGLaw.rotCurve θ c : ℝ → ℂ) =
      GMS4b.simC (Complex.exp (θ * Complex.I)) 0 (Complex.exp_ne_zero _) ∘ c := by
  funext t
  simp [IGLaw.rotCurve]

theorem locBall_rotCurve_subset_iff (s θ φ : ℝ) (c : C(ℝ, ℂ)) :
    GMS4b.locBall s (IGLaw.rotCurve φ c) 0 ⊆ closedBall (0 : ℂ) θ ↔
      GMS4b.locBall s c 0 ⊆ closedBall (0 : ℂ) θ := by
  rw [locBall_subset_closedBall_iff, locBall_subset_closedBall_iff, rotCurve_eq_simC,
    GMS4b.locWindow_simC, GMS4b.diam_simC_image]
  simp [Complex.norm_exp_ofReal_mul_I]

theorem maskedLocUStar_rotCurve (θ s φ : ℝ) (c : C(ℝ, ℂ)) :
    maskedLocUStar θ s (IGLaw.rotCurve φ c) = maskedLocUStar θ s c := by
  unfold maskedLocUStar
  rw [show (GMS4b.locUStar s (IGLaw.rotCurve φ c) 0) = GMS4b.locUStar s c 0 by
    rw [rotCurve_eq_simC, GMS4b.locUStar, GMS4b.locUStar, GMS4b.locDA_simC, GMS4b.locDegIn_simC,
      GMS4b.locDegOut_simC]]
  simp only [locBall_rotCurve_subset_iff]

theorem maskedLocDA_rotCurve (θ s φ : ℝ) (c : C(ℝ, ℂ)) :
    maskedLocDA θ s (IGLaw.rotCurve φ c) = maskedLocDA θ s c := by
  unfold maskedLocDA
  rw [show (GMS4b.locDA s (IGLaw.rotCurve φ c) 0) = GMS4b.locDA s c 0 by
    rw [rotCurve_eq_simC, GMS4b.locDA_simC]]
  simp only [locBall_rotCurve_subset_iff]

/-! ## The fixed-phase slice -/

/-- **The fixed-phase slice bound.** Let `O = H(B, F(R, U))` almost surely, with `(B, R) ⟂ U` and `O ⟂ U`, and
`E[O] ≤ C`. Then for almost every phase value `u`, `E[H(B, F(R, u))] ≤ C`. -/
theorem phase_slice_ae_le {Ω E₁ E₂ E₃ : Type*} [MeasurableSpace Ω] [MeasurableSpace E₁]
    [MeasurableSpace E₂] [MeasurableSpace E₃] {P : Measure Ω} [IsProbabilityMeasure P]
    {Bv : Ω → E₁} {Rv : Ω → E₂} {Uv : Ω → ℝ} {O : Ω → ℝ≥0∞}
    (hB : AEMeasurable Bv P) (hR : AEMeasurable Rv P) (hU : AEMeasurable Uv P)
    (hO : AEMeasurable O P) {F : E₂ × ℝ → E₃} (hF : Measurable F) {H : E₁ × E₃ → ℝ≥0∞}
    (hH : Measurable H) (hBRU : IndepFun (fun ω => (Bv ω, Rv ω)) Uv P) (hOU : IndepFun O Uv P)
    (hOH : ∀ᵐ ω ∂P, O ω = H (Bv ω, F (Rv ω, Uv ω))) {C : ℝ≥0∞} (hC : ∫⁻ ω, O ω ∂P ≤ C) :
    ∀ᵐ u ∂(P.map Uv), ∫⁻ ℓ, H (ℓ.1, F (ℓ.2, u)) ∂(P.map fun ω => (Bv ω, Rv ω)) ≤ C := by
  set lBR := P.map fun ω => (Bv ω, Rv ω) with hlBR
  set Ψ : ℝ → ℝ≥0∞ := fun u => ∫⁻ ℓ, H (ℓ.1, F (ℓ.2, u)) ∂lBR with hΨ
  have hJm : Measurable fun y : (E₁ × E₂) × ℝ => H (y.1.1, F (y.1.2, y.2)) :=
    hH.comp ((measurable_fst.comp measurable_fst).prodMk
      (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hΨm : Measurable Ψ := by
    have := hJm.lintegral_prod_left' (μ := lBR)
    exact this
  have hprod : P.map (fun ω => ((Bv ω, Rv ω), Uv ω)) = lBR.prod (P.map Uv) :=
    (indepFun_iff_map_prod_eq_prod_map_map (hB.prodMk hR) hU).1 hBRU
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hΨm fun S hS _ => ?_
  have hSU : AEMeasurable (fun ω => S.indicator (fun _ => (1 : ℝ≥0∞)) (Uv ω)) P :=
    (measurable_const.indicator hS).comp_aemeasurable hU
  have hindS : IndepFun O (fun ω => S.indicator (fun _ => (1 : ℝ≥0∞)) (Uv ω)) P :=
    hOU.comp measurable_id (measurable_const.indicator hS)
  calc ∫⁻ u in S, Ψ u ∂(P.map Uv)
      = ∫⁻ u, S.indicator (fun _ => (1 : ℝ≥0∞)) u * Ψ u ∂(P.map Uv) := by
        rw [← lintegral_indicator hS]
        congr 1
        funext u
        by_cases hu : u ∈ S <;> simp [Set.indicator, hu]
    _ = ∫⁻ u, ∫⁻ ℓ, S.indicator (fun _ => (1 : ℝ≥0∞)) u * H (ℓ.1, F (ℓ.2, u)) ∂lBR
          ∂(P.map Uv) := by
        congr 1
        funext u
        exact (lintegral_const_mul (f := fun ℓ : E₁ × E₂ => H (ℓ.1, F (ℓ.2, u))) _
          (hH.comp (measurable_fst.prodMk
            (hF.comp (measurable_snd.prodMk measurable_const))))).symm
    _ = ∫⁻ y, S.indicator (fun _ => (1 : ℝ≥0∞)) y.2 * H (y.1.1, F (y.1.2, y.2))
          ∂(lBR.prod (P.map Uv)) := by
        exact (lintegral_prod_symm
          (fun y : (E₁ × E₂) × ℝ => S.indicator (fun _ => (1 : ℝ≥0∞)) y.2 *
            H (y.1.1, F (y.1.2, y.2)))
          (((measurable_const.indicator hS).comp measurable_snd).mul hJm).aemeasurable).symm
    _ = ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (Uv ω) * H (Bv ω, F (Rv ω, Uv ω)) ∂P := by
        rw [← hprod]
        exact lintegral_map'
          (f := fun y : (E₁ × E₂) × ℝ => S.indicator (fun _ => (1 : ℝ≥0∞)) y.2 *
            H (y.1.1, F (y.1.2, y.2)))
          (((measurable_const.indicator hS).comp measurable_snd).mul hJm).aemeasurable
          ((hB.prodMk hR).prodMk hU)
    _ = ∫⁻ ω, O ω * S.indicator (fun _ => (1 : ℝ≥0∞)) (Uv ω) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hOH] with ω hω
        rw [hω, mul_comm]
    _ = (∫⁻ ω, O ω ∂P) * ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (Uv ω) ∂P :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hO hSU hindS
    _ ≤ C * (P.map Uv) S := by
        refine mul_le_mul' hC (le_of_eq ?_)
        rw [← lintegral_map' (f := S.indicator (fun _ => (1 : ℝ≥0∞)))
          (measurable_const.indicator hS).aemeasurable hU, lintegral_indicator_const hS, one_mul]
    _ = ∫⁻ u in S, C ∂(P.map Uv) := by rw [setLIntegral_const, mul_comm]

/-! ## The phase-aware core -/

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The phase-aware core of [18] Lemma 4.9 for the 0-cone.** As `lemma49_core`, with the conditioning variable
`(h₀,r(z), (hIG₀,r(z), U))`, for a Borel, rotation-invariant observable. -/
theorem lemma49_core_phase
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {W V : TopologicalSpace.Opens ℂ}
    (hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1) (hVb : Bornology.IsBounded (V : Set ℂ)) {δ : ℝ}
    (hδ : 0 < δ)
    (hVδ : ((GMS4c.thickOpen V δ : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {obs : ℝ → (ℝ → ℂ) → ℝ≥0∞} (hloc : ZeroConeRescaledLocality D obs W V)
    (hobsm : ∀ s : ℝ, 0 < s → Measurable fun c : C(ℝ, ℂ) => obs s c)
    (hobsrot : ∀ (s φ : ℝ) (c : C(ℝ, ℂ)), obs s (IGLaw.rotCurve φ c) = obs s c)
    {p : ℝ} {C : ℝ≥0∞} (hC : ∀ s : ℝ, 0 < s → ∫⁻ ω, obs s (η₀ ω) ^ p ∂P ≤ C)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ ball (0 : ℂ) 1) {ε : ℝ} (hε : 0 < ε)
    {Y : Ω → ℝ≥0∞}
    (hY : ∀ᵐ ω ∂P, Y ω ≤ obs (ε / timeScale γ (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) r)
      (rescaledCurve (η₀ ω) z r (timeScale γ (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) r)) ^ p)
    {A : Set (ℝ × (ℝ × ℝ))} (hA : MeasurableSet A) :
    ∫⁻ ω in (fun ω => (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z,
        (circleAvg (hIG₀ ω) r z, U ω))) ⁻¹' A, Y ω ∂P ≤
      C * P ((fun ω => (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z,
        (circleAvg (hIG₀ ω) r z, U ω))) ⁻¹' A) := by
  have := D.isProbabilityMeasure
  have hRf : Fact (0 < 2 * Real.pi * igChi γ) := ⟨igPeriod_pos hγ⟩
  set R : ℝ := 2 * Real.pi * igChi γ with hRdef
  obtain ⟨G, hGm, hbase, hresc⟩ := hloc
  set h₀ : Ω → Field := zeroConeField γ X₀ B₀ B₀' with hh₀def
  have hh₀ : AEMeasurable h₀ P := GMS4.aemeasurable_prop48ZeroConeField D
  have hhIG : Measurable hIG₀ := D.igField.1.1.measurable
  have hηL : Measurable ηL := D.measurable_curves.1
  have hη₀ : Measurable η₀ := D.measurable_curves.2.2.1
  have hUm : AEMeasurable U P := MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif hRf.out D.igField.2.1
  set W' := GMS4c.thickOpen V δ with hW'def
  have hVW : (V : Set ℂ) ⊆ (W' : Set ℂ) := self_subset_thickening hδ _
  have hVc : ((V : Set ℂ)ᶜ).Nonempty := compl_nonempty_of_subset_ball (hVW.trans hVδ)
  -- the coordinates
  set a1 : Ω → ℝ := fun ω => circleAvg (h₀ ω) r z with ha1def
  set a2 : Ω → ℝ := fun ω => circleAvg (hIG₀ ω) r z with ha2def
  set L1 : Ω → DistOn W := fun ω => restrictTo W (IGLaw.affField r 0 z (h₀ ω)) with hL1def
  set L2 : Ω → ℚ × ℚ → ℝ → ℂ := fun ω => excursionData V (affineReroot z r 0 (ηL ω))
    with hL2def
  set B1 : Ω → DistOn W := fun ω => restrictTo W (h₀ ω) with hB1def
  set Rpp : Ω → DistOn W' := fun ω => restrictTo W' (IGLaw.affField r 0 z (hIG₀ ω)) with hRppdef
  set Rz : Ω → DistOn W' := fun ω => restrictTo W' (hIG₀ ω) with hRzdef
  set U' : Ω → ℝ := fun ω => IGLaw.modRep R (a2 ω + U ω) with hU'def
  have ha1 : AEMeasurable a1 P := (measurable_circleAvg_left r z).comp_aemeasurable hh₀
  have ha2m : Measurable a2 := (measurable_circleAvg_left r z).comp hhIG
  have hL1 : AEMeasurable L1 P :=
    ((measurable_restrictTo W).comp (IGLaw.measurable_affField r 0 z)).comp_aemeasurable hh₀
  have hL2 : AEMeasurable L2 P :=
    ((measurable_excursionData V hVc).comp ((measurable_affineReroot z r 0).comp hηL)).aemeasurable
  have hB1 : AEMeasurable B1 P := (measurable_restrictTo W).comp_aemeasurable hh₀
  have hRppm : Measurable Rpp :=
    (measurable_restrictTo W').comp ((IGLaw.measurable_affField r 0 z).comp hhIG)
  have hRzm : Measurable Rz := (measurable_restrictTo W').comp hhIG
  have hU'm : AEMeasurable U' P :=
    (IGLaw.measurable_modRep R).comp_aemeasurable (ha2m.aemeasurable.add hUm)
  -- the IG phase package and the field side
  obtain ⟨F, hFm, -, hFae, hlawIG, hindIG, hlawR⟩ :=
    igRecentre_phase D V hVb hδ hVδ hr (hzr.trans ball_subset_closedBall)
  have hF := map_circleAvg_restrict_affField_zeroCone D hγ hW hr hzr
  have hlaw1 : P.map L1 = P.map B1 := map_snd_of_map_eq_prod ha1 hL1 hF
  have h1 : IndepFun a1 L1 P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map ha1 hL1, hlaw1]
    exact hF
  -- cross independence
  obtain ⟨Φ, hΦ, -, hroot, -, -⟩ := D.igMap
  have hIGdata : IndepFun h₀ (fun ω => (hIG₀ ω, U ω)) P :=
    GMS4.prop48_zeroCone_indepFun_IGdata D hγ
  have hcurve : IndepFun h₀ (fun ω => ((hIG₀ ω, U ω), ηL ω)) P := by
    have hg : Measurable fun x : Field × ℝ => (x, Φ (IGLaw.igCircleAvgInput x)) :=
      measurable_id.prodMk (hΦ.comp IGLaw.measurable_igCircleAvgInput)
    refine (hIGdata.comp measurable_id hg).congr (ae_of_all _ fun _ => rfl) ?_
    filter_upwards [hroot] with ω hω
    simp only [Function.comp]
    rw [hω]
    rfl
  have hf1 : Measurable fun x : Field =>
      (circleAvg x r z, restrictTo W (IGLaw.affField r 0 z x)) :=
    (measurable_circleAvg_left r z).prodMk
      ((measurable_restrictTo W).comp (IGLaw.measurable_affField r 0 z))
  have hfS : Measurable fun y : (Field × ℝ) × C(ℝ, ℂ) =>
      ((circleAvg y.1.1 r z, y.1.2), excursionData V (affineReroot z r 0 y.2)) :=
    (((measurable_circleAvg_left r z).comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_excursionData V hVc).comp ((measurable_affineReroot z r 0).comp measurable_snd))
  have hfR : Measurable fun y : (Field × ℝ) × C(ℝ, ℂ) =>
      ((circleAvg y.1.1 r z, y.1.2), restrictTo W' (IGLaw.affField r 0 z y.1.1)) :=
    (((measurable_circleAvg_left r z).comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_restrictTo W').comp ((IGLaw.measurable_affField r 0 z).comp
        (measurable_fst.comp measurable_fst)))
  have hcrossS : IndepFun (fun ω => (a1 ω, L1 ω))
      (fun ω => ((a2 ω, U ω), L2 ω)) P := hcurve.comp hf1 hfS
  have hcrossR : IndepFun (fun ω => (a1 ω, L1 ω))
      (fun ω => ((a2 ω, U ω), Rpp ω)) P := hcurve.comp hf1 hfR
  have hcrossB : IndepFun B1 (fun ω => (Rz ω, U ω)) P :=
    hcurve.comp (measurable_restrictTo W)
      (((measurable_restrictTo W').comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst))
  -- replace the excursion data by the frozen-phase factor
  set Fmod : (ℝ × ℝ) × DistOn W' → (ℝ × ℝ) × (ℚ × ℚ → ℝ → ℂ) :=
    fun y => (y.1, F (y.2, IGLaw.modRep R (y.1.1 + y.1.2))) with hFmoddef
  have hFmodm : Measurable Fmod :=
    measurable_fst.prodMk (hFm.comp (measurable_snd.prodMk
      ((IGLaw.measurable_modRep R).comp
        ((measurable_fst.comp measurable_fst).add (measurable_snd.comp measurable_fst)))))
  have hcrossS' : IndepFun (fun ω => (a1 ω, L1 ω))
      (fun ω => Fmod ((a2 ω, U ω), Rpp ω)) P := hcrossR.comp measurable_id hFmodm
  have hS2 : AEMeasurable (fun ω => ((a2 ω, U ω), L2 ω)) P :=
    (ha2m.aemeasurable.prodMk hUm).prodMk hL2
  have hS2' : AEMeasurable (fun ω => Fmod ((a2 ω, U ω), Rpp ω)) P :=
    hFmodm.comp_aemeasurable ((ha2m.aemeasurable.prodMk hUm).prodMk hRppm.aemeasurable)
  have hT1 : AEMeasurable (fun ω => (a1 ω, L1 ω)) P := ha1.prodMk hL1
  have hlaw4 : P.map (fun ω => ((a1 ω, L1 ω), ((a2 ω, U ω), L2 ω))) =
      P.map (fun ω => ((a1 ω, L1 ω), Fmod ((a2 ω, U ω), Rpp ω))) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hT1 hS2).1 hcrossS,
      (indepFun_iff_map_prod_eq_prod_map_map hT1 hS2').1 hcrossS']
    congr 1
  -- the freezing data
  set aP : Ω → ℝ × (ℝ × ℝ) := fun ω => (a1 ω, (a2 ω, U ω)) with haPdef
  set LP : Ω → DistOn W × DistOn W' := fun ω => (L1 ω, Rpp ω) with hLPdef
  have haP : AEMeasurable aP P := ha1.prodMk (ha2m.aemeasurable.prodMk hUm)
  have hLP : AEMeasurable LP P := hL1.prodMk hRppm.aemeasurable
  have hindP : IndepFun aP LP P :=
    indepFun_prod_prod ha1 (ha2m.aemeasurable.prodMk hUm) hL1 hRppm.aemeasurable hcrossR h1 hindIG
  set σ : ℝ → ℝ := fun x => ε / timeScale γ x r with hσdef
  have hσm : Measurable σ := measurable_const.div (measurable_timeScale γ r)
  have hσpos : ∀ x, 0 < σ x := fun x => div_pos hε (timeScale_pos γ x hr)
  set GP : (ℝ × (ℝ × ℝ)) × (DistOn W × DistOn W') → ℝ≥0∞ :=
    fun x => G (σ x.1.1, (x.2.1, F (x.2.2, IGLaw.modRep R (x.1.2.1 + x.1.2.2)))) ^ p with hGPdef
  have hGPm : Measurable GP := by
    refine (hGm.comp (Measurable.prodMk (hσm.comp (measurable_fst.comp measurable_fst)) ?_)).pow_const p
    refine (measurable_fst.comp measurable_snd).prodMk (hFm.comp ?_)
    exact (measurable_snd.comp measurable_snd).prodMk ((IGLaw.measurable_modRep R).comp
      (((measurable_fst.comp measurable_snd).comp measurable_fst).add
        ((measurable_snd.comp measurable_snd).comp measurable_fst)))
  -- the fixed-phase slices
  set Ψ : ℝ → ℝ → ℝ≥0∞ := fun s u =>
    ∫⁻ ℓ, G (s, (ℓ.1, F (ℓ.2, u))) ^ p ∂(P.map fun ω => (B1 ω, Rz ω)) with hΨdef
  have hUR : IndepFun U Rz P := (D.igField.2.2.symm).comp measurable_id (measurable_restrictTo W')
  have hBRU : IndepFun (fun ω => (B1 ω, Rz ω)) U P := by
    have h3 := indepFun_prod_of_indep hUm hRzm.aemeasurable hB1
      (by
        have := hcrossB.symm
        exact this.comp (Measurable.prodMk measurable_snd measurable_fst) measurable_id)
      hUR
    exact (h3.comp measurable_id (Measurable.prodMk measurable_snd measurable_fst)).symm
  have hslice : ∀ s : ℝ, 0 < s → ∀ᵐ u ∂(P.map U), Ψ s u ≤ C := by
    intro s hs
    have hO : AEMeasurable (fun ω => obs s (η₀ ω) ^ p) P :=
      ((hobsm s hs).comp hη₀).pow_const p |>.aemeasurable
    have hOU : IndepFun (fun ω => obs s (η₀ ω) ^ p) U P := by
      have := GMS4O.p48o_indepFun_rotInvariant_zeroConeCurve_phase D hγ
        (Ψ := fun c : C(ℝ, ℂ) => obs s c ^ p) ((hobsm s hs).pow_const p)
        (fun φ c => by simp only [hobsrot s φ c])
      exact this
    refine phase_slice_ae_le hB1 hRzm.aemeasurable hUm hO hFm ((hGm.comp
      (measurable_const.prodMk measurable_id)).pow_const p) hBRU hOU ?_ (hC s hs)
    filter_upwards [hbase, hFae] with ω hb hfa
    rw [hb s hs, ← hfa]
    rfl
  have hlawLP : P.map LP = P.map (fun ω => (B1 ω, Rz ω)) := by
    have hL12 : IndepFun L1 Rpp P := hcrossR.comp measurable_snd measurable_snd
    have hBR : IndepFun B1 Rz P := hcrossB.comp measurable_id measurable_fst
    rw [(indepFun_iff_map_prod_eq_prod_map_map hL1 hRppm.aemeasurable).1 hL12,
      (indepFun_iff_map_prod_eq_prod_map_map hB1 hRzm.aemeasurable).1 hBR, hlaw1, hlawR]
  have hpairU' : P.map (fun ω => (hIG₀ ω, U' ω)) = P.map (fun ω => (hIG₀ ω, U ω)) :=
    IGLaw.map_pair_shift_mod hhIG D.igField.2.1 D.igField.2.2 (V := fun x => circleAvg x r z)
      (measurable_circleAvg_left r z)
  have hlawU' : P.map U' = P.map U := by
    have h2 := congrArg (fun μ : Measure (Field × ℝ) => μ.map Prod.snd) hpairU'
    rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        (hhIG.aemeasurable.prodMk hU'm),
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        (hhIG.aemeasurable.prodMk hUm)] at h2
    exact h2
  have hM : ∀ᵐ x ∂(P.map aP), ∫⁻ ω, GP (x, LP ω) ∂P ≤ C := by
    have hslice_eq : ∀ x : ℝ × (ℝ × ℝ), ∫⁻ ω, GP (x, LP ω) ∂P =
        Ψ (σ x.1) (IGLaw.modRep R (x.2.1 + x.2.2)) := by
      intro x
      have hm : Measurable fun ℓ : DistOn W × DistOn W' =>
          G (σ x.1, (ℓ.1, F (ℓ.2, IGLaw.modRep R (x.2.1 + x.2.2)))) ^ p :=
        (hGm.comp (measurable_const.prodMk (measurable_fst.prodMk
          (hFm.comp (measurable_snd.prodMk measurable_const))))).pow_const p
      calc ∫⁻ ω, GP (x, LP ω) ∂P
          = ∫⁻ ℓ, G (σ x.1, (ℓ.1, F (ℓ.2, IGLaw.modRep R (x.2.1 + x.2.2)))) ^ p ∂(P.map LP) :=
            (lintegral_map' hm.aemeasurable hLP).symm
        _ = _ := by rw [hlawLP]
    have hΨm : Measurable fun y : ℝ × ℝ => Ψ y.1 y.2 := by
      have hJ : Measurable fun q : (ℝ × ℝ) × (DistOn W × DistOn W') =>
          G (q.1.1, (q.2.1, F (q.2.2, q.1.2))) ^ p :=
        (hGm.comp ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_fst.comp measurable_snd).prodMk (hFm.comp
            ((measurable_snd.comp measurable_snd).prodMk
              (measurable_snd.comp measurable_fst)))))).pow_const p
      exact hJ.lintegral_prod_right'
    set N : Set (ℝ × (ℝ × ℝ)) :=
      {x | C < Ψ (σ x.1) (IGLaw.modRep R (x.2.1 + x.2.2))} with hNdef
    have hNm : MeasurableSet N :=
      measurableSet_lt measurable_const (hΨm.comp ((hσm.comp measurable_fst).prodMk
        ((IGLaw.measurable_modRep R).comp
          ((measurable_fst.comp measurable_snd).add (measurable_snd.comp measurable_snd)))))
    have hmapP : P.map aP = (P.map a1).prod (P.map fun ω => (a2 ω, U ω)) :=
      (indepFun_iff_map_prod_eq_prod_map_map ha1 (ha2m.aemeasurable.prodMk hUm)).1
        (hcrossR.comp measurable_fst measurable_fst)
    have hN0 : (P.map aP) N = 0 := by
      rw [hmapP, Measure.prod_apply hNm]
      have hsec0 : ∀ x1 : ℝ, (P.map fun ω => (a2 ω, U ω)) (Prod.mk x1 ⁻¹' N) = 0 := by
        intro x1
        -- the section at `x1` is the event that the reduced phase is bad
        have hS' : MeasurableSet {u : ℝ | C < Ψ (σ x1) u} :=
          measurableSet_lt measurable_const (hΨm.comp (measurable_const.prodMk measurable_id))
        have hsec : (P.map fun ω => (a2 ω, U ω)) (Prod.mk x1 ⁻¹' N) =
            (P.map U') {u | C < Ψ (σ x1) u} := by
          rw [Measure.map_apply_of_aemeasurable (ha2m.aemeasurable.prodMk hUm)
              (measurable_prodMk_left hNm), Measure.map_apply_of_aemeasurable hU'm hS']
          rfl
        rw [hsec, hlawU']
        have h := hslice (σ x1) (hσpos x1)
        rw [ae_iff] at h
        simpa only [not_le] using h
      simp only [hsec0, lintegral_zero]
    refine (ae_iff.2 ?_).mono fun x hx => (hslice_eq x).le.trans (not_lt.1 hx)
    simpa [hNdef] using hN0
  -- domination, law transfer, and freezing
  set Γ : (ℝ × DistOn W) × ((ℝ × ℝ) × (ℚ × ℚ → ℝ → ℂ)) → ℝ≥0∞ :=
    fun t => A.indicator (fun _ => (1 : ℝ≥0∞)) (t.1.1, t.2.1) *
      G (σ t.1.1, (t.1.2, t.2.2)) ^ p with hΓdef
  have hΓm : Measurable Γ :=
    ((measurable_const.indicator hA).comp
      ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))).mul
      ((hGm.comp ((hσm.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_snd.comp measurable_fst).prodMk
          (measurable_snd.comp measurable_snd)))).pow_const p)
  have hpre : NullMeasurableSet (aP ⁻¹' A) P := haP.nullMeasurable hA
  calc ∫⁻ ω in aP ⁻¹' A, Y ω ∂P
      ≤ ∫⁻ ω, Γ ((a1 ω, L1 ω), ((a2 ω, U ω), L2 ω)) ∂P := by
        rw [← lintegral_indicator₀ hpre]
        refine lintegral_mono_ae ?_
        filter_upwards [hY, hresc z r hr hzr] with ω hYω hrω
        by_cases hω : ω ∈ aP ⁻¹' A
        · have hω' : (a1 ω, (a2 ω, U ω)) ∈ A := hω
          rw [Set.indicator_of_mem hω]
          simp only [hΓdef, Set.indicator_of_mem hω', one_mul]
          refine hYω.trans (le_of_eq ?_)
          rw [hrω _ (hσpos _)]
        · rw [Set.indicator_of_notMem hω]
          exact bot_le
    _ = ∫⁻ ω, Γ ((a1 ω, L1 ω), Fmod ((a2 ω, U ω), Rpp ω)) ∂P := by
        rw [← lintegral_map' hΓm.aemeasurable (hT1.prodMk hS2), hlaw4,
          lintegral_map' hΓm.aemeasurable (hT1.prodMk hS2')]
    _ = ∫⁻ ω in aP ⁻¹' A, GP (aP ω, LP ω) ∂P := by
        rw [← lintegral_indicator₀ hpre]
        congr 1
        funext ω
        by_cases hω : ω ∈ aP ⁻¹' A
        · have hω' : (a1 ω, (a2 ω, U ω)) ∈ A := hω
          rw [Set.indicator_of_mem hω]
          simp only [hΓdef, hFmoddef, Set.indicator_of_mem hω', one_mul, hGPdef]
          rfl
        · have hω' : (a1 ω, (a2 ω, U ω)) ∉ A := hω
          rw [Set.indicator_of_notMem hω]
          simp only [hΓdef, hFmoddef, Set.indicator_of_notMem hω', zero_mul]
    _ ≤ C * P (aP ⁻¹' A) := setLIntegral_comp_indep_le_ae haP hLP hindP hGPm hM hA

/-- The phase-aware conditioning triple `(h₀,r(z), (hIG₀,r(z), U))`. -/
def circleTriple (γ : ℝ) (X₀ hIG₀ : Ω → Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ) (r : ℝ)
    (z : ℂ) (ω : Ω) : ℝ × (ℝ × ℝ) :=
  (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z, (circleAvg (hIG₀ ω) r z, U ω))

/-- **[18] (4.25) for the 0-quantum cone, phase-aware** (conditional on the named Lemma 4.3 input): the bound of
`lemma49_zeroCone_uStar` holds conditionally on the triple `(h₀,r(z), (hIG₀,r(z), U))`. -/
theorem lemma49_zeroCone_uStar_phase
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hloc : ZeroConeRescaledLocality D (maskedLocUStar (1 / 2)) fieldRegion excursionRegion)
    {ρ q ζ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hζ : 0 < ζ) (hζq : 4 * ζ < q) :
    epsStar ρ q ζ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ z ∈ ball (0 : ℂ) ρ, ∀ ε ∈ Ioc (0 : ℝ) (epsStar ρ q ζ),
          ∀ A : Set (ℝ × (ℝ × ℝ)), MeasurableSet A →
            ∫⁻ ω in circleTriple γ X₀ hIG₀ B₀ B₀' U (averageRadius q ζ ε) z ⁻¹' A,
              (diamEvent η₀ ε q z).indicator (fun ω => GMS4b.uStar ε (η₀ ω) z) ω ^ p ∂P ≤
            C * P (circleTriple γ X₀ hIG₀ B₀ B₀' U (averageRadius q ζ ε) z ⁻¹' A) := by
  refine ⟨epsStar_mem hρ, fun p hp1 hpK => ?_⟩
  obtain ⟨C, hCtop, hC⟩ := CellScaling.ZeroConeScaling.uStarMoments_uniform D hγ p hp1 hpK
  refine ⟨C, hCtop, fun z hz ε hε A hA => ?_⟩
  obtain ⟨hr, hzr, hθ⟩ := scale_admissible hρ hζ hζq hε.1 hε.2 hz
  have hC' : ∀ s : ℝ, 0 < s → ∫⁻ ω, maskedLocUStar (1 / 2) s (η₀ ω) ^ p ∂P ≤ C := by
    intro s hs
    refine (lintegral_mono fun ω => ?_).trans (hC s hs)
    exact ENNReal.rpow_le_rpow (maskedLocUStar_le _ _ _) (by linarith)
  have hY := ae_indicator_le_rescaled (Xo := fun ε c z => GMS4b.uStar ε c z)
    (obs := maskedLocUStar (1 / 2)) D (fun c z r l ε q hcz hr hl hd hθ =>
      uStar_eq_maskedLocUStar_rescaled hcz hr hl hd hθ) (p := p) (z := z)
    (r := averageRadius q ζ ε) (ε := ε) (q := q) (by linarith) hr hθ
    (P := P) (X₀ := X₀) (B₀ := B₀) (B₀' := B₀')
  exact lemma49_core_phase D hγ (W := fieldRegion) (V := excursionRegion) (fun x hx => hx)
    isBounded_excursionRegion (δ := 1 / 8) (by norm_num) thickOpen_excursionRegion_subset hloc
    (fun s hs => measurable_maskedLocUStar _ hs.le) (fun s φ c => maskedLocUStar_rotCurve _ _ _ _)
    hC' hr hzr hε.1 hY hA

/-- **[18] (4.24) for the 0-quantum cone, phase-aware** (conditional on the named Lemma 4.3 input). -/
theorem lemma49_zeroCone_DA_phase
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hloc : ZeroConeRescaledLocality D (maskedLocDA (1 / 2)) fieldRegion excursionRegion)
    {ρ q ζ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hζ : 0 < ζ) (hζq : 4 * ζ < q) :
    epsStar ρ q ζ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ z ∈ ball (0 : ℂ) ρ, ∀ ε ∈ Ioc (0 : ℝ) (epsStar ρ q ζ),
          ∀ A : Set (ℝ × (ℝ × ℝ)), MeasurableSet A →
            ∫⁻ ω in circleTriple γ X₀ hIG₀ B₀ B₀' U (averageRadius q ζ ε) z ⁻¹' A,
              (diamEvent η₀ ε q z).indicator (fun ω => GMS4b.areaRatio ε (η₀ ω) z) ω ^ p ∂P ≤
            C * P (circleTriple γ X₀ hIG₀ B₀ B₀' U (averageRadius q ζ ε) z ⁻¹' A) := by
  refine ⟨epsStar_mem hρ, fun p hp1 => ?_⟩
  have hmom := (CellScaling.ZeroConeScaling.cellMoments_uniform D hγ).1 p hp1
  refine ⟨∫⁻ ω, GMS4b.locDA 1 (η₀ ω) 0 ^ p ∂P, (hmom 1 one_pos).2, fun z hz ε hε A hA => ?_⟩
  obtain ⟨hr, hzr, hθ⟩ := scale_admissible hρ hζ hζq hε.1 hε.2 hz
  have hC' : ∀ s : ℝ, 0 < s →
      ∫⁻ ω, maskedLocDA (1 / 2) s (η₀ ω) ^ p ∂P ≤ ∫⁻ ω, GMS4b.locDA 1 (η₀ ω) 0 ^ p ∂P := by
    intro s hs
    refine (lintegral_mono fun ω => ?_).trans (le_of_eq (hmom s hs).1)
    exact ENNReal.rpow_le_rpow (maskedLocDA_le _ _ _) (by linarith)
  have hY := ae_indicator_le_rescaled (Xo := fun ε c z => GMS4b.areaRatio ε c z)
    (obs := maskedLocDA (1 / 2)) D (fun c z r l ε q hcz hr hl hd hθ =>
      areaRatio_eq_maskedLocDA_rescaled hcz hr hl hd hθ) (p := p) (z := z)
    (r := averageRadius q ζ ε) (ε := ε) (q := q) (by linarith) hr hθ
    (P := P) (X₀ := X₀) (B₀ := B₀) (B₀' := B₀')
  exact lemma49_core_phase D hγ (W := fieldRegion) (V := excursionRegion) (fun x hx => hx)
    isBounded_excursionRegion (δ := 1 / 8) (by norm_num) thickOpen_excursionRegion_subset hloc
    (fun s _ => measurable_maskedLocDA _ _) (fun s φ c => maskedLocDA_rotCurve _ _ _ _)
    hC' hr hzr hε.1 hY hA

end Bundle

end MatedCRTHarmonic.L43O
