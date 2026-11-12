/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.MQ.SphereMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.SphereCover
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.ShiftNull
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Thm12Reduce
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux

/-!
# MQ Theorem 1.2 for weak γ-LQG metrics: `MQSphereInter` (task P2-MQ2)

Source: J. Miller, W. Qian, arXiv:1812.03913, `literature/src/1812.03913/lqg_geodesics.tex`,
proof of Theorem 1.2, l. 462–506. MQ's remaining claim (l. 466–467): for fixed `r > 0`, a.s. on
`{r < D_h(x,y)}` the set `∂B_h(x,r) ∩ ∂B_h(y,s)` has at most one point.

Argument (MQ's, with decision D-C4's unconditional repair of MQ l. 502–506):
1. two distinct points `w ≠ w'` of the intersection give a geodesic `x → w → y` that misses a
   rational ball around `w'` (`exists_rat_bump`; MQ l. 476–480);
2. for the bump `φ` of that ball (`mqBump`, `φ ≥ 0`, `φ = 1` near `w'`) the field is in the
   tie event `sphereBad` (MQ l. 496–502: `φ` vanishes along one geodesic and equals `1` where the
   other one passes);
3. a.s. the tie event fails for each of the countably many rational bumps:
   along the shift `h + aφ`, `a ∈ [0,1]`, it holds for at most one `a`
   (`shift_set_subsingleton`, MQ l. 503–505 "strictly increasing in `α`"), so by Fubini over
   `A` uniform and the Cameron–Martin theorem (`measure_pair0_eq_zero_of_shift_null`,
   MQ l. 505–506) it has probability `0` for the field normalized by `⟨h, ρ₀⟩ = 0`
   (`mqNorm`, MQ l. 486), and Weyl scaling by constants transfers this to `h`.

Deviation (DV-MQ2, own simplification of MQ l. 469–497): MQ separates the two geodesics by
balls `B(x_i, ε/2)`, `B(x_j, ε/2)` of an `ε/2`-net of `∂B_h(x,r)` on the event `E(R,ε,δ)` and
compares the quantities `X_i, X_j`; we compare the two geodesics directly through
`D_{h+φ}(x,y) ≤ D_h(x,y)` (one geodesic avoids `supp φ`) and "a point of `B̄(q,ρ)` lies on a
geodesic" (the other one crosses `{φ = 1}`), which needs neither `E(R,ε,δ)`, nor the net, nor
the radii `u`, nor the locality of metric balls. The probabilistic core (bump, monotonicity in
`A`, `A` uniform, absolute continuity) is MQ's.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.MQ

open Blueprint

section Prob

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- **MQ l. 505–506 for the normalized field.** If a.s. the set of `a ∈ [0,1]` with
`recenter (h + aφ) ∈ S` is Lebesgue-null, then `P[recenter h ∈ S] = 0`. -/
theorem measure_recenter_eq_zero_of_shift_null (hh : IsWholePlaneGFF h P) {ρ₀ : TestC}
    (hρ₀ : ∫ x, ρ₀ x = 1) (φ : TestC) {S : Set DistC} (hS : MeasurableSet S)
    (hnull : ∀ᵐ ω ∂P, volume {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧
      GFFLaw.recenter ρ₀ (addFun (h ω) (testCont (a • φ))) ∈ S} = 0) :
    P {ω | GFFLaw.recenter ρ₀ (h ω) ∈ S} = 0 := by
  obtain ⟨T, hT, hTS⟩ := GFFLaw.measurable_recenter_sigma0 hρ₀ hS
  have key : ∀ g, GFFLaw.recenter ρ₀ g ∈ S ↔ pair0 g ∈ T := fun g => by
    rw [← mem_preimage (f := GFFLaw.recenter ρ₀), ← hTS]
    exact Iff.rfl
  have e1 : {ω | GFFLaw.recenter ρ₀ (h ω) ∈ S} = {ω | pair0 (h ω) ∈ T} := by
    ext ω; exact key _
  rw [e1]
  refine measure_pair0_eq_zero_of_shift_null hh φ hT ?_
  filter_upwards [hnull] with ω hω
  simpa only [key] using hω

omit [IsProbabilityMeasure P] in
lemma isGFFPlusCont_addFun_mq (hh : IsWholePlaneGFF h P) (φ : TestC) :
    IsGFFPlusCont (fun ω => addFun (h ω) (testCont φ)) P :=
  ⟨(measurable_addFun_left _).comp hh.measurable, fun _ => testCont φ, measurable_const,
    by simpa [addFun] using hh⟩

omit [IsProbabilityMeasure P] in
lemma isWholePlaneGFF_recenter (hh : IsWholePlaneGFF h P) (ρ₀ : TestC) :
    IsWholePlaneGFF (fun ω => GFFLaw.recenter ρ₀ (h ω)) P :=
  hh.addConst ((GFFInv.measurable_pair ρ₀).comp hh.measurable).neg

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- The tie event has probability `0` for the field normalized by `⟨h, mqNorm q ρ⟩ = 0`
(MQ l. 503–506 with D-C4). -/
theorem measure_recenter_sphereBad (hγ : 0 < γ) (hD : IsWeakLQGMetric γ D c)
    (hh : IsWholePlaneGFF h P) (x y q : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    P {ω | GFFLaw.recenter (mqNorm q ρ) (h ω) ∈ sphereBad D x y q ρ (mqBump q ρ hρ)} = 0 := by
  set φ := mqBump q ρ hρ
  set ρ₀ := mqNorm q ρ
  have hĥ := isWholePlaneGFF_recenter hh ρ₀
  refine measure_recenter_eq_zero_of_shift_null hh (integral_mqNorm q ρ) φ
    (measurableSet_sphereBad hD.measurable x y q ρ φ) ?_
  filter_upwards [hD.weyl P _ (GM.Tight.isGFFPlusCont_of_wp hĥ)] with ω hW
  set g := GFFLaw.recenter ρ₀ (h ω)
  by_cases hx : 3 * ρ ≤ ‖x - q‖
  swap
  · refine measure_mono_null (fun a ha => ?_) measure_empty
    exact hx ha.2.1
  have hWa : ∀ (a : ℝ) (z w : ℂ), weylScale (xiGamma γ) (a • testCont φ) (D g) z w =
      ENNReal.ofReal ((D (addFun g (testCont (a • φ)))).1 (z, w)) := fun a z w => by
    rw [← testCont_smul]; exact hW _ z w
  refine measure_mono_null ?_ (Set.Subsingleton.measure_zero
    (shift_set_subsingleton (GM.xiGamma_pos hγ) (D g)
      (fun a => D (addFun g (testCont (a • φ)))) (testCont φ) (mqBump_nonneg q ρ hρ) hρ
      (fun z hz => mqBump_eq_one hρ hz) (by linarith) hWa (y := y)) volume)
  rintro a ⟨ha01, hab⟩
  rw [recenter_addFun (mqNorm_mul_mqBump hρ)] at hab
  obtain ⟨-, h1, h2⟩ := hab
  refine ⟨ha01, ?_, h2⟩
  rwa [addFun_addFun_mq, testCont_smul_add_one] at h1

/-- The tie event a.s. fails for `h` itself (Weyl scaling by the constant `⟨h, ρ₀⟩`). -/
theorem ae_notMem_sphereBad (hγ : 0 < γ) (hD : IsWeakLQGMetric γ D c)
    (hh : IsWholePlaneGFF h P) (x y q : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, h ω ∉ sphereBad D x y q ρ (mqBump q ρ hρ) := by
  set φ := mqBump q ρ hρ
  set ρ₀ := mqNorm q ρ
  have hĥ := isWholePlaneGFF_recenter hh ρ₀
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_recenter_sphereBad hγ hD hh x y q hρ),
    hD.ae_dist_addConst (GM.Tight.isGFFPlusCont_of_wp hĥ),
    hD.ae_dist_addConst (isGFFPlusCont_addFun_mq hĥ φ)] with ω h1 h2 h3 hbad
  apply h1
  set g := GFFLaw.recenter ρ₀ (h ω)
  set k := h ω ρ₀
  have hg : h ω = addConst g k := by
    simp only [g, k, GFFLaw.recenter, GFFLaw.addConst_addConst, neg_add_cancel,
      GFFLaw.addConst_zero']
  rw [hg] at hbad
  obtain ⟨hx, hA, w, hw, hT⟩ := hbad
  rw [addFun_addConst_mq, h3, h2] at hA
  rw [h2, h2, h2] at hT
  have he := Real.exp_pos (xiGamma γ * k)
  refine ⟨hx, le_of_mul_le_mul_left hA he, w, hw, le_of_mul_le_mul_left ?_ he⟩
  linarith

end Prob

/-- **MQ's remaining claim (l. 466–467) for weak γ-LQG metrics**, proved following MQ
l. 469–506 (with D-C4 and DV-MQ2). Existence of geodesics: GM.S1.1 (`gm_S1_1`, DFGPS L3.8). -/
theorem mqSphereInter (h38 : DFGPSLem3_8) : MQSphereInter := by
  intro γ hγ hγ2 D c hD Ω _ P _ h hh x y _ r _
  have hall : ∀ᵐ ω ∂P, ∀ i : ℚ × ℚ × ℚ, ∀ hρ : (0 : ℝ) < i.2.2,
      h ω ∉ sphereBad D x y ⟨i.1, i.2.1⟩ i.2.2 (mqBump ⟨i.1, i.2.1⟩ i.2.2 hρ) := by
    rw [ae_all_iff]
    intro i
    by_cases hρ : (0 : ℝ) < i.2.2
    · filter_upwards [ae_notMem_sphereBad hγ hD hh x y ⟨i.1, i.2.1⟩ hρ] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h' => absurd h' hρ
  filter_upwards [hall, GM.gm_S1_1 h38 hγ hγ2 hD P h hh,
    hD.weyl P h (GM.Tight.isGFFPlusCont_of_wp hh)] with ω hall hex hW
  intro _ w w' hw1 hw2 hw1' hw2'
  by_contra hne
  obtain ⟨η₁, η₂, a, b, ρ, hη₁, hη₂, hρ, hq, hfar⟩ :=
    exists_rat_bump hex hne (by linarith) (by linarith) (by rw [hw1, hw1'])
  apply hall (a, b, ρ) hρ
  set φ := mqBump ⟨a, b⟩ ρ hρ
  have hz₁ : ∀ t, testCont φ (η₁ t) = 0 := fun t => mqBump_eq_zero hρ (hfar t).1
  have hz₂ : ∀ t, testCont φ (η₂ t) = 0 := fun t => mqBump_eq_zero hρ (hfar t).2
  have e1 := weylScale_le_of_isGeod01 (ξ := xiGamma γ) hη₁ hz₁
  have e2 := weylScale_le_of_isGeod01 (ξ := xiGamma γ) hη₂ hz₂
  rw [hW, ENNReal.ofReal_le_ofReal_iff ((D (h ω)).nonneg _ _)] at e1 e2
  refine ⟨?_, ?_, w', mem_closedBall.2 (by rw [dist_eq_norm]; exact hq), by linarith⟩
  · have := (hfar 0).1
    rwa [hη₁.1] at this
  · calc (D (addFun (h ω) (testCont φ))).1 (x, y)
        ≤ (D (addFun (h ω) (testCont φ))).1 (x, w) + (D (addFun (h ω) (testCont φ))).1 (w, y) :=
          (D _).2.triangle x w y
      _ ≤ (D (h ω)).1 (x, w) + (D (h ω)).1 (w, y) := add_le_add e1 e2
      _ = (D (h ω)).1 (x, y) := by linarith

/-- **MQ Theorem 1.2 for weak γ-LQG metrics** (`Blueprint.MQThm1_2Weak`), from DFGPS L3.8. -/
theorem mqThm1_2Weak (h38 : DFGPSLem3_8) : MQThm1_2Weak :=
  mqThm1_2Weak_of_sphereInter h38 (mqSphereInter h38)

end LQGMetric.MQ
