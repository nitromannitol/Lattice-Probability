/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperScale at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperPath
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36LowerR
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputsDG2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.21 at a scaled box (upper half of DFGPS Lemma 3.6)

Decision D52: the boundary layer of DFGPS Lemma 3.6 (T:1645–1650) is covered by boxes
`c + r B(a, R)`; in each, DG Proposition 3.21 (`Blueprint.DGProp3_21`) applied to the rescaled
field `h(c + r·) − h_r(c)` (a normalized whole-plane GFF, `CircleAvg.map_affine_sub_circleAvg`,
DFGPS T:1638 "scale and translation invariance of the law of `h`, modulo additive constant")
gives a DG path from `c + r b` to `c + r a` in `c + r B̄(a, R)` of LFPP length
`≤ 2 r e^{ξ h_r(c)} (δ/r)^{λ − ζ}`, except on an event of probability `≤ C (δ/r)^p`
(`box_bound`). The constants are uniform in `r, c` (D52 reading of DG Prop 3.21).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

open Blueprint
open LQGDimension (IsGFFCircleAverage lfppLength)

/-- `h(r₂ · + z₂)(r₁ · + z₁) = h(r₂ r₁ · + r₂ z₁ + z₂)` (copy of `GM.affineComp_comp`,
`Papers/GM/S1/Dilate.lean`) -/
theorem affComp_comp {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (z₁ z₂ : ℂ) (h : DistC) :
    affineComp r₁ z₁ (affineComp r₂ z₂ h) = affineComp (r₂ * r₁) ((r₂ : ℂ) * z₁ + z₂) h := by
  refine DFunLike.ext _ _ fun φ => ?_
  have e : testAffinePull r₂ z₂ (testAffinePull r₁ z₁ φ) =
      testAffinePull (r₂ * r₁) ((r₂ : ℂ) * z₁ + z₂) φ :=
    TestFunction.ext fun x => by
      rw [testAffinePull_apply _ _ h₂, testAffinePull_apply _ _ h₁,
        testAffinePull_apply _ _ (mul_ne_zero h₂ h₁)]
      congr 1
      have : (r₁ : ℂ) ≠ 0 := by exact_mod_cast h₁
      have : (r₂ : ℂ) ≠ 0 := by exact_mod_cast h₂
      push_cast
      field_simp
      ring
  rw [GFFInv.affineComp_apply, GFFInv.affineComp_apply, GFFInv.affineComp_apply, e, mul_pow]
  ring

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- the rescaled field `h(r · + c) − h_r(c)` is a normalized whole-plane GFF -/
theorem isNormalizedWPGFF_rescale (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (c : ℂ) :
    IsNormalizedWPGFF (fun ω => addConst (affineComp r c (h ω)) (-circleAvg (h ω) r c)) P := by
  have hg : IsWholePlaneGFF (fun ω => affineComp r c (h ω)) P := hh.1.affineComp hr c
  have hcm : Measurable fun ω => circleAvg (h ω) r c :=
    (measurable_circleAvg_left r c).comp hh.1.measurable
  refine ⟨hg.addConst hcm.neg, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst hg 0 one_pos,
    CircleAvg.ae_circleAvg_affineComp hh.1 hr c] with ω h1 h2
  rw [h1, h2]; ring

/-- pathwise identification of the circle-average versions of `h(r · + c) − h_r(c)` and `h` -/
theorem ae_rescale_eq (hh : IsNormalizedWPGFF h P) {H H' : ℝ → ℂ → Ω → ℝ}
    (hH : IsGFFCircleAverage H P)
    (hHae : ∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z)
    {r : ℝ} (hr : 0 < r) (c : ℂ) (hH' : IsGFFCircleAverage H' P)
    (hH'ae : ∀ ρ, 0 < ρ → ∀ z, (fun ω => H' ρ z ω) =ᵐ[P]
      fun ω => circleAvg (addConst (affineComp r c (h ω)) (-circleAvg (h ω) r c)) ρ z)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∀ x, H' ρ x ω = H (r * ρ) ((r : ℂ) * x + c) ω - H r c ω := by
  have hg : IsWholePlaneGFF (fun ω => affineComp r c (h ω)) P := hh.1.affineComp hr c
  have hpt : ∀ x, ∀ᵐ ω ∂P, H' ρ x ω = H (r * ρ) ((r : ℂ) * x + c) ω - H r c ω := fun x => by
    filter_upwards [hH'ae ρ hρ x, CircleAvg.ae_circleAvg_addConst hg x hρ,
      CircleAvg.ae_circleAvg_affineComp hg hρ x,
      CircleAvg.ae_circleAvg_affineComp hh.1 (mul_pos hr hρ) ((r : ℂ) * x + c),
      hHae (r * ρ) (mul_pos hr hρ) ((r : ℂ) * x + c), hHae r hr c] with ω h1 h2 h3 h4 h5 h6
    rw [h1, h2, ← h3, affComp_comp hρ.ne' hr.ne', h4, h5, h6]
    ring
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hall : ∀ᵐ ω ∂P, ∀ x ∈ s, H' ρ x ω = H (r * ρ) ((r : ℂ) * x + c) ω - H r c ω :=
    (ae_ball_iff hsc).2 fun x _ => hpt x
  filter_upwards [hall] with ω hω
  intro x
  have hc1 : Continuous fun x => H' ρ x ω := hH'.continuous ρ hρ ω
  have hc2 : Continuous fun x => H (r * ρ) ((r : ℂ) * x + c) ω - H r c ω :=
    ((hH.continuous (r * ρ) (mul_pos hr hρ) ω).comp
      ((continuous_const.mul continuous_id).add continuous_const)).sub continuous_const
  exact congrFun (Continuous.ext_on hsd hc1 hc2 hω) x

/-- the affine image of a DG path -/
lemma isDGPath_affine {T : Set ℂ} {z w : ℂ} {q : ℝ → ℂ} (hq : DG.IsDGPath T z w q) (r : ℝ)
    (c : ℂ) : DG.IsDGPath ((fun x => (r : ℂ) * x + c) '' T) ((r : ℂ) * z + c) ((r : ℂ) * w + c)
      (fun t => (r : ℂ) * q t + c) := by
  obtain ⟨k, t, h1, h2, h3, h4⟩ := hq.piecewise_contDiff
  refine ⟨by simp [hq.source], by simp [hq.target], fun t ht => ⟨q t, hq.mapsTo ht, rfl⟩,
    (continuousOn_const.mul hq.continuousOn).add continuousOn_const,
    ⟨k, t, h1, h2, h3, fun i => (contDiffOn_const.mul (h4 i)).add contDiffOn_const⟩⟩

/-- LFPP length of the affine image of a path -/
lemma lfppLength_affine {r : ℝ} (hr : 0 < r) (c : ℂ) (ξ a : ℝ) {Φ φ : ℂ → ℝ}
    (hφ : ∀ x, Φ ((r : ℂ) * x + c) = φ x + a) (q : ℝ → ℂ) :
    lfppLength ξ Φ (fun t => (r : ℂ) * q t + c) = r * Real.exp (ξ * a) * lfppLength ξ φ q := by
  unfold lfppLength
  have hd : ∀ t, deriv (fun t => (r : ℂ) * q t + c) t = (r : ℂ) * deriv q t := fun t => by
    rw [deriv_add_const, deriv_const_mul_field']
  simp_rw [hd, hφ]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext t
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, mul_add, Real.exp_add]
  ring

/-- the segment from `b` to `a` is a DG path in `B̄(a, R)` -/
lemma isDGPath_segment_ball {a b : ℂ} {R : ℝ} (hab : ‖b - a‖ ≤ R) :
    DG.IsDGPath (Metric.closedBall a R) b a (fun t => b + (t : ℂ) * (a - b)) := by
  refine ⟨by simp, by simp, fun t ht => ?_, by fun_prop, ⟨1, ![0, 1], ?_, rfl, rfl, ?_⟩⟩
  · have hb : b ∈ Metric.closedBall a R := by rwa [Metric.mem_closedBall, dist_eq_norm]
    have ha : a ∈ Metric.closedBall a R := Metric.mem_closedBall_self ((norm_nonneg _).trans hab)
    have := (convex_closedBall a R).add_smul_sub_mem hb ha ht
    rwa [Complex.real_smul] at this
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    exact (contDiff_const.add ((Complex.ofRealCLM.contDiff).mul contDiff_const)).contDiffOn

/-- **DG Prop 3.21 at the box `c + r B(a, R)`.** -/
theorem box_bound (hP : DGProp3_21) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (a b : ℂ) {R : ℝ}
    (hab : ‖b - a‖ < R) {ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) 1) :
    ∃ p C ρ₀ : ℝ, 0 < p ∧ 0 < ρ₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      ∀ H : ℝ → ℂ → Ω → ℝ, IsGFFCircleAverage H P →
      (∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P] fun ω => circleAvg (h ω) r z) →
      ∀ r : ℝ, 0 < r → ∀ c : ℂ, ∀ δ : ℝ, 0 < δ → δ / r < ρ₀ →
        P {ω | ¬ ∃ q : ℝ → ℂ, DG.IsDGPath ((fun x => (r : ℂ) * x + c) '' Metric.closedBall a R)
          ((r : ℂ) * b + c) ((r : ℂ) * a + c) q ∧
          lfppLength (xiGamma γ) (fun x => H δ x ω) q ≤
            2 * r * Real.exp (xiGamma γ * H r c ω) * (δ / r) ^ (DG.dgLambda γ - ζ)} ≤
          ENNReal.ofReal (C * (δ / r) ^ p) := by
  have hR : 0 < R := (norm_nonneg _).trans_lt hab
  have hK : ({a, b} : Set ℂ) ⊆ Metric.ball a R := by
    intro x hx
    rcases hx with rfl | rfl
    · exact Metric.mem_ball_self hR
    · rwa [Metric.mem_ball, dist_eq_norm]
  obtain ⟨p, C, ρ₀, hp, hρ₀, hbd⟩ := hP γ hγ0 hγ2 (Metric.ball a R) {a, b} Metric.isOpen_ball
    (Metric.isConnected_ball hR) (Set.toFinite _).isCompact hK ζ hζ
  refine ⟨p, C, ρ₀, hp, hρ₀, ?_⟩
  intro Ω _ P _ h hh H hH hHae r hr c δ hδ hρ
  set ξ := xiGamma γ with hξ
  have hh' := isNormalizedWPGFF_rescale hh hr c
  obtain ⟨H', hH', -, hH'ae⟩ := CircleAvg.exists_isGFFCircleAverage_normalized hh'
  have hρ0 : 0 < δ / r := div_pos hδ hr
  have hid := ae_rescale_eq hh hH hHae hr c hH' hH'ae hρ0
  have hF := hbd P H' hH' (δ / r) ⟨hρ0, hρ⟩
  set N := {ω | ¬ ∀ x, H' (δ / r) x ω = H (r * (δ / r)) ((r : ℂ) * x + c) ω - H r c ω}
  have hN : P N = 0 := by rw [ae_iff] at hid; exact hid
  set F := {ω | ¬ DG.dgDiam ξ (fun x => H' (δ / r) x ω) (Metric.ball a R) {a, b} ≤
    ENNReal.ofReal ((δ / r) ^ (DG.dgLambda γ - ζ))} with hFdef
  refine (measure_mono ?_).trans ((measure_union_le F N).trans ?_)
  · intro ω hω
    by_contra hc
    simp only [mem_union, not_or] at hc
    obtain ⟨hdiam, hω'⟩ := hc
    simp only [hFdef, mem_setOf_eq, not_not] at hdiam
    simp only [N, mem_setOf_eq, not_not] at hω'
    apply hω
    set M := (δ / r) ^ (DG.dgLambda γ - ζ) with hM
    have hM0 : 0 < M := Real.rpow_pos_of_pos hρ0 _
    have hrd : r * (δ / r) = δ := by field_simp
    rw [hrd] at hω'
    -- the DG distance from `b` to `a` in `B̄(a, R)` is `≤ M`
    have hle : DG.dgLFPP ξ (fun x => H' (δ / r) x ω) (closure (Metric.ball a R)) b a ≤ M := by
      have h1 : ENNReal.ofReal (DG.dgLFPP ξ (fun x => H' (δ / r) x ω)
          (closure (Metric.ball a R)) b a) ≤ ENNReal.ofReal M := by
        refine le_trans ?_ hdiam
        unfold DG.dgDiam
        exact le_iSup₂_of_le b (by simp) (le_iSup₂_of_le a (by simp) le_rfl)
      exact (ENNReal.ofReal_le_ofReal_iff hM0.le).1 h1
    rw [closure_ball a hR.ne'] at hle
    have : Nonempty {q : ℝ → ℂ // DG.IsDGPath (Metric.closedBall a R) b a q} :=
      ⟨⟨_, isDGPath_segment_ball hab.le⟩⟩
    obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt (lt_of_le_of_lt hle (by linarith : M < 2 * M))
    refine ⟨_, isDGPath_affine q.2 r c, ?_⟩
    rw [lfppLength_affine hr c ξ (H r c ω) (φ := fun x => H' (δ / r) x ω)
      (fun x => by rw [hω' x]; ring)]
    have hexp : 0 < r * Real.exp (ξ * H r c ω) := by positivity
    calc r * Real.exp (ξ * H r c ω) * lfppLength ξ (fun x => H' (δ / r) x ω) q.1
        ≤ r * Real.exp (ξ * H r c ω) * (2 * M) := by gcongr
      _ = _ := by ring
  · rw [hN, add_zero]; exact hF

end LQGMetric.DFGPS.L36
