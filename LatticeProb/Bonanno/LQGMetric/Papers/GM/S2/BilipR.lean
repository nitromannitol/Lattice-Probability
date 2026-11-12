/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.BilipR at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Bilip
import LatticeProb.Bonanno.LQGMetric.Papers.LM.LocJoint

/-!
# GM S2.3 and Proposition 2.2 without `Blueprint.LMLem1_4`

Primed copies of `Bilip.gm_S2_3`, `Bilip.ae_le_mul_of_blueprint`, `Bilip.gm_P2_2`: GM apply LM
Lemma 1.4 (l. 905–914) only to metrics `D_h`, `D̃_h` determined by `h` (Axiom II), for which
joint locality is `LM.isJointlyLocal2_of_determined` (Papers/LM/LocJoint.lean) with
`famSigma_internal_le`. Wiring only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

namespace Bilip


variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
variable {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}

/-- **GM S2.3** (l. 905–914) without LM Lemma 1.4. -/
theorem gm_S2_3' (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c')
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) :
    IsXiAdditive2 (xiGamma γ) P h (fun ω => D (h ω)) (fun ω => D' (h ω)) := by
  have jl : ∀ {k : Ω → DistC}, IsWholePlaneGFF k P →
      IsJointlyLocal2 P k (fun ω => D (k ω)) (fun ω => D' (k ω)) := fun {k} hk => by
    have l1 := isLocalMetric_comp hD hk
    have l2 := isLocalMetric_comp hD' hk
    exact LM.isJointlyLocal2_of_determined hk.measurable l1.1 l2.1
      (l1.2.1.and l2.2.1) (famSigma_internal_le hD hk) (famSigma_internal_le hD' hk)
  refine ⟨jl hh, fun z r _ => ?_⟩
  have hk := hh.addConst ((measurable_circleAvg_left r z).comp hh.measurable).neg
  refine isJointlyLocalFam_congr (jl hk).2.2.2 ?_ ?_
  · filter_upwards [hD.ae_internal_addFun_of_eq_const (Tight.isGFFPlusCont_of_wp hh)]
      with ω hω V hV
    funext u v
    rw [show -xiGamma γ * circleAvg (h ω) r z = xiGamma γ * -circleAvg (h ω) r z by ring]
    exact (hω (ContinuousMap.const ℂ (-circleAvg (h ω) r z)) V _ hV (fun _ _ => rfl) u v).symm
  · filter_upwards [hD'.ae_internal_addFun_of_eq_const (Tight.isGFFPlusCont_of_wp hh)]
      with ω hω V hV
    funext u v
    rw [show -xiGamma γ * circleAvg (h ω) r z = xiGamma γ * -circleAvg (h ω) r z by ring]
    exact (hω (ContinuousMap.const ℂ (-circleAvg (h ω) r z)) V _ hV (fun _ _ => rfl) u v).symm



variable {D₁ D₂ : DistC → ContMetric} {c : ℝ → ℝ}


/-- For a normalized whole-plane GFF `k`, there is `C > 0` with a.s. `D₂_k ≤ C D₁_k` (GM's proof
of Prop 2.2, l. 927–936, via LM Thm 1.6). -/
theorem ae_le_mul_of_blueprint' (hLM16 : LMThm1_6) (h24a : GMS2_4a)
    (h24c : GMS2_4c) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hD₁ : IsWeakLQGMetric γ D₁ c)
    (hD₂ : IsWeakLQGMetric γ D₂ c) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {k : Ω → DistC} (hk : IsNormalizedWPGFF k P) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂P, ∀ u v : ℂ, (D₂ (k ω)).1 (u, v) ≤ C * (D₁ (k ω)).1 (u, v) := by
  obtain ⟨p, hp0, hp1, hLM⟩ := hLM16
  have hp'1 : (1 + p) / 2 < 1 := by linarith
  obtain ⟨s, hs, hsA⟩ := (h24a.perSpace γ hγ0 hγ2 D₁ c hD₁ P k hk.1).1 (Metric.ball 0 1)
    (Metric.sphere 0 (1 / 2)) Metric.isOpen_ball Metric.isBounded_ball (isCompact_sphere _ _)
    (Metric.sphere_subset_ball (by norm_num)) _ hp'1
  obtain ⟨S, hS, hSc⟩ := h24c.perSpace γ hγ0 hγ2 D₂ c hD₂ P k hk.1 (annulus 0 (1 / 2) 2)
    (Metric.sphere 0 1) (annulus 0 (1 / 2) 2).isOpen (isBounded_annulus_zero _ _)
    (isPreconnected_annulus_zero (by norm_num)) (isCompact_sphere _ _)
    (sphere_subset_annulus_zero (by norm_num) (by norm_num)) _ hp'1
  have hC : 0 < S / s := div_pos hS hs
  refine ⟨S / s, hC, hLM (xiGamma γ) P k (fun ω => D₁ (k ω)) (fun ω => D₂ (k ω)) hk
    (gm_S2_3' hD₁ hD₂ hk.1) (S / s) hC fun K _ => ⟨1, one_pos, fun z _ r hr => ?_⟩⟩
  have hr0 : 0 < r := hr.1
  have hA := hsA z r hr0
  have hB := hSc z r hr0
  rw [frontier_ball (0 : ℂ) one_ne_zero, scaleSet_sphere hr0, scaleSet_sphere hr0,
    mul_one, show r * (1 / 2) = r / 2 by ring] at hA
  rw [scaleSet_sphere hr0, scaleSet_annulus hr0, mul_one, show r * (1 / 2) = r / 2 by ring,
    mul_comm r 2] at hB
  refine ofReal_le_of_compl_le hp0.le hp1.le ?_
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans ((add_le_add hA hB).trans ?_))
  · rw [← compl_inter]
    refine compl_subset_compl.2 fun ω ⟨h1, h2⟩ => ?_
    simp only [mem_setOf_eq] at h1 h2 ⊢
    have hF : 0 < scaleFac (xiGamma γ) c (k ω) r z :=
      mul_pos (hD₁.tightness.1 r hr0) (Real.exp_pos _)
    calc internalDiam (D₂ (k ω)) (Metric.sphere z r) (annulus z (r / 2) (2 * r))
        ≤ ENNReal.ofReal (S * scaleFac (xiGamma γ) c (k ω) r z) := h2
      _ = ENNReal.ofReal (S / s) * ENNReal.ofReal (s * scaleFac (xiGamma γ) c (k ω) r z) := by
          rw [← ENNReal.ofReal_mul hC.le]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (S / s) *
          setDist (D₁ (k ω)) (Metric.sphere z (r / 2)) (Metric.sphere z r) := by
          gcongr
  · rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ## GM Proposition 2.2 -/

/-- **GM Proposition 2.2** (l. 890–896, proof l. 927–936), from LM Theorem 1.6 (no LM Lemma 1.4) and
the tightness facts GM S2.4a(i), S2.4c. -/
theorem gm_P2_2' (hLM16 : LMThm1_6) (h24a : GMS2_4a) (h24c : GMS2_4c) :
    P2_2 := by
  intro γ D D' c ⟨hγ0, hγ2, hD, hD'⟩
  by_cases hex : ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀)
      (_ : IsProbabilityMeasure P₀) (h₀ : Ω₀ → DistC), IsWholePlaneGFF h₀ P₀
  swap
  · exact ⟨1, one_pos, fun P _ h hh => (hex ⟨_, _, P, inferInstance, h, hh⟩).elim⟩
  obtain ⟨Ω₀, _, P₀, _, h₀, hh₀⟩ := hex
  have hN := measurable_circleAvg_left 1 0
  have hk₀ := hh₀.addConst (hN.comp hh₀.measurable).neg
  have hn₀ : IsNormalizedWPGFF (fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) P₀ :=
    ⟨hk₀, by
      filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh₀] with ω hω
      rw [hω]; ring⟩
  obtain ⟨C₁, hC₁, h₁⟩ := ae_le_mul_of_blueprint' hLM16 h24a h24c hγ0 hγ2 hD hD' hn₀
  obtain ⟨C₂, hC₂, h₂⟩ := ae_le_mul_of_blueprint' hLM16 h24a h24c hγ0 hγ2 hD' hD hn₀
  have hC : 0 < max C₁ C₂ := lt_max_of_lt_left hC₁
  refine ⟨max C₁ C₂, hC, fun {Ω} _ P _ h hh => ?_⟩
  have hT := measurableSet_bilip hD.measurable hD'.measurable (max C₁ C₂)
  have h0 : ∀ᵐ ω ∂P₀, (fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) ω ∈
      {g : DistC | ∀ u v : ℂ, (max C₁ C₂)⁻¹ * (D g).1 (u, v) ≤ (D' g).1 (u, v) ∧
        (D' g).1 (u, v) ≤ max C₁ C₂ * (D g).1 (u, v)} := by
    filter_upwards [h₁, h₂] with ω e1 e2 u v
    set g := addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)
    have d1 := Tight.cmetric_nonneg (D g).2 (u, v)
    have d2 := Tight.cmetric_nonneg (D' g).2 (u, v)
    constructor
    · rw [inv_mul_le_iff₀ hC]
      exact (e2 u v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) d2)
    · exact (e1 u v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) d1)
  have hkm : Measurable fun ω => addConst (h ω) (-circleAvg (h ω) 1 0) :=
    (hh.addConst (hN.comp hh.measurable).neg).measurable
  have hk₀m : Measurable fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0) := hn₀.1.measurable
  have h1 := (ae_map_iff hk₀m.aemeasurable hT).2 h0
  rw [← Tight.map_normalize_eq hh hh₀] at h1
  have h2 := (ae_map_iff hkm.aemeasurable hT).1 h1
  filter_upwards [h2, hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh),
    hD'.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh)] with ω hT' w1 w2 u v
  obtain ⟨a1, a2⟩ := hT' u v
  rw [w1, w2] at a1 a2
  have he := Real.exp_pos (xiGamma γ * -circleAvg (h ω) 1 0)
  constructor
  · refine le_of_mul_le_mul_left ?_ he
    linarith [a1]
  · refine le_of_mul_le_mul_left ?_ he
    linarith [a2]

end Bilip

end LQGMetric.GM
