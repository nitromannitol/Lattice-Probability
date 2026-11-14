/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1N2P1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndep
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Lem41
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110A
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes58Indep




 
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration

open LQGMetric

private theorem circleAverage_iff_tendsto (g : DistC) (r : Set.Ioi (0 : ℝ)) (z : ℂ)
    (a : ℝ) : IsCircleAverage g r z a ↔
      Tendsto (fun n => LQGMetric.CircleAvg.mollAvg g n z (r : ℝ)) atTop (𝓝 a) := by
  rfl

theorem circleAvg_eq_of_isCircleAverage (g : DistC) (r : Set.Ioi (0 : ℝ))
    (z : ℂ) (a : ℝ) (ha : IsCircleAverage g r z a) :
    LQGMetric.circleAvg g (r : ℝ) z = a := by
  exact LQGMetric.CircleAvg.circleAvg_eq_of_tendsto
    ((circleAverage_iff_tendsto g r z a).mp ha)

theorem normalized_old_of_new {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) : IsNormalizedWPGFF h P := by
  refine ⟨hh.1, ?_⟩
  filter_upwards [hh.2] with ω hω
  exact circleAvg_eq_of_isCircleAverage (h ω) ⟨1, by norm_num⟩ 0 0 hω


theorem ae_isCircleAverage_circleAvg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    ∀ᵐ ω ∂P, IsCircleAverage (h ω) r z (LQGMetric.circleAvg (h ω) (r : ℝ) z) := by
  filter_upwards [LQGMetric.CircleAvg.ae_tendsto_mollAvg hh z r.2] with ω hω
  obtain ⟨a, ha⟩ := hω
  have heq : LQGMetric.circleAvg (h ω) (r : ℝ) z = a :=
    LQGMetric.CircleAvg.circleAvg_eq_of_tendsto ha
  rw [heq]
  exact (circleAverage_iff_tendsto (h ω) r z a).mpr ha

theorem normalized_new_of_old {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) : IsNormalizedWholePlaneGFF h P := by
  refine ⟨hh.1, ?_⟩
  filter_upwards [ae_isCircleAverage_circleAvg hh.1 ⟨1, by norm_num⟩ 0, hh.2]
    with ω hω heq
  simpa only [heq] using hω

theorem translateDist_eq_affineComp_one (g : DistC) (z : ℂ) :
    SupercriticalLQGUniqueness.translateDist z g = LQGMetric.affineComp 1 z g := by
  apply DFunLike.ext
  intro φ
  have ht : SupercriticalLQGUniqueness.testTranslate z φ =
      LQGMetric.testAffinePull 1 z φ := by
    ext x
    rw [LQGMetric.testAffinePull_apply 1 z one_ne_zero]
    simp only [Complex.ofReal_one, div_one]
    rfl
  change g (SupercriticalLQGUniqueness.testTranslate z φ) =
    (LQGMetric.affineComp 1 z g) φ
  rw [LQGMetric.GFFInv.affineComp_apply, ht]
  norm_num


theorem circleAvg_translateDist (g : DistC) (r : ℝ) (z w : ℂ) :
    LQGMetric.circleAvg (translateDist z g) r w = LQGMetric.circleAvg g r (w + z) := by
  rw [translateDist_eq_affineComp_one]
  exact LQGMetric.GM.circleAvg_affineComp_one_at g r z w

theorem translated_normalized {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ) :
    IsNormalizedWholePlaneGFF
      (fun ω => LQGMetric.addConst (translateDist z (h ω))
        (-LQGMetric.circleAvg (h ω) 1 z)) P := by
  have hEq : (fun ω => LQGMetric.addConst (translateDist z (h ω))
        (-LQGMetric.circleAvg (h ω) 1 z)) =
      (fun ω => LQGMetric.addConst (LQGMetric.affineComp 1 z (h ω))
        (-LQGMetric.circleAvg (LQGMetric.affineComp 1 z (h ω)) 1 0)) := by
    funext ω
    rw [translateDist_eq_affineComp_one,
      LQGMetric.GM.circleAvg_affineComp_one_at]
    simp only [zero_add]
  rw [hEq]
  exact normalized_new_of_old (LQGMetric.GM.isNormalized_shift hh z)


theorem ae_centered_translate {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P,
      LQGMetric.addConst
        (LQGMetric.addConst (translateDist z (h ω)) (-LQGMetric.circleAvg (h ω) 1 z))
        (-LQGMetric.circleAvg
          (LQGMetric.addConst (translateDist z (h ω)) (-LQGMetric.circleAvg (h ω) 1 z)) r 0) =
      translateDist z (LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z)) := by
  have htr : IsWholePlaneGFF (fun ω => translateDist z (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using hh.affineComp one_pos z
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst htr 0 hr] with ω hω
  rw [hω, circleAvg_translateDist]
  simp only [zero_add]
  rw [LQGMetric.GM.addConst_addConst]
  have hc : -LQGMetric.circleAvg (h ω) 1 z +
      -(LQGMetric.circleAvg (h ω) r z + -LQGMetric.circleAvg (h ω) 1 z) =
      -LQGMetric.circleAvg (h ω) r z := by ring
  rw [hc, translateDist_eq_affineComp_one]
  conv_rhs => rw [translateDist_eq_affineComp_one]
  exact (LQGMetric.GM.affineComp_addConst one_pos z (h ω)
    (-LQGMetric.circleAvg (h ω) r z)).symm


theorem annulus_iteration_ae_open (s₁ s₂ : ℝ) (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) (a : ℝ) (ha : 0 < a)
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω),
          (∀ k, 0 < r k) → Antitone r →
          (∀ k, r (k + 1) / r k ≤ s₁) →
          (∀ k, LQGMetric.Blueprint.AEEventIn P
            (LQGMetric.Blueprint.fieldSigma
              (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) 0))
              (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k))) (E k)) →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E K ω : ℝ) < b * K} ≤
            ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ :=
    LQGMetric.LM.lmLem3_1a s₁ s₂ hs₁ hs₁₂ hs₂ a ha b hb hb1
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh r E hr hanti hratio hE hpE K
  classical
  choose F hFm hEF using hE
  have hF : LQGMetric.Blueprint.AnnulusIterHyp h s₁ s₂ r F :=
    ⟨hr, hanti, hratio, hFm⟩
  have hpF : ∀ k, ENNReal.ofReal p ≤ P (F k) := by
    intro k
    rw [← measure_congr (hEF k)]
    exact hpE k
  rw [LQGMetric.LM.prob_countOcc_congr hEF b K]
  exact hmain P h (normalized_old_of_new hh) r F hF hpF K


theorem aeEventIn_translated_centered {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    (V W : TopologicalSpace.Opens ℂ)
    (hVW : ∀ y : ℂ, y ∈ W ↔ y + z ∈ V) (E : Set Ω)
    (hE : LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z)) V) E) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω =>
          let hz := LQGMetric.addConst (translateDist z (h ω))
            (-LQGMetric.circleAvg (h ω) 1 z)
          LQGMetric.addConst hz (-LQGMetric.circleAvg hz r 0)) W) E := by
  obtain ⟨F, hFm, hEF⟩ := hE
  have hVW' : ∀ y : ℂ, y ∈ W ↔ (1 : ℝ) • y + z ∈ V := by
    intro y
    simpa only [one_smul] using hVW y
  have hE1 : LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.affineComp 1 z
          (LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z))) W) E :=
    ⟨F, (LQGMetric.GM.fieldSigma_le_affineComp one_pos hVW'
      (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z))) F hFm,
      hEF⟩
  apply LQGMetric.GM.aeEventIn_of_ae_eq (P := P) _ W hE1
  filter_upwards [ae_centered_translate hh z hr] with ω hω
  simpa only [translateDist_eq_affineComp_one] using hω.symm


theorem annulus_iteration_ae_translated_open (s₁ s₂ : ℝ) (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1) (a : ℝ) (ha : 0 < a)
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ (z : ℂ) (r : ℕ → ℝ) (E : ℕ → Set Ω),
          (∀ k, 0 < r k) → Antitone r →
          (∀ k, r (k + 1) / r k ≤ s₁) →
          (∀ k, LQGMetric.Blueprint.AEEventIn P
            (LQGMetric.Blueprint.fieldSigma
              (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) z))
              (LQGMetric.Blueprint.annulus z (s₁ * r k) (s₂ * r k))) (E k)) →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E K ω : ℝ) < b * K} ≤
            ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ :=
    annulus_iteration_ae_open s₁ s₂ hs₁ hs₁₂ hs₂ a ha b hb hb1
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh z r E hr hanti hratio hE hpE K
  let hz : Ω → DistC := fun ω => LQGMetric.addConst (translateDist z (h ω))
    (-LQGMetric.circleAvg (h ω) 1 z)
  have hnorm : IsNormalizedWholePlaneGFF hz P := translated_normalized hh z
  apply hmain P hz hnorm r E hr hanti hratio _ hpE K
  intro k
  have hVW : ∀ y : ℂ, y ∈ LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k) ↔
      y + z ∈ LQGMetric.Blueprint.annulus z (s₁ * r k) (s₂ * r k) := by
    intro y
    change (s₁ * r k < ‖y - 0‖ ∧ ‖y - 0‖ < s₂ * r k) ↔
      (s₁ * r k < ‖y + z - z‖ ∧ ‖y + z - z‖ < s₂ * r k)
    simp only [sub_zero, add_sub_cancel_right]
  exact aeEventIn_translated_centered hh z (hr k)
    (LQGMetric.Blueprint.annulus z (s₁ * r k) (s₂ * r k))
    (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k)) hVW (E k) (hE k)


end SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration


