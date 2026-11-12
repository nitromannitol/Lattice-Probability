/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusL38Trans at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusCompare
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicCore
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG

/-!
# GM Lemma 3.8, per-scale step: condition 1 of `𝖤_r(z)` at a general centre (task P2-M2E2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 3.8, l. 1393: "If (B) holds … then for each `z ∈ ℂ` and each `k ∈ [1,K]`,
condition 1 … in the definition of `𝖤_{r_k}(z)` holds with probability at least `1 − (1−p̃)/3`."
(B) (l. 1294) is condition 1 at the centre `0`; the passage to a general `z` is translation
invariance (Axiom IV′ and the translation invariance of the law of `h` modulo additive constant,
as in GM l. 1203).

* `ga_isGeod01_iff_of_scale`, `isGeod01_iff_of_translate`, `uniqueGeodIn_iff_of_*`,
  `mem_gaCompare_iff_of_scale`, `mem_gaCompare_iff_of_translate`: deterministic transport of
  geodesics and of condition 1 (own elementary steps).
* `prob_eq_of_ae_addConst_iff_um`: the law transfer of `prob_eq_of_ae_addConst_iff` for
  universally measurable sets.
* `prob_gaCompare_compl_le`: `P[condition 1 of 𝖤_r(z) fails] ≤ p` when `P[(B) at r] ≥ 1 − p`.
  The measurability of condition 1 (`uMeasurableSet_gaCompareB`, D48) needs geodesics between
  all pairs of points, i.e. GM.S1.1 (`gm_S1_1_bcpt`, from `Blueprint.DFGPSLem3_8`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint GFFInv GFFLaw

/-! ## Deterministic transport -/

lemma ga_isGeod01_iff_of_scale {D₁ D₂ : ContMetric} {e : ℝ} (he : 0 < e)
    (h : ∀ u v, D₂.1 (u, v) = e * D₁.1 (u, v)) (u v : ℂ) (η : C(unitInterval, ℂ)) :
    IsGeod01 D₂ u v η ↔ IsGeod01 D₁ u v η := by
  simp only [IsGeod01, h]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun s t => ?_
  rw [show |(t : ℝ) - s| * (e * D₁.1 (u, v)) = e * (|(t : ℝ) - s| * D₁.1 (u, v)) by ring,
    mul_right_inj' he.ne']

lemma uniqueGeodIn_iff_of_scale {D₁ D₂ : ContMetric} {e : ℝ} (he : 0 < e)
    (h : ∀ u v, D₂.1 (u, v) = e * D₁.1 (u, v)) (u v : ℂ) (S : Set ℂ) :
    UniqueGeodIn D₂ u v S ↔ UniqueGeodIn D₁ u v S := by
  simp only [UniqueGeodIn, UniqueGeod, ga_isGeod01_iff_of_scale he h]

lemma mem_gaCompare_iff_of_scale {D D' : DistC → ContMetric} {α C' r : ℝ} {z : ℂ}
    {g₁ g₂ : DistC} {e : ℝ} (he : 0 < e) (h1 : ∀ u v, (D g₂).1 (u, v) = e * (D g₁).1 (u, v))
    (h2 : ∀ u v, (D' g₂).1 (u, v) = e * (D' g₁).1 (u, v)) :
    g₂ ∈ gaCompare D D' α C' r z ↔ g₁ ∈ gaCompare D D' α C' r z := by
  simp only [gaCompare, mem_ofPred_eq, uniqueGeodIn_iff_of_scale he h1, h1, h2]
  refine forall₂_congr fun u _ => forall₂_congr fun v _ => imp_congr_right fun _ => ?_
  rw [show C' * (e * (D g₁).1 (u, v)) = e * (C' * (D g₁).1 (u, v)) by ring]
  exact ⟨fun H => le_of_mul_le_mul_left H he, fun H => mul_le_mul_of_nonneg_left H he.le⟩

lemma isGeod01_iff_of_translate {D₁ D₂ : ContMetric} {z : ℂ}
    (h : ∀ u v, D₂.1 (u, v) = D₁.1 (u + z, v + z)) (u v : ℂ) (η : C(unitInterval, ℂ)) :
    IsGeod01 D₂ u v η ↔
      IsGeod01 D₁ (u + z) (v + z) (Equiv.addRight (ContinuousMap.const unitInterval z) η) := by
  simp only [IsGeod01, Equiv.coe_addRight, ContinuousMap.add_apply, ContinuousMap.const_apply, h,
    add_left_inj]

lemma mem_closure_annulus_translate (z x : ℂ) (a b : ℝ) :
    x ∈ closure (annulus 0 a b : Set ℂ) ↔ x + z ∈ closure (annulus z a b : Set ℂ) := by
  have e : (annulus 0 a b : Set ℂ) = (Homeomorph.addRight z) ⁻¹' (annulus z a b : Set ℂ) := by
    ext y
    show a < ‖y - 0‖ ∧ ‖y - 0‖ < b ↔ a < ‖y + z - z‖ ∧ ‖y + z - z‖ < b
    simp
  rw [e, ← Homeomorph.preimage_closure]
  rfl

lemma uniqueGeodIn_iff_of_translate {D₁ D₂ : ContMetric} {z : ℂ}
    (h : ∀ u v, D₂.1 (u, v) = D₁.1 (u + z, v + z)) (u v : ℂ) (a b : ℝ) :
    UniqueGeodIn D₂ u v (closure (annulus 0 a b : Set ℂ)) ↔
      UniqueGeodIn D₁ (u + z) (v + z) (closure (annulus z a b : Set ℂ)) := by
  set e := Equiv.addRight (ContinuousMap.const unitInterval z)
  have hr : ∀ η : C(unitInterval, ℂ), range η ⊆ closure (annulus 0 a b : Set ℂ) ↔
      range (e η) ⊆ closure (annulus z a b : Set ℂ) := fun η => by
    simp only [range_subset_iff, e, Equiv.coe_addRight, ContinuousMap.add_apply,
      ContinuousMap.const_apply, ← mem_closure_annulus_translate]
  simp only [UniqueGeodIn, UniqueGeod]
  refine and_congr (e.existsUnique_congr fun η => isGeod01_iff_of_translate h u v η)
    (e.forall_congr fun η => ?_)
  rw [isGeod01_iff_of_translate h u v η, hr η]

lemma sphere_translate {z u : ℂ} {ρ : ℝ} : u ∈ sphere (0 : ℂ) ρ ↔ u + z ∈ sphere z ρ := by
  simp only [mem_sphere, dist_eq_norm, sub_zero, add_sub_cancel_right]

/-- condition 1 at `z` for `g` is condition 1 at `0` for `g' = g(· + z)` -/
lemma mem_gaCompare_iff_of_translate {D D' : DistC → ContMetric} {α C' r : ℝ} {z : ℂ}
    {g g' : DistC} (h1 : ∀ u v, (D g').1 (u, v) = (D g).1 (u + z, v + z))
    (h2 : ∀ u v, (D' g').1 (u, v) = (D' g).1 (u + z, v + z)) :
    g' ∈ gaCompare D D' α C' r 0 ↔ g ∈ gaCompare D D' α C' r z := by
  simp only [gaCompare, mem_ofPred_eq]
  constructor
  · intro H u hu v hv hU
    have hu' : u - z ∈ sphere (0 : ℂ) (α * r) := by
      rw [sphere_translate (z := z), sub_add_cancel]; exact hu
    have hv' : v - z ∈ sphere (0 : ℂ) r := by
      rw [sphere_translate (z := z), sub_add_cancel]; exact hv
    have := H (u - z) hu' (v - z) hv'
      (by rw [uniqueGeodIn_iff_of_translate h1, sub_add_cancel, sub_add_cancel]; exact hU)
    rwa [h1, h2, sub_add_cancel, sub_add_cancel] at this
  · intro H u hu v hv hU
    rw [uniqueGeodIn_iff_of_translate h1] at hU
    rw [h1, h2]
    exact H (u + z) (sphere_translate.1 hu) (v + z) (sphere_translate.1 hv) hU

/-! ## Law transfer for universally measurable events modulo constants -/

/-- `prob_eq_of_ae_addConst_iff` for a universally measurable `S` (GM l. 1203). -/
theorem prob_eq_of_ae_addConst_iff_um {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P') {S : Set DistC}
    (hS : UMeasurableSet S) (hinv : ∀ᵐ ω ∂P, ∀ a : ℝ, addConst (h ω) a ∈ S ↔ h ω ∈ S)
    (hinv' : ∀ᵐ ω ∂P', ∀ a : ℝ, addConst (h' ω) a ∈ S ↔ h' ω ∈ S) :
    P (h ⁻¹' S) = P' (h' ⁻¹' S) := by
  have hmap := map_comp_eq_of_sigma0 (measurable_recenter_sigma0 integral_detRho) hh hh'
  have hle : sigma0 ≤ (inferInstance : MeasurableSpace DistC) := by
    rw [sigma0, ← measurable_iff_comap_le]
    exact measurable_pi_iff.2 fun φ => measurable_pair φ.1
  have hrm : Measurable (recenter detRho) :=
    (measurable_recenter_sigma0 integral_detRho).mono hle le_rfl
  have e1 : P (h ⁻¹' S) = P ((recenter detRho ∘ h) ⁻¹' S) := by
    refine measure_congr ?_
    filter_upwards [hinv] with ω hω
    exact propext ((hω _).symm)
  have e2 : P' (h' ⁻¹' S) = P' ((recenter detRho ∘ h') ⁻¹' S) := by
    refine measure_congr ?_
    filter_upwards [hinv'] with ω hω
    exact propext ((hω _).symm)
  rw [e1, e2, ← Measure.map_apply₀ (hrm.comp hh.measurable).aemeasurable (hS _ inferInstance),
    ← Measure.map_apply₀ (hrm.comp hh'.measurable).aemeasurable (hS _ inferInstance), hmap]

/-! ## Condition 1 at a general centre -/

section Prob
variable {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- a.s. geodesics exist between all pairs for `D_{h+a}`, all `a` (GM.S1.1) -/
lemma ae_exists_geod_addConst (h38 : DFGPSLem3_8) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, (∀ u v : ℂ, ∃ η, (D (h ω)).IsGeod01 u v η) ∧
      ∀ a : ℝ, ∀ u v : ℂ, ∃ η, (D (addConst (h ω) a)).IsGeod01 u v η := by
  filter_upwards [gm_S1_1_bcpt h38 hγ0 hγ2 hD P h hh,
    hD.length P h (Tight.isGFFPlusCont_of_wp hh),
    hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh)] with ω hb hl hw
  refine ⟨fun u v => exists_isGeod01_of_bcpt _ hl hb u v, fun a u v => ?_⟩
  obtain ⟨η, hη⟩ := exists_isGeod01_of_bcpt _ hl hb u v
  exact ⟨η, (ga_isGeod01_iff_of_scale (Real.exp_pos _) (hw a) u v η).2 hη⟩

/-- a.s. condition 1 equals its Borel form, and the Borel form is invariant under constants -/
lemma ae_gaCompareB (h38 : DFGPSLem3_8) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') (hh : IsWholePlaneGFF h P)
    (α C' r : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂P, (h ω ∈ gaCompare D D' α C' r z ↔ h ω ∈ gaCompareB D D' α C' r z) ∧
      ∀ a : ℝ, addConst (h ω) a ∈ gaCompareB D D' α C' r z ↔
        h ω ∈ gaCompareB D D' α C' r z := by
  filter_upwards [ae_exists_geod_addConst h38 hγ0 hγ2 hD hh,
    hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh),
    hD'.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh)] with ω ⟨hex, hexa⟩ hw hw'
  refine ⟨mem_gaCompare_iff hex, fun a => ?_⟩
  rw [← mem_gaCompare_iff (hexa a), ← mem_gaCompare_iff hex]
  exact mem_gaCompare_iff_of_scale (Real.exp_pos _) (hw a) (hw' a)

/-- **GM l. 1393**: if `P[(B) at r] ≥ 1 − p`, then condition 1 of `𝖤_r(z)` fails with probability
at most `p`, for every `z`. -/
theorem prob_gaCompare_compl_le (h38 : DFGPSLem3_8) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') (hh : IsWholePlaneGFF h P)
    {α C' r p : ℝ} (z : ℂ) (hB : ENNReal.ofReal (1 - p) ≤ P (h ⁻¹' badScale D D' α r C')) :
    P (h ⁻¹' gaCompare D D' α C' r z)ᶜ ≤ ENNReal.ofReal p := by
  have hz := hh.affineComp one_pos z
  set hz' : Ω → DistC := fun ω => affineComp 1 z (h ω) with hz'def
  have hUM := uMeasurableSet_gaCompareB hD.measurable hD'.measurable α C' r 0
  -- `P[h ∈ (B)] = P[h ∈ B₀]`
  have e1 : P (h ⁻¹' badScale D D' α r C') = P (h ⁻¹' gaCompareB D D' α C' r 0) := by
    refine measure_congr ?_
    filter_upwards [ae_gaCompareB h38 hγ0 hγ2 hD hD' hh α C' r 0] with ω hω
    exact propext hω.1
  -- law transfer
  have e2 : P (h ⁻¹' gaCompareB D D' α C' r 0) = P (hz' ⁻¹' gaCompareB D D' α C' r 0) :=
    prob_eq_of_ae_addConst_iff_um hh hz hUM
      ((ae_gaCompareB h38 hγ0 hγ2 hD hD' hh α C' r 0).mono fun _ hω => hω.2)
      ((ae_gaCompareB h38 hγ0 hγ2 hD hD' hz α C' r 0).mono fun _ hω => hω.2)
  -- translation
  have e3 : (h ⁻¹' gaCompare D D' α C' r z) =ᵐ[P] (hz' ⁻¹' gaCompareB D D' α C' r 0) := by
    filter_upwards [ae_gaCompareB h38 hγ0 hγ2 hD hD' hz α C' r 0,
      hD.translation P h (Tight.isGFFPlusCont_of_wp hh) z,
      hD'.translation P h (Tight.isGFFPlusCont_of_wp hh) z] with ω hω ht ht'
    exact propext ((mem_gaCompare_iff_of_translate ht ht').symm.trans hω.1)
  have hnull : NullMeasurableSet (hz' ⁻¹' gaCompareB D D' α C' r 0) P :=
    hUM.nullMeasurableSet_preimage hz.measurable.aemeasurable
  rw [measure_congr e3.compl, prob_compl_eq_one_sub₀ hnull, ← e2, ← e1]
  calc 1 - P (h ⁻¹' badScale D D' α r C') ≤ 1 - ENNReal.ofReal (1 - p) := tsub_le_tsub_left hB 1
    _ ≤ ENNReal.ofReal p := by
      rw [tsub_le_iff_right]
      calc (1 : ℝ≥0∞) = ENNReal.ofReal (p + (1 - p)) := by
            rw [add_sub_cancel, ENNReal.ofReal_one]
        _ ≤ _ := ENNReal.ofReal_add_le

end Prob

end LQGMetric.GM
