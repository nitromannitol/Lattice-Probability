/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.SetupGeoBdy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimatesF
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBasic

/-!
# GM.S4.8: GM Lemma 2.12 at centre `𝕫` for filled metric balls

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`; GM Lemma 2.12 (`lem-geo-bdy`,
l. 1077–1084) = DFGPS Proposition 4.3 (`Blueprint.DFGPSProp4_3`, centre `0`, ordinary metric balls,
normalized field). GM apply it in the proof of Lemma 4.8 (l. 1806–1810) at centre `𝕫` and for the
filled balls `𝓑^•_{t_k}(𝕫; D_h)`; the inventory (`blueprint/GM_B.md` §2b, L4.8 row) records the
implicit steps "translation `0 → 𝕫` and unfilled → filled ball (`∂𝓑^• ⊂ ∂𝓑`)" as GM.S4.8.

* `gm_S4_8_det` (deterministic): if `D'(u,v) = κ D₀(u + 𝕫, v + 𝕫)` (`κ > 0`) and the conclusion of
  DFGPS Prop 4.3 holds for `D'` at centre `0`, it holds for `D₀` at centre `𝕫` with filled balls.
  Ingredients: metric balls of `D'` are translates of those of `D₀` (radius `κs`), geodesics are
  translated and reparametrized, Lebesgue measure is translation invariant, and
  `∂𝓑^•_s ⊆ ∂𝓑_s` (`jb_frontier_subset_closure`, `jb_disjoint_ballM_frontier`, P2-M2I's
  `JordanBasic`).
* `gm_S4_8_detF` (deterministic, decision D68): the same transfer from centre `0` filled balls of
  `D'` to centre `𝕫` filled balls of `D₀` (`filledBall_preimage_addRight`: filled balls are
  translated with the metric).
* `gm_S4_8`: GM Lemma 2.12 at centre `𝕫` for filled balls and any whole-plane GFF, from
  `DFGPSProp4_3F` (D68; formerly `DFGPSProp4_3` with `gm_S4_8_det`) applied to `h(· + 𝕫) − (h(· + 𝕫))_1(0)` (Axiom IV′ `translation`, Axiom III via
  `IsWeakLQGMetric.ae_dist_addConst`, translation invariance of the GFF `IsWholePlaneGFF.affineComp`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- translation preserves boundedness -/
theorem gm_isBounded_image_addRight (z : ℂ) (A : Set ℂ) :
    Bornology.IsBounded ((Homeomorph.addRight z) '' A) ↔ Bornology.IsBounded A := by
  simp only [Metric.isBounded_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x hx y hy => ?_⟩
    have := hC (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
    simpa only [Homeomorph.coe_addRight, dist_add_right] using this
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa only [Homeomorph.coe_addRight, dist_add_right] using hC hx hy

/-- filled balls of `D'(u,v) = κ D₀(u + z, v + z)` are translates of those of `D₀` -/
theorem filledBall_preimage_addRight {D₀ D' : ContMetric} {κ : ℝ} (hκ : 0 < κ) {z : ℂ}
    (hD : ∀ u v, D'.1 (u, v) = κ * D₀.1 (u + z, v + z)) (s : ℝ) :
    filledBall D' 0 (κ * s) = (Homeomorph.addRight z) ⁻¹' filledBall D₀ z s := by
  set f := Homeomorph.addRight z
  have hpre : ballM D' 0 (κ * s) = f ⁻¹' ballM D₀ z s := by
    ext x
    show D'.1 (0, x) < κ * s ↔ D₀.1 (z, x + z) < s
    rw [hD, zero_add]
    exact ⟨fun h => lt_of_mul_lt_mul_left h hκ.le, fun h => mul_lt_mul_of_pos_left h hκ⟩
  have hX : closure (ballM D' 0 (κ * s)) = f ⁻¹' closure (ballM D₀ z s) := by
    rw [hpre, f.preimage_closure]
  ext x
  simp only [filledBall, mem_union, mem_preimage, mem_ofPred_eq, hX]
  refine or_congr Iff.rfl (and_congr_right fun hx => ?_)
  rw [← preimage_compl, ← gm_isBounded_image_addRight z,
    f.image_connectedComponentIn (show x ∈ f ⁻¹' (closure (ballM D₀ z s))ᶜ from hx),
    f.image_preimage]

/-- **GM.S4.8, deterministic transfer for filled balls** (D68): centre `0` filled balls of `D'`
⇒ centre `𝕫` filled balls of `D₀` -/
theorem gm_S4_8_detF {D₀ D' : ContMetric} {κ : ℝ} (hκ : 0 < κ) {z : ℂ}
    (hD : ∀ u v, D'.1 (u, v) = κ * D₀.1 (u + z, v + z)) {R a : ℝ} {V : ℝ≥0∞}
    (hgood : ∀ s : ℝ, 0 < s → filledBall D' 0 s ⊆ ball 0 R → ∀ w : ℂ, w ∉ filledBall D' 0 s →
      ∀ (G : ℝ → ℂ) (L : ℝ), IsGeodesicL D' G L 0 w →
        volume (thickening a (G '' Icc 0 L) ∩ thickening a (frontier (filledBall D' 0 s))) ≤ V) :
    ∀ s : ℝ, 0 < s → filledBall D₀ z s ⊆ ball z R → ∀ w : ℂ, w ∉ filledBall D₀ z s →
      ∀ (G : ℝ → ℂ) (L : ℝ), IsGeodesicL D₀ G L z w →
        volume (thickening a (G '' Icc 0 L) ∩ thickening a (frontier (filledBall D₀ z s))) ≤ V := by
  intro s hs hsub w hw G L hG
  have hpre := filledBall_preimage_addRight hκ hD s
  have h1 : filledBall D' 0 (κ * s) ⊆ ball 0 R := by
    intro x hx
    rw [hpre] at hx
    have := hsub hx
    rw [Homeomorph.coe_addRight, mem_ball, dist_eq_norm, add_sub_cancel_right] at this
    rwa [mem_ball, dist_zero_right]
  have h2 : w - z ∉ filledBall D' 0 (κ * s) := by
    rw [hpre, mem_preimage, Homeomorph.coe_addRight]
    show ¬ (w - z + z ∈ filledBall D₀ z s)
    rw [sub_add_cancel]
    exact hw
  set G' : ℝ → ℂ := fun u => G (u / κ) - z
  have hmem : ∀ u ∈ Icc 0 (κ * L), u / κ ∈ Icc 0 L := fun u hu =>
    ⟨div_nonneg hu.1 hκ.le, (div_le_iff₀ hκ).mpr (by linarith [hu.2])⟩
  have hG' : IsGeodesicL D' G' (κ * L) 0 (w - z) := by
    refine ⟨mul_nonneg hκ.le hG.1, ?_, ?_, ?_⟩
    · simp only [G', zero_div, hG.2.1, sub_self]
    · simp only [G', mul_div_cancel_left₀ _ hκ.ne', hG.2.2.1]
    · intro u hu v hv
      simp only [G']
      rw [hD, sub_add_cancel, sub_add_cancel, hG.2.2.2 _ (hmem u hu) _ (hmem v hv), ← sub_div,
        abs_div, abs_of_pos hκ, mul_div_cancel₀ _ hκ.ne']
  have hV := hgood (κ * s) (mul_pos hκ hs) h1 (w - z) h2 G' (κ * L) hG'
  refine le_trans (measure_mono ?_) ((measure_preimage_add_right volume (-z) _).le.trans hV)
  rintro x ⟨hx1, hx2⟩
  rw [mem_thickening_iff] at hx1 hx2
  obtain ⟨y, ⟨u, hu, rfl⟩, hxy⟩ := hx1
  obtain ⟨y', hy', hxy'⟩ := hx2
  refine ⟨mem_thickening_iff.mpr ⟨G' (κ * u), ⟨κ * u, ⟨mul_nonneg hκ.le hu.1,
    mul_le_mul_of_nonneg_left hu.2 hκ.le⟩, rfl⟩, ?_⟩, mem_thickening_iff.mpr ⟨y' - z, ?_, ?_⟩⟩
  · simp only [G', mul_div_cancel_left₀ _ hκ.ne']
    rwa [sub_eq_add_neg, dist_add_right]
  · rw [hpre, ← (Homeomorph.addRight z).preimage_frontier]
    show y' - z + z ∈ frontier (filledBall D₀ z s)
    rwa [sub_add_cancel]
  · rwa [sub_eq_add_neg, dist_add_right]

/-- **GM.S4.8** (GM Lemma 2.12 as used at l. 1806–1810): DFGPS Prop 4.3 at centre `𝕫`, for filled
balls and any whole-plane GFF, with constants uniform in the probability space and in `𝕫`
(D75: DFGPS Prop 4.3 is uniform, `SuperPolyHighProbU`). -/
theorem gm_S4_8U (hDF43 : DFGPSProp4_3F) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {M : ℝ} (hM : 0 < M) :
    ∀ p : ℝ, 0 < p → ∃ C ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ 𝕫 : ℂ, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
    P {ω | ∀ s : ℝ, 0 < s →
      filledBall (D (h ω)) 𝕫 s ⊆ ball 𝕫 (ε ^ (-M) * 𝕣) →
      ∀ w : ℂ, w ∉ filledBall (D (h ω)) 𝕫 s → ∀ (G : ℝ → ℂ) (L : ℝ),
        IsGeodesicL (D (h ω)) G L 𝕫 w →
        volume (thickening (ε * 𝕣) (G '' Icc 0 L) ∩
            thickening (ε * 𝕣) (frontier (filledBall (D (h ω)) 𝕫 s))) ≤
          ENNReal.ofReal (ε ^ (2 - 1 / M) * 𝕣 ^ 2)}ᶜ ≤ ENNReal.ofReal (C * ε ^ p) := by
  intro p hp
  obtain ⟨C, ε₀, hε₀, hC⟩ := hDF43 γ hγ hγ2 D c hD M hM p hp
  refine ⟨C, ε₀, hε₀, fun {Ω} _ P _ h hh 𝕫 ε hε 𝕣 h𝕣 => ?_⟩
  have hh₁ := hh.affineComp one_pos 𝕫
  have hN := measurable_circleAvg_left 1 0
  set h₁ : Ω → DistC := fun ω => affineComp 1 𝕫 (h ω)
  set h' : Ω → DistC := fun ω => addConst (h₁ ω) (-circleAvg (h₁ ω) 1 0)
  have hh' : IsNormalizedWPGFF h' P := by
    refine ⟨hh₁.addConst (hN.comp hh₁.measurable).neg, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh₁] with ω hω
    simp only [h', hω, add_neg_cancel]
  have hc : ∀ {g : Ω → DistC}, IsWholePlaneGFF g P → IsGFFPlusCont g P := by
    intro g hg
    refine ⟨hg.measurable, fun _ => 0, measurable_const, ?_⟩
    have h0 : ofCont 0 = 0 := by
      ext φ
      simp [ofCont]
    simpa [h0] using hg
  refine le_trans (measure_mono_ae ?_) (hC P h' hh' ε hε 𝕣 h𝕣)
  filter_upwards [hD.translation P h (hc hh) 𝕫, hD.ae_dist_addConst (hc hh₁)] with ω hT hA
  intro hnot hgood
  apply hnot
  exact gm_S4_8_detF (κ := Real.exp (xiGamma γ * -circleAvg (h₁ ω) 1 0)) (Real.exp_pos _)
    (fun u v => by rw [hA, hT]) hgood

end LQGMetric.GM
