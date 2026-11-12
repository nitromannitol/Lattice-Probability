/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.GeodesicsCM at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Meas.Geod

/-!
# GM S1.2 for `h + φ` (task P2-M2C, WP-M2c)

GM (arXiv:1905.00383v3, l. 648) use the a.s. uniqueness of the `D_h`-geodesic between fixed points
also for the field `h − φ`, `φ` a deterministic smooth bump (inventory GM_B l. 293: "for `h − φ`
(by absolute continuity)"; decision D33: "h−φ by a transfer corollary"). Here, for every test
function `φ ∈ 𝓓(ℂ)` (so `h − φ = h + (−φ)`):

* `ae_notMem_addFun_of_ae` (transfer corollary): a universally measurable set `B` of fields which
  `h` a.s. avoids, and which is a.s. invariant under recentring `g ↦ g − ⟨g, ρ⟩` for both `h` and
  `h + φ`, is a.s. avoided by `h + φ`. Proof: Cameron–Martin on the mean-zero pairings
  (`lawPair0_addFun_ac`, task P2-FCM) applied to the `σ₀`-measurable event `{recenter g ∈ B₂}`,
  `B₂ ⊇ B` a Borel hull of `B` for the law of `recenter h` (D-C1 universal measurability).
* `gm_S1_2_addFun`, `gm_S1_2_addFun_rat`: the geodesic of `D_{h+φ}` between fixed points (all `ℚ²`
  pairs) is a.s. unique. The recentring invariance is Axiom III (`ae_dist_addConst`) plus
  `uniqueGeod_iff_of_scale` (a constant multiple of a metric has the same geodesics).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- a constant multiple `l D` (`l > 0`) of a metric has the same geodesics -/
lemma isGeod01_iff_of_scale {D₁ D₂ : ContMetric} {l : ℝ} (hl : 0 < l)
    (hD : ∀ u v, D₁.1 (u, v) = l * D₂.1 (u, v)) (z w : ℂ) (η : C(unitInterval, ℂ)) :
    IsGeod01 D₁ z w η ↔ IsGeod01 D₂ z w η := by
  unfold IsGeod01
  simp only [hD]
  constructor
  · rintro ⟨h0, h1, h⟩
    refine ⟨h0, h1, fun s t => ?_⟩
    have e : l * D₂.1 (η s, η t) = l * (|(t : ℝ) - s| * D₂.1 (z, w)) := by rw [h s t]; ring
    exact mul_left_cancel₀ hl.ne' e
  · rintro ⟨h0, h1, h⟩
    refine ⟨h0, h1, fun s t => ?_⟩
    rw [h s t]; ring

/-! ### Steps of the transfer corollary -/

lemma measurable_recenter_cm {ρ : TestC} (hρ : ∫ x, ρ x = 1) : Measurable (GFFLaw.recenter ρ) := by
  have hR : Measurable[GFFLaw.sigma0] (GFFLaw.recenter ρ) := GFFLaw.measurable_recenter_sigma0 hρ
  have hev : Measurable GFFLaw.ev0 := measurable_pi_iff.2 fun ψ => measurable_evalDist _
  exact hR.mono hev.comap_le le_rfl

lemma exists_ev0_preimage_cm {ρ : TestC} (hρ : ∫ x, ρ x = 1) {B : Set DistC}
    (hB : MeasurableSet B) :
    ∃ A : Set (TestC0 → ℝ), MeasurableSet A ∧ GFFLaw.ev0 ⁻¹' A = GFFLaw.recenter ρ ⁻¹' B := by
  have hR : Measurable[GFFLaw.sigma0] (GFFLaw.recenter ρ) := GFFLaw.measurable_recenter_sigma0 hρ
  obtain ⟨A, hA, hAeq⟩ := hR hB
  exact ⟨A, hA, hAeq⟩

lemma ae_pair0_addFun_notMem_cm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (φ : TestC)
    (A : Set (TestC0 → ℝ))
    (hA : MeasurableSet A)
    (hPh : lawPair0 h P A = 0) : ∀ᵐ ω ∂P, pair0 (addFun (h ω) (testCont φ)) ∉ A := by
  have hPφ : lawPair0 (fun ω => addFun (h ω) (testCont φ)) P A = 0 :=
    lawPair0_addFun_ac hh φ hPh
  rw [lawPair0, Measure.map_apply (measurable_pair0_addFun hh φ) hA,
    measure_eq_zero_iff_ae_notMem] at hPφ
  exact hPφ

lemma map_recenter_null_cm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {ρ : TestC} {B : Set DistC} (hB : UMeasurableSet B) (hRb : Measurable (GFFLaw.recenter ρ))
    (h0 : ∀ᵐ ω ∂P, h ω ∉ B)
    (hinv1 : ∀ᵐ ω ∂P, (h ω ∈ B ↔ GFFLaw.recenter ρ (h ω) ∈ B)) :
    (P.map fun ω => GFFLaw.recenter ρ (h ω)) B = 0 := by
  have hf₁ : Measurable fun ω => GFFLaw.recenter ρ (h ω) := hRb.comp hh.measurable
  rw [Measure.map_apply₀ hf₁.aemeasurable (hB.nullMeasurableSet _),
      measure_eq_zero_iff_ae_notMem]
  filter_upwards [h0, hinv1] with ω h1 h2
  exact fun hm => h1 (h2.2 hm)

lemma preimage_pair0_eq_cm {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistC}
    {ρ : TestC} {B : Set DistC} (A : Set (TestC0 → ℝ))
    (hAeq : GFFLaw.ev0 ⁻¹' A = GFFLaw.recenter ρ ⁻¹' B) :
    (fun ω => pair0 (h ω)) ⁻¹' A =
        (fun ω => GFFLaw.recenter ρ (h ω)) ⁻¹' B := by
      ext ω
      show h ω ∈ GFFLaw.ev0 ⁻¹' A ↔ h ω ∈ GFFLaw.recenter ρ ⁻¹' B
      rw [hAeq]

lemma pair0_mem_of_recenter_cm {ρ : TestC} {B B₂ : Set DistC} {A : Set (TestC0 → ℝ)}
    (hAeq : GFFLaw.ev0 ⁻¹' A = GFFLaw.recenter ρ ⁻¹' B₂) (hsub : B ⊆ B₂) (x : DistC)
    (hx : GFFLaw.recenter ρ x ∈ B) : pair0 x ∈ A := by
  have hmem : x ∈ GFFLaw.ev0 ⁻¹' A := by
    rw [hAeq]
    exact hsub hx
  exact hmem

lemma lawPair0_null_cm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {ρ : TestC} {B₂ : Set DistC} (hB₂ : MeasurableSet B₂) (hRb : Measurable (GFFLaw.recenter ρ))
    {A : Set (TestC0 → ℝ)} (hA : MeasurableSet A)
    (hAeq : GFFLaw.ev0 ⁻¹' A = GFFLaw.recenter ρ ⁻¹' B₂)
    (hν : (P.map fun ω => GFFLaw.recenter ρ (h ω)) B₂ = 0) : lawPair0 h P A = 0 := by
  have hf₁ : Measurable fun ω => GFFLaw.recenter ρ (h ω) := hRb.comp hh.measurable
  rw [lawPair0, Measure.map_apply (measurable_pair0_comp hh) hA, preimage_pair0_eq_cm A hAeq,
    ← Measure.map_apply hf₁ hB₂]
  exact hν

/-- **Transfer corollary** (D33): Cameron–Martin for null events invariant under recentring. -/
theorem ae_notMem_addFun_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (φ : TestC)
    {ρ : TestC} (hρ : ∫ x, ρ x = 1) {B : Set DistC} (hB : UMeasurableSet B)
    (h0 : ∀ᵐ ω ∂P, h ω ∉ B)
    (hinv1 : ∀ᵐ ω ∂P, (h ω ∈ B ↔ GFFLaw.recenter ρ (h ω) ∈ B))
    (hinv2 : ∀ᵐ ω ∂P, (addFun (h ω) (testCont φ) ∈ B ↔
      GFFLaw.recenter ρ (addFun (h ω) (testCont φ)) ∈ B)) :
    ∀ᵐ ω ∂P, addFun (h ω) (testCont φ) ∉ B := by
  have hRb := measurable_recenter_cm hρ
  have hνB := map_recenter_null_cm hh hB hRb h0 hinv1
  have hB₂ : MeasurableSet (toMeasurable (P.map fun ω => GFFLaw.recenter ρ (h ω)) B) :=
    measurableSet_toMeasurable _ _
  have hνB₂ : (P.map fun ω => GFFLaw.recenter ρ (h ω))
      (toMeasurable (P.map fun ω => GFFLaw.recenter ρ (h ω)) B) = 0 := by
    rw [measure_toMeasurable]; exact hνB
  obtain ⟨A, hA, hAeq⟩ := exists_ev0_preimage_cm hρ hB₂
  filter_upwards [ae_pair0_addFun_notMem_cm hh φ A hA (lawPair0_null_cm hh hB₂ hRb hA hAeq hνB₂),
    hinv2] with ω h1 h2 hm
  exact h1 (pair0_mem_of_recenter_cm hAeq (subset_toMeasurable _ _) _ (h2.1 hm))

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

end LQGMetric.GM
