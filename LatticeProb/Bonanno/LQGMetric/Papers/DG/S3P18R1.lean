/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P18R1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P18T5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryLaw

/-!
# DG:1774–1777, 1593–1595: law transfer between zero-boundary GFFs (task P2-DG105q)

DG pass from P3.22 / P3.17 for the coupling `(ĥ, h^{𝕊(1)})` to "the same is true with a
whole-plane GFF" (DG:1776, DG:1593–1595). The LFPP events only see a version of the circle
averages of `h^{𝕊(1)}` on a closed square `X`, and the law of a zero-boundary GFF is unique.

* `r18_circ_factor` — `T ↦ T_r(z)` factors measurably through `T|_U` when `∂B_r(z) ⊆ U`
  (from `GM.measurable_circleAvg_fieldSigma` with `h = id` and mathlib's
  `Measurable.exists_eq_measurable_comp`);
* `r18_law_eq` — two fields whose restrictions to `U` are zero-boundary GFFs
  (`IsZeroBoundaryGFF.map_eq`) have equal laws of countably many circle averages;
* `r18Cl` — the clamping retraction of `ℂ` onto the square `[a,b]²`;
* **`r18_transfer`** — for a functional `F` with the comparison property `T18Cmp` that only
  depends on `[a,b]²`, `P{F(hc) ∈ S} = P'{F(hc') ∈ S}` for continuous versions `hc, hc'` of the
  circle averages of the two fields.

Own routine glue (DV-D105m-1 pattern: measurability of the LFPP events in countably many
coordinates, which DG use silently).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DG

/-- `T ↦ T_r(z)` is a measurable function of `T|_U` when `∂B_r(z) ⊆ U` -/
theorem r18_circ_factor (U : Opens ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hS : sphere z r ⊆ (U : Set ℂ)) :
    ∃ Ψ : DistOn U → ℝ, Measurable Ψ ∧ ∀ T : DistC, circleAvg T r z = Ψ (restrictTo U T) := by
  obtain ⟨ε, hε, hεU⟩ := (isCompact_sphere z r).exists_thickening_subset_open U.isOpen hS
  have hεU' : thickening ε (sphere z |r|) ⊆ (U : Set ℂ) := by rwa [abs_of_pos hr]
  have hm : Measurable[Blueprint.fieldSigma (id : DistC → DistC) U]
      fun T : DistC => circleAvg T r z :=
    (GM.measurable_circleAvg_fieldSigma (id : DistC → DistC) r z hε).mono
      (GM.fieldSigma_mono (id : DistC → DistC) (V := Blueprint.nbhdO ε (sphere z |r|)) (W := U)
        hεU') le_rfl
  obtain ⟨Ψ, hΨ, he⟩ := Measurable.exists_eq_measurable_comp hm
  exact ⟨Ψ, hΨ, fun T => congrFun he T⟩

/-- **equal laws of countably many circle averages** of two zero-boundary GFFs on `U` -/
theorem r18_law_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} (U : Opens ℂ) {hz : Ω → DistC} {hz' : Ω' → DistC}
    (hg : IsZeroBoundaryGFF U (fun ω => restrictTo U (hz ω)) P)
    (hg' : IsZeroBoundaryGFF U (fun ω => restrictTo U (hz' ω)) P')
    {ι : Type} [Countable ι] {r : ℝ} (hr : 0 < r) (x : ι → ℂ)
    (hS : ∀ i, sphere (x i) r ⊆ (U : Set ℂ)) :
    Measurable (fun ω i => circleAvg (hz ω) r (x i)) ∧
      Measurable (fun ω i => circleAvg (hz' ω) r (x i)) ∧
      P.map (fun ω i => circleAvg (hz ω) r (x i)) =
        P'.map (fun ω i => circleAvg (hz' ω) r (x i)) := by
  choose Ψ hΨ he using fun i => r18_circ_factor U hr (hS i)
  have hm : Measurable fun (T : DistOn U) (i : ι) => Ψ i T := measurable_pi_iff.2 hΨ
  have e1 : (fun ω i => circleAvg (hz ω) r (x i)) =
      (fun (T : DistOn U) (i : ι) => Ψ i T) ∘ fun ω => restrictTo U (hz ω) := by
    funext ω i; exact he i _
  have e2 : (fun ω i => circleAvg (hz' ω) r (x i)) =
      (fun (T : DistOn U) (i : ι) => Ψ i T) ∘ fun ω => restrictTo U (hz' ω) := by
    funext ω i; exact he i _
  rw [e1, e2]
  refine ⟨hm.comp hg.measurable, hm.comp hg'.measurable, ?_⟩
  rw [← Measure.map_map hm hg.measurable, ← Measure.map_map hm hg'.measurable,
    IsZeroBoundaryGFF.map_eq hg hg']

/-- the clamping retraction of `ℂ` onto `[a,b]²` -/
def r18Cl (a b : ℝ) (x : ℂ) : ℂ := ⟨max a (min b x.re), max a (min b x.im)⟩

/-- the closed square `[a,b]²` -/
def r18X (a b : ℝ) : Set ℂ := {x | x.re ∈ Icc a b ∧ x.im ∈ Icc a b}

lemma r18Cl_continuous (a b : ℝ) : Continuous (r18Cl a b) := by
  have h1 : Continuous fun x : ℂ => max a (min b x.re) := by fun_prop
  have h2 : Continuous fun x : ℂ => max a (min b x.im) := by fun_prop
  exact Complex.equivRealProdCLM.symm.continuous.comp (h1.prodMk h2)

lemma r18Cl_mem {a b : ℝ} (hab : a ≤ b) (x : ℂ) : r18Cl a b x ∈ r18X a b :=
  ⟨⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩,
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩⟩

lemma r18Cl_eq {a b : ℝ} {x : ℂ} (hx : x ∈ r18X a b) : r18Cl a b x = x := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  apply Complex.ext <;> simp [r18Cl, *]

lemma r18X_bdd (a b : ℝ) : r18X a b ⊆ closedBall 0 (|a| + |b| + |a| + |b|) := fun x hx => by
  rw [mem_closedBall, dist_zero_right]
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  have hre : |x.re| ≤ |a| + |b| := abs_le.2 ⟨by
    linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b], by
    linarith [le_abs_self b, abs_nonneg a]⟩
  have him : |x.im| ≤ |a| + |b| := abs_le.2 ⟨by
    linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b], by
    linarith [le_abs_self b, abs_nonneg a]⟩
  linarith [Complex.norm_le_abs_re_add_abs_im x]

/-- **Law transfer for a local LFPP-type functional** (DG:1776, DG:1593–1595) -/
theorem r18_transfer {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {ξ a b : ℝ} (hab : a ≤ b) {F : (ℂ → ℝ) → ℝ≥0∞}
    (hF : T18Cmp ξ (r18X a b) F) (hloc : ∀ φ ψ : ℂ → ℝ, EqOn φ ψ (r18X a b) → F φ = F ψ)
    (U : Opens ℂ) {δ : ℝ} (hδ : 0 < δ) (hXU : ∀ x ∈ r18X a b, sphere x δ ⊆ (U : Set ℂ))
    {hz : Ω → DistC} {hz' : Ω' → DistC}
    (hg : IsZeroBoundaryGFF U (fun ω => restrictTo U (hz ω)) P)
    (hg' : IsZeroBoundaryGFF U (fun ω => restrictTo U (hz' ω)) P')
    {hc : ℂ → Ω → ℝ} {hc' : ℂ → Ω' → ℝ}
    (hcc : ∀ ω, ContinuousOn (fun x => hc x ω) (r18X a b))
    (hcc' : ∀ ω, ContinuousOn (fun x => hc' x ω) (r18X a b))
    (hcv : ∀ x ∈ r18X a b, hc x =ᵐ[P] fun ω => circleAvg (hz ω) δ x)
    (hcv' : ∀ x ∈ r18X a b, hc' x =ᵐ[P'] fun ω => circleAvg (hz' ω) δ x)
    (S : Set ℝ≥0∞) (hS : MeasurableSet S) :
    P {ω | F (fun x => hc x ω) ∈ S} = P' {ω | F (fun x => hc' x ω) ∈ S} := by
  obtain ⟨Φ, hΦ, hΦF⟩ := t18_repr (r18X_bdd a b) hF
  set p : ℚ × ℚ → ℂ := fun q => r18Cl a b (t18pt0 q)
  have hp : ∀ q, p q ∈ r18X a b := fun q => r18Cl_mem hab _
  -- `F` in the clamped coordinates
  have hrep : ∀ {Ω₀ : Type} (k : ℂ → Ω₀ → ℝ), (∀ ω, ContinuousOn (fun x => k x ω) (r18X a b)) →
      ∀ ω, F (fun x => k x ω) = Φ (fun q => k (p q) ω) := fun k hk ω => by
    have hcont : Continuous fun x => k (r18Cl a b x) ω :=
      (hk ω).comp_continuous (r18Cl_continuous a b) (fun x => r18Cl_mem hab x)
    rw [hΦF _ hcont]
    exact hloc _ _ fun x hx => by simp only [r18Cl_eq hx]
  obtain ⟨hm, hm', hlaw⟩ := r18_law_eq U hg hg' hδ p fun q => hXU _ (hp q)
  have hae : (fun ω q => hc (p q) ω) =ᵐ[P] fun ω q => circleAvg (hz ω) δ (p q) := by
    have := ae_all_iff.2 fun q => hcv (p q) (hp q)
    filter_upwards [this] with ω hω
    funext q; exact hω q
  have hae' : (fun ω q => hc' (p q) ω) =ᵐ[P'] fun ω q => circleAvg (hz' ω) δ (p q) := by
    have := ae_all_iff.2 fun q => hcv' (p q) (hp q)
    filter_upwards [this] with ω hω
    funext q; exact hω q
  have e1 : {ω | F (fun x => hc x ω) ∈ S} = (fun ω q => hc (p q) ω) ⁻¹' (Φ ⁻¹' S) := by
    ext ω; simp only [mem_ofPred_eq, mem_preimage, hrep hc hcc ω]
  have e2 : {ω | F (fun x => hc' x ω) ∈ S} = (fun ω q => hc' (p q) ω) ⁻¹' (Φ ⁻¹' S) := by
    ext ω; simp only [mem_ofPred_eq, mem_preimage, hrep hc' hcc' ω]
  rw [e1, e2, measure_congr (hae.preimage _), measure_congr (hae'.preimage _),
    ← Measure.map_apply hm (hΦ hS), ← Measure.map_apply hm' (hΦ hS), hlaw]

end LQGMetric.DG
