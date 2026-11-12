/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedP36Conf at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedP36Det
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Geodesics
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas

/-!
# GM Prop 3.6, Step 1: geodesic confinement (task P2-M2F2, WP-M2f, row 8 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, l. 1434–1436: "By Axiom V (tightness across scales),
there is some large bounded open set `U` … such that for each `𝕣 > 0`, it holds with probability
at least `1 − β/2`, the `D_h`-diameter of `B_𝕣(0)` is smaller than the `D_h`-distance from
`B_𝕣(0)` to `∂(𝕣U)`, in which case every `D_h`-geodesic between points of `B_𝕣(0)` is contained in
`𝕣U`."

* `confSet r R`: the closed set of metrics with `d(u,v) ≤ d(u,x)` for `u, v ∈ B_r(0)`,
  `x ∈ ∂B_{Rr}(0)` (implied by GM's event);
* `range_subset_of_confSet`: on it, geodesics between points of `B_r(0)` stay in `B̄_{Rr}(0)`;
* `conf_prob`: from `Blueprint.GMS2_4e` (form of decision D56: `R` before `∀ Ω P h`),
  `P[D_h ∉ confSet r R] ≤ β` uniformly over all whole-plane GFFs;
* `denseRange_ratPt`: `ℚ²` is dense in `ℂ` (for GM's last sentence, l. 1497–1499).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the confinement set: `d(u,v) ≤ d(u,x)` for `u, v ∈ B_r(0)`, `x ∈ ∂B_{Rr}(0)` -/
def confSet (r R : ℝ) : Set ContMetric :=
  {d | ∀ u ∈ ball (0 : ℂ) r, ∀ v ∈ ball (0 : ℂ) r, ∀ x ∈ sphere (0 : ℂ) (R * r),
    d.1 (u, v) ≤ d.1 (u, x)}

/-- on `confSet r R`, a geodesic between points of `B_r(0)` stays in `B̄_{Rr}(0)` -/
theorem range_subset_of_confSet {d : ContMetric} {r R : ℝ} (hR : 1 < R) (hd : d ∈ confSet r R)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) r) (hw : w ∈ ball (0 : ℂ) r) {η : C(unitInterval, ℂ)}
    (hη : d.IsGeod01 z w η) : range η ⊆ closedBall (0 : ℂ) (R * r) := by
  rintro _ ⟨t, rfl⟩
  rw [mem_closedBall_zero_iff]
  by_contra hn
  push Not at hn
  have hz' : ‖z‖ < r := mem_ball_zero_iff.1 hz
  have hr : 0 < r := (norm_nonneg z).trans_lt hz'
  have hRr : r < R * r := by nlinarith
  set g : ℝ → ℝ := fun τ => ‖η (pj τ)‖ with hg
  have hgc : Continuous g :=
    (η.continuous.comp (continuous_projIcc (h := zero_le_one))).norm
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have hg0 : g 0 = ‖z‖ := by
    simp only [hg]; rw [pj_eq_of_mem ⟨le_rfl, zero_le_one⟩]; exact congrArg _ hη.1
  have hgt : g t = ‖η t‖ := by
    simp only [hg]; rw [pj_eq_of_mem t.2]
  obtain ⟨τ, hτ, hgτ⟩ := intermediate_value_Icc ht0 hgc.continuousOn
    (show R * r ∈ Icc (g 0) (g t) by rw [hg0, hgt]; exact ⟨by linarith, hn.le⟩)
  have hτt : τ < t := by
    rcases eq_or_lt_of_le hτ.2 with h | h
    · rw [h, hgt] at hgτ; linarith
    · exact h
  have hx : η (pj τ) ∈ sphere (0 : ℂ) (R * r) := mem_sphere_zero_iff_norm.2 hgτ
  have h1 := hd z hz w hw _ hx
  have e1 : d.1 (z, η (pj τ)) = τ * d.1 (z, w) := by
    have := hη.2.2 0 (pj τ); rw [hη.1] at this
    rw [this, pj_coe_of_mem ⟨hτ.1, hτ.2.trans t.2.2⟩]; simp [abs_of_nonneg hτ.1]
  have e2 : d.1 (z, η t) = t * d.1 (z, w) := by
    have := hη.2.2 0 t; rw [hη.1] at this
    rw [this]; simp [abs_of_nonneg ht0]
  have hL : 0 ≤ d.1 (z, w) := by
    have := d.2.triangle z w z
    rw [d.2.self_eq_zero, d.2.symm w z] at this; linarith
  rcases eq_or_lt_of_le hL with h0 | h0
  · rw [← h0, mul_zero] at e2
    have := d.2.eq_of_eq_zero _ _ e2
    rw [← this] at hn; linarith
  · have ht1 : (t : ℝ) ≤ 1 := t.2.2
    nlinarith

/-- GM l. 1434: confinement with probability `≥ 1 − β`, `R` uniform over all whole-plane GFFs -/
theorem conf_prob (h24e : GMS2_4e) {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ R : ℝ, 1 < R ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
        P (h ⁻¹' (D ⁻¹' confSet r R)ᶜ) ≤ ENNReal.ofReal β := by
  obtain ⟨R, hR, H⟩ := h24e γ hγ hγ2 D c hD β hβ hβ1
  refine ⟨R, hR, fun {Ω} _ P _ h hh r hr => ?_⟩
  refine le_trans (measure_mono fun ω hω => ?_) (H P h hh 0 r hr)
  intro hgood
  apply hω
  intro u hu v hv x hx
  have h1 : ENNReal.ofReal ((D (h ω)).1 (u, v)) ≤
      ⨆ u ∈ ball (0 : ℂ) r, ⨆ v ∈ ball (0 : ℂ) r, ENNReal.ofReal ((D (h ω)).1 (u, v)) :=
    (le_iSup₂ (f := fun v (_ : v ∈ ball (0 : ℂ) r) => ENNReal.ofReal ((D (h ω)).1 (u, v))) v hv).trans
      (le_iSup₂ (f := fun u (_ : u ∈ ball (0 : ℂ) r) =>
        ⨆ v ∈ ball (0 : ℂ) r, ENNReal.ofReal ((D (h ω)).1 (u, v))) u hu)
  have h2 : setDist (D (h ω)) (ball 0 r) (sphere 0 (R * r)) ≤
      ENNReal.ofReal ((D (h ω)).1 (u, x)) := by
    rw [setDist_eq_iInf]
    exact (iInf₂_le u hu).trans (iInf₂_le x hx)
  exact ((ENNReal.ofReal_lt_ofReal_iff'.1 ((h1.trans_lt hgood).trans_le h2)).1).le

/-- `ℚ²` is dense in `ℂ` -/
lemma denseRange_ratPt : DenseRange ratPt := by
  have h1 : DenseRange (Prod.map (fun q : ℚ => (q : ℝ)) (fun q : ℚ => (q : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h2 : DenseRange (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) :=
    Complex.equivRealProdCLM.symm.surjective.denseRange
  have := h2.comp h1 Complex.equivRealProdCLM.symm.continuous
  convert this using 1
  funext q
  apply Complex.ext <;> simp [ratPt]

end LQGMetric.GM
