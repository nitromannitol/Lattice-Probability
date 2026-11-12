/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusAround at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulus
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DefsLemmas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightD

/-!
# GM Lemma 3.8, per-scale steps: conditions 1 and 3 of `𝖤_r(z)` (task P2-M2E)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 3.8 (l. 1375–1396).

* `gaCompare_zero`: condition 1 of `𝖤_r(0)` is the event of (B) (GM l. 1294) at radius `r`.
* `mem_gaAround_of`, `gm_gaAround_prob` (GM l. 1391: "We can again apply Axiom V … there exists
  `A > 1` depending on `α` and `p̃` such that for each `z` and `r > 0`, condition 3 … occurs with
  probability at least `1 − (1 − p̃)/3`"): from the proved GM.S2.4d (`Tight.gm_S2_4d`, distance
  around `𝔸_{αr,r}(z)` at most `A₀ D_h(x, y)` for all `x ∈ ∂B_{αr}(z)`, `y ∈ ∂B_r(z)`). The
  infimum `D_h(∂B_{αr}(z), ∂B_r(z))` is attained and positive, so for `A > A₀` the infimum
  defining the distance around is beaten by an actual disconnecting path (own elementary step).
* `goodAnnulus_compl_le`: the union bound over the three conditions (GM l. 1395 "Combining the
  three preceding paragraphs").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- union bound over the three conditions of `𝖤_r(z)` (GM l. 1395) -/
lemma goodAnnulus_compl_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → ContMetric) (α A C' r : ℝ) (z : ℂ) :
    P (h ⁻¹' goodAnnulus D D' α A C' r z)ᶜ ≤ P (h ⁻¹' gaCompare D D' α C' r z)ᶜ +
      P (h ⁻¹' gaLong D D' α r z)ᶜ + P (h ⁻¹' gaAround D α A r z)ᶜ := by
  have : (h ⁻¹' goodAnnulus D D' α A C' r z)ᶜ = (h ⁻¹' gaCompare D D' α C' r z)ᶜ ∪
      (h ⁻¹' gaLong D D' α r z)ᶜ ∪ (h ⁻¹' gaAround D α A r z)ᶜ := by
    simp only [goodAnnulus, preimage_inter, compl_inter]
  rw [this]
  exact (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)

/-- if the distance around `𝔸_{αr,r}(z)` is at most `A₀ D(x,y)` for all `x ∈ ∂B_{αr}(z)`,
`y ∈ ∂B_r(z)`, then condition 3 of `𝖤_r(z)` holds with any `A > A₀` -/
lemma mem_gaAround_of {D : DistC → ContMetric} {g : DistC} {α A₀ A r : ℝ} {z : ℂ} (hr : 0 < r)
    (hα0 : 0 < α) (hα1 : α < 1) (hA₀ : 0 ≤ A₀) (hA : A₀ < A)
    (H : ∀ x ∈ sphere z (α * r), ∀ y ∈ sphere z r,
      (D g).aroundDist {w | α * r < ‖w - z‖ ∧ ‖w - z‖ < r} (sphere z (α * r)) (sphere z r) ≤
        ENNReal.ofReal (A₀ * (D g).1 (x, y))) :
    g ∈ gaAround D α A r z := by
  set Dg := D g with hDg
  have hc1 : IsCompact (Dg.pt '' sphere z (α * r)) :=
    (isCompact_sphere _ _).image (ContMetric.continuous_pt Dg)
  have hc2 : IsCompact (Dg.pt '' sphere z r) :=
    (isCompact_sphere _ _).image (ContMetric.continuous_pt Dg)
  have hne1 : (Dg.pt '' sphere z (α * r)).Nonempty :=
    (NormedSpace.sphere_nonempty.2 (by positivity)).image _
  have hne2 : (Dg.pt '' sphere z r).Nonempty :=
    (NormedSpace.sphere_nonempty.2 hr.le).image _
  obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, he⟩ := MetricGeometry.IsCompact.exists_setEDist_eq_edist hc1 hc2 hne1 hne2
  have hxy : x ≠ y := by
    rintro rfl
    rw [mem_sphere] at hx hy
    nlinarith
  have hpos := dist_pos_of_ne Dg hxy
  have hsd : setDist Dg (sphere z (α * r)) (sphere z r) = ENNReal.ofReal (Dg.1 (x, y)) := by
    rw [setDist, he, edist_dist]; rfl
  have hlt : Dg.aroundDist {w | α * r < ‖w - z‖ ∧ ‖w - z‖ < r} (sphere z (α * r)) (sphere z r) <
      ENNReal.ofReal A * setDist Dg (sphere z (α * r)) (sphere z r) := by
    calc _ ≤ ENNReal.ofReal (A₀ * Dg.1 (x, y)) := H x hx y hy
      _ < ENNReal.ofReal (A * Dg.1 (x, y)) :=
          (ENNReal.ofReal_lt_ofReal_iff (by nlinarith)).2 (by nlinarith)
      _ = _ := by rw [hsd, ← ENNReal.ofReal_mul (by linarith)]
  unfold ContMetric.aroundDist at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨a, b, G, hab, hG, hGA, hdisc, hlen⟩ := hlt
  exact ⟨a, b, G, hab, hG, hGA, hdisc, hlen.le⟩

/-- **GM l. 1391** (proof of Lemma 3.8): for `α ∈ (0,1)` and `ε > 0` there is `A > 1` such that
for every whole-plane GFF `h`, `r > 0` and `z`, condition 3 of `𝖤_r(z)` fails with probability
`< ε`. From GM.S2.4d (`Tight.gm_S2_4d`). -/
theorem gm_gaAround_prob {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : ℝ, 1 < A ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P (h ⁻¹' gaAround D α A r z)ᶜ < ε := by
  obtain ⟨A₀, hA₀, H⟩ := Tight.gm_S2_4d hD hα0 hα1 hε
  refine ⟨A₀ + 1, by linarith, fun P _ h hh r hr z =>
    lt_of_le_of_lt (measure_mono fun ω hω => ?_) (H P h hh r hr z)⟩
  intro hall
  exact hω (mem_gaAround_of hr hα0 hα1 hA₀.le (by linarith) hall)

end LQGMetric.GM
