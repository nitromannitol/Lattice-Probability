/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedSwap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedCount

/-!
# GM §3.2: Propositions 3.2, 3.3, 3.5 (task P2-M2F, WP-M2f, row 9 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.
See `AttainedCount.lean` for the overview.

* `cs_pos_of_ratios`: `0 < c_* ≤ C_*` (GM l. 1184) from Proposition 2.2 and the existence of a
  whole-plane GFF.
* `S3_2fn`: GM's footnote (l. 1222, "footnote-G-prob"), cited at l. 1265: for `C'' ∈ (0, C_*)`
  there is `β ∈ (0,1)` with `P[Ḡ_1(C'', β)] ≥ β`. (Open node: GM's footnote proof uses the
  definition of `C_*`, a geodesic subdivision, a covering by `N` balls, translation invariance
  and a union bound.)
* `attainedUp_subset_GUp`: GM.S3.3 (l. 1263) in the corrected form.
* `gm_P3_2`, `gm_P3_5`, `gm_P3_3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `0 < c_* ≤ C_*` (GM l. 1184), from GM Proposition 2.2 -/
theorem cs_pos_of_ratios (h22 : P2_2) {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}
    {cs Cs : ℝ} (hS : PairSetting γ D D' c) (hR : RatiosAre D D' cs Cs) : 0 < cs ∧ cs ≤ Cs := by
  obtain ⟨Ω, _, P, h, hP, hh⟩ := GFFExist.exists_wholePlaneGFF
  obtain ⟨C, hC, H⟩ := gm_S1_23 h22 hS
  obtain ⟨ω, h1, h2⟩ := ((H P h hh).and (hR P h hh)).exists
  rw [h2.1, h2.2] at h1
  exact ⟨(inv_pos.2 hC).trans_le h1.1, h1.2.1⟩

/-- **GM footnote at l. 1222** (`footnote-G-prob`, used at l. 1265): for each `C'' ∈ (0, C_*)`
there is `β ∈ (0,1)` with `P[Ḡ_1(C'', β)] ≥ β` (uniformly over whole-plane GFFs: the law of `h`
modulo additive constants is unique). -/
def S3_2fn : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → ∀ C'' ∈ Ioo (0 : ℝ) Cs, ∃ β ∈ Ioo (0 : ℝ) 1,
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ENNReal.ofReal β ≤ P (h ⁻¹' GUp D D' 1 C'' β)

/-- **GM.S3.3** (l. 1263), corrected: for `C' < C₁`, the event of (A) with `C₁` is contained in
`Ḡ_r(C', (1 − α)/2)` (move `v ∈ ∂B_r(0)` radially into `B_r(0)` by continuity). -/
theorem attainedUp_subset_GUp {D D' : DistC → ContMetric} {α r C₁ C' : ℝ} (hα : 1 / 2 < α)
    (hα1 : α < 1) (hr : 0 < r) (hC : C' < C₁) :
    attainedUp D D' α r C₁ ⊆ GUp D D' r C' ((1 - α) / 2) := by
  rintro g ⟨u, hu, v, hv, hle, -⟩
  rw [mem_sphere_zero_iff_norm] at hu hv
  have huv : u ≠ v := by
    rintro rfl; rw [hu] at hv; nlinarith
  have hD := dist_pos_of_ne (D g) huv
  have h1 : C' * (D g).1 (u, v) < (D' g).1 (u, v) :=
    (mul_lt_mul_of_pos_right hC hD).trans_le hle
  set f : ℝ → ℝ := fun t => (D' g).1 (u, (t : ℂ) * v) - C' * (D g).1 (u, (t : ℂ) * v) with hf
  have hfc : Continuous f := by
    have e1 : Continuous fun t : ℝ => (u, (t : ℂ) * v) := by fun_prop
    exact ((D' g).1.continuous.comp e1).sub (continuous_const.mul ((D g).1.continuous.comp e1))
  have hf1 : 0 < f 1 := by simp only [hf, Complex.ofReal_one, one_mul]; linarith
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.1
    ((hfc.tendsto 1).eventually (lt_mem_nhds hf1))
  set t : ℝ := 1 - min (δ / 2) ((1 - α) / 4) with ht
  have hm0 : 0 < min (δ / 2) ((1 - α) / 4) := lt_min (by linarith) (by linarith)
  have hm1 : min (δ / 2) ((1 - α) / 4) ≤ (1 - α) / 4 := min_le_right _ _
  have hft : 0 < f t := hδf (by
    rw [Real.dist_eq, ht, show 1 - min (δ / 2) ((1 - α) / 4) - 1 = -min (δ / 2) ((1 - α) / 4)
      by ring, abs_neg, abs_of_pos hm0]
    exact (min_le_left _ _).trans_lt (by linarith))
  have ht0 : 0 < t := by linarith
  have htv : ‖(t : ℂ) * v‖ = t * r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, hv]
  refine ⟨u, ?_, (t : ℂ) * v, ?_, ?_, ?_⟩
  · rw [mem_ball_zero_iff, hu]; nlinarith
  · rw [mem_ball_zero_iff, htv]; nlinarith
  · have := norm_sub_norm_le ((t : ℂ) * v) u
    rw [htv, hu, norm_sub_rev] at this
    nlinarith
  · simp only [hf] at hft; linarith

/-- **GM Proposition 3.2** from Proposition 3.4 at `𝕣 = 1` (GM.S3.3, l. 1263–1267), with
`β̄ = (1 − α_*)/2` -/
theorem gm_P3_2 (h34 : P3_4) (hfn : S3_2fn) : P3_2 := by
  intro γ D D' c cs Cs hS hR μ ν hμ hμν hν1
  obtain ⟨α₀, p, hα₀, hp, H⟩ := h34 hS hR hμ hμν hν1
  refine ⟨(1 - α₀) / 2, p, ⟨by linarith [hα₀.2], by linarith [hα₀.1]⟩, hp, fun C' hC' => ?_⟩
  have hC₁ : (C' + Cs) / 2 ∈ Ioo (0 : ℝ) Cs := ⟨by linarith [hC'.1, hC'.2], by linarith [hC'.2]⟩
  obtain ⟨C'', hC'', H1⟩ := H α₀ ⟨le_rfl, hα₀.2⟩ ((C' + Cs) / 2) hC₁
  obtain ⟨β, hβ, Hβ⟩ := hfn hS hR C'' ⟨hC₁.1.trans hC''.1, hC''.2⟩
  obtain ⟨ε₀, hε₀, H2⟩ := H1 β hβ
  refine ⟨ε₀, hε₀, fun P _ h hh ε hε => ?_⟩
  refine (H2 P h hh 1 one_pos (Hβ P h hh) ε ⟨hε.1, hε.2.le⟩).trans
    (Nat.cast_le.2 (scaleCount_mono hε.1 fun k _ hk => hk.trans (measure_mono
      (preimage_mono ?_))))
  have := attainedUp_subset_GUp (D := D) (D' := D') (r := (8 : ℝ)⁻¹ ^ k) hα₀.1 hα₀.2
    (by positivity) (show C' < (C' + Cs) / 2 by linarith [hC'.2])
  rwa [mul_one]

/-- **GM Proposition 3.5** = Proposition 3.4 for `(D̃, D)` (GM.S3.4, l. 1269) -/
theorem gm_P3_5 (h22 : P2_2) (h34 : P3_4) : P3_5 := by
  intro γ D D' c cs Cs hS hR μ ν hμ hμν hν1
  obtain ⟨hcs, -⟩ := cs_pos_of_ratios h22 hS hR
  obtain ⟨C, hC, hb⟩ := h22 hS
  obtain ⟨α₀, p, hα₀, hp, H⟩ := h34 hS.swap (RatiosAre.swap hC hb hR) hμ hμν hν1
  refine ⟨α₀, p, hα₀, hp, fun α hα c' hc' => ?_⟩
  have hc'0 : 0 < c' := hcs.trans hc'
  obtain ⟨C'', ⟨h1, h2⟩, H1⟩ := H α hα c'⁻¹ ⟨inv_pos.2 hc'0, (inv_lt_inv₀ hc'0 hcs).2 hc'⟩
  have hC''0 : 0 < C'' := (inv_pos.2 hc'0).trans h1
  refine ⟨C''⁻¹, ⟨(lt_inv_comm₀ hcs hC''0).2 h2, (inv_lt_comm₀ hC''0 hc'0).2 h1⟩,
    fun β hβ => ?_⟩
  obtain ⟨ε₀, hε₀, H2⟩ := H1 β hβ
  refine ⟨ε₀, hε₀, fun P _ h hh R hR0 hG ε hε => ?_⟩
  rw [GLow_swap D' D R β (inv_pos.2 hC''0), inv_inv] at hG
  have e : ∀ r, attainedUp D' D α r c'⁻¹ = attainedLow D D' α r c' := fun r => by
    rw [attainedUp_swap D D' α r (inv_pos.2 hc'0), inv_inv]
  have := H2 P h hh R hR0 hG ε hε
  simpa only [e] using this

/-- **GM Proposition 3.3** = Proposition 3.2 for `(D̃, D)` (GM.S3.4, l. 1269, 1283) -/
theorem gm_P3_3 (h22 : P2_2) (h32 : P3_2) : P3_3 := by
  intro γ D D' c cs Cs hS hR μ ν hμ hμν hν1
  obtain ⟨hcs, -⟩ := cs_pos_of_ratios h22 hS hR
  obtain ⟨C, hC, hb⟩ := h22 hS
  obtain ⟨βb, pb, hβb, hpb, H⟩ := h32 hS.swap (RatiosAre.swap hC hb hR) hμ hμν hν1
  refine ⟨βb, pb, hβb, hpb, fun c' hc' => ?_⟩
  have hc'0 : 0 < c' := hcs.trans hc'
  obtain ⟨ε₀, hε₀, H1⟩ := H c'⁻¹ ⟨inv_pos.2 hc'0, (inv_lt_inv₀ hc'0 hcs).2 hc'⟩
  refine ⟨ε₀, hε₀, fun P _ h hh ε hε => ?_⟩
  have e : ∀ r β, GUp D' D r c'⁻¹ β = GLow D D' r c' β := fun r β => by
    rw [GUp_swap D D' r β (inv_pos.2 hc'0), inv_inv]
  have := H1 P h hh ε hε
  simpa only [e] using this

end LQGMetric.GM
