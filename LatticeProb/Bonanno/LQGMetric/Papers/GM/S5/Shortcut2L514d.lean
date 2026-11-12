/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2L514d at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2L514c
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2Cross

/-!
# GM Lemma 5.14, first assertion

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

`gm_L5_14a`: GM Lemma 5.14 (`lem-geomove-restrict`, l. 3420–3461), first assertion: every point
of `P̄^φ` (times outside both hitting balls) lies in `B_{2ζr}(U ∪ 𝒲)`. GM's proof (l. 3447–3460):
`P̄^φ` enters `B_{ζr}(U) ∪ 𝒲` (`gm_L5_14_enter`); a path from there to a point outside
`B_{2ζr}(U ∪ 𝒲)` has a sub-path in `𝔸_{r/4,4r}(0) ∖ (B_{ζr}(U) ∪ 𝒲)` of diameter `≥ ζr`
(`exists_cross_m2m2`), which `gm_L5_14_across` excludes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter
open scoped ENNReal Topology

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- **GM Lemma 5.14**, first assertion (l. 3447–3460). -/
theorem gm_L5_14a {D D' : DistC → ContMetric} {S : EData} (hS : S.Ranges) {r : ℝ}
    (hr : 0 < r) (hcr : 0 < S.c r) {U : ℂ → ℂ → Set ℂ} {fb gb : Set ℂ → TestC}
    (hU : IsTubeFam S U r) (hB : IsBumpChoice S U fb gb r) {g : DistC}
    (hg : g ∈ eventE D D' S U fb gb r)
    {z w x' y' : ℂ} (hz : 4 * r ≤ ‖z‖) (hw : 4 * r ≤ ‖w‖)
    (hx' : IsHitPt (D g) z x' r) (hy' : IsHitPt (D g) w y' r)
    (hsep : S.δ * r ≤ ‖(2 / 3 : ℂ) * x' - (2 / 3 : ℂ) * y'‖) (hlen : (D g).IsLength)
    {Q : C(unitInterval, ℂ)} (hQ : IsGeod01 (D g) z w Q)
    (hhit : (range Q ∩ Metric.ball (0 : ℂ) (2 * r)).Nonempty)
    (hW : ∀ a b : ℂ, ENNReal.ofReal ((D (subTest g (phiChoice S U fb gb r x' y'))).1 (a, b)) =
      weylScale S.ξ (-testCont (phiChoice S U fb gb r x' y')) (D g) a b)
    {Qφ : C(unitInterval, ℂ)} (hQφ : IsGeod01 (D (subTest g (phiChoice S U fb gb r x' y'))) z w Qφ) :
    ∀ τ : unitInterval, ((D g).1 (z, x') ≤ (D g).1 (z, Qφ τ) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ τ)) →
      infDist (Qφ τ) (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') ∪
        (thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * x')) ∪
          thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * y')))) < 2 * S.ζ * r := by
  obtain ⟨τ', hout', hK⟩ := gm_L5_14_enter hS hr hcr hU hB hg hz hw hx' hy' hsep hlen hQ hhit hW hQφ
  have hS' := hS
  set x : ℂ := (2 / 3 : ℂ) * x' with hxdef
  set y : ℂ := (2 / 3 : ℂ) * y' with hydef
  have hxs : x ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, hxdef, norm_mul, hx'.1]; norm_num; ring
  have hys : y ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, hydef, norm_mul, hy'.1]; norm_num; ring
  set Wc := thickening (S.θ ^ 2 * r) (lineTube S.θ r x) ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r y)
  set Y := U x y ∪ Wc with hY
  obtain ⟨-, -, -, hsT, hxU, -⟩ := hU x hxs y hys hsep
  have hYne : Y.Nonempty := ⟨x, Or.inl hxU⟩
  have hUne : (U x y).Nonempty := ⟨x, hxU⟩
  set ζr := S.ζ * r
  have hζr : 0 < ζr := mul_pos hS.2.2.2.2.2.2.1.1 hr
  -- norm bounds on `Y`
  obtain ⟨-, -, hb, -, hε, -, hζ, -, hθ, -⟩ := hS
  have hsq : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hθ1 : S.θ ≤ 1 / 100 := by
    have := hθ.2; have := hζ.2; have := hε.2; have := hb.2; linarith
  have hεs : S.ε₀ ≤ 1 / 10000 := by have := hε.2; have := hb.2; linarith
  have hζs : S.ζ ≤ 1 / 10000 := by have := hζ.2; linarith
  have hθp : 0 < S.θ * r := mul_pos hθ.1 hr
  have hεp : 0 < S.ε₀ * r := mul_pos hε.1 hr
  have h2ε : √2 * (S.ε₀ * r) ≤ 1.415 * (S.ε₀ * r) := mul_le_mul_of_nonneg_right hsq.le hεp.le
  have h2θ : √2 * (S.θ * r) ≤ 1.415 * (S.θ * r) := mul_le_mul_of_nonneg_right hsq.le hθp.le
  have hθθ : S.θ ^ 2 * r ≤ (1 / 100) * (S.θ * r) := by
    rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_right hθ1 hθp.le
  have hεr : S.ε₀ * r ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hεs hr.le
  have hθr : S.θ * r ≤ 1 / 100 * r := mul_le_mul_of_nonneg_right hθ1 hr.le
  have hζr' : ζr ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hζs hr.le
  have hYn : ∀ p ∈ Y, r / 3 ≤ ‖p‖ ∧ ‖p‖ ≤ 3 * r := by
    rintro p (hp | hp | hp)
    · obtain ⟨F, hF, hUe⟩ := hsT
      have := norm_bounds_sqTube_m2m2 hεp.le (X := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r})
        (fun q hq => hq) hF (by rw [hUe] at hp; simpa only [Finset.mem_coe] using hp)
      constructor <;> nlinarith [this.1, this.2]
    all_goals
      first
      | (obtain ⟨v, hv, hd⟩ := mem_thickening_iff.1 hp
         have hT := norm_bounds_sqTube_m2m2 hθp.le
           (fun q hq => norm_mem_segment_m2m2 (by linarith)
             (by rwa [mem_sphere, dist_zero_right] at hxs) hq) subset_rfl hv
         rw [dist_eq_norm] at hd
         have h2 := norm_sub_norm_le p v
         have h3 := norm_sub_norm_le v p
         rw [norm_sub_rev] at h3
         constructor <;> nlinarith [hT.1, hT.2])
      | (obtain ⟨v, hv, hd⟩ := mem_thickening_iff.1 hp
         have hT := norm_bounds_sqTube_m2m2 hθp.le
           (fun q hq => norm_mem_segment_m2m2 (by linarith)
             (by rwa [mem_sphere, dist_zero_right] at hys) hq) subset_rfl hv
         rw [dist_eq_norm] at hd
         have h2 := norm_sub_norm_le p v
         have h3 := norm_sub_norm_le v p
         rw [norm_sub_rev] at h3
         constructor <;> nlinarith [hT.1, hT.2])
  -- points in the band `ζr ≤ dist(·, Y) ≤ 2ζr`
  have hband : ∀ q : ℂ, ζr ≤ infDist q Y → infDist q Y ≤ 2 * ζr →
      q ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ) \ (thickening ζr (U x y) ∪ Wc) := by
    intro q h1 h2
    refine ⟨?_, ?_⟩
    · obtain ⟨p, hp, hd⟩ := (infDist_lt_iff hYne).1 (show infDist q Y < 3 * ζr by linarith)
      rw [dist_eq_norm] at hd
      have := hYn p hp
      have h4 := norm_sub_norm_le q p
      have h5 := norm_sub_norm_le p q
      rw [norm_sub_rev] at h5
      show r / 4 < ‖q - 0‖ ∧ ‖q - 0‖ < 4 * r
      rw [sub_zero]; constructor <;> nlinarith [this.1, this.2]
    · rintro (hq | hq)
      · have := (mem_thickening_iff_infDist_lt hUne).1 hq
        have := infDist_le_infDist_of_subset (x := q) (subset_union_left (t := Wc)) hUne
        linarith
      · have := infDist_zero_of_mem (x := q) (show q ∈ Y from Or.inr hq)
        linarith
  have hnear : infDist (Qφ τ') Y ≤ ζr := by
    rcases hK with hq | hq
    · have := (mem_thickening_iff_infDist_lt hUne).1 hq
      have := infDist_le_infDist_of_subset (x := Qφ τ') (subset_union_left (t := Wc)) hUne
      linarith
    · rw [infDist_zero_of_mem (show Qφ τ' ∈ Y from Or.inr hq)]; exact hζr.le
  intro τ hout
  by_contra hfar
  push_neg at hfar
  set P : ℝ → ℂ := fun γ => Qφ (projIcc 0 1 zero_le_one γ) with hP
  have hPc : Continuous P := Qφ.continuous.comp continuous_projIcc
  have hPt : ∀ σ : unitInterval, P σ = Qφ σ := fun σ => by
    show Qφ (projIcc 0 1 zero_le_one (σ : ℝ)) = Qφ σ; rw [projIcc_val]
  -- the final step, for a crossing `[α, β] ⊆ [a, b]`
  have final : ∀ a b : unitInterval, a ≤ b →
      ((D g).1 (z, x') ≤ (D g).1 (z, Qφ a) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ a)) →
      ((D g).1 (z, x') ≤ (D g).1 (z, Qφ b) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ b)) →
      ∀ α β : ℝ, (a : ℝ) ≤ α → α ≤ β → β ≤ b → ζr ≤ ‖P α - P β‖ →
      (∀ γ ∈ Icc α β, ζr ≤ infDist (P γ) Y ∧ infDist (P γ) Y ≤ 2 * ζr) → False := by
    intro a b hab ha hb α β haα hαβ hβb hn hγ
    have hα01 : α ∈ Icc (0 : ℝ) 1 := ⟨a.2.1.trans haα, hαβ.trans (hβb.trans b.2.2)⟩
    have hβ01 : β ∈ Icc (0 : ℝ) 1 := ⟨a.2.1.trans (haα.trans hαβ), hβb.trans b.2.2⟩
    have := gm_L5_14_across hS' hr hcr hU hB hg hx' hy' hsep hlen hW hQφ hab ha hb ⟨α, hα01⟩ ⟨haα, hαβ.trans hβb⟩ ⟨β, hβ01⟩ ⟨haα.trans hαβ, hβb⟩ hαβ
      (fun σ hσ => by
        have h := hγ σ ⟨hσ.1, hσ.2⟩
        rw [hPt] at h
        exact hband _ h.1 h.2)
    have e1 : P α = Qφ ⟨α, hα01⟩ := by
      show Qφ (projIcc 0 1 zero_le_one α) = _; rw [projIcc_of_mem _ hα01]
    have e2 : P β = Qφ ⟨β, hβ01⟩ := by
      show Qφ (projIcc 0 1 zero_le_one β) = _; rw [projIcc_of_mem _ hβ01]
    rw [e1, e2] at hn
    linarith
  rcases le_total τ' τ with h | h
  · obtain ⟨α, β, h1, h2, h3, h4, h5⟩ := exists_cross_m2m2 (P := P) (a := τ') (b := τ) h
      hPc.continuousOn hζr (by rw [hPt]; exact hnear) (by rw [hPt]; have hζdef : ζr = S.ζ * r := rfl; rw [hζdef]; linarith)
    exact final τ' τ h hout' hout α β h1 h2 h3 h4 h5
  · obtain ⟨α, β, h1, h2, h3, h4, h5⟩ := exists_cross_m2m2 (P := fun γ => P (-γ))
      (a := -(τ' : ℝ)) (b := -(τ : ℝ)) (neg_le_neg h)
      (hPc.comp continuous_neg).continuousOn hζr (by simp only [neg_neg]; rw [hPt]; exact hnear)
      (show 2 * ζr ≤ infDist (P (-(-(τ : ℝ)))) Y by
        rw [neg_neg, hPt]; have hζdef : ζr = S.ζ * r := rfl; rw [hζdef]; linarith)
    refine final τ τ' h hout hout' (-β) (-α) (by linarith) (by linarith) (by linarith) ?_ ?_
    · rw [norm_sub_rev]; simpa only using h4
    · intro γ hγ
      have := h5 (-γ) ⟨by linarith [hγ.2], by linarith [hγ.1]⟩
      simpa only [neg_neg] using this

end LQGMetric.GM
