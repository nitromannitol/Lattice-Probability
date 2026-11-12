/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut3Win at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut3Tip

/-!
# GM Lemma 5.11, entry step: elementary tools (decision D83, steps 4–5)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M3). Own elementary arguments for facts GM uses tacitly at l. 3477–3486:

* `norm_sub_le_scale_m2m3`: `|𝕩 − 𝕪| ≤ |λ𝕩 − μ𝕪|` for `|𝕩| = |𝕪|`, `λ, μ ≥ 1` (the tubes `W^𝕩`,
  `W^𝕪` stay `≈ δr` apart);
* `lineTube_near_m2m3`: a point of `B_{θ²r}(W_r^𝕩)` is within `θ²r + √2θr` of some `c𝕩`,
  `c ∈ [1, 3/2]`;
* `window_m2m3`: a path from near `A` to near `B` (`A`, `B` more than `2d` apart) has a window
  `(σ₁, σ₂)` during which it is `d`-far from both.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `|x − y| ≤ |λx − μy|` if `|x| = |y|` and `λ, μ ≥ 1` -/
lemma norm_sub_le_scale_m2m3 {x y : ℂ} (hxy : ‖x‖ = ‖y‖) {l m : ℝ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    ‖x - y‖ ≤ ‖(l : ℂ) * x - (m : ℂ) * y‖ := by
  have e : (l : ℂ) * x - (m : ℂ) * y = l • x - m • y := by simp [Complex.real_smul]
  rw [e]
  have h1 := norm_sub_sq_real x y
  have h2 := norm_sub_sq_real (l • x) (m • y)
  rw [norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h2
  have hk : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  rw [← hxy] at h1 h2 hk
  have hsq : ‖x - y‖ ^ 2 ≤ ‖l • x - m • y‖ ^ 2 := by
    rw [h1, h2]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 hm)) (sub_nonneg.2 hk),
      sq_nonneg ((l - m) * ‖x‖), mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 hk),
      mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hk)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- a point of `B_{θ²r}(W_r^𝕩)` is within `θ²r + √2θr` of a point `c𝕩`, `c ∈ [1, 3/2]` -/
lemma lineTube_near_m2m3 {θ r : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hr : 0 ≤ r) {x p : ℂ}
    (hp : p ∈ thickening (θ ^ 2 * r) (lineTube θ r x)) :
    ∃ c : ℝ, 1 ≤ c ∧ c ≤ 3 / 2 ∧ ‖p - (c : ℂ) * x‖ < θ ^ 2 * r + √2 * (θ * r) := by
  obtain ⟨v, hv, hpv⟩ := mem_thickening_iff.1 hp
  rw [dist_eq_norm] at hpv
  have hv' := interior_subset hv
  simp only [mem_iUnion] at hv'
  obtain ⟨m, hm, hvm⟩ := hv'
  obtain ⟨s, hsm, hsX⟩ := hm
  have h1 := norm_sub_le_of_gridSquare_m2m2 (mul_nonneg hθ0 hr) hvm hsm
  rw [segment_eq_image] at hsX
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hsX
  refine ⟨(1 - t) + t * (3 / 2 - θ), by nlinarith, by nlinarith, ?_⟩
  have he : (1 - t) • x + t • (((3 / 2 - θ : ℝ) : ℂ) * x) =
      (((1 - t) + t * (3 / 2 - θ) : ℝ) : ℂ) * x := by
    simp only [Complex.real_smul]; push_cast; ring
  simp only at h1
  rw [he] at h1
  calc ‖p - _‖ ≤ ‖p - v‖ + ‖v - _‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < _ := by linarith

/-- **the crossing window**: a path from `d`-near `A` to `d`-near `B`, where `A` and `B` are
`D₀ > 2d` apart, has times `σ₁ < σ₂` with `P(σ₁)` `d`-near `A`, `P(σ₂)` `d`-near `B` and `P`
`d`-far from both on `(σ₁, σ₂)` -/
lemma window_m2m3 {P : ℝ → ℂ} (hP : Continuous P) {a b d D₀ : ℝ} (hab : a ≤ b) {A B : Set ℂ}
    (hA : A.Nonempty) (hBne : B.Nonempty) (hD : 2 * d < D₀) (hsep : ∀ p ∈ A, ∀ q ∈ B, D₀ ≤ dist p q)
    (ha : infDist (P a) A ≤ d) (hb : infDist (P b) B ≤ d) :
    ∃ σ₁ σ₂ : ℝ, a ≤ σ₁ ∧ σ₁ < σ₂ ∧ σ₂ ≤ b ∧ infDist (P σ₁) A ≤ d ∧ infDist (P σ₂) B ≤ d ∧
      ∀ τ ∈ Ioo σ₁ σ₂, d < infDist (P τ) A ∧ d < infDist (P τ) B := by
  -- no point is `d`-near both sets
  have both : ∀ q : ℂ, infDist q A ≤ d → infDist q B ≤ d → False := by
    intro q h1 h2
    set κ := (D₀ - 2 * d) / 2 with hκ
    have hκ0 : 0 < κ := by rw [hκ]; linarith
    obtain ⟨p, hp, hqp⟩ := (infDist_lt_iff hA).1 (show infDist q A < d + κ by linarith)
    obtain ⟨p', hp', hqp'⟩ := (infDist_lt_iff hBne).1 (show infDist q B < d + κ by linarith)
    have := hsep p hp p' hp'
    have := dist_triangle_left p p' q
    linarith
  have hcB : Continuous fun τ => infDist (P τ) B := (continuous_infDist_pt B).comp hP
  have hcA : Continuous fun τ => infDist (P τ) A := (continuous_infDist_pt A).comp hP
  set T : Set ℝ := Icc a b ∩ {τ | infDist (P τ) B ≤ d} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le hcB continuous_const)
  have hTb : BddBelow T := ⟨a, fun t ht => ht.1.1⟩
  have hTne : T.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hb⟩
  set σ₂ := sInf T with hσ₂
  have hσ₂T : σ₂ ∈ T := hTc.csInf_mem hTne hTb
  have haT : a ∉ T := fun h => both _ ha h.2
  have hσ₂a : a < σ₂ := lt_of_le_of_ne hσ₂T.1.1 (fun h => haT (h ▸ hσ₂T))
  set T' : Set ℝ := Icc a σ₂ ∩ {τ | infDist (P τ) A ≤ d} with hT'
  have hT'c : IsClosed T' := isClosed_Icc.inter (isClosed_le hcA continuous_const)
  have hT'b : BddAbove T' := ⟨σ₂, fun t ht => ht.1.2⟩
  have hT'ne : T'.Nonempty := ⟨a, ⟨le_rfl, hσ₂a.le⟩, ha⟩
  set σ₁ := sSup T' with hσ₁
  have hσ₁T : σ₁ ∈ T' := hT'c.csSup_mem hT'ne hT'b
  have hσ₁₂ : σ₁ < σ₂ := lt_of_le_of_ne hσ₁T.1.2 (fun h => both _ hσ₁T.2 (h ▸ hσ₂T.2))
  refine ⟨σ₁, σ₂, hσ₁T.1.1, hσ₁₂, hσ₂T.1.2, hσ₁T.2, hσ₂T.2, fun τ hτ => ⟨?_, ?_⟩⟩
  · by_contra h
    push_neg at h
    have := le_csSup hT'b ⟨⟨hσ₁T.1.1.trans hτ.1.le, hτ.2.le⟩, h⟩
    linarith [hτ.1]
  · by_contra h
    push_neg at h
    have := csInf_le hTb ⟨⟨hσ₁T.1.1.trans hτ.1.le, hτ.2.le.trans hσ₂T.1.2⟩, h⟩
    linarith [hτ.2]

end LQGMetric.GM
