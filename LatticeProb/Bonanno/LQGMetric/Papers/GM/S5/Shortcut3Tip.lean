/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut3Tip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut3Hit
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2L514d

/-!
# GM Lemma 5.11, entry step: the hitting times `τ₁ < τ₂` near `𝕩'` and `𝕪'` (decision D83 (a))

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M3, decision D83 packet P2, steps 1–3 of `decisions/DEC-83.md` §3).

* `near_tip_m2m3`, `hit_near_tip_m2m3`: a point of `∂B_{3r}(0)` within `2ζr` of `U ∪ 𝒲` is within
  `5ζr` of `𝕩' = (3/2)𝕩` or `𝕪' = (3/2)𝕪` (`U ⊂ B_{(2+√2ε₀)r}(0)`; `W_r^𝕩` consists of squares of
  side `θr` meeting `[𝕩, (3/2 − θ)𝕩]`); own elementary geometry.
* `gm_entry_hits`: on `E_r`, the first hitting time `τ₁` and the last hitting time `τ₂` of
  `cl B_{3r}(0)` by `P^φ` satisfy `τ₁ < τ₂`, `|P^φ(τ₁) − 𝕩'| < 5ζr`, `|P^φ(τ₂) − 𝕪'| < 5ζr`, and every
  time in `[τ₁, τ₂]` lies outside both hitting balls (so Lemma 5.14 applies there). This is the
  repair (a) of D83 of GM's tacit assumption (l. 3477–3486) that `P̄^φ` runs from the `𝕩'`-side to
  the `𝕪'`-side.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- a point of `∂B_{3r}(0)` within `d` of a point of `[𝕩, (3/2 − θ)𝕩]` (`|𝕩| = 2r`) is within
`2d` of `(3/2)𝕩` -/
lemma near_tip_m2m3 {θ r d : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) {x q s : ℂ} (hx : ‖x‖ = 2 * r)
    (hq : ‖q‖ = 3 * r) (hs : s ∈ segment ℝ x (((3 / 2 - θ : ℝ) : ℂ) * x)) (hd : ‖q - s‖ ≤ d) :
    ‖q - (3 / 2 : ℂ) * x‖ ≤ 2 * d := by
  rw [segment_eq_image] at hs
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hs
  set c : ℝ := (1 - t) + t * (3 / 2 - θ) with hc
  have he : (1 - t) • x + t • (((3 / 2 - θ : ℝ) : ℂ) * x) = (c : ℂ) * x := by
    simp only [Complex.real_smul, hc]; push_cast; ring
  have hc1 : 1 ≤ c := by nlinarith
  have hc2 : c ≤ 3 / 2 := by nlinarith
  have hr : 0 ≤ r := by have := norm_nonneg x; linarith
  simp only at hd
  rw [he] at hd
  have hn : ‖(c : ℂ) * x‖ = c * (2 * r) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), hx]
  have hn2 : ‖(c : ℂ) * x - (3 / 2 : ℂ) * x‖ = (3 / 2 - c) * (2 * r) := by
    rw [← sub_mul, norm_mul, hx]
    have : (c : ℂ) - 3 / 2 = ((c - 3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
  have h1 : ‖q‖ ≤ ‖q - (c : ℂ) * x‖ + ‖(c : ℂ) * x‖ := norm_le_norm_sub_add q _
  have h2 : ‖q - (3 / 2 : ℂ) * x‖ ≤ ‖q - (c : ℂ) * x‖ + ‖(c : ℂ) * x - (3 / 2 : ℂ) * x‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [hn] at h1
  rw [hn2] at h2
  linarith

/-- **Lemma 5.14 at `∂B_{3r}(0)`**: a point of `∂B_{3r}(0)` within `2ζr` of `U ∪ 𝒲` lies within
`5ζr` of `(3/2)𝕩` or of `(3/2)𝕪` -/
lemma hit_near_tip_m2m3 {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r) {V : Set ℂ}
    (hsT : IsSquareTube V (S.ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) {x y q : ℂ}
    (hVne : V.Nonempty) (hx : ‖x‖ = 2 * r) (hy : ‖y‖ = 2 * r) (hq : ‖q‖ = 3 * r)
    (hd : infDist q (V ∪ (thickening (S.θ ^ 2 * r) (lineTube S.θ r x) ∪
      thickening (S.θ ^ 2 * r) (lineTube S.θ r y))) < 2 * S.ζ * r) :
    ‖q - (3 / 2 : ℂ) * x‖ < 5 * S.ζ * r ∨ ‖q - (3 / 2 : ℂ) * y‖ < 5 * S.ζ * r := by
  obtain ⟨-, -, hb, -, hε, -, hζ, -, hθ, -⟩ := hS
  have hsq : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hθ1 : S.θ ≤ 1 / 100 := by
    have := hθ.2; have := hζ.2; have := hε.2; have := hb.2; linarith
  have hεs : S.ε₀ ≤ 1 / 10000 := by have := hε.2; have := hb.2; linarith
  have hζs : S.ζ ≤ 1 / 10000 := by have := hζ.2; linarith
  have hθp : 0 < S.θ * r := mul_pos hθ.1 hr
  have hεp : 0 < S.ε₀ * r := mul_pos hε.1 hr
  have hζp : 0 < S.ζ * r := mul_pos hζ.1 hr
  have hεr : S.ε₀ * r ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hεs hr.le
  have hζr : S.ζ * r ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hζs hr.le
  have h2ε : √2 * (S.ε₀ * r) ≤ 1.415 * (S.ε₀ * r) := mul_le_mul_of_nonneg_right hsq.le hεp.le
  have h2θ : √2 * (S.θ * r) ≤ 1.415 * (S.θ * r) := mul_le_mul_of_nonneg_right hsq.le hθp.le
  have hθθ : S.θ ^ 2 * r ≤ (1 / 100) * (S.θ * r) := by
    rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_right hθ1 hθp.le
  have hθζ : S.θ * r ≤ S.ζ / 100 * r := mul_le_mul_of_nonneg_right hθ.2.le hr.le
  have hεr : S.ε₀ * r ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hεs hr.le
  have hζr : S.ζ * r ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hζs hr.le
  have hne : (V ∪ (thickening (S.θ ^ 2 * r) (lineTube S.θ r x) ∪
      thickening (S.θ ^ 2 * r) (lineTube S.θ r y))).Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    exact ⟨v, Or.inl hv⟩
  obtain ⟨p, hp, hqp⟩ := (infDist_lt_iff hne).1 hd
  rw [dist_eq_norm] at hqp
  -- the tube case
  have tube : ∀ x₀ : ℂ, ‖x₀‖ = 2 * r → p ∈ thickening (S.θ ^ 2 * r) (lineTube S.θ r x₀) →
      ‖q - (3 / 2 : ℂ) * x₀‖ < 5 * S.ζ * r := by
    intro x₀ hx₀ hp₀
    obtain ⟨v, hv, hpv⟩ := mem_thickening_iff.1 hp₀
    rw [dist_eq_norm] at hpv
    have hv' := interior_subset hv
    simp only [mem_iUnion] at hv'
    obtain ⟨m, hm, hvm⟩ := hv'
    obtain ⟨s, hsm, hsX⟩ := hm
    have h1 := norm_sub_le_of_gridSquare_m2m2 hθp.le hvm hsm
    have h3 : ‖q - s‖ ≤ ‖q - p‖ + ‖p - v‖ + ‖v - s‖ := by
      calc ‖q - s‖ = ‖(q - p) + (p - v) + (v - s)‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    have := near_tip_m2m3 hθ.1.le (by linarith) hx₀ hq hsX
      (d := 2 * S.ζ * r + S.θ ^ 2 * r + √2 * (S.θ * r)) (by linarith)
    linarith
  rcases hp with hp | hp | hp
  · exfalso
    obtain ⟨F, hF, hUe⟩ := hsT
    have := norm_bounds_sqTube_m2m2 hεp.le (X := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r})
      (fun q hq => hq) hF (by rw [hUe] at hp; simpa only [Finset.mem_coe] using hp)
    have h4 := norm_le_norm_sub_add q p
    linarith [this.2]
  · exact Or.inl (tube x hx hp)
  · exact Or.inr (tube y hy hp)

/-- **the hitting times of the entry step** (decision D83 (a), GM l. 3477–3486 repaired): on
`E_r`, `P^φ` has times `τ₁ < τ₂` with `P^φ(τ₁)` within `5ζr` of `𝕩'`, `P^φ(τ₂)` within `5ζr` of
`𝕪'`, both on `∂B_{3r}(0)`, `P^φ` outside `cl B_{3r}(0)` before `τ₁` and after `τ₂`, and every time
of `[τ₁, τ₂]` outside both hitting balls (the hypothesis of Lemma 5.14). -/
theorem gm_entry_hits {D D' : DistC → ContMetric} {S : EData} (hS : S.Ranges) {r : ℝ}
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
    ∃ τ₁ τ₂ : unitInterval, τ₁ < τ₂ ∧ ‖Qφ τ₁‖ = 3 * r ∧ ‖Qφ τ₂‖ = 3 * r ∧
      ‖Qφ τ₁ - x'‖ < 5 * S.ζ * r ∧ ‖Qφ τ₂ - y'‖ < 5 * S.ζ * r ∧
      (∀ τ : unitInterval, τ < τ₁ → 3 * r < ‖Qφ τ‖) ∧
      (∀ τ : unitInterval, τ₂ < τ → 3 * r < ‖Qφ τ‖) ∧
      (∀ τ : unitInterval, τ₁ ≤ τ → τ ≤ τ₂ →
        (D g).1 (z, x') ≤ (D g).1 (z, Qφ τ) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ τ)) := by
  have hS' := hS
  have h14 := gm_L5_14a hS hr hcr hU hB hg hz hw hx' hy' hsep hlen hQ hhit hW hQφ
  have h513 := gm_L5_13 hS hr hcr hU hB hg hx'.1 hy'.1 hsep hW
  set x : ℂ := (2 / 3 : ℂ) * x' with hxdef
  set y : ℂ := (2 / 3 : ℂ) * y' with hydef
  have hxn : ‖x‖ = 2 * r := by rw [hxdef, norm_mul, hx'.1]; norm_num; ring
  have hyn : ‖y‖ = 2 * r := by rw [hydef, norm_mul, hy'.1]; norm_num; ring
  have hxs : x ∈ sphere (0 : ℂ) (2 * r) := by rw [mem_sphere_zero_iff_norm]; exact hxn
  have hys : y ∈ sphere (0 : ℂ) (2 * r) := by rw [mem_sphere_zero_iff_norm]; exact hyn
  have ex : (3 / 2 : ℂ) * x = x' := by rw [hxdef]; ring
  have ey : (3 / 2 : ℂ) * y = y' := by rw [hydef]; ring
  have hφ : phiChoice S U fb gb r x' y' = bumpPhi S U fb gb r x y := by
    unfold phiChoice; rw [ite_eq_left_iff.2 (fun h => absurd hsep h)]
  rw [hφ] at hW hQφ h513
  set φ := bumpPhi S U fb gb r x y with hφdef
  have hξ := hS.1
  have hKf := Kf_pos_m2m hS
  have hKg := Kf_le_Kg_m2m hS
  obtain ⟨hfU0, -, -⟩ := hB.1 x hxs y hys hsep
  obtain ⟨hgx0, -, -⟩ := hB.2 x hxs
  obtain ⟨hgy0, -, -⟩ := hB.2 y hys
  have hφ0 : ∀ q, 0 ≤ φ q := fun q => by
    rw [hφdef, bumpPhi_apply_m2m]
    have := mul_nonneg hKf.le (hfU0 q).1
    have := mul_nonneg (hKf.le.trans hKg) (add_nonneg (hgx0 q).1 (hgy0 q).1)
    linarith
  have hfe : ∀ q, S.ξ * (-testCont φ) q = -(S.ξ * φ q) := fun q => by
    simp only [ContinuousMap.neg_apply, testCont, ContinuousMap.coe_mk]; ring
  have hsupp := bumpFam_tsupport_m2m2 hS hr hU hB φ (Or.inl ⟨x, hxs, y, hys, hsep, rfl⟩)
  have hf0 : ∀ q ∉ closedBall (0 : ℂ) (3 * r), S.ξ * (-testCont φ) q = 0 := fun q hq => by
    rw [hfe]
    by_contra hne
    have hq0 : φ q ≠ 0 := fun h => hne (by rw [h]; ring)
    have := hsupp (subset_tsupport _ (Function.mem_support.2 hq0))
    have h3 : ‖q - 0‖ < 3 * r := this.2
    rw [sub_zero] at h3
    exact hq (by rw [mem_closedBall, dist_zero_right]; exact h3.le)
  have hf : ∀ q, S.ξ * (-testCont φ) q ≤ 0 := fun q => by
    rw [hfe]; have := mul_nonneg hξ.le (hφ0 q); linarith
  -- constants
  set sf := scaleFac S.ξ S.c g r 0 with hsfdef
  have hsf : 0 < sf := mul_pos hcr (Real.exp_pos _)
  obtain ⟨-, hδ, hb, -, hε, hΔ, hζ, ha, -, hA, -, -, hζδ⟩ := hS
  have hΛ : Real.exp (-S.ξ * S.Kf) * (S.A + 4) * sf < S.Δ * sf := by
    rw [exp_Kf_m2m2 hS']
    refine mul_lt_mul_of_pos_right ?_ hsf
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith [mul_pos ha.1 hΔ.1, mul_pos (sub_pos.2 ha.2) hΔ.1]
  have hsetd := (hg.2.1 x hxs x hxs (by rw [sub_self, norm_zero]; exact mul_pos hδ.1 hr)).2
  have hsum := gm_L5_12_sum hr hQ hz hw hx' hy' hhit hsetd
  obtain ⟨-, -, -, hsT, hxU, -⟩ := hU x hxs y hys hsep
  have hζr : 0 < S.ζ * r := mul_pos hζ.1 hr
  have hζδr : S.ζ * r < S.δ / 100 * r := mul_lt_mul_of_pos_right hζδ hr
  -- condition (4) near `x'` and `y'`
  have h4 : ∀ (e : ℂ), e ∈ sphere (0 : ℂ) (2 * r) → ∀ q : ℂ, ‖q‖ = 3 * r →
      ‖q - (3 / 2 : ℂ) * e‖ < 5 * S.ζ * r → (D g).1 (q, (3 / 2 : ℂ) * e) ≤ S.Δ * sf := by
    intro e he q hq hqe
    have hq2 : (2 / 3 : ℂ) * q ∈ sphere (0 : ℂ) (2 * r) := by
      rw [mem_sphere_zero_iff_norm, norm_mul, hq]; norm_num; ring
    have hd : ‖(2 / 3 : ℂ) * q - e‖ < S.δ * r := by
      have : (2 / 3 : ℂ) * q - e = (2 / 3 : ℂ) * (q - (3 / 2 : ℂ) * e) := by ring
      rw [this, norm_mul]; norm_num
      nlinarith
    have h := (hg.2.1 _ hq2 e he hd).1
    rw [show (3 / 2 : ℂ) * ((2 / 3 : ℂ) * q) = q by ring] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_pos hΔ.1 hsf).le).1 ((ofReal_le_internal_m2m _ _ _ _).trans h)
  -- the first hitting time
  obtain ⟨τ₁, hn₁, hnx, hbef, haft⟩ := entry_first_hit_m2m3 hW hlen hf hf0
    (by linarith) hx' hy' hQφ h513 hΛ hsum
    (fun τ hτ h1 h2 => by
      have := hit_near_tip_m2m3 hS' hr hsT ⟨x, hxU⟩ hxn hyn hτ (h14 τ ⟨h1, h2⟩)
      rwa [ex, ey] at this)
    (fun q hq hqy => by have := h4 y hys q hq (by rwa [ey]); rwa [ey] at this)
  -- the last hitting time: the first one of the reversed path
  have hσ : ∀ τ : unitInterval, revPath01 Qφ τ = Qφ (unitInterval.symm τ) := fun τ => rfl
  have hσlt : ∀ a b : unitInterval, a < b → unitInterval.symm b < unitInterval.symm a :=
    fun a b h => by
      have : (a : ℝ) < b := h
      show 1 - (b : ℝ) < 1 - (a : ℝ); linarith
  have hσle : ∀ a b : unitInterval, a ≤ b → unitInterval.symm b ≤ unitInterval.symm a :=
    fun a b h => by
      have : (a : ℝ) ≤ b := h
      show 1 - (b : ℝ) ≤ 1 - (a : ℝ); linarith
  obtain ⟨τ₂', hn₂, hny, hbef₂, haft₂⟩ := entry_first_hit_m2m3 hW hlen hf hf0
    (by linarith) hy' hx' (isGeod01_rev_m2m3 hQφ) (Λ := Real.exp (-S.ξ * S.Kf) * (S.A + 4) * sf)
    (by rw [dist_comm_m2m]; exact h513) hΛ
    (by have := dist_comm_m2m (D g) w z; linarith)
    (fun τ hτ h1 h2 => by
      rw [hσ] at hτ h1 h2 ⊢
      have := hit_near_tip_m2m3 hS' hr hsT ⟨x, hxU⟩ hxn hyn hτ (h14 _ ⟨h2, h1⟩)
      rw [ex, ey] at this
      exact this.symm)
    (fun q hq hqx => by have := h4 x hxs q hq (by rwa [ex]); rwa [ex] at this)
  set τ₂ := unitInterval.symm τ₂' with hτ₂
  have hQτ₂ : revPath01 Qφ τ₂' = Qφ τ₂ := rfl
  rw [hQτ₂] at hn₂ hny
  have h12 : τ₁ ≤ τ₂ := by
    by_contra h
    have := hbef τ₂ (not_le.1 h)
    linarith
  have hne : τ₁ ≠ τ₂ := by
    intro he
    rw [← he] at hny
    have e : x' - y' = (3 / 2 : ℂ) * (x - y) := by rw [← ex, ← ey]; ring
    have h1 : ‖x' - y'‖ ≤ ‖Qφ τ₁ - x'‖ + ‖Qφ τ₁ - y'‖ := by
      calc ‖x' - y'‖ = ‖(Qφ τ₁ - y') - (Qφ τ₁ - x')‖ := by ring_nf
        _ ≤ _ := by rw [add_comm]; exact norm_sub_le _ _
    rw [e, norm_mul] at h1
    norm_num at h1
    nlinarith
  refine ⟨τ₁, τ₂, lt_of_le_of_ne h12 hne, hn₁, hn₂, hnx, hny, hbef, fun τ hτ => ?_,
    fun τ h1 h2 => ⟨haft τ h1, ?_⟩⟩
  · have := hbef₂ _ (show unitInterval.symm τ < τ₂' by
      have := hσlt _ _ hτ; rwa [hτ₂, unitInterval.symm_symm] at this)
    rwa [hσ, unitInterval.symm_symm] at this
  · have := haft₂ _ (show τ₂' ≤ unitInterval.symm τ by
      have := hσle _ _ h2; rwa [hτ₂, unitInterval.symm_symm] at this)
    rwa [hσ, unitInterval.symm_symm] at this

end LQGMetric.GM
