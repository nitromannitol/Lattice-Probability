/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut3Entry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut3Visit
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut3L511

/-!
# GM Lemma 5.11: the entry step and the assembly (decision D83, packets P2, P3)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M3).

* `gm_entry_step` (GM l. 3477–3489, repaired as in decision D83 (a)–(c)): on `E_r`, the
  `D_{h−φ}`-geodesic `P^φ` visits `O_u` and `O_v`, one strictly before the other. Steps: the
  hitting times `τ₁ < τ₂` of `cl B_{3r}(0)` near `𝕩'`, `𝕪'` (`gm_entry_hits`); the sides
  `C_𝕩 ∪ 𝒲^𝕩`, `((U ∖ O_u) ∖ C_𝕩) ∪ 𝒲^𝕪` (`sep_sides_m2m3`); the visit (`entry_visit_m2m3`); the same
  with `(u, 𝕩) ↔ (v, 𝕪)`; `O_u ∩ O_v = ∅` since `|u − v| ≥ br > 40ε₀r`.
* `gm_L5_11 : L5_11` from `gm_L5_11_of_entry2` and `gm_entry_step`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- a point of `∂B_{3r}(0)` within `5ζr` of `(3/2)𝕩` and within `2ζr` of `U ∪ 𝒲` is within `2ζr`
of `B_{θ²r}(W^𝕩)` -/
lemma start_near_m2m3 {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r) {V : Set ℂ}
    (hsT : IsSquareTube V (S.ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) (hVne : V.Nonempty)
    {x y q : ℂ} (hxn : ‖x‖ = 2 * r) (hyn : ‖y‖ = 2 * r) (hxy : S.δ * r ≤ ‖x - y‖)
    (hq : ‖q‖ = 3 * r) (hqx : ‖q - (3 / 2 : ℂ) * x‖ < 5 * S.ζ * r)
    (hd : infDist q (V ∪ (thickening (S.θ ^ 2 * r) (lineTube S.θ r x) ∪
      thickening (S.θ ^ 2 * r) (lineTube S.θ r y))) < 2 * S.ζ * r) :
    ∃ p ∈ thickening (S.θ ^ 2 * r) (lineTube S.θ r x), dist q p < 2 * S.ζ * r := by
  obtain ⟨hθ0, hθζ, hζ0, hζε, hζδ, hε0, hεs, -, -⟩ := ranges_small_m2m3 hS
  have hsq : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hθp : 0 < S.θ * r := mul_pos hθ0 hr
  have hεp : 0 < S.ε₀ * r := mul_pos hε0 hr
  have h2ε : √2 * (S.ε₀ * r) ≤ 1.415 * (S.ε₀ * r) := mul_le_mul_of_nonneg_right hsq.le hεp.le
  have h2θ : √2 * (S.θ * r) ≤ 1.415 * (S.θ * r) := mul_le_mul_of_nonneg_right hsq.le hθp.le
  have hθ1 : S.θ ≤ 1 / 100 := by linarith
  have hθθ : S.θ ^ 2 * r ≤ (1 / 100) * (S.θ * r) := by
    rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_right hθ1 hθp.le
  have hθζr : S.θ * r ≤ S.ζ / 100 * r := mul_le_mul_of_nonneg_right hθζ hr.le
  have hζεr : S.ζ * r ≤ S.ε₀ / 100 * r := mul_le_mul_of_nonneg_right hζε hr.le
  have hζδr : S.ζ * r ≤ S.δ / 100 * r := mul_le_mul_of_nonneg_right hζδ hr.le
  have hεr : S.ε₀ * r ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hεs hr.le
  obtain ⟨p, hp, hqp⟩ := (infDist_lt_iff (hVne.mono subset_union_left)).1 hd
  rcases hp with hp | hp | hp
  · exfalso
    obtain ⟨F, hF, hUe⟩ := hsT
    have := norm_bounds_sqTube_m2m2 hεp.le (X := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r})
      (fun q hq => hq) hF (by rw [hUe] at hp; simpa only [Finset.mem_coe] using hp)
    have h4 := norm_le_norm_sub_add q p
    rw [dist_eq_norm] at hqp
    linarith [this.2]
  · exact ⟨p, hp, hqp⟩
  · exfalso
    obtain ⟨c, hc1, -, hpc⟩ := lineTube_near_m2m3 hθ0.le (by linarith) hr.le hp
    have h1 := norm_sub_le_scale_m2m3 (by rw [hxn, hyn]) (show (1 : ℝ) ≤ 3 / 2 by norm_num) hc1
      (x := x) (y := y)
    have h2 : ‖((3 / 2 : ℝ) : ℂ) * x - (c : ℂ) * y‖ ≤
        ‖q - (3 / 2 : ℂ) * x‖ + ‖q - p‖ + ‖p - (c : ℂ) * y‖ := by
      calc ‖((3 / 2 : ℝ) : ℂ) * x - (c : ℂ) * y‖
          = ‖-(q - (3 / 2 : ℂ) * x) + (q - p) + (p - (c : ℂ) * y)‖ := by push_cast; ring_nf
        _ ≤ ‖-(q - (3 / 2 : ℂ) * x)‖ + ‖q - p‖ + ‖p - (c : ℂ) * y‖ := norm_add₃_le
        _ = _ := by rw [norm_neg]
    rw [← dist_eq_norm q p] at h2
    nlinarith

/-- points near `O` (near `u`, `|u| < (1+4ρ)r`) which are near `A₀ ∪ 𝒲^𝕩`, resp. `B₀ ∪ 𝒲^𝕪`, are
near `A₀`, resp. `B₀`; hence they are `> ε₀r/100` apart if `A₀`, `B₀` are `ε₀r` apart -/
lemma hdiam_m2m3 {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r) {O A₀ B₀ : Set ℂ}
    {x y u : ℂ} (hxn : ‖x‖ = 2 * r) (hyn : ‖y‖ = 2 * r) (hOne : O.Nonempty)
    (hO : O ⊆ ball u (20 * S.ε₀ * r)) (hu : ‖u‖ < (1 + 4 * S.ρ) * r) (hAne : A₀.Nonempty)
    (hBne : B₀.Nonempty) (hAB : ∀ a ∈ A₀, ∀ b ∈ B₀, S.ε₀ * r ≤ dist a b) :
    ∀ p q : ℂ, infDist p O ≤ 2 * S.ζ * r → infDist q O ≤ 2 * S.ζ * r →
      infDist p (A₀ ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r x)) ≤ 2 * S.ζ * r →
      infDist q (B₀ ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r y)) ≤ 2 * S.ζ * r →
      S.ε₀ * r / 100 < ‖p - q‖ := by
  obtain ⟨hθ0, hθζ, hζ0, hζε, -, hε0, hεs, hρ0, hρs⟩ := ranges_small_m2m3 hS
  have hsq : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hθp : 0 < S.θ * r := mul_pos hθ0 hr
  have hζp : 0 < S.ζ * r := mul_pos hζ0 hr
  have h2θ : √2 * (S.θ * r) ≤ 1.415 * (S.θ * r) := mul_le_mul_of_nonneg_right hsq.le hθp.le
  have hθ1 : S.θ ≤ 1 / 100 := by linarith
  have hθθ : S.θ ^ 2 * r ≤ (1 / 100) * (S.θ * r) := by
    rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_right hθ1 hθp.le
  have hθζr : S.θ * r ≤ S.ζ / 100 * r := mul_le_mul_of_nonneg_right hθζ hr.le
  have hζεr : S.ζ * r ≤ S.ε₀ / 100 * r := mul_le_mul_of_nonneg_right hζε hr.le
  have hεr : S.ε₀ * r ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hεs hr.le
  have hρr : S.ρ * r ≤ 1 / 100 * r := mul_le_mul_of_nonneg_right hρs hr.le
  -- points near `O` have modulus `< 1.1 r`
  have hsmall : ∀ p : ℂ, infDist p O ≤ 2 * S.ζ * r → ‖p‖ < 11 / 10 * r := by
    intro p hp
    obtain ⟨o, ho, hpo⟩ := (infDist_lt_iff hOne).1 (show infDist p O < 3 * S.ζ * r by linarith)
    have h1 := hO ho
    rw [mem_ball, dist_eq_norm] at h1
    rw [dist_eq_norm] at hpo
    have : ‖p‖ ≤ ‖p - o‖ + ‖o - u‖ + ‖u‖ := by
      calc ‖p‖ = ‖(p - o) + (o - u) + u‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    nlinarith
  -- such points are `3ζr`-far from the tubes
  have hfar : ∀ (e p a : ℂ), ‖e‖ = 2 * r → ‖p‖ < 11 / 10 * r →
      a ∈ thickening (S.θ ^ 2 * r) (lineTube S.θ r e) → 3 * S.ζ * r ≤ dist p a := by
    intro e p a he hp ha
    obtain ⟨c, hc1, -, hac⟩ := lineTube_near_m2m3 hθ0.le (by linarith) hr.le ha
    have hce : ‖(c : ℂ) * e‖ = c * (2 * r) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), he]
    have : ‖(c : ℂ) * e‖ ≤ ‖(c : ℂ) * e - a‖ + ‖a - p‖ + ‖p‖ := by
      calc ‖(c : ℂ) * e‖ = ‖((c : ℂ) * e - a) + (a - p) + p‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    rw [norm_sub_rev _ a, hce, norm_sub_rev a p, ← dist_eq_norm p a] at this
    have hc2 : 1 * (2 * r) ≤ c * (2 * r) := mul_le_mul_of_nonneg_right hc1 (by linarith)
    linarith
  intro p q hpO hqO hpA hqB
  have hp := hsmall p hpO
  have hq := hsmall q hqO
  obtain ⟨a, ha, hpa⟩ := (infDist_lt_iff (hAne.mono subset_union_left)).1
    (show infDist p _ < 3 * S.ζ * r by linarith)
  obtain ⟨b, hb, hqb⟩ := (infDist_lt_iff (hBne.mono subset_union_left)).1
    (show infDist q _ < 3 * S.ζ * r by linarith)
  have ha' : a ∈ A₀ := ha.resolve_right fun h => by linarith [hfar x p a hxn hp h]
  have hb' : b ∈ B₀ := hb.resolve_right fun h => by linarith [hfar y q b hyn hq h]
  have h1 := hAB a ha' b hb'
  have h2 := dist_triangle4 a p q b
  rw [dist_comm a p, dist_eq_norm p q] at h2
  linarith

/-- **the entry step of GM Lemma 5.11** (GM l. 3477–3489, decision D83 (a)–(c)): `P^φ` visits
`O_u` and `O_v`, one strictly before the other. -/
theorem gm_entry_step {D D' : DistC → ContMetric} {S : EData} (hS : S.Ranges) {r : ℝ}
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
    {Qφ : C(unitInterval, ℂ)} (hQφ : IsGeod01 (D (subTest g (phiChoice S U fb gb r x' y'))) z w Qφ)
    {u v : ℂ}
    (hu : u ∈ (annulus 0 ((1 - 4 * S.ρ) * r) ((1 + 4 * S.ρ) * r) : Set ℂ) ∩ U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y'))
    (hv : v ∈ (annulus 0 ((1 - 4 * S.ρ) * r) ((1 + 4 * S.ρ) * r) : Set ℂ) ∩ U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y'))
    (huv : S.b * r ≤ ‖u - v‖)
    (h2u : SepDiscNear (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) u
      ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') (S.ε₀ * r))
    (h2v : SepDiscNear (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) v
      ((2 / 3 : ℂ) * y') ((2 / 3 : ℂ) * x') (S.ε₀ * r)) :
    ∃ s t : unitInterval, s < t ∧
      ((Qφ s ∈ nearComp (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) u ∧
        Qφ t ∈ nearComp (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) v) ∨
       (Qφ s ∈ nearComp (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) v ∧
        Qφ t ∈ nearComp (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) u)) := by
  have hS' := hS
  obtain ⟨τ₁, τ₂, h12, hn₁, hn₂, hx₁, hy₂, -, -, hbetw⟩ :=
    gm_entry_hits hS hr hcr hU hB hg hz hw hx' hy' hsep hlen hQ hhit hW hQφ
  have h14 := gm_L5_14a hS hr hcr hU hB hg hz hw hx' hy' hsep hlen hQ hhit hW hQφ
  have hxs : (2 / 3 : ℂ) * x' ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, norm_mul, hx'.1]; norm_num; ring
  have hys : (2 / 3 : ℂ) * y' ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, norm_mul, hy'.1]; norm_num; ring
  have hxn : ‖(2 / 3 : ℂ) * x'‖ = 2 * r := by rwa [mem_sphere_zero_iff_norm] at hxs
  have hyn : ‖(2 / 3 : ℂ) * y'‖ = 2 * r := by rwa [mem_sphere_zero_iff_norm] at hys
  obtain ⟨-, -, -, hsT, hxU, hyU, hTx, hTy⟩ := hU _ hxs _ hys hsep
  have hsep' : S.δ * r ≤ ‖(2 / 3 : ℂ) * y' - (2 / 3 : ℂ) * x'‖ := by rwa [norm_sub_rev]
  have ex : (3 / 2 : ℂ) * ((2 / 3 : ℂ) * x') = x' := by ring
  have ey : (3 / 2 : ℂ) * ((2 / 3 : ℂ) * y') = y' := by ring
  obtain ⟨hθ0, hθζ, hζ0, hζε, -, hε0, hεs, hρ0, hρs⟩ := ranges_small_m2m3 hS
  have hεr : S.ε₀ * r ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hεs hr.le
  have hρr : S.ρ * r ≤ 1 / 100 * r := mul_le_mul_of_nonneg_right hρs hr.le
  have hbε : S.ε₀ * r < S.b / 100 * r := mul_lt_mul_of_pos_right hS.2.2.2.2.1.2 hr
  have hεp : 0 < S.ε₀ * r := mul_pos hε0 hr
  -- the hitting times and the points near the tips
  have hnear : ∀ τ : unitInterval, τ₁ ≤ τ → τ ≤ τ₂ → _ := fun τ h1 h2 => h14 τ (hbetw τ h1 h2)
  obtain ⟨px, hpx, hdx⟩ := start_near_m2m3 hS' hr hsT ⟨_, hxU⟩ hxn hyn hsep hn₁ (by rwa [ex])
    (h14 τ₁ (hbetw τ₁ le_rfl h12.le))
  obtain ⟨py, hpy, hdy⟩ := start_near_m2m3 hS' hr hsT ⟨_, hxU⟩ hyn hxn hsep' hn₂ (by rwa [ey])
    (by rw [union_comm (thickening _ (lineTube S.θ r ((2 / 3 : ℂ) * y')))]
        exact h14 τ₂ (hbetw τ₂ h12.le le_rfl))
  -- the visit of `O_e`, `e ∈ {u, v}`
  have visit : ∀ (e : ℂ) (a b : ℂ), e ∈ (annulus 0 ((1 - 4 * S.ρ) * r) ((1 + 4 * S.ρ) * r) : Set ℂ) ∩
      U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') →
      SepDiscNear (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) e a b (S.ε₀ * r) →
      (a = (2 / 3 : ℂ) * x' ∧ b = (2 / 3 : ℂ) * y' ∨ a = (2 / 3 : ℂ) * y' ∧ b = (2 / 3 : ℂ) * x') →
      ∃ s : unitInterval, τ₁ < s ∧ s < τ₂ ∧
        Qφ s ∈ nearComp (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) (20 * S.ε₀ * r) e := by
    intro e a b he h2e hab
    set V := U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') with hV
    set O := nearComp V (20 * S.ε₀ * r) e with hOdef
    have hO : O ⊆ ball e (20 * S.ε₀ * r) := (connectedComponentIn_subset _ _).trans inter_subset_right
    have he' : ‖e‖ < (1 + 4 * S.ρ) * r := by simpa using he.1.2
    have hOne : O.Nonempty := ⟨e, mem_connectedComponentIn ⟨he.2, mem_ball_self (by positivity)⟩⟩
    have hnotO : ∀ q : ℂ, ‖q‖ = 2 * r → q ∉ O := fun q hq hqO => by
      have h1 := hO hqO
      rw [mem_ball, dist_eq_norm] at h1
      have := norm_sub_norm_le q e
      linarith
    set C := connectedComponentIn (V \ O) a with hC
    have han : ‖a‖ = 2 * r := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hbn : ‖b‖ = 2 * r := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have haV : a ∈ V := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hbV : b ∈ V := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hTa : V ∩ ball a (4 * S.ε₀ * r) ⊆ connectedComponentIn (V ∩ ball a (5 * S.ε₀ * r)) a := by
      rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hTb : V ∩ ball b (4 * S.ε₀ * r) ⊆ connectedComponentIn (V ∩ ball b (5 * S.ε₀ * r)) b := by
      rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have habs : S.δ * r ≤ ‖a - b‖ := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hsepF := h2e.sepFrom
    have hbC := h2e.not_mem_comp
    have hsides := sep_sides_m2m3 hS' hr hsT han hbn habs haV hbV hO he' hTa hTb hsepF hbC
    have haC : a ∈ C := mem_connectedComponentIn ⟨haV, hnotO a han⟩
    have hbR : b ∈ (V \ O) \ C := ⟨⟨hbV, hnotO b hbn⟩, hbC⟩
    have hdiam0 := hdiam_m2m3 hS' hr han hbn hOne hO he' ⟨a, haC⟩ ⟨b, hbR⟩
      (fun p hp q hq => hsepF p hp q hq.1 hq.2)
    have hUAB : V \ O ⊆ (C ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r a)) ∪
        (((V \ O) \ C) ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r b)) := fun p hp => by
      by_cases hpC : p ∈ C
      · exact Or.inl (Or.inl hpC)
      · exact Or.inr (Or.inl ⟨hp, hpC⟩)
    have hAn : (C ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r a)).Nonempty := ⟨a, Or.inl haC⟩
    have hBn : (((V \ O) \ C) ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r b)).Nonempty :=
      ⟨b, Or.inl hbR⟩
    have hsides2 : ∀ p ∈ ((V \ O) \ C) ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r b),
        ∀ q ∈ C ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r a), 5 * S.ζ * r ≤ dist p q :=
      fun p hp q hq => by rw [dist_comm]; exact hsides q hq p hp
    have hUAB2 : V \ O ⊆ (((V \ O) \ C) ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r b)) ∪
        (C ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r a)) := fun p hp => (hUAB hp).symm
    have hdiam2 : ∀ p q : ℂ, infDist p O ≤ 2 * S.ζ * r → infDist q O ≤ 2 * S.ζ * r →
        infDist p (((V \ O) \ C) ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r b)) ≤ 2 * S.ζ * r →
        infDist q (C ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r a)) ≤ 2 * S.ζ * r →
        S.ε₀ * r / 100 < ‖p - q‖ := fun p q h1 h2 h3 h4 => by
      rw [norm_sub_rev]; exact hdiam0 q p h2 h1 h4 h3
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact entry_visit_m2m3 hS' hr hcr hU hB hg hx' hy' hsep hlen hW hQφ h12.le hbetw hnear
        hAn hBn hsides hUAB subset_union_right subset_union_right
        ((infDist_le_dist_of_mem (mem_union_right _ hpx)).trans hdx.le)
        ((infDist_le_dist_of_mem (mem_union_right _ hpy)).trans hdy.le) hdiam0
    · exact entry_visit_m2m3 hS' hr hcr hU hB hg hx' hy' hsep hlen hW hQφ h12.le hbetw hnear
        hBn hAn hsides2 hUAB2 subset_union_right subset_union_right
        ((infDist_le_dist_of_mem (mem_union_right _ hpx)).trans hdx.le)
        ((infDist_le_dist_of_mem (mem_union_right _ hpy)).trans hdy.le) hdiam2
  obtain ⟨s, -, -, hs⟩ := visit u _ _ hu h2u (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨t, -, -, ht⟩ := visit v _ _ hv h2v (Or.inr ⟨rfl, rfl⟩)
  -- `O_u ∩ O_v = ∅`
  have hst : s ≠ t := by
    rintro rfl
    have h1 := (connectedComponentIn_subset _ _ hs).2
    have h2 := (connectedComponentIn_subset _ _ ht).2
    rw [mem_ball, dist_eq_norm] at h1 h2
    have : ‖u - v‖ ≤ ‖Qφ s - u‖ + ‖Qφ s - v‖ := by
      calc ‖u - v‖ = ‖(Qφ s - v) - (Qφ s - u)‖ := by ring_nf
        _ ≤ _ := by rw [add_comm]; exact norm_sub_le _ _
    linarith
  rcases lt_or_gt_of_ne hst with h | h
  · exact ⟨s, t, h, Or.inl ⟨hs, ht⟩⟩
  · exact ⟨t, s, h, Or.inr ⟨ht, hs⟩⟩

/-- **GM Lemma 5.11** (`lem-internal-geo`, l. 3360–3373) -/
theorem gm_L5_11 : L5_11 := by
  intro D D' c₂ S hS hcs hc₁ hc₁₂ hc₂ hηc r hr hcr U fb gb hU hB g z w x' y' Q Qφ hz hw hx' hy'
    φ hlen hlen' hW hW' hbl₀ hbl₁ hQ hhit hg hQφ
  have hz4 : 4 * r ≤ ‖z‖ := by simpa [mem_ball, dist_zero_right] using hz
  have hw4 : 4 * r ≤ ‖w‖ := by simpa [mem_ball, dist_zero_right] using hw
  exact gm_L5_11_of_entry2 S hS hcs hc₁ (hc₁.trans (hc₁₂.trans hc₂)) hηc r hr hcr U fb gb hU hB g z w x' y' Q
    Qφ hz hw hx' hy' hlen hlen' hW hW' hbl₀ hbl₁ hQ hhit hg hQφ
    (fun hsep u v hu hv huv h2u h2v => gm_entry_step hS hr hcr hU hB hg hz4 hw4 hx' hy' hsep hlen
      hQ hhit hW hQφ hu hv huv h2u h2v)

end LQGMetric.GM
