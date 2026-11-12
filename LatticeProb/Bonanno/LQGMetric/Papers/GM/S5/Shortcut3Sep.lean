/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut3Sep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut3Win

/-!
# GM Lemma 5.11, entry step: the two sides of `(U ∪ 𝒲) ∖ O_u` are separated (D83 (c))

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M3, decision D83 packet P2, step 4 of `decisions/DEC-83.md` §3).

GM (l. 3480–3483): "the connected component of `(U ∪ 𝒲) ∖ O_u` containing `𝕩'` lies at distance
`≥ ε₀r` from the other components". With `C_𝕩` the component of `𝕩` in `U ∖ O_u` and
`R = (U ∖ O_u) ∖ C_𝕩`, `sep_sides_m2m3` shows that `C_𝕩 ∪ 𝒲^𝕩` and `R ∪ 𝒲^𝕪` are `5ζr` apart, from
condition (2) of Lemma 5.8 (`SepFrom`), the local attachment (T5) of `U` at `𝕩`, `𝕪` (D83 (c)), and
the geometry of the tubes `W_r^𝕩`, `W_r^𝕪` (`norm_sub_le_scale_m2m3`). Own elementary argument
following D83 (c).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the numerical consequences of `S.Ranges` used below -/
lemma ranges_small_m2m3 {S : EData} (hS : S.Ranges) :
    0 < S.θ ∧ S.θ ≤ S.ζ / 100 ∧ 0 < S.ζ ∧ S.ζ ≤ S.ε₀ / 100 ∧ S.ζ ≤ S.δ / 100 ∧
      0 < S.ε₀ ∧ S.ε₀ ≤ 1 / 10000 ∧ 0 < S.ρ ∧ S.ρ ≤ 1 / 100 := by
  obtain ⟨-, -, hb, hρ, hε, -, hζ, -, hθ, -, -, -, hζδ⟩ := hS
  exact ⟨hθ.1, hθ.2.le, hζ.1, hζ.2.le, hζδ.le, hε.1, by linarith [hε.2, hb.2], hρ.1, hρ.2.le⟩

/-- a point of `U` within `5ζr` of `B_{θ²r}(W_r^e)` lies within `4ε₀r` of `e` -/
lemma near_end_m2m3 {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r) {V : Set ℂ}
    (hsT : IsSquareTube V (S.ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) {e s w : ℂ}
    (he : ‖e‖ = 2 * r) (hs : s ∈ V) (hw : w ∈ thickening (S.θ ^ 2 * r) (lineTube S.θ r e))
    (hd : dist s w < 5 * S.ζ * r) : ‖s - e‖ < 4 * S.ε₀ * r := by
  obtain ⟨hθ0, hθζ, hζ0, hζε, -, hε0, hεs, -, -⟩ := ranges_small_m2m3 hS
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
  obtain ⟨c, hc1, hc2, hwc⟩ := lineTube_near_m2m3 hθ0.le (by linarith) hr.le hw
  obtain ⟨F, hF, hUe⟩ := hsT
  have hsn := (norm_bounds_sqTube_m2m2 hεp.le (X := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r})
    (fun q hq => hq) hF (by rw [hUe] at hs; simpa only [Finset.mem_coe] using hs)).2
  have hce : ‖(c : ℂ) * e‖ = c * (2 * r) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), he]
  rw [dist_eq_norm] at hd
  by_cases hc : 1 + S.ε₀ ≤ c
  · exfalso
    have h1 : ‖(c : ℂ) * e‖ ≤ ‖(c : ℂ) * e - w‖ + ‖w - s‖ + ‖s‖ := by
      calc ‖(c : ℂ) * e‖ = ‖((c : ℂ) * e - w) + (w - s) + s‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    rw [norm_sub_rev ((c : ℂ) * e) w, norm_sub_rev w s, hce] at h1
    nlinarith
  · push_neg at hc
    have hce' : ‖(c : ℂ) * e - e‖ = (c - 1) * (2 * r) := by
      have : (c : ℂ) * e - e = ((c - 1 : ℝ) : ℂ) * e := by push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), he]
    have h1 : ‖s - e‖ ≤ ‖s - w‖ + ‖w - (c : ℂ) * e‖ + ‖(c : ℂ) * e - e‖ := by
      calc ‖s - e‖ = ‖(s - w) + (w - (c : ℂ) * e) + ((c : ℂ) * e - e)‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    rw [hce'] at h1
    nlinarith

/-- **the two sides are separated** (GM l. 3480–3483, D83 (c)): `C_𝕩 ∪ B_{θ²r}(W^𝕩)` and
`((U ∖ O) ∖ C_𝕩) ∪ B_{θ²r}(W^𝕪)` are at distance `≥ 5ζr`. -/
theorem sep_sides_m2m3 {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r) {V O : Set ℂ}
    (hsT : IsSquareTube V (S.ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) {x y u : ℂ}
    (hxn : ‖x‖ = 2 * r) (hyn : ‖y‖ = 2 * r) (hxy : S.δ * r ≤ ‖x - y‖) (hxV : x ∈ V)
    (hyV : y ∈ V) (hO : O ⊆ ball u (20 * S.ε₀ * r)) (hu : ‖u‖ < (1 + 4 * S.ρ) * r)
    (hTx : V ∩ ball x (4 * S.ε₀ * r) ⊆ connectedComponentIn (V ∩ ball x (5 * S.ε₀ * r)) x)
    (hTy : V ∩ ball y (4 * S.ε₀ * r) ⊆ connectedComponentIn (V ∩ ball y (5 * S.ε₀ * r)) y)
    (hsep : SepFrom V O x (S.ε₀ * r)) (hyC : y ∉ connectedComponentIn (V \ O) x) :
    ∀ p ∈ connectedComponentIn (V \ O) x ∪ thickening (S.θ ^ 2 * r) (lineTube S.θ r x),
    ∀ q ∈ ((V \ O) \ connectedComponentIn (V \ O) x) ∪
      thickening (S.θ ^ 2 * r) (lineTube S.θ r y), 5 * S.ζ * r ≤ dist p q := by
  have hS' := hS
  obtain ⟨hθ0, hθζ, hζ0, hζε, hζδ, hε0, hεs, hρ0, hρs⟩ := ranges_small_m2m3 hS
  have hεp : 0 < S.ε₀ * r := mul_pos hε0 hr
  have hζεr : S.ζ * r ≤ S.ε₀ / 100 * r := mul_le_mul_of_nonneg_right hζε hr.le
  have hζδr : S.ζ * r ≤ S.δ / 100 * r := mul_le_mul_of_nonneg_right hζδ hr.le
  have hεr : S.ε₀ * r ≤ 1 / 10000 * r := mul_le_mul_of_nonneg_right hεs hr.le
  have hρr : S.ρ * r ≤ 1 / 100 * r := mul_le_mul_of_nonneg_right hρs hr.le
  -- `O` is far from `x` and `y`
  have hOfar : ∀ e : ℂ, ‖e‖ = 2 * r → ∀ o ∈ O, 5 * S.ε₀ * r ≤ ‖o - e‖ := by
    intro e he o ho
    have h1 := hO ho
    rw [mem_ball, dist_eq_norm] at h1
    have h2 : ‖e‖ ≤ ‖e - o‖ + ‖o - u‖ + ‖u‖ := by
      calc ‖e‖ = ‖(e - o) + (o - u) + u‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    rw [norm_sub_rev e o] at h2
    nlinarith
  -- (T5): points of `U` near `e ∈ {x, y}` lie in the component of `e` in `U ∖ O`
  have hT : ∀ e : ℂ, ‖e‖ = 2 * r → e ∈ V →
      V ∩ ball e (4 * S.ε₀ * r) ⊆ connectedComponentIn (V ∩ ball e (5 * S.ε₀ * r)) e →
      V ∩ ball e (4 * S.ε₀ * r) ⊆ connectedComponentIn (V \ O) e := by
    intro e he heV hTe s hs
    have he5 : e ∈ V ∩ ball e (5 * S.ε₀ * r) := ⟨heV, mem_ball_self (by positivity)⟩
    refine (IsPreconnected.subset_connectedComponentIn (F := V \ O)
      (isPreconnected_connectedComponentIn (F := V ∩ ball e (5 * S.ε₀ * r)) (x := e))
      (mem_connectedComponentIn he5)
      ((connectedComponentIn_subset _ _).trans fun q hq => ⟨hq.1, fun hqO => ?_⟩)) (hTe hs)
    have := hOfar e he q hqO
    have h2 := hq.2
    rw [mem_ball, dist_eq_norm] at h2
    linarith
  have hTx' := hT x hxn hxV hTx
  have hTy' := hT y hyn hyV hTy
  have hyO : y ∈ V \ O := ⟨hyV, fun h => by have := hOfar y hyn y h; simp at this; linarith⟩
  -- the components of `x` and `y` are disjoint
  have hdisj : ∀ s, s ∈ connectedComponentIn (V \ O) x → s ∉ connectedComponentIn (V \ O) y := by
    intro s hsx hsy
    rw [connectedComponentIn_eq hsx, ← connectedComponentIn_eq hsy] at hyC
    exact hyC (mem_connectedComponentIn hyO)
  intro p hp q hq
  by_contra hlt
  push_neg at hlt
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · -- `C_𝕩` and `R`: condition (2)
    have := hsep p hp q hq.1 hq.2
    linarith
  · -- `C_𝕩` and `W^𝕪`: (T5) at `𝕪`
    have hpV : p ∈ V := (connectedComponentIn_subset _ _ hp).1
    have h := near_end_m2m3 hS' hr hsT hyn hpV hq hlt
    exact hdisj p hp (hTy' ⟨hpV, by rw [mem_ball, dist_eq_norm]; exact h⟩)
  · -- `W^𝕩` and `R`: (T5) at `𝕩`
    have h := near_end_m2m3 hS' hr hsT hxn hq.1.1 hp (by rwa [dist_comm])
    exact hq.2 (hTx' ⟨hq.1.1, by rw [mem_ball, dist_eq_norm]; exact h⟩)
  · -- the two tubes
    have hsq : √2 < 1.415 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hθp : 0 < S.θ * r := mul_pos hθ0 hr
    have h2θ : √2 * (S.θ * r) ≤ 1.415 * (S.θ * r) := mul_le_mul_of_nonneg_right hsq.le hθp.le
    have hθ1 : S.θ ≤ 1 / 100 := by linarith
    have hθθ : S.θ ^ 2 * r ≤ (1 / 100) * (S.θ * r) := by
      rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_right hθ1 hθp.le
    have hθζr : S.θ * r ≤ S.ζ / 100 * r := mul_le_mul_of_nonneg_right hθζ hr.le
    obtain ⟨c, hc1, -, hpc⟩ := lineTube_near_m2m3 hθ0.le (by linarith) hr.le hp
    obtain ⟨c', hc1', -, hqc⟩ := lineTube_near_m2m3 hθ0.le (by linarith) hr.le hq
    have h1 := norm_sub_le_scale_m2m3 (by rw [hxn, hyn]) hc1 hc1' (x := x) (y := y)
    have h2 : ‖(c : ℂ) * x - (c' : ℂ) * y‖ ≤ ‖(c : ℂ) * x - p‖ + ‖p - q‖ + ‖q - (c' : ℂ) * y‖ := by
      calc ‖(c : ℂ) * x - (c' : ℂ) * y‖ = ‖((c : ℂ) * x - p) + (p - q) + (q - (c' : ℂ) * y)‖ := by
            ring_nf
        _ ≤ _ := norm_add₃_le
    rw [norm_sub_rev _ p, ← dist_eq_norm p q] at h2
    nlinarith

end LQGMetric.GM
