/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2Eq541 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2UV

/-!
# GM §5.5: the bound (5.41) of Lemma 5.15

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

GM l. 3498–3511: from linkEvent (1) (`D̃_h(u,v) ≤ (c_*/C_*)² D̃_h(u, ∂B_{4ρr}(u))`), `φ ≤ K_f` on
`B_{4ρr}(u)` and (5.43), `D̃_{h−φ}(p, q) ≤ (c_*/C_*) D̃_{h−φ}(p, ∂B_{3r}(0))` for `p ∈ O_u`,
`q ∈ O_v` (`gm_eq541`).

**Deviation (own repair of GM's step, proposed DEVIATIONS entry P2-M2M2-2).** GM writes
`(c_*/C_*)² D̃_{h−φ}(u, ∂B_{4ρr}(u)) ≤ (c_*/C_*)² D̃_{h−φ}(P^φ(s), ∂B_{3r}(0))`, which compares
distances from two different points `u` and `p = P^φ(s)`. The triangle inequality gives
`D̃_{h−φ}(p, ∂B_{3r}(0)) ≥ D̃_{h−φ}(u, ∂B_{4ρr}(u)) − η D̃_{h−φ}(u,v)`, and then (5.41) follows
when `(1 + 3η) c_*/C_* ≤ 1`, i.e. `1 + 3η ≤ C_*/c_*` (hypothesis `hη3`). GM's (5.15) only has
`1 + 2η < C_*/c_*`; `η` is GM's "small" constant, so `1 + 3η ≤ C_*/c_*` is the same kind of choice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric EMetric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- in a length metric, a lower bound `m` for `d(u, ·)` on `∂B_R(u)` holds outside `B_R(u)` -/
lemma le_of_sphere_out_m2m2 {D : ContMetric} (hlen : D.IsLength) {u : ℂ} {R m : ℝ} (hR : 0 < R)
    (hsph : ∀ q ∈ sphere u R, m ≤ D.1 (u, q)) {w : ℂ} (hw : R ≤ ‖w - u‖) : m ≤ D.1 (u, w) := by
  by_contra h
  push_neg at h
  obtain ⟨q, hq, hq'⟩ := DFGPS.P43.exists_sphere_lt' (z₀ := u) hlen hw
    (show ‖u - u‖ ≤ R by simpa using hR.le) h
  exact absurd (hsph q hq) (not_le.2 hq')

/-- `e^a m ≤ (e^{ξ f}·d)(u,v)` when `ξ f ≥ a` on `B_R(u)`, `m ≤ d(u, ·)` on `∂B_R(u)` and
`m ≤ d(u, v)` (`d` a length metric) -/
lemma weyl_ge_of_sphere_m2m2' {D D' : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y) (hlen : D.IsLength)
    {u v : ℂ} {R a m : ℝ} (hR : 0 < R) (ha : ∀ x ∈ ball u R, a ≤ ξ * f x)
    (hsph : ∀ q ∈ sphere u R, m ≤ D.1 (u, q)) (hm : m ≤ D.1 (u, v)) :
    Real.exp a * m ≤ D'.1 (u, v) := by
  by_contra hlt
  push_neg at hlt
  have hV : IsOpen (ball u R) := isOpen_ball
  have hD0 : 0 ≤ D'.1 (u, v) := nonneg_m2m D' u v
  have hm0 : 0 < m := by
    have := hD0.trans_lt hlt
    exact pos_of_mul_pos_right this (Real.exp_pos a).le
  have hinf : ENNReal.ofReal m ≤ infEDist (D.pt u) (D.pt '' (ball u R)ᶜ) := by
    refine le_infEDist.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (show m ≤ D.1 (u, w) from le_of_sphere_out_m2m2 (w := w) hlen
      hR hsph (show R ≤ ‖w - u‖ by simpa [mem_ball, dist_eq_norm] using hw))
  have hglob : weylScale ξ f D u v <
      ENNReal.ofReal (Real.exp a) * infEDist (D.pt u) (D.pt '' (ball u R)ᶜ) := by
    rw [← hD']
    calc ENNReal.ofReal (D'.1 (u, v)) < ENNReal.ofReal (Real.exp a * m) :=
          (ENNReal.ofReal_lt_ofReal_iff (hD0.trans_lt hlt)).2 hlt
      _ = ENNReal.ofReal (Real.exp a) * ENNReal.ofReal m :=
          ENNReal.ofReal_mul (Real.exp_pos a).le
      _ ≤ _ := by gcongr
  have h1 := weylScaleOn_le_weylScale_of_lt (U := ball u R) hV subset_rfl ha hglob
  have h2 : ENNReal.ofReal (Real.exp a) * D.internal (ball u R) u v ≤
      weylScaleOn ξ f D (ball u R) u v := le_weylScaleOn_of_le ha
  have h3 : ENNReal.ofReal m ≤ D.internal (ball u R) u v :=
    (ENNReal.ofReal_le_ofReal hm).trans (ofReal_le_internal_m2m D (ball u R) u v)
  have h4 : ENNReal.ofReal (Real.exp a * m) ≤ ENNReal.ofReal (D'.1 (u, v)) := by
    rw [hD', ENNReal.ofReal_mul (Real.exp_pos a).le]
    exact (by gcongr : _ ≤ ENNReal.ofReal (Real.exp a) * D.internal (ball u R) u v).trans
      (h2.trans h1)
  exact absurd ((ENNReal.ofReal_le_ofReal_iff hD0).1 h4) (not_le.2 hlt)

/-- **GM (5.41)** (l. 3498–3511), with the repair `hη3` (see the module docstring): for
`p ∈ O_u`, `q ∈ O_v`, `D̃_{h−φ}(p,q) ≤ (c_*/C_*) D̃_{h−φ}(p, ∂B_{3r}(0))`. Here `e₀ = D̃_h`,
`e₁ = D̃_{h−φ} = e^{ξ f}·e₀`, `R = 4ρr`, `S = ∂B_{3r}(0)` lies outside `B_R(u)`. -/
theorem gm_eq541 {e₀ e₁ : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (he : ∀ x y : ℂ, ENNReal.ofReal (e₁.1 (x, y)) = weylScale ξ f e₀ x y)
    (hlen : e₀.IsLength) {cs Cs η : ℝ} (hcs : 0 < cs) (hcC : cs < Cs) (hη0 : 0 ≤ η)
    (hη3 : 1 + 3 * η ≤ Cs / cs) {U S : Set ℂ} (hUo : IsOpen U) {u v p q : ℂ} {R K : ℝ}
    (hR : 0 < R) (huv : u ≠ v) (hS : ∀ y ∈ S, R ≤ ‖y - u‖)
    (hsd : ENNReal.ofReal (e₀.1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist e₀ {u} (sphere u R))
    (hgeo : UniqueGeodIn e₀ u v U)
    (hp : e₀.internal U u p ≤ ENNReal.ofReal (η * e₀.1 (u, v)))
    (hq : e₀.internal U v q ≤ ENNReal.ofReal (η * e₀.1 (u, v)))
    (hball : ∀ x ∈ ball u R, -ξ * K ≤ ξ * f x) (hU : ∀ x ∈ U, ξ * f x ≤ -ξ * K) :
    ENNReal.ofReal (e₁.1 (p, q)) ≤ ENNReal.ofReal (cs / Cs) * setDist e₁ {p} S := by
  have hC : 0 < Cs := hcs.trans hcC
  set t := cs / Cs with ht
  have ht0 : 0 < t := div_pos hcs hC
  have ht1 : t < 1 := (div_lt_one hC).2 hcC
  have hκ0 : 0 < t ^ 2 := by positivity
  have hκ1 : t ^ 2 < 1 := by nlinarith
  have hsph := le_sphere_of_setDist_m2m2 hκ0.le hsd
  have h542 := gm_eq542 he hlen hUo hR hκ0 hκ1 huv hsph hgeo hball hU
  set A := e₁.1 (u, v)
  have hA0 : 0 ≤ A := nonneg_m2m e₁ u v
  have hB0 : 0 ≤ η * A := mul_nonneg hη0 hA0
  have hup := le_of_internal_le_m2m2 e₁ hB0 (gm_eq543 he hUo hU h542 hp)
  have hvq := le_of_internal_le_m2m2 e₁ hB0 (gm_eq543 he hUo hU h542 hq)
  -- `e₁(u, y) ≥ A / t²` for `y ∈ S`
  have hfar : ∀ y ∈ S, A / t ^ 2 ≤ e₁.1 (u, y) := by
    intro y hy
    set m := e₀.1 (u, v) / t ^ 2
    have hsm : ∀ w ∈ sphere u R, m ≤ e₀.1 (u, w) := fun w hw => by
      rw [div_le_iff₀ hκ0, mul_comm]; exact hsph w hw
    have := weyl_ge_of_sphere_m2m2' he hlen hR hball hsm
      (le_of_sphere_out_m2m2 hlen hR hsm (hS y hy))
    calc A / t ^ 2 = Real.exp (-ξ * K) * m := by
          simp only [A, m, h542]; ring
      _ ≤ e₁.1 (u, y) := this
  have hpq : e₁.1 (p, q) ≤ (1 + 2 * η) * A := by
    have t1 := dist_triangle_m2m e₁ p u q
    have t2 := dist_triangle_m2m e₁ u v q
    have t3 := dist_comm_m2m e₁ u p
    have t4 := dist_comm_m2m e₁ v q
    linarith
  have hη3' : (1 + 3 * η) * t ≤ 1 := by
    rw [le_div_iff₀ hcs] at hη3
    rw [ht, ← mul_div_assoc, div_le_one hC]; exact hη3
  -- `(1 + 2η) A ≤ t (A/t² − ηA)` from `(1 + 3η) t ≤ 1`
  have key : (1 + 2 * η) * A ≤ t * (A / t ^ 2 - η * A) := by
    have e1 : t * (A / t ^ 2 - η * A) = A / t - t * η * A := by field_simp
    rw [e1]
    have h1t : 1 + 3 * η ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
    have e2 : A / t = A * (1 / t) := by ring
    have h3 : (1 + 3 * η) * A ≤ A * (1 / t) := by nlinarith
    have : t * η * A ≤ η * A := by nlinarith
    linarith
  have hlow : ENNReal.ofReal (e₁.1 (p, q) / t) ≤ setDist e₁ {p} S := by
    unfold setDist
    refine le_setEDist.2 ?_
    rintro _ ⟨p', hp', rfl⟩ _ ⟨y, hy, rfl⟩
    rw [mem_singleton_iff.1 hp', edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    show e₁.1 (p, q) / t ≤ e₁.1 (p, y)
    rw [div_le_iff₀ ht0, mul_comm]
    have hpy : A / t ^ 2 - η * A ≤ e₁.1 (p, y) := by
      have := dist_triangle_m2m e₁ u p y
      have := hfar y hy
      linarith
    calc e₁.1 (p, q) ≤ (1 + 2 * η) * A := hpq
      _ ≤ t * (A / t ^ 2 - η * A) := key
      _ ≤ t * e₁.1 (p, y) := mul_le_mul_of_nonneg_left hpy ht0.le
  calc ENNReal.ofReal (e₁.1 (p, q)) = ENNReal.ofReal t * ENNReal.ofReal (e₁.1 (p, q) / t) := by
        rw [← ENNReal.ofReal_mul ht0.le]; congr 1; field_simp
    _ ≤ ENNReal.ofReal t * setDist e₁ {p} S := by gcongr

end LQGMetric.GM
