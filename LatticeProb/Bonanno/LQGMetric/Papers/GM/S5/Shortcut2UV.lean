/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2UV at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2Final
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes55Det
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3FTop

/-!
# GM §5.5: the metrics `D_{h−φ}`, `D̃_{h−φ}` at the points `u, v` (GM (5.42), (5.43), (5.45))

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

Deterministic, for metrics `d₀ = D_h`, `e₀ = D̃_h` (length metrics, `c_* d₀ ≤ e₀ ≤ C_* d₀`), their
Weyl rescalings `d₁ = e^{ξ f}·d₀`, `e₁ = e^{ξ f}·e₀` with `f = −φ`, and the points `u ≠ v` of
`linkEvent` (Lemma 5.8, conditions (1), (3)), where `ξ f ≥ −ξK_f` on `B_R(u)`, `R = 4ρr`
(`φ ≤ K_f` there) and `ξ f ≤ −ξK_f` on `U` (`φ ≥ K_f` there):
* `weyl_ge_of_sphere_m2m2`: if `d(u,v) ≤ d(u,q)` for all `q ∈ ∂B_R(u)` and `ξ f ≥ a` on
  `B_R(u)`, then `e^a d(u, v) ≤ (e^{ξ f}·d)(u, v)` (GM l. 3545: "each `D_{h−φ}`-geodesic from `u`
  to `v` is disjoint from `𝒲` and `D_{h−φ}(u,v) ≥ e^{−ξK_f} D_h(u,v)`").
* `gm_eq542`: (5.42) `D̃_{h−φ}(u,v) = e^{−ξK_f} D̃_h(u,v)` (GM l. 3472–3476).
* `gm_eq545`: (5.45) `D̃_{h−φ}(u,v) ≤ c_1' D_{h−φ}(u,v)` (GM l. 3544–3548).
* `gm_eq543`: (5.43) `D̃_{h−φ}(u, p; U) ≤ η D̃_{h−φ}(u,v)` for `p ∈ O_u` (GM l. 3491–3495).
* `gm_L5_11_uv`: with `gm_L5_11_final`, `D̃_{h−φ}(p,q) ≤ c_2' D_{h−φ}(p,q)` for `p ∈ O_u`,
  `q ∈ O_v` (GM (5.46), l. 3513–3550).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric EMetric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- `e^a d(u,v) ≤ (e^{ξ f}·d)(u,v)` when `ξ f ≥ a` on `B_R(u)` and `d(u,v) ≤ d(u, ∂B_R(u))`
(`d` a length metric) -/
lemma weyl_ge_of_sphere_m2m2 {D D' : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y) (hlen : D.IsLength)
    {u v : ℂ} {R a : ℝ} (hR : 0 < R) (ha : ∀ x ∈ ball u R, a ≤ ξ * f x)
    (hsph : ∀ q ∈ sphere u R, D.1 (u, v) ≤ D.1 (u, q)) :
    Real.exp a * D.1 (u, v) ≤ D'.1 (u, v) := by
  by_contra hlt
  push_neg at hlt
  have hV : IsOpen (ball u R) := isOpen_ball
  have hinf : ENNReal.ofReal (D.1 (u, v)) ≤ infEDist (D.pt u) (D.pt '' (ball u R)ᶜ) := by
    refine le_infEDist.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    by_contra h
    push_neg at h
    have hw' : R ≤ ‖w - u‖ := by
      simpa [mem_ball, dist_eq_norm] using hw
    obtain ⟨q, hq, hq'⟩ := DFGPS.P43.exists_sphere_lt' (z₀ := u) hlen hw'
      (show ‖u - u‖ ≤ R by simpa using hR.le) h
    exact absurd (hsph q hq) (not_le.2 hq')
  have hD0 : 0 ≤ D'.1 (u, v) := nonneg_m2m D' u v
  have hglob : weylScale ξ f D u v <
      ENNReal.ofReal (Real.exp a) * infEDist (D.pt u) (D.pt '' (ball u R)ᶜ) := by
    rw [← hD']
    calc ENNReal.ofReal (D'.1 (u, v)) < ENNReal.ofReal (Real.exp a * D.1 (u, v)) :=
          (ENNReal.ofReal_lt_ofReal_iff (hD0.trans_lt hlt)).2 hlt
      _ = ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (D.1 (u, v)) :=
          ENNReal.ofReal_mul (Real.exp_pos a).le
      _ ≤ _ := by gcongr
  have h1 := weylScaleOn_le_weylScale_of_lt (U := ball u R) hV subset_rfl ha hglob
  have h2 : ENNReal.ofReal (Real.exp a) * D.internal (ball u R) u v ≤
      weylScaleOn ξ f D (ball u R) u v := le_weylScaleOn_of_le ha
  have h3 := ofReal_le_internal_m2m D (ball u R) u v
  have h4 : ENNReal.ofReal (Real.exp a * D.1 (u, v)) ≤ ENNReal.ofReal (D'.1 (u, v)) := by
    rw [hD', ENNReal.ofReal_mul (Real.exp_pos a).le]
    exact (by gcongr : _ ≤ ENNReal.ofReal (Real.exp a) * D.internal (ball u R) u v).trans (h2.trans h1)
  exact absurd ((ENNReal.ofReal_le_ofReal_iff hD0).1 h4) (not_le.2 hlt)

/-- linkEvent (1): `e(u,v) ≤ (c_*/C_*)² e(u,q)` for `q ∈ ∂B_R(u)` -/
lemma le_sphere_of_setDist_m2m2 {e : ContMetric} {u v : ℂ} {R κ : ℝ} (hκ : 0 ≤ κ)
    (hsd : ENNReal.ofReal (e.1 (u, v)) ≤ ENNReal.ofReal κ * setDist e {u} (sphere u R)) :
    ∀ q ∈ sphere u R, e.1 (u, v) ≤ κ * e.1 (u, q) := by
  intro q hq
  have h1 : ENNReal.ofReal (e.1 (u, v)) ≤ ENNReal.ofReal κ * ENNReal.ofReal (e.1 (u, q)) :=
    hsd.trans (by gcongr; exact setDist_le_m2m e (mem_singleton u) hq)
  rw [← ENNReal.ofReal_mul hκ] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hκ (nonneg_m2m e u q))).1 h1

/-- the `e₀`-geodesic from `u` to `v` stays in `B_R(u)` (GM l. 3471: its length is at most
`(c_*/C_*)² e₀(u, ∂B_{4ρr}(u))`) -/
lemma range_geod_subset_ball_m2m2 {e : ContMetric} (hlen : e.IsLength) {u v : ℂ} {R κ : ℝ}
    (hR : 0 < R) (hκ0 : 0 < κ) (hκ1 : κ < 1) (huv : u ≠ v)
    (hsph : ∀ q ∈ sphere u R, e.1 (u, v) ≤ κ * e.1 (u, q)) {η : C(unitInterval, ℂ)}
    (hη : IsGeod01 e u v η) : range η ⊆ ball u R := by
  rintro _ ⟨t, rfl⟩
  by_contra hout
  have hw' : R ≤ ‖η t - u‖ := by simpa [mem_ball, dist_eq_norm] using hout
  have hpos : 0 < e.1 (u, v) := by
    have : dist (e.pt u) (e.pt v) ≠ 0 := dist_ne_zero.2 huv
    exact lt_of_le_of_ne (nonneg_m2m e u v) (Ne.symm this)
  have hut : e.1 (u, η t) ≤ e.1 (u, v) := by
    have := hη.2.2 0 t
    rw [hη.1] at this
    rw [this]
    have h0 : |((t : ℝ)) - ((0 : unitInterval) : ℝ)| ≤ 1 := by
      simp only [Set.Icc.coe_zero, sub_zero, abs_le]
      constructor <;> linarith [t.2.1, t.2.2]
    nlinarith
  have hlt : e.1 (u, η t) < e.1 (u, v) / κ := by
    rw [lt_div_iff₀ hκ0]; nlinarith
  obtain ⟨q, hq, hq'⟩ := DFGPS.P43.exists_sphere_lt' (z₀ := u) hlen hw'
    (show ‖u - u‖ ≤ R by simpa using hR.le) hlt
  have := hsph q hq
  rw [lt_div_iff₀ hκ0] at hq'
  linarith


section uv

variable {d₀ e₀ d₁ e₁ : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}

/-- **GM (5.42)** (l. 3472–3476): `D̃_{h−φ}(u,v) = e^{−ξK_f} D̃_h(u,v)`; `φ ≡ K_f` on
`U ∩ B_{4ρr}(u)`, which contains the `D̃_h`-geodesic from `u` to `v`, and `φ ≤ K_f` on
`B_{4ρr}(u)`. -/
theorem gm_eq542 (he : ∀ x y : ℂ, ENNReal.ofReal (e₁.1 (x, y)) = weylScale ξ f e₀ x y)
    (hlen : e₀.IsLength) {U : Set ℂ} (hUo : IsOpen U) {u v : ℂ} {R κ K : ℝ} (hR : 0 < R)
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (huv : u ≠ v)
    (hsph : ∀ q ∈ sphere u R, e₀.1 (u, v) ≤ κ * e₀.1 (u, q)) (hgeo : UniqueGeodIn e₀ u v U)
    (hball : ∀ x ∈ ball u R, -ξ * K ≤ ξ * f x) (hU : ∀ x ∈ U, ξ * f x ≤ -ξ * K) :
    e₁.1 (u, v) = Real.exp (-ξ * K) * e₀.1 (u, v) := by
  obtain ⟨⟨η, hη, -⟩, hin⟩ := hgeo
  have hrange : range η ⊆ U ∩ ball u R := fun x hx =>
    ⟨hin η hη hx, range_geod_subset_ball_m2m2 hlen hR hκ0 hκ1 huv hsph hη hx⟩
  refine le_antisymm (weyl_le_of_internal_m2m he (hUo.inter isOpen_ball)
    (fun x hx => hU x hx.1) (nonneg_m2m e₀ u v) (internal_le_of_isGeod01 hη hrange)) ?_
  exact weyl_ge_of_sphere_m2m2 he hlen hR hball (fun q hq => (hsph q hq).trans
    (mul_le_of_le_one_left (nonneg_m2m e₀ u q) hκ1.le))

/-- the bi-Lipschitz bounds turn `e₀(u,v) ≤ (c_*/C_*)² e₀(u,q)` into `d₀(u,v) ≤ d₀(u,q)` -/
lemma le_sphere_d_m2m2 {cs Cs : ℝ} (hcs : 0 < cs) (hCs : cs ≤ Cs)
    (hbl : ∀ x y : ℂ, cs * d₀.1 (x, y) ≤ e₀.1 (x, y) ∧ e₀.1 (x, y) ≤ Cs * d₀.1 (x, y))
    {u v q : ℂ} (hq : e₀.1 (u, v) ≤ (cs / Cs) ^ 2 * e₀.1 (u, q)) : d₀.1 (u, v) ≤ d₀.1 (u, q) := by
  have hC : 0 < Cs := hcs.trans_le hCs
  have hk : (cs / Cs) ^ 2 * Cs ≤ cs := by
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hCs (mul_pos hcs hC).le]
  have hd := nonneg_m2m d₀ u q
  refine le_of_mul_le_mul_left ?_ hcs
  calc cs * d₀.1 (u, v) ≤ e₀.1 (u, v) := (hbl u v).1
    _ ≤ (cs / Cs) ^ 2 * e₀.1 (u, q) := hq
    _ ≤ (cs / Cs) ^ 2 * (Cs * d₀.1 (u, q)) :=
        mul_le_mul_of_nonneg_left (hbl u q).2 (by positivity)
    _ = ((cs / Cs) ^ 2 * Cs) * d₀.1 (u, q) := by ring
    _ ≤ cs * d₀.1 (u, q) := mul_le_mul_of_nonneg_right hk hd

/-- **GM (5.45)** (l. 3544–3548): `D̃_{h−φ}(u,v) ≤ c_1' D_{h−φ}(u,v)`. -/
theorem gm_eq545 (hd : ∀ x y : ℂ, ENNReal.ofReal (d₁.1 (x, y)) = weylScale ξ f d₀ x y)
    (hlend : d₀.IsLength) {cs Cs c₁ : ℝ} (hcs : 0 < cs) (hCs : cs ≤ Cs) (hc₁ : 0 ≤ c₁)
    (hbl : ∀ x y : ℂ, cs * d₀.1 (x, y) ≤ e₀.1 (x, y) ∧ e₀.1 (x, y) ≤ Cs * d₀.1 (x, y))
    {u v : ℂ} {R K : ℝ} (hR : 0 < R)
    (hsph : ∀ q ∈ sphere u R, e₀.1 (u, v) ≤ (cs / Cs) ^ 2 * e₀.1 (u, q))
    (hball : ∀ x ∈ ball u R, -ξ * K ≤ ξ * f x)
    (h542 : e₁.1 (u, v) = Real.exp (-ξ * K) * e₀.1 (u, v)) (h1 : e₀.1 (u, v) ≤ c₁ * d₀.1 (u, v)) :
    e₁.1 (u, v) ≤ c₁ * d₁.1 (u, v) := by
  have h2 := weyl_ge_of_sphere_m2m2 hd hlend hR hball
    (fun q hq => le_sphere_d_m2m2 hcs hCs hbl (hsph q hq))
  rw [h542]
  calc Real.exp (-ξ * K) * e₀.1 (u, v) ≤ Real.exp (-ξ * K) * (c₁ * d₀.1 (u, v)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = c₁ * (Real.exp (-ξ * K) * d₀.1 (u, v)) := by ring
    _ ≤ c₁ * d₁.1 (u, v) := mul_le_mul_of_nonneg_left h2 hc₁

/-- **GM (5.43)** (l. 3491–3495): `D̃_{h−φ}(u, p; U) ≤ η D̃_{h−φ}(u,v)` from linkEvent (3), since
`φ ≥ K_f` on `U` and (5.42). -/
theorem gm_eq543 (he : ∀ x y : ℂ, ENNReal.ofReal (e₁.1 (x, y)) = weylScale ξ f e₀ x y)
    {U : Set ℂ} (hUo : IsOpen U) {u v a p : ℂ} {K η : ℝ}
    (hU : ∀ x ∈ U, ξ * f x ≤ -ξ * K) (h542 : e₁.1 (u, v) = Real.exp (-ξ * K) * e₀.1 (u, v))
    (hp : e₀.internal U a p ≤ ENNReal.ofReal (η * e₀.1 (u, v))) :
    e₁.internal U a p ≤ ENNReal.ofReal (η * e₁.1 (u, v)) := by
  rw [← weylScaleOn_eq_internal e₁ he hUo]
  refine (weylScaleOn_le_of_le hU).trans ?_
  calc ENNReal.ofReal (Real.exp (-ξ * K)) * e₀.internal U a p ≤
        ENNReal.ofReal (Real.exp (-ξ * K)) * ENNReal.ofReal (η * e₀.1 (u, v)) := by gcongr
    _ = ENNReal.ofReal (η * e₁.1 (u, v)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, h542]; congr 1; ring

/-- **GM (5.46)** (l. 3513–3550) at `p ∈ O_u`, `q ∈ O_v`: from linkEvent (1), (3) at `h`, Weyl
scaling and the bi-Lipschitz bounds at `h` and `h − φ`, `D̃_{h−φ}(p,q) ≤ c_2' D_{h−φ}(p,q)`. -/
theorem gm_L5_11_uv (hd : ∀ x y : ℂ, ENNReal.ofReal (d₁.1 (x, y)) = weylScale ξ f d₀ x y)
    (he : ∀ x y : ℂ, ENNReal.ofReal (e₁.1 (x, y)) = weylScale ξ f e₀ x y)
    (hlend : d₀.IsLength) (hlene : e₀.IsLength) {cs Cs c₁ c₂ η : ℝ} (hcs : 0 < cs)
    (hcC : cs < Cs) (hc₁ : cs < c₁) (hηc : EtaChoice cs Cs c₁ c₂ η) (hpos : 2 * cs⁻¹ * Cs * η < 1)
    (hbl₀ : ∀ x y : ℂ, cs * d₀.1 (x, y) ≤ e₀.1 (x, y) ∧ e₀.1 (x, y) ≤ Cs * d₀.1 (x, y))
    (hbl₁ : ∀ x y : ℂ, cs * d₁.1 (x, y) ≤ e₁.1 (x, y) ∧ e₁.1 (x, y) ≤ Cs * d₁.1 (x, y))
    {U : Set ℂ} (hUo : IsOpen U) {u v p q : ℂ} {R K : ℝ} (hR : 0 < R) (huv : u ≠ v)
    (h1 : e₀.1 (u, v) ≤ c₁ * d₀.1 (u, v))
    (hsd : ENNReal.ofReal (e₀.1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist e₀ {u} (sphere u R))
    (hgeo : UniqueGeodIn e₀ u v U)
    (hp : e₀.internal U u p ≤ ENNReal.ofReal (η * e₀.1 (u, v)))
    (hq : e₀.internal U v q ≤ ENNReal.ofReal (η * e₀.1 (u, v)))
    (hball : ∀ x ∈ ball u R, -ξ * K ≤ ξ * f x) (hU : ∀ x ∈ U, ξ * f x ≤ -ξ * K) :
    e₁.1 (p, q) ≤ c₂ * d₁.1 (p, q) := by
  have hC : 0 < Cs := hcs.trans hcC
  have hκ0 : 0 < (cs / Cs) ^ 2 := by positivity
  have hκ1 : (cs / Cs) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]; nlinarith
  have hsph := le_sphere_of_setDist_m2m2 hκ0.le hsd
  have h542 := gm_eq542 he hlene hUo hR hκ0 hκ1 huv hsph hgeo hball hU
  have h545 := gm_eq545 hd hlend hcs hcC.le (by linarith) hbl₀ hR hsph hball h542 h1
  exact gm_L5_11_final hcs hc₁ hηc hpos hbl₁ (gm_eq543 he hUo hU h542 hp)
    (gm_eq543 he hUo hU h542 hq) h545

end uv

end LQGMetric.GM
