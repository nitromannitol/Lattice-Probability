/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.ShortcutDist at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.ShortcutHit
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLength
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.EventStmts

/-!
# GM Lemma 5.13: an upper bound for `D_{h−φ}(𝕩', 𝕪')`

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, Lemma 5.13 (`lem-geomove-dist`,
l. 3405–3428), proof followed verbatim: by condition (8) of `E_r` and `D_{h−φ} ≤ D_h` (5.37), the
points `𝕩', 𝕪'` are `e^{−ξK_f}𝔠_r e^{ξh_r(0)}`-close to `W_r^𝕩`, `W_r^𝕪`; by condition (9) and Weyl
scaling with `φ ≥ K_g` on `W` the internal `D_{h−φ}`-diameters of `W_r^𝕩, W_r^𝕪` are
`≤ e^{−ξK_g} M 𝔠_r e^{ξh_r(0)} = e^{−ξK_f}𝔠_r e^{ξh_r(0)}` (5.38); by condition (5) and `φ ≥ K_f` on
`U` the internal `D_{h−φ}`-diameter of `U` is `≤ e^{−ξK_f} A 𝔠_r e^{ξh_r(0)}` (5.39); since `W_r^𝕩`,
`W_r^𝕪` meet `U` the triangle inequality gives (5.36).

* `weyl_le_of_internal_m2m`: the Weyl-scaling step (GM.S5.W) used three times, via
  `LQGMetric.weylScaleOn_eq_internal` and `weylScaleOn_of_eq_const` (P2-WEYL).
* `subset_interior_squares_m2m`: `X ⊆ int ⋃ 𝓢_s(X)` (used for `[x, (3/2−θ)x] ⊆ W_r^x`, which GM uses
  implicitly at l. 3410 and 3427; own elementary proof).
* `gm_L5_13_det`: Lemma 5.13 for one pair of metrics `D, D' = e^{ξ f}·D`, abstract sets.
* `gm_L5_13`: Lemma 5.13 in GM's notation on `E_r`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the Weyl-scaling step: if `D' = e^{ξ f}·D`, `ξ f ≤ c` on the open set `V` and the
`D`-internal distance in `V` of `a, b` is at most `B`, then `D'(a, b) ≤ e^c B` -/
lemma weyl_le_of_internal_m2m {D D' : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y)
    {V : Set ℂ} (hV : IsOpen V) {c : ℝ} (hc : ∀ x ∈ V, ξ * f x ≤ c) {a b : ℂ} {B : ℝ}
    (hB0 : 0 ≤ B) (hB : D.internal V a b ≤ ENNReal.ofReal B) :
    D'.1 (a, b) ≤ Real.exp c * B := by
  have h1 : ENNReal.ofReal (D'.1 (a, b)) ≤ D'.internal V a b := ofReal_le_internal_m2m D' V a b
  have h2 : D'.internal V a b ≤ ENNReal.ofReal (Real.exp c) * D.internal V a b := by
    rw [← weylScaleOn_eq_internal D' hD' hV]
    calc weylScaleOn ξ f D V a b ≤ weylScaleOn 1 (ContinuousMap.const ℂ c) D V a b :=
          weylScaleOn_mono fun x hx => by simpa using hc x hx
      _ = ENNReal.ofReal (Real.exp c) * D.internal V a b :=
          weylScaleOn_of_eq_const fun x _ => by simp
  have h3 : ENNReal.ofReal (D'.1 (a, b)) ≤ ENNReal.ofReal (Real.exp c) * ENNReal.ofReal B :=
    h1.trans (h2.trans (by gcongr))
  rw [← ENNReal.ofReal_mul (Real.exp_pos c).le] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos c).le hB0)).1 h3

lemma internal_le_internalDiam_m2m (D : ContMetric) {V : Set ℂ} {a b : ℂ} (ha : a ∈ V)
    (hb : b ∈ V) : D.internal V a b ≤ internalDiam D V V :=
  le_iSup₂_of_le a ha (le_iSup₂_of_le (f := fun v (_ : v ∈ V) => D.internal V a v) b hb le_rfl)

lemma dist_triangle_m2m (D : ContMetric) (a b c : ℂ) : D.1 (a, c) ≤ D.1 (a, b) + D.1 (b, c) :=
  dist_triangle (D.pt a) (D.pt b) (D.pt c)

lemma dist_comm_m2m (D : ContMetric) (a b : ℂ) : D.1 (a, b) = D.1 (b, a) :=
  dist_comm (D.pt a) (D.pt b)

/-- two reals at distance `< 1` near `a` lie in a common unit interval with integer endpoints -/
lemma exists_int_Icc_m2m (a b : ℝ) (hb : b ∈ Ioo ((⌈a⌉ : ℝ) - 1) ((⌊a⌋ : ℝ) + 1)) :
    ∃ k : ℤ, (k : ℝ) ≤ a ∧ a ≤ k + 1 ∧ (k : ℝ) ≤ b ∧ b ≤ k + 1 := by
  by_cases h : (⌊a⌋ : ℝ) ≤ b
  · exact ⟨⌊a⌋, Int.floor_le a, (Int.lt_floor_add_one a).le, h, hb.2.le⟩
  · rw [not_le] at h
    have h1 : (⌈a⌉ : ℝ) < ⌊a⌋ + 1 := by linarith [hb.1]
    have h2 : ⌈a⌉ ≤ ⌊a⌋ := by exact_mod_cast (Int.lt_add_one_iff.1 (by exact_mod_cast h1))
    have h3 : (⌈a⌉ : ℝ) ≤ a := by
      calc (⌈a⌉ : ℝ) ≤ ⌊a⌋ := by exact_mod_cast h2
        _ ≤ a := Int.floor_le a
    have h4 : (⌊a⌋ : ℝ) ≤ ⌈a⌉ := by exact_mod_cast Int.floor_le_ceil a
    refine ⟨⌈a⌉ - 1, ?_, ?_, ?_, ?_⟩ <;> push_cast
    · linarith [Int.le_ceil a]
    · linarith [Int.le_ceil a]
    · linarith [hb.1]
    · linarith

/-- `X ⊆ int ⋃_{S ∈ 𝓢_s(X)} S` (own elementary proof) -/
lemma subset_interior_squares_m2m {s : ℝ} (hs : 0 < s) (X : Set ℂ) :
    X ⊆ interior (⋃ m ∈ squareSet s X, gridSquare s m) := by
  intro p hp
  rw [mem_interior]
  refine ⟨{q : ℂ | q.re / s ∈ Ioo ((⌈p.re / s⌉ : ℝ) - 1) ((⌊p.re / s⌋ : ℝ) + 1) ∧
      q.im / s ∈ Ioo ((⌈p.im / s⌉ : ℝ) - 1) ((⌊p.im / s⌋ : ℝ) + 1)}, ?_, ?_, ?_⟩
  · rintro q ⟨hq1, hq2⟩
    obtain ⟨k₁, a1, a2, b1, b2⟩ := exists_int_Icc_m2m _ _ hq1
    obtain ⟨k₂, c1, c2, d1, d2⟩ := exists_int_Icc_m2m _ _ hq2
    have key : ∀ x : ℂ, (k₁ : ℝ) ≤ x.re / s → x.re / s ≤ k₁ + 1 → (k₂ : ℝ) ≤ x.im / s →
        x.im / s ≤ k₂ + 1 → x ∈ gridSquare s (k₁, k₂) := by
      intro x e1 e2 e3 e4
      exact ⟨(le_div_iff₀ hs).1 e1, (div_le_iff₀ hs).1 e2, (le_div_iff₀ hs).1 e3,
        (div_le_iff₀ hs).1 e4⟩
    refine mem_iUnion₂.2 ⟨(k₁, k₂), ?_, key q b1 b2 d1 d2⟩
    exact ⟨p, key p a1 a2 c1 c2, hp⟩
  · have hc1 : Continuous fun q : ℂ => q.re / s := Complex.continuous_re.div_const s
    have hc2 : Continuous fun q : ℂ => q.im / s := Complex.continuous_im.div_const s
    exact (isOpen_Ioo.preimage hc1).inter (isOpen_Ioo.preimage hc2)
  · have e : ∀ a : ℝ, a ∈ Ioo ((⌈a⌉ : ℝ) - 1) ((⌊a⌋ : ℝ) + 1) := fun a =>
      ⟨by linarith [Int.ceil_lt_add_one a], Int.lt_floor_add_one a⟩
    exact ⟨e _, e _⟩

/-- the segment `[x, (3/2 − θ)x]` lies in `W_r^x` -/
lemma segment_subset_lineTube_m2m {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r) (x : ℂ) :
    segment ℝ x (((3 / 2 - θ : ℝ) : ℂ) * x) ⊆ lineTube θ r x :=
  subset_interior_squares_m2m (mul_pos hθ hr) _

/-- **GM Lemma 5.13**, deterministic core: `D' = e^{ξ f}·D` with `ξ f ≤ 0` on the open set `O`
(the annulus), `ξ f ≤ −ξK_f` on `U` and `ξ f ≤ −ξK_g` on `W₁, W₂`; `x'` is joined to
`p₁ ∈ W₁` inside `O` at `D`-cost `≤ e^{−ξK_f} T` (same for `y'`, `p₂ ∈ W₂`); `W₁, W₂` have internal
`D`-diameter `≤ M T` and `U` has `≤ A T`; `W₁ ∩ U ∋ q₁`, `W₂ ∩ U ∋ q₂`. -/
theorem gm_L5_13_det {D D' : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hD' : ∀ x y : ℂ, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y)
    {O U W₁ W₂ : Set ℂ} (hO : IsOpen O) (hU : IsOpen U) (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    {Kf Kg M A T : ℝ} (hT : 0 < T) (hM : 0 < M) (hA : 0 ≤ A)
    (hKg : Real.exp (-ξ * Kg) * M ≤ Real.exp (-ξ * Kf))
    (hfO : ∀ x ∈ O, ξ * f x ≤ 0) (hfU : ∀ x ∈ U, ξ * f x ≤ -ξ * Kf)
    (hfW₁ : ∀ x ∈ W₁, ξ * f x ≤ -ξ * Kg) (hfW₂ : ∀ x ∈ W₂, ξ * f x ≤ -ξ * Kg)
    {x' y' p₁ p₂ q₁ q₂ : ℂ} (hp₁ : p₁ ∈ W₁) (hp₂ : p₂ ∈ W₂) (hq₁ : q₁ ∈ W₁ ∩ U)
    (hq₂ : q₂ ∈ W₂ ∩ U)
    (h8x : D.internal O x' p₁ ≤ ENNReal.ofReal (Real.exp (-ξ * Kf) * T))
    (h8y : D.internal O y' p₂ ≤ ENNReal.ofReal (Real.exp (-ξ * Kf) * T))
    (h9x : internalDiam D W₁ W₁ ≤ ENNReal.ofReal (M * T))
    (h9y : internalDiam D W₂ W₂ ≤ ENNReal.ofReal (M * T))
    (h5 : internalDiam D U U ≤ ENNReal.ofReal (A * T)) :
    D'.1 (x', y') ≤ Real.exp (-ξ * Kf) * (A + 4) * T := by
  have eT : 0 ≤ Real.exp (-ξ * Kf) * T := (mul_pos (Real.exp_pos _) hT).le
  -- (5.37)
  have t1 : D'.1 (x', p₁) ≤ Real.exp (-ξ * Kf) * T := by
    simpa using weyl_le_of_internal_m2m hD' hO hfO eT h8x
  have t5 : D'.1 (y', p₂) ≤ Real.exp (-ξ * Kf) * T := by
    simpa using weyl_le_of_internal_m2m hD' hO hfO eT h8y
  -- (5.38)
  have hMT : 0 ≤ M * T := (mul_pos hM hT).le
  have t2 : D'.1 (p₁, q₁) ≤ Real.exp (-ξ * Kf) * T := by
    have := weyl_le_of_internal_m2m hD' hW₁ hfW₁ hMT
      ((internal_le_internalDiam_m2m D hp₁ hq₁.1).trans h9x)
    nlinarith
  have t4 : D'.1 (q₂, p₂) ≤ Real.exp (-ξ * Kf) * T := by
    have := weyl_le_of_internal_m2m hD' hW₂ hfW₂ hMT
      ((internal_le_internalDiam_m2m D hq₂.1 hp₂).trans h9y)
    nlinarith
  -- (5.39)
  have t3 : D'.1 (q₁, q₂) ≤ Real.exp (-ξ * Kf) * (A * T) :=
    weyl_le_of_internal_m2m hD' hU hfU (mul_nonneg hA hT.le)
      ((internal_le_internalDiam_m2m D hq₁.2 hq₂.2).trans h5)
  rw [dist_comm_m2m D' y' p₂] at t5
  have := (dist_triangle_m2m D' x' p₁ y').trans (add_le_add t1
    ((dist_triangle_m2m D' p₁ q₁ y').trans (add_le_add t2
      ((dist_triangle_m2m D' q₁ q₂ y').trans (add_le_add t3
        ((dist_triangle_m2m D' q₂ p₂ y').trans (add_le_add t4 t5)))))))
  nlinarith

lemma bumpPhi_apply_m2m (S : EData) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC) (r : ℝ) (x y z : ℂ) :
    bumpPhi S U fb gb r x y z = S.Kf * fb (U x y) z +
      S.Kg * (gb (lineTube S.θ r x) z + gb (lineTube S.θ r y) z) := rfl

lemma Kf_pos_m2m {S : EData} (hS : S.Ranges) : 0 < S.Kf := by
  obtain ⟨hξ, -, -, -, -, hΔ, -, ha, -, hA, -, -⟩ := hS
  unfold EData.Kf
  refine mul_pos (inv_pos.2 hξ) (Real.log_pos ?_)
  rw [one_lt_div (mul_pos ha.1 hΔ.1)]
  nlinarith [mul_lt_mul'' ha.2 hΔ.2 ha.1.le hΔ.1.le]

lemma Kf_le_Kg_m2m {S : EData} (hS : S.Ranges) : S.Kf ≤ S.Kg := by
  have hξ := hS.1
  have hM := hS.2.2.2.2.2.2.2.2.2.2.1
  unfold EData.Kg
  have := mul_pos (inv_pos.2 hξ) (Real.log_pos hM)
  linarith

lemma exp_Kg_m2m {S : EData} (hS : S.Ranges) :
    Real.exp (-S.ξ * S.Kg) * S.M = Real.exp (-S.ξ * S.Kf) := by
  have hξ := hS.1
  have hM : 0 < S.M := by linarith [hS.2.2.2.2.2.2.2.2.2.2.1]
  unfold EData.Kg
  rw [show -S.ξ * (S.Kf + S.ξ⁻¹ * Real.log S.M) = -S.ξ * S.Kf + -Real.log S.M by
    field_simp; ring, Real.exp_add, Real.exp_neg, Real.exp_log hM, mul_assoc, inv_mul_cancel₀ hM.ne',
    mul_one]

/-- **GM Lemma 5.13** (`lem-geomove-dist`, l. 3405–3428) on `E_r`: for `𝕩', 𝕪' ∈ ∂B_{3r}(0)` with
`|𝕩 − 𝕪| ≥ δr` (Lemma 5.12), `φ` as in (5.35) and `D_{g−φ} = e^{−ξφ}·D_g`,
`D_{g−φ}(𝕩', 𝕪') ≤ e^{−ξK_f}(A + 4)𝔠_r e^{ξh_r(0)}`. -/
theorem gm_L5_13 {D D' : DistC → ContMetric} {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r)
    (hcr : 0 < S.c r) {U : ℂ → ℂ → Set ℂ} {fb gb : Set ℂ → TestC} (hU : IsTubeFam S U r)
    (hB : IsBumpChoice S U fb gb r) {g : DistC} (hg : g ∈ eventE D D' S U fb gb r) {x' y' : ℂ}
    (hx' : ‖x'‖ = 3 * r) (hy' : ‖y'‖ = 3 * r)
    (hsep : S.δ * r ≤ ‖(2 / 3 : ℂ) * x' - (2 / 3 : ℂ) * y'‖)
    (hW : ∀ x y : ℂ, ENNReal.ofReal ((D (subTest g (phiChoice S U fb gb r x' y'))).1 (x, y)) =
      weylScale S.ξ (-testCont (phiChoice S U fb gb r x' y')) (D g) x y) :
    (D (subTest g (phiChoice S U fb gb r x' y'))).1 (x', y') ≤
      Real.exp (-S.ξ * S.Kf) * (S.A + 4) * scaleFac S.ξ S.c g r 0 := by
  set x : ℂ := (2 / 3 : ℂ) * x' with hxdef
  set y : ℂ := (2 / 3 : ℂ) * y' with hydef
  have hxs : x ∈ Metric.sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, hxdef, norm_mul, hx']; norm_num; ring
  have hys : y ∈ Metric.sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, hydef, norm_mul, hy']; norm_num; ring
  have ex : (3 / 2 : ℂ) * x = x' := by rw [hxdef]; ring
  have ey : (3 / 2 : ℂ) * y = y' := by rw [hydef]; ring
  have hφ : phiChoice S U fb gb r x' y' = bumpPhi S U fb gb r x y := by
    unfold phiChoice; rw [ite_eq_left_iff.2 (fun h => absurd hsep h)]
  rw [hφ] at hW ⊢
  obtain ⟨-, -, h5, -, -, h8, h9, -⟩ := hg
  obtain ⟨hUo, -, -, -, hxU, hyU, -⟩ := hU x hxs y hys hsep
  obtain ⟨hfU0, hfU1, -⟩ := hB.1 x hxs y hys hsep
  obtain ⟨hgx0, hgx1, -⟩ := hB.2 x hxs
  obtain ⟨hgy0, hgy1, -⟩ := hB.2 y hys
  have hξ := hS.1
  have hθ := hS.2.2.2.2.2.2.2.2.1.1
  have hKf := Kf_pos_m2m hS
  have hKg := Kf_le_Kg_m2m hS
  have hfb0 : ∀ z, 0 ≤ fb (U x y) z := fun z => (hfU0 z).1
  have hφ0 : ∀ z, 0 ≤ bumpPhi S U fb gb r x y z := fun z => by
    rw [bumpPhi_apply_m2m]
    have := mul_nonneg hKf.le (hfb0 z)
    have := mul_nonneg (hKf.le.trans hKg) (add_nonneg (hgx0 z).1 (hgy0 z).1)
    linarith
  have hφU : ∀ z ∈ U x y, S.Kf ≤ bumpPhi S U fb gb r x y z := fun z hz => by
    rw [bumpPhi_apply_m2m, hfU1 z hz]
    have := (hgx0 z).1; have := (hgy0 z).1
    nlinarith
  have hφWx : ∀ z ∈ lineTube S.θ r x, S.Kg ≤ bumpPhi S U fb gb r x y z := fun z hz => by
    rw [bumpPhi_apply_m2m, hgx1 z hz]
    have := (hgy0 z).1; have := hfb0 z
    nlinarith
  have hφWy : ∀ z ∈ lineTube S.θ r y, S.Kg ≤ bumpPhi S U fb gb r x y z := fun z hz => by
    rw [bumpPhi_apply_m2m, hgy1 z hz]
    have := (hgx0 z).1; have := hfb0 z
    nlinarith
  have hneg : ∀ (K : ℝ) (z : ℂ), K ≤ bumpPhi S U fb gb r x y z →
      S.ξ * (-testCont (bumpPhi S U fb gb r x y)) z ≤ -S.ξ * K := fun K z hz => by
    simp only [ContinuousMap.neg_apply, testCont, ContinuousMap.coe_mk]
    nlinarith
  have hseg : ∀ v : ℂ, segment ℝ v (((3 / 2 - S.θ : ℝ) : ℂ) * v) ⊆ lineTube S.θ r v :=
    fun v => segment_subset_lineTube_m2m hθ hr v
  have hT : 0 < scaleFac S.ξ S.c g r 0 := mul_pos hcr (Real.exp_pos _)
  have h8x := h8 x hxs
  have h8y := h8 y hys
  rw [ex] at h8x
  rw [ey] at h8y
  exact gm_L5_13_det hW (annulus 0 r (4 * r)).isOpen hUo isOpen_interior isOpen_interior hT
    (by linarith [hS.2.2.2.2.2.2.2.2.2.2.1]) (by linarith [hS.2.2.2.2.2.2.2.2.2.1])
    (exp_Kg_m2m hS).le (fun z _ => by simpa using hneg 0 z (hφ0 z))
    (fun z hz => hneg _ z (hφU z hz)) (fun z hz => hneg _ z (hφWx z hz))
    (fun z hz => hneg _ z (hφWy z hz))
    (hseg x (right_mem_segment _ _ _)) (hseg y (right_mem_segment _ _ _))
    ⟨hseg x (left_mem_segment _ _ _), hxU⟩ ⟨hseg y (left_mem_segment _ _ _), hyU⟩
    h8x h8y (h9 x hxs) (h9 y hys) (h5 x hxs y hys hsep)

/-- **GM P5.2 (B)** (l. 3290: "immediate from condition (10)"): on `E_r`,
`|(h,φ)_∇| + ½(φ,φ)_∇ ≤ Λ₀` for all `φ ∈ 𝓖_r`. -/
theorem gm_P5_2_B {D D' : DistC → ContMetric} {S : EData} {U : ℂ → ℂ → Set ℂ}
    {fb gb : Set ℂ → TestC} {r : ℝ} {g : DistC} (hg : g ∈ eventE D D' S U fb gb r) :
    ∀ φ ∈ bumpFam S U fb gb r, |dirInner g φ| + gradEnergy φ / 2 ≤ S.Λ₀ :=
  hg.2.2.2.2.2.2.2

/-- the bump function (5.35) lies in `𝓖_r` (GM l. 3354) -/
theorem phiChoice_mem_bumpFam {S : EData} {U : ℂ → ℂ → Set ℂ} {fb gb : Set ℂ → TestC} {r : ℝ}
    {x' y' : ℂ} (hx' : ‖x'‖ = 3 * r) (hy' : ‖y'‖ = 3 * r) :
    phiChoice S U fb gb r x' y' ∈ bumpFam S U fb gb r := by
  unfold phiChoice
  split_ifs with h
  · refine Or.inl ⟨(2 / 3 : ℂ) * x', ?_, (2 / 3 : ℂ) * y', ?_, h, rfl⟩
    · rw [mem_sphere_zero_iff_norm, norm_mul, hx']; norm_num; ring
    · rw [mem_sphere_zero_iff_norm, norm_mul, hy']; norm_num; ring
  · exact Or.inr rfl

end LQGMetric.GM
