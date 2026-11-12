/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2L514a at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2L514

/-!
# GM Lemma 5.14: no long crossing of `𝔸_{r/4,4r}(0) ∖ (B_{ζr}(U) ∪ 𝒲)`

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

`gm_L5_14_across`: the step of GM's proof of the first assertion of Lemma 5.14 (l. 3449–3453):
"since `φ ≡ 0` on `ℂ ∖ (B_{ζr}(U) ∪ 𝒲)`, condition (7) implies that the `D_{h−φ}`-length of any
curve contained in `𝔸_{r/4,4r}(0) ∖ (B_{ζr}(U) ∪ 𝒲)` of Euclidean diameter at least `ζr` is at
least `a𝔠_r e^{ξh_r(0)}`, which is larger than the right side of (5.40); so no segment of `P̄^φ`
of diameter at least `ζr` is contained in `𝔸_{r/4,4r}(0) ∖ (B_{ζr}(U) ∪ 𝒲)`". Here: two points
`P^φ(τ₁), P^φ(τ₂)` with `P^φ([τ₁,τ₂])` in that set and `s ≤ τ₁ ≤ τ₂ ≤ t`, `s, t` outside the
hitting balls, are at distance `< ζr`.
As in `gm_L5_14b` we use `φ < ξ⁻¹ log 2` on an open neighbourhood (a factor `1/2`, absorbed by
`(A + 4)Δ/(100A) < 1/2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- `e^{−ξK_f} = aΔ/(100A)` (GM (5.29)) -/
lemma exp_Kf_m2m2 {S : EData} (hS : S.Ranges) :
    Real.exp (-S.ξ * S.Kf) = S.a * S.Δ / (100 * S.A) := by
  have hξ := hS.1
  have ha := hS.2.2.2.2.2.2.2.1.1
  have hΔ := hS.2.2.2.2.2.1.1
  have hA : 0 < S.A := by linarith [hS.2.2.2.2.2.2.2.2.2.1]
  unfold EData.Kf
  rw [show -S.ξ * (S.ξ⁻¹ * Real.log (100 * S.A / (S.a * S.Δ))) =
      -Real.log (100 * S.A / (S.a * S.Δ)) by field_simp, Real.exp_neg,
    Real.exp_log (by positivity), inv_div]

/-- **GM Lemma 5.14**, crossing step of the first assertion (l. 3449–3453). -/
theorem gm_L5_14_across {D D' : DistC → ContMetric} {S : EData} (hS : S.Ranges) {r : ℝ}
    (hr : 0 < r) (hcr : 0 < S.c r) {U : ℂ → ℂ → Set ℂ} {fb gb : Set ℂ → TestC}
    (hU : IsTubeFam S U r) (hB : IsBumpChoice S U fb gb r) {g : DistC}
    (hg : g ∈ eventE D D' S U fb gb r)
    {z w x' y' : ℂ} (hx' : IsHitPt (D g) z x' r) (hy' : IsHitPt (D g) w y' r)
    (hsep : S.δ * r ≤ ‖(2 / 3 : ℂ) * x' - (2 / 3 : ℂ) * y'‖) (hlen : (D g).IsLength)
    (hW : ∀ a b : ℂ, ENNReal.ofReal ((D (subTest g (phiChoice S U fb gb r x' y'))).1 (a, b)) =
      weylScale S.ξ (-testCont (phiChoice S U fb gb r x' y')) (D g) a b)
    {Qφ : C(unitInterval, ℂ)} (hQφ : IsGeod01 (D (subTest g (phiChoice S U fb gb r x' y'))) z w Qφ)
    {s t : unitInterval} (hst : s ≤ t)
    (hs : (D g).1 (z, x') ≤ (D g).1 (z, Qφ s) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ s))
    (ht : (D g).1 (z, x') ≤ (D g).1 (z, Qφ t) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ t)) :
    ∀ τ₁ ∈ Icc s t, ∀ τ₂ ∈ Icc s t, τ₁ ≤ τ₂ →
      (∀ τ ∈ Icc τ₁ τ₂, Qφ τ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ) \
        (thickening (S.ζ * r) (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) ∪
          (thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * x')) ∪
            thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * y'))))) →
      ‖Qφ τ₁ - Qφ τ₂‖ < S.ζ * r := by
  have h513 := gm_L5_13 hS hr hcr hU hB hg hx'.1 hy'.1 hsep hW
  set x : ℂ := (2 / 3 : ℂ) * x' with hxdef
  set y : ℂ := (2 / 3 : ℂ) * y' with hydef
  have hxs : x ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, hxdef, norm_mul, hx'.1]; norm_num; ring
  have hys : y ∈ sphere (0 : ℂ) (2 * r) := by
    rw [mem_sphere_zero_iff_norm, hydef, norm_mul, hy'.1]; norm_num; ring
  have hφ : phiChoice S U fb gb r x' y' = bumpPhi S U fb gb r x y := by
    unfold phiChoice; rw [ite_eq_left_iff.2 (fun h => absurd hsep h)]
  rw [hφ] at hW hQφ h513
  set φ := bumpPhi S U fb gb r x y with hφdef
  set D₁ := D (subTest g φ)
  have hξ := hS.1
  have hA := hS.2.2.2.2.2.2.2.2.2.1
  have hKf := Kf_pos_m2m hS
  have hKg := Kf_le_Kg_m2m hS
  obtain ⟨hfU0, -, -⟩ := hB.1 x hxs y hys hsep
  obtain ⟨hgx0, -, hgx2⟩ := hB.2 x hxs
  obtain ⟨hgy0, -, hgy2⟩ := hB.2 y hys
  have hφ0 : ∀ q, 0 ≤ φ q := fun q => by
    rw [hφdef, bumpPhi_apply_m2m]
    have := mul_nonneg hKf.le (hfU0 q).1
    have := mul_nonneg (hKf.le.trans hKg) (add_nonneg (hgx0 q).1 (hgy0 q).1)
    linarith
  have hfe : ∀ q, S.ξ * (-testCont φ) q = -(S.ξ * φ q) := fun q => by
    simp only [ContinuousMap.neg_apply, testCont, ContinuousMap.coe_mk]; ring
  -- `φ` vanishes off `cl B_{3r}(0)`
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
  have hclose := gm_out_close hW hlen hf hf0 hx' hy' hQφ hs ht
  set sf := scaleFac S.ξ S.c g r 0
  have hsf : 0 < sf := mul_pos hcr (Real.exp_pos _)
  have hfU2 := (hB.1 x hxs y hys hsep).2.2
  have hζr : 0 < S.ζ * r := mul_pos hS.2.2.2.2.2.2.1.1 hr
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hξi : S.ξ * S.ξ⁻¹ = 1 := mul_inv_cancel₀ hξ.ne'
  intro τ₁ h₁ τ₂ h₂ h12 hin
  by_contra hfar
  push_neg at hfar
  set P : ℝ → ℂ := fun τ => Qφ (projIcc 0 1 zero_le_one τ) with hP
  have hPc : Continuous P := Qφ.continuous.comp continuous_projIcc
  have hPt : ∀ τ : unitInterval, P τ = Qφ τ := fun τ => by
    show Qφ (projIcc 0 1 zero_le_one (τ : ℝ)) = Qφ τ; rw [projIcc_val]
  have hinP : ∀ τ ∈ Icc (τ₁ : ℝ) τ₂, P τ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ) \
      (thickening (S.ζ * r) (U x y) ∪
        (thickening (S.θ ^ 2 * r) (lineTube S.θ r x) ∪
          thickening (S.θ ^ 2 * r) (lineTube S.θ r y))) := by
    intro τ hτ
    have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨τ₁.2.1.trans hτ.1, hτ.2.trans τ₂.2.2⟩
    show Qφ (projIcc 0 1 zero_le_one τ) ∈ _
    rw [projIcc_of_mem _ hτ01]
    exact hin _ ⟨hτ.1, hτ.2⟩
  -- condition (7) and the internal distance
  have h7 := hg.2.2.2.2.1 (P τ₁) (hinP τ₁ ⟨le_rfl, h12⟩).1 (P τ₂) (hinP τ₂ ⟨h12, le_rfl⟩).1
    (by rw [hPt, hPt]; exact hfar)
  have hc : ContinuousOn ((D g).pt ∘ P) (Icc (τ₁ : ℝ) τ₂) :=
    ((continuous_weylPt (D g)).comp hPc).continuousOn
  have hint : (D g).internal (annulus 0 (r / 4) (4 * r)) (P τ₁) (P τ₂) ≤
      curveLength ((D g).pt ∘ P) τ₁ τ₂ :=
    internalEDist_le_curveLength (show (τ₁ : ℝ) ≤ τ₂ from h12) hc
      (fun τ hτ => ⟨P τ, (hinP τ hτ).1, rfl⟩)
  -- `φ < ξ⁻¹ log 2` near the curve
  set V : Set ℂ := {q | φ q < S.ξ⁻¹ * Real.log 2} with hV
  have hVo : IsOpen V := isOpen_lt (testCont φ).continuous continuous_const
  have hPV : ∀ τ ∈ Icc (τ₁ : ℝ) τ₂, P τ ∈ V := fun τ hτ => by
    have h := (hinP τ hτ).2
    rw [mem_union, mem_union, not_or, not_or] at h
    show φ (P τ) < S.ξ⁻¹ * Real.log 2
    rw [hφdef, bumpPhi_apply_m2m, hfU2 _ h.1, hgx2 _ h.2.1, hgy2 _ h.2.2]
    have : 0 < S.ξ⁻¹ * Real.log 2 := mul_pos (inv_pos.2 hξ) hl2
    linarith
  have ha : ∀ q ∈ V, -Real.log 2 ≤ S.ξ * (-testCont φ) q := fun q hq => by
    rw [hfe]
    have hq' : φ q < S.ξ⁻¹ * Real.log 2 := hq
    have := mul_lt_mul_of_pos_left hq' hξ
    rw [← mul_assoc, hξi, one_mul] at this
    linarith
  have hlow := le_curveLength_weyl D₁ hW hc hVo hPV ha
  set L := D₁.1 (z, w)
  have hL0 : 0 ≤ L := nonneg_m2m D₁ z w
  have hup : curveLength (D₁.pt ∘ P) τ₁ τ₂ ≤ ENNReal.ofReal (L * ((τ₂ : ℝ) - τ₁)) := by
    refine curveLength_le_lip_m2m2 hL0 fun a _ b _ => ?_
    show D₁.1 (P a, P b) ≤ L * dist a b
    rw [hQφ.2.2, Real.dist_eq, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    have := abs_projIcc_sub_projIcc (h := (zero_le_one : (0 : ℝ) ≤ 1)) (c := b) (d := a)
    rw [abs_sub_comm a b]; exact this
  have hLst : L * ((τ₂ : ℝ) - τ₁) ≤ Real.exp (-S.ξ * S.Kf) * (S.A + 4) * sf := by
    have e := hQφ.2.2 s t
    rw [abs_of_nonneg (sub_nonneg.2 (show (s : ℝ) ≤ t from hst))] at e
    have : L * ((τ₂ : ℝ) - τ₁) ≤ L * ((t : ℝ) - s) :=
      mul_le_mul_of_nonneg_left (by linarith [show (s : ℝ) ≤ τ₁ from h₁.1,
        show (τ₂ : ℝ) ≤ t from h₂.2]) hL0
    refine this.trans ?_
    rw [mul_comm, ← e]; exact hclose.trans h513
  have hchain : ENNReal.ofReal (Real.exp (-Real.log 2) * (S.a * sf)) ≤
      ENNReal.ofReal (Real.exp (-S.ξ * S.Kf) * (S.A + 4) * sf) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    calc ENNReal.ofReal (Real.exp (-Real.log 2)) * ENNReal.ofReal (S.a * sf)
        ≤ ENNReal.ofReal (Real.exp (-Real.log 2)) * curveLength ((D g).pt ∘ P) τ₁ τ₂ := by
          gcongr; exact h7.trans hint
      _ ≤ curveLength (D₁.pt ∘ P) τ₁ τ₂ := hlow
      _ ≤ _ := hup.trans (ENNReal.ofReal_le_ofReal hLst)
  have hE : 0 < Real.exp (-S.ξ * S.Kf) * sf := mul_pos (Real.exp_pos _) hsf
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity), Real.exp_neg, Real.exp_log (by norm_num),
    exp_Kf_m2m2 hS] at hchain
  have ha0 := hS.2.2.2.2.2.2.2.1
  have hΔ := hS.2.2.2.2.2.1
  have hA1 := hS.2.2.2.2.2.2.2.2.2.1
  have hA0 : 0 < S.A := by linarith
  have e2 : S.a * S.Δ / (100 * S.A) * (S.A + 4) * sf = S.a * sf * (S.Δ * (S.A + 4) / (100 * S.A)) := by
    field_simp
  rw [e2] at hchain
  have hq : S.Δ * (S.A + 4) / (100 * S.A) < 2⁻¹ := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith [hΔ.2, hΔ.1]
  have hasf : 0 < S.a * sf := mul_pos ha0.1 hsf
  nlinarith

end LQGMetric.GM
