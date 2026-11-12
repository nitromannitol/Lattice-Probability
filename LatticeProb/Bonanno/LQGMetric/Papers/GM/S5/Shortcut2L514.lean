/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2L514 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2Out
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2Bump
import LatticeProb.Bonanno.LQGMetric.Metric.WeylPathLength

/-!
# GM Lemma 5.14, second assertion

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

`gm_L5_14b`: GM Lemma 5.14 (`lem-geomove-restrict`, l. 3420–3461), second assertion: no segment
of `P̄^φ` of Euclidean diameter `≥ ε₀r/100` is contained in `B_{2ζr}(∂U) ∖ 𝒲`. GM's proof
(l. 3438–3441): `φ ≤ K_f` off `𝒲`, so by Weyl scaling and condition (6) such a segment has
`D_{h−φ}`-length `≥ 100 e^{−ξK_f} A 𝔠_r e^{ξh_r(0)}`, more than the bound (5.40). Here the segment
is `P^φ([s, t])` with `s, t` outside the hitting balls; we use `φ < K_f + ξ⁻¹ log 2` on an open
neighbourhood of `ℂ ∖ 𝒲` (a factor `1/2`, absorbed since `50A > A + 4`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- a `C`-Lipschitz curve on `[a, b]` has length at most `C (b − a)` -/
lemma curveLength_le_lip_m2m2 {X : Type*} [PseudoMetricSpace X] {P : ℝ → X} {C a b : ℝ}
    (hC : 0 ≤ C) (hP : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (P s) (P t) ≤ C * dist s t) :
    curveLength P a b ≤ ENNReal.ofReal (C * (b - a)) := by
  have hL : LipschitzOnWith C.toNNReal P (Icc a b) :=
    LipschitzOnWith.of_dist_le_mul fun s hs t ht => by
      rw [Real.coe_toNNReal _ hC]; exact hP s hs t ht
  calc curveLength P a b = eVariationOn (P ∘ id) (Icc a b) := rfl
    _ ≤ C.toNNReal * eVariationOn id (Icc a b) := hL.comp_eVariationOn_le (mapsTo_id _)
    _ = ENNReal.ofReal (C * (b - a)) := by
        rw [eVariationOn_id_Icc, ENNReal.ofReal_mul hC]; rfl

/-- **GM Lemma 5.14**, second assertion (l. 3438–3441). -/
theorem gm_L5_14b {D D' : DistC → ContMetric} {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r)
    (hcr : 0 < S.c r) {U : ℂ → ℂ → Set ℂ} {fb gb : Set ℂ → TestC} (hU : IsTubeFam S U r)
    (hB : IsBumpChoice S U fb gb r) {g : DistC} (hg : g ∈ eventE D D' S U fb gb r)
    {z w x' y' : ℂ} (hx' : IsHitPt (D g) z x' r) (hy' : IsHitPt (D g) w y' r)
    (hsep : S.δ * r ≤ ‖(2 / 3 : ℂ) * x' - (2 / 3 : ℂ) * y'‖) (hlen : (D g).IsLength)
    (hW : ∀ a b : ℂ, ENNReal.ofReal ((D (subTest g (phiChoice S U fb gb r x' y'))).1 (a, b)) =
      weylScale S.ξ (-testCont (phiChoice S U fb gb r x' y')) (D g) a b)
    {Qφ : C(unitInterval, ℂ)} (hQφ : IsGeod01 (D (subTest g (phiChoice S U fb gb r x' y'))) z w Qφ)
    {s t : unitInterval} (hst : s ≤ t)
    (hs : (D g).1 (z, x') ≤ (D g).1 (z, Qφ s) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ s))
    (ht : (D g).1 (z, x') ≤ (D g).1 (z, Qφ t) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ t))
    (hin : ∀ τ ∈ Icc s t, Qφ τ ∈
      thickening (2 * S.ζ * r) (frontier (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y'))) \
        (thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * x')) ∪
          thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * y')))) :
    Metric.diam (Qφ '' Icc s t) < S.ε₀ * r / 100 := by
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
  by_contra hdiam
  push_neg at hdiam
  -- the curve on `[s, t] ⊂ ℝ`
  set P : ℝ → ℂ := fun τ => Qφ (projIcc 0 1 zero_le_one τ) with hP
  have hPc : Continuous P := Qφ.continuous.comp continuous_projIcc
  have himg : P '' Icc (s : ℝ) t = Qφ '' Icc s t := by
    ext q
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨s.2.1.trans hτ.1, hτ.2.trans t.2.2⟩
      refine ⟨projIcc 0 1 zero_le_one τ, ?_, rfl⟩
      rw [projIcc_of_mem _ hτ01]
      exact ⟨hτ.1, hτ.2⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨σ, ⟨hσ.1, hσ.2⟩, ?_⟩
      show Qφ (projIcc 0 1 zero_le_one (σ : ℝ)) = Qφ σ
      rw [projIcc_val]
  have hinP : ∀ τ ∈ Icc (s : ℝ) t, P τ ∈
      thickening (2 * S.ζ * r) (frontier (U x y)) \
        (thickening (S.θ ^ 2 * r) (lineTube S.θ r x) ∪
          thickening (S.θ ^ 2 * r) (lineTube S.θ r y)) := by
    intro τ hτ
    have : P τ ∈ Qφ '' Icc s t := himg ▸ mem_image_of_mem P hτ
    obtain ⟨σ, hσ, hσe⟩ := this
    rw [← hσe]; exact hin σ hσ
  -- condition (6)
  have h6 := hg.2.2.2.1 x hxs y hys hsep P s t hst hPc.continuousOn
    (fun q ⟨τ, hτ, hq⟩ => hq ▸ (hinP τ hτ).1) (by rw [himg]; exact hdiam)
  -- `φ ≤ K_f` off `𝒲`, hence on an open neighbourhood `V`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hξi : S.ξ * S.ξ⁻¹ = 1 := mul_inv_cancel₀ hξ.ne'
  set V : Set ℂ := {q | φ q < S.Kf + S.ξ⁻¹ * Real.log 2} with hV
  have hVo : IsOpen V := isOpen_lt (testCont φ).continuous continuous_const
  have hPV : ∀ τ ∈ Icc (s : ℝ) t, P τ ∈ V := fun τ hτ => by
    have h := (hinP τ hτ).2
    rw [mem_union, not_or] at h
    show φ (P τ) < S.Kf + S.ξ⁻¹ * Real.log 2
    rw [hφdef, bumpPhi_apply_m2m, hgx2 _ h.1, hgy2 _ h.2]
    have := (hfU0 (P τ)).2
    have : 0 < S.ξ⁻¹ * Real.log 2 := mul_pos (inv_pos.2 hξ) hl2
    nlinarith
  have ha : ∀ q ∈ V, -S.ξ * S.Kf - Real.log 2 ≤ S.ξ * (-testCont φ) q := fun q hq => by
    rw [hfe]
    have hq' : φ q < S.Kf + S.ξ⁻¹ * Real.log 2 := hq
    have := mul_lt_mul_of_pos_left hq' hξ
    rw [mul_add, ← mul_assoc, hξi, one_mul] at this
    linarith
  have hc : ContinuousOn ((D g).pt ∘ P) (Icc (s : ℝ) t) :=
    ((continuous_weylPt (D g)).comp hPc).continuousOn
  have hlow := le_curveLength_weyl D₁ hW hc hVo hPV ha
  -- the `D_{h−φ}`-length of the geodesic piece
  set L := D₁.1 (z, w)
  have hL0 : 0 ≤ L := nonneg_m2m D₁ z w
  have hup : curveLength (D₁.pt ∘ P) s t ≤ ENNReal.ofReal (L * ((t : ℝ) - s)) := by
    refine curveLength_le_lip_m2m2 hL0 fun a _ b _ => ?_
    show D₁.1 (P a, P b) ≤ L * dist a b
    rw [hQφ.2.2, Real.dist_eq, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    have := abs_projIcc_sub_projIcc (h := (zero_le_one : (0 : ℝ) ≤ 1)) (c := b) (d := a)
    rw [abs_sub_comm a b]; exact this
  have hLst : L * ((t : ℝ) - s) ≤ Real.exp (-S.ξ * S.Kf) * (S.A + 4) * sf := by
    have e := hQφ.2.2 s t
    rw [abs_of_nonneg (sub_nonneg.2 (show (s : ℝ) ≤ t from hst))] at e
    rw [mul_comm, ← e]; exact hclose.trans h513
  have hchain : ENNReal.ofReal (Real.exp (-S.ξ * S.Kf - Real.log 2) * (100 * S.A * sf)) ≤
      ENNReal.ofReal (Real.exp (-S.ξ * S.Kf) * (S.A + 4) * sf) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    calc ENNReal.ofReal (Real.exp (-S.ξ * S.Kf - Real.log 2)) * ENNReal.ofReal (100 * S.A * sf)
        ≤ ENNReal.ofReal (Real.exp (-S.ξ * S.Kf - Real.log 2)) *
            curveLength ((D g).pt ∘ P) s t := by gcongr; exact h6
      _ ≤ curveLength (D₁.pt ∘ P) s t := hlow
      _ ≤ _ := hup.trans (ENNReal.ofReal_le_ofReal hLst)
  have hE : 0 < Real.exp (-S.ξ * S.Kf) * sf := mul_pos (Real.exp_pos _) hsf
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity), Real.exp_sub, Real.exp_log (by norm_num)]
    at hchain
  nlinarith

end LQGMetric.GM
