/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2L514c at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2L514a

/-!
# GM Lemma 5.14: `P̄^φ` enters `B_{ζr}(U) ∪ 𝒲`

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

* `geod_lower_m2m2`: the bound of GM's proof of Lemma 5.12 (l. 3395–3398): a `D_h`-geodesic from
  `𝕫` to `𝕨` entering `B_{2r}(0)` has length `≥ σ + σ̂ + 2Δ'` when `Δ' ≤ D_h(∂B_{2r}, ∂B_{3r})`
  (the argument of `gm_L5_12`, `ShortcutHit.lean`, without its last step).
* `gm_L5_14_enter`: GM l. 3433–3437: "If `P̄^φ` did not enter the support `B_{ζr}(U) ∪ 𝒲` of `φ`,
  then the `D_{h−φ}`-length of `P̄^φ` would be the same as its `D_h`-length, which must be at least
  `2Δ𝔠_r e^{ξh_r(0)}` … Hence (5.40) implies that `P̄^φ` must enter `B_{ζr}(U) ∪ 𝒲`." Here: some
  time `τ` outside both hitting balls has `P^φ(τ) ∈ B_{ζr}(U) ∪ 𝒲`. (Proof: otherwise `φ ≡ 0` along
  all of `P^φ`, so `D_h(𝕫,𝕨) ≤ D_{h−φ}(𝕫,𝕨) ≤ σ + D_{h−φ}(𝕩',𝕪') + σ̂`, against
  `geod_lower_m2m2` and Lemma 5.13.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter
open scoped ENNReal Topology

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- GM l. 3395–3398 (proof of Lemma 5.12) -/
theorem geod_lower_m2m2 {D : ContMetric} {z w x' y' : ℂ} {r Δ' : ℝ} {Q : C(unitInterval, ℂ)}
    (hr : 0 < r) (hQ : IsGeod01 D z w Q) (hz : 4 * r ≤ ‖z‖) (hw : 4 * r ≤ ‖w‖)
    (hx : IsHitPt D z x' r) (hy : IsHitPt D w y' r)
    (hhit : (range Q ∩ Metric.ball (0 : ℂ) (2 * r)).Nonempty)
    (hsep : ENNReal.ofReal Δ' ≤ setDist D (Metric.sphere 0 (2 * r)) (Metric.sphere 0 (3 * r))) :
    D.1 (z, x') + D.1 (w, y') + 2 * Δ' ≤ D.1 (z, w) := by
  have hpq : ∀ p q : ℂ, ‖p‖ = 2 * r → ‖q‖ = 3 * r → Δ' ≤ D.1 (p, q) := by
    intro p q hp hq
    have := hsep.trans (setDist_le_m2m D (a := p) (b := q) (by simpa using hp) (by simpa using hq))
    exact (ENNReal.ofReal_le_ofReal_iff (nonneg_m2m D _ _)).1 this
  -- the times
  set L := D.1 (z, w) with hL
  let p : ℝ → unitInterval := fun t => projIcc 0 1 zero_le_one t
  have hpv : ∀ t ∈ Icc (0 : ℝ) 1, (p t : ℝ) = t := fun t ht => by
    simp only [p, projIcc_of_mem _ ht]
  have hdist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, D.1 (Q (p s), Q (p t)) = |t - s| * L :=
    fun s hs t ht => by rw [hQ.2.2, hpv s hs, hpv t ht]
  obtain ⟨_, ⟨s₀, rfl⟩, hs₀⟩ := hhit
  have hs₀' : ‖Q s₀‖ < 2 * r := by simpa using hs₀
  have hps₀ : projIcc (0 : ℝ) 1 zero_le_one s₀ = s₀ := projIcc_val zero_le_one s₀
  have hQ0 : Q (projIcc (0 : ℝ) 1 zero_le_one 0) = z := by
    rw [projIcc_left]; exact hQ.1
  have hQ1 : Q (projIcc (0 : ℝ) 1 zero_le_one 1) = w := by
    rw [projIcc_right]; exact hQ.2.1
  have s0m : (s₀ : ℝ) ∈ Icc (0 : ℝ) 1 := s₀.2
  -- first crossing (before `s₀`)
  obtain ⟨t₂, ht₂, hQt₂⟩ := exists_norm_eq_m2m Q le_rfl s0m.1 s0m.2 (c := 2 * r) (by
    rw [hps₀, hQ0]; exact mem_uIcc.2 (Or.inr ⟨hs₀'.le, by linarith⟩))
  obtain ⟨t₁, ht₁, hQt₁⟩ := exists_norm_eq_m2m Q le_rfl ht₂.1 (ht₂.2.trans s0m.2) (c := 3 * r) (by
    rw [hQ0, hQt₂]; exact mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩))
  -- second crossing (after `s₀`)
  obtain ⟨t₃, ht₃, hQt₃⟩ := exists_norm_eq_m2m Q s0m.1 s0m.2 le_rfl (c := 2 * r) (by
    rw [hps₀, hQ1]; exact mem_uIcc.2 (Or.inl ⟨hs₀'.le, by linarith⟩))
  obtain ⟨t₄, ht₄, hQt₄⟩ := exists_norm_eq_m2m Q (s0m.1.trans ht₃.1) ht₃.2 le_rfl (c := 3 * r) (by
    rw [hQ1, hQt₃]; exact mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩))
  have m1 : t₁ ∈ Icc (0 : ℝ) 1 := ⟨ht₁.1, ht₁.2.trans (ht₂.2.trans s0m.2)⟩
  have m2 : t₂ ∈ Icc (0 : ℝ) 1 := ⟨ht₂.1, ht₂.2.trans s0m.2⟩
  have m3 : t₃ ∈ Icc (0 : ℝ) 1 := ⟨s0m.1.trans ht₃.1, ht₃.2⟩
  have m4 : t₄ ∈ Icc (0 : ℝ) 1 := ⟨s0m.1.trans (ht₃.1.trans ht₄.1), ht₄.2⟩
  have z0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have o1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- the four pieces
  have d1 : D.1 (z, x') ≤ t₁ * L := by
    have := hx.2 (Q (p t₁)) (by simpa using hQt₁.le)
    rw [show z = Q (p 0) from hQ0.symm, hdist 0 z0 t₁ m1, sub_zero, abs_of_nonneg ht₁.1] at this
    rwa [show Q (p 0) = z from hQ0] at this
  have d2 : Δ' ≤ (t₂ - t₁) * L := by
    have := hpq (Q (p t₂)) (Q (p t₁)) hQt₂ hQt₁
    rwa [hdist t₂ m2 t₁ m1, abs_of_nonpos (by linarith [ht₁.2]), neg_sub] at this
  have d3 : Δ' ≤ (t₄ - t₃) * L := by
    have := hpq (Q (p t₃)) (Q (p t₄)) hQt₃ hQt₄
    rwa [hdist t₃ m3 t₄ m4, abs_of_nonneg (by linarith [ht₄.1])] at this
  have d4 : D.1 (w, y') ≤ (1 - t₄) * L := by
    have := hy.2 (Q (p t₄)) (by simpa using hQt₄.le)
    rw [show w = Q (p 1) from hQ1.symm, hdist 1 o1 t₄ m4, abs_of_nonpos (by linarith [ht₄.2]),
      neg_sub] at this
    rwa [show Q (p 1) = w from hQ1] at this
  have hord : t₂ ≤ t₃ := ht₂.2.trans ht₃.1
  have hL0 : 0 ≤ L := nonneg_m2m D _ _
  nlinarith [mul_le_mul_of_nonneg_right hord hL0]

/-- **GM Lemma 5.14**, entry step of the first assertion (l. 3433–3437). -/
theorem gm_L5_14_enter {D D' : DistC → ContMetric} {S : EData} (hS : S.Ranges) {r : ℝ}
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
    ∃ τ : unitInterval, ((D g).1 (z, x') ≤ (D g).1 (z, Qφ τ) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ τ)) ∧
      Qφ τ ∈ thickening (S.ζ * r) (U ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y')) ∪
        (thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * x')) ∪
          thickening (S.θ ^ 2 * r) (lineTube S.θ r ((2 / 3 : ℂ) * y'))) := by
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
  have hfU2 := (hB.1 x hxs y hys hsep).2.2
  set sf := scaleFac S.ξ S.c g r 0
  have hsf : 0 < sf := mul_pos hcr (Real.exp_pos _)
  by_contra hno
  push_neg at hno
  -- `φ ≡ 0` along `P^φ`
  have hzero : ∀ τ : unitInterval, φ (Qφ τ) = 0 := by
    intro τ
    by_cases hout : (D g).1 (z, x') ≤ (D g).1 (z, Qφ τ) ∧ (D g).1 (w, y') ≤ (D g).1 (w, Qφ τ)
    · have h := hno τ hout
      rw [mem_union, mem_union, not_or, not_or] at h
      rw [hφdef, bumpPhi_apply_m2m, hfU2 _ h.1, hgx2 _ h.2.1, hgy2 _ h.2.2]; ring
    · have hnb : Qφ τ ∉ closedBall (0 : ℂ) (3 * r) := by
        intro hc
        exact hout ⟨hx'.2 _ hc, hy'.2 _ hc⟩
      have := hf0 _ hnb
      rw [hfe] at this
      have : S.ξ * φ (Qφ τ) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hξ.ne'
  set P : ℝ → ℂ := fun τ => Qφ (projIcc 0 1 zero_le_one τ) with hP
  have hPc : Continuous P := Qφ.continuous.comp continuous_projIcc
  have hc : ContinuousOn ((D g).pt ∘ P) (Icc (0 : ℝ) 1) :=
    ((continuous_weylPt (D g)).comp hPc).continuousOn
  set L := D₁.1 (z, w)
  have hL0 : 0 ≤ L := nonneg_m2m D₁ z w
  have hup : curveLength (D₁.pt ∘ P) 0 1 ≤ ENNReal.ofReal (L * (1 - 0)) := by
    refine curveLength_le_lip_m2m2 hL0 fun a _ b _ => ?_
    show D₁.1 (P a, P b) ≤ L * dist a b
    rw [hQφ.2.2, Real.dist_eq, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    have := abs_projIcc_sub_projIcc (h := (zero_le_one : (0 : ℝ) ≤ 1)) (c := b) (d := a)
    rw [abs_sub_comm a b]; exact this
  have hP0 : P 0 = z := by show Qφ (projIcc 0 1 zero_le_one 0) = z; rw [projIcc_left]; exact hQφ.1
  have hP1 : P 1 = w := by
    show Qφ (projIcc 0 1 zero_le_one 1) = w; rw [projIcc_right]; exact hQφ.2.1
  -- `D_h(𝕫, 𝕨) ≤ e^ε L` for all `ε > 0`
  have hle : ∀ ε : ℝ, 0 < ε → (D g).1 (z, w) ≤ Real.exp ε * L := by
    intro ε hε
    have hVo : IsOpen {q : ℂ | φ q < ε / S.ξ} := isOpen_lt (testCont φ).continuous continuous_const
    have hPV : ∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ {q : ℂ | φ q < ε / S.ξ} := fun τ _ => by
      show φ (Qφ _) < ε / S.ξ
      rw [hzero]; exact div_pos hε hξ
    have ha : ∀ q ∈ {q : ℂ | φ q < ε / S.ξ}, -ε ≤ S.ξ * (-testCont φ) q := fun q hq => by
      rw [hfe]
      have hq' : φ q < ε / S.ξ := hq
      have := mul_lt_mul_of_pos_left hq' hξ
      rw [mul_div_cancel₀ _ hξ.ne'] at this
      linarith
    have hlow := le_curveLength_weyl D₁ hW hc hVo hPV ha
    have hd0 := edist_le_curveLength ((D g).pt ∘ P) (zero_le_one (α := ℝ))
    rw [edist_dist] at hd0
    have hd : ENNReal.ofReal ((D g).1 (z, w)) ≤ curveLength ((D g).pt ∘ P) 0 1 := by
      calc ENNReal.ofReal ((D g).1 (z, w)) = ENNReal.ofReal ((D g).1 (P 0, P 1)) := by
            rw [hP0, hP1]
        _ ≤ _ := hd0
    have h1 : ENNReal.ofReal (Real.exp (-ε)) * ENNReal.ofReal ((D g).1 (z, w)) ≤
        ENNReal.ofReal (L * (1 - 0)) := by
      refine le_trans ?_ (hlow.trans hup)
      gcongr
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_le_ofReal_iff (by positivity),
      sub_zero, mul_one] at h1
    have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos ε).le
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at this
  have hDL : (D g).1 (z, w) ≤ L := by
    have ht : Tendsto (fun ε : ℝ => Real.exp ε * L) (𝓝[>] 0) (𝓝 L) := by
      have := ((Real.continuous_exp.mul continuous_const).tendsto (0 : ℝ) (f := fun ε => Real.exp ε * L))
      rw [Real.exp_zero, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
  -- `L ≤ σ + D'(𝕩', 𝕪') + σ̂`
  have hL : L ≤ (D g).1 (z, x') + D₁.1 (x', y') + (D g).1 (w, y') := by
    have t1 := dist_triangle_m2m D₁ z x' w
    have t2 := dist_triangle_m2m D₁ x' y' w
    have t3 := weyl_le_self_m2m2 hW hlen hf z x'
    have t4 := weyl_le_self_m2m2 hW hlen hf y' w
    have t5 := dist_comm_m2m (D g) w y'
    linarith
  have hlow := geod_lower_m2m2 hr hQ hz hw hx' hy' hhit
    ((hg.2.1 x hxs x hxs (by rw [sub_self, norm_zero]; exact mul_pos hS.2.1.1 hr)).2)
  rw [exp_Kf_m2m2 hS] at h513
  have ha0 := hS.2.2.2.2.2.2.2.1
  have hΔ := hS.2.2.2.2.2.1
  have hA1 := hS.2.2.2.2.2.2.2.2.2.1
  have hA0 : 0 < S.A := by linarith
  have e2 : S.a * S.Δ / (100 * S.A) * (S.A + 4) * sf = S.Δ * sf * (S.a * (S.A + 4) / (100 * S.A)) := by
    field_simp
  rw [e2] at h513
  have hq : S.a * (S.A + 4) / (100 * S.A) < 2 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith [ha0.2, ha0.1]
  have hΔsf : 0 < S.Δ * sf := mul_pos hΔ.1 hsf
  nlinarith

end LQGMetric.GM
