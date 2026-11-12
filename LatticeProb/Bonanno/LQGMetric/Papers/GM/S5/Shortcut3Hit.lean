/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut3Hit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut3Core

/-!
# GM Lemma 5.11, entry step: the first hitting time (decision D83 (a))

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M3, decision D83 packet P2, steps 1 and 3 of `decisions/DEC-83.md` §3).

* `gm_L5_12_sum`: the inequality `D(𝕫,𝕩') + 2Δ' + D(𝕨,𝕪') ≤ D(𝕫,𝕨)` from GM's proof of
  Lemma 5.12 (l. 3395–3399), for a `D`-geodesic from `𝕫` to `𝕨` entering `B_{2r}(0)`; the proof is
  the corresponding part of `gm_L5_12` (`ShortcutHit.lean`).
* `entry_first_hit_m2m3`: decision D83 (a) in abstract form. If `D₁ = e^{ξ f}·D` with
  `ξ f ≤ 0` vanishing off `cl B_{3r}(0)`, `Qφ` is a `D₁`-geodesic from `𝕫` to `𝕨`,
  `D₁(𝕩',𝕪') ≤ Λ < Δ'`, the Lemma 5.12 inequality holds, every point of `Qφ` on `∂B_{3r}(0)` between
  the hitting balls is within `c` of `𝕩'` or `𝕪'` (Lemma 5.14) and points of `∂B_{3r}(0)` within
  `c` of `𝕪'` are `D`-close to `𝕪'` (condition (4)), then the first hitting time `τ₁` of
  `cl B_{3r}(0)` by `Qφ` has `Qφ(τ₁)` within `c` of `𝕩'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the inequality of GM's proof of Lemma 5.12 (l. 3395–3399):
`D(𝕫,𝕩') + 2Δ' + D(𝕨,𝕪') ≤ D(𝕫,𝕨)` (proof copied from `gm_L5_12`) -/
theorem gm_L5_12_sum {D : ContMetric} {z w x' y' : ℂ} {r Δ' : ℝ} {Q : C(unitInterval, ℂ)}
    (hr : 0 < r) (hQ : IsGeod01 D z w Q) (hz : 4 * r ≤ ‖z‖) (hw : 4 * r ≤ ‖w‖)
    (hx : IsHitPt D z x' r) (hy : IsHitPt D w y' r)
    (hhit : (range Q ∩ Metric.ball (0 : ℂ) (2 * r)).Nonempty)
    (hsep : ENNReal.ofReal Δ' ≤ setDist D (Metric.sphere 0 (2 * r)) (Metric.sphere 0 (3 * r))) :
    D.1 (z, x') + 2 * Δ' + D.1 (w, y') ≤ D.1 (z, w) := by
  have hpq : ∀ p q : ℂ, ‖p‖ = 2 * r → ‖q‖ = 3 * r → Δ' ≤ D.1 (p, q) := by
    intro p q hp hq
    have := hsep.trans (setDist_le_m2m D (a := p) (b := q) (by simpa using hp) (by simpa using hq))
    exact (ENNReal.ofReal_le_ofReal_iff (nonneg_m2m D _ _)).1 this
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
  obtain ⟨t₂, ht₂, hQt₂⟩ := exists_norm_eq_m2m Q le_rfl s0m.1 s0m.2 (c := 2 * r) (by
    rw [hps₀, hQ0]; exact mem_uIcc.2 (Or.inr ⟨hs₀'.le, by linarith⟩))
  obtain ⟨t₁, ht₁, hQt₁⟩ := exists_norm_eq_m2m Q le_rfl ht₂.1 (ht₂.2.trans s0m.2) (c := 3 * r) (by
    rw [hQ0, hQt₂]; exact mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩))
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

/-- **decision D83 (a)**, abstract form: the first hitting time `τ₁` of `cl B_{3r}(0)` by the
`D₁`-geodesic `Qφ` lies near `𝕩'`, and after `τ₁` the path stays outside the hitting ball of `𝕫`. -/
theorem entry_first_hit_m2m3 {Dg D₁ : ContMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hW : ∀ a b : ℂ, ENNReal.ofReal (D₁.1 (a, b)) = weylScale ξ f Dg a b) (hlen : Dg.IsLength)
    (hf : ∀ q, ξ * f q ≤ 0) {r : ℝ} (hf0 : ∀ q ∉ closedBall (0 : ℂ) (3 * r), ξ * f q = 0)
    {z w x' y' : ℂ} (hz : 3 * r < ‖z‖) (hx : IsHitPt Dg z x' r) (hy : IsHitPt Dg w y' r)
    {Qφ : C(unitInterval, ℂ)} (hQ : IsGeod01 D₁ z w Qφ) {Λ Δ' c : ℝ}
    (hxy : D₁.1 (x', y') ≤ Λ) (hΛ : Λ < Δ')
    (hsum : Dg.1 (z, x') + 2 * Δ' + Dg.1 (w, y') ≤ Dg.1 (z, w))
    (hnear : ∀ τ : unitInterval, ‖Qφ τ‖ = 3 * r → Dg.1 (z, x') ≤ Dg.1 (z, Qφ τ) →
      Dg.1 (w, y') ≤ Dg.1 (w, Qφ τ) → ‖Qφ τ - x'‖ < c ∨ ‖Qφ τ - y'‖ < c)
    (h4 : ∀ q : ℂ, ‖q‖ = 3 * r → ‖q - y'‖ < c → Dg.1 (q, y') ≤ Δ') :
    ∃ τ₁ : unitInterval, ‖Qφ τ₁‖ = 3 * r ∧ ‖Qφ τ₁ - x'‖ < c ∧
      (∀ τ : unitInterval, τ < τ₁ → 3 * r < ‖Qφ τ‖) ∧
      (∀ τ : unitInterval, τ₁ ≤ τ → Dg.1 (z, x') ≤ Dg.1 (z, Qφ τ)) := by
  set L := D₁.1 (z, w) with hLdef
  have hL0 : 0 ≤ L := nonneg_m2m _ _ _
  have hzτ : ∀ τ : unitInterval, D₁.1 (z, Qφ τ) = τ * L := fun τ => by
    rw [← hQ.1, hQ.2.2, Set.Icc.coe_zero, sub_zero, abs_of_nonneg τ.2.1, hLdef]
  have hwτ : ∀ τ : unitInterval, D₁.1 (w, Qφ τ) = (1 - τ) * L := fun τ => by
    rw [← hQ.2.1, hQ.2.2, Set.Icc.coe_one, abs_of_nonpos (by linarith [τ.2.2]), hLdef]; ring
  have hle : ∀ a b : ℂ, D₁.1 (a, b) ≤ Dg.1 (a, b) := weyl_le_self_m2m2 hW hlen hf
  have hxy0 : 0 ≤ D₁.1 (x', y') := nonneg_m2m _ _ _
  -- `L ≤ σ_𝕫 + Λ + σ_𝕨`
  have hL : L ≤ Dg.1 (z, x') + Λ + Dg.1 (w, y') := by
    have t1 := dist_triangle_m2m D₁ z x' w
    have t2 := dist_triangle_m2m D₁ x' y' w
    have t3 := hle z x'
    have t4 := hle y' w
    have t5 := dist_comm_m2m Dg w y'
    linarith
  set V : Set ℂ := (closedBall (0 : ℂ) (3 * r))ᶜ with hV
  have hVo : IsOpen V := isClosed_closedBall.isOpen_compl
  have hfV : ∀ q ∈ V, ξ * f q = 0 := fun q hq => hf0 q hq
  -- the set of hitting times is nonempty
  set P : ℝ → ℂ := fun t => Qφ (projIcc 0 1 zero_le_one t) with hP
  have hPc : Continuous P := Qφ.continuous.comp continuous_projIcc
  set T : Set ℝ := Icc 0 1 ∩ {t | ‖P t‖ ≤ 3 * r} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le hPc.norm continuous_const)
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  have hTne : T.Nonempty := by
    by_contra hne
    have hall : ∀ t : unitInterval, Qφ t ∈ V := fun t => by
      by_contra hn
      refine hne ⟨t, t.2, ?_⟩
      simp only [hV, mem_compl_iff, not_not, mem_closedBall, dist_zero_right] at hn
      show ‖Qφ (projIcc 0 1 zero_le_one (t : ℝ))‖ ≤ 3 * r
      rwa [projIcc_val]
    have h := dist_le_weyl_of_geod_m2m3 hW hVo hfV hQ (fun t _ => hall t)
    linarith
  set t₁ := sInf T with ht₁
  have ht₁T : t₁ ∈ T := hTc.csInf_mem hTne hTb
  set τ₁ : unitInterval := ⟨t₁, ht₁T.1⟩ with hτ₁
  have hPτ₁ : P t₁ = Qφ τ₁ := by
    show Qφ (projIcc 0 1 zero_le_one t₁) = _; rw [projIcc_of_mem _ ht₁T.1]
  -- before `τ₁` the path is outside `cl B_{3r}(0)`
  have hbefore : ∀ τ : unitInterval, τ < τ₁ → 3 * r < ‖Qφ τ‖ := fun τ hτ => by
    by_contra hn
    push_neg at hn
    have hmem : (τ : ℝ) ∈ T := ⟨τ.2, by
      show ‖Qφ (projIcc 0 1 zero_le_one (τ : ℝ))‖ ≤ 3 * r; rwa [projIcc_val]⟩
    have := csInf_le hTb hmem
    exact absurd hτ (not_lt.2 this)
  -- `‖Qφ τ₁‖ = 3r`
  have hQ0 : P 0 = z := by
    show Qφ (projIcc 0 1 zero_le_one 0) = z; rw [projIcc_left]; exact hQ.1
  have hn₁ : ‖Qφ τ₁‖ = 3 * r := by
    obtain ⟨t, ht, hPt⟩ := exists_norm_eq_m2m Qφ le_rfl ht₁T.1.1 ht₁T.1.2 (c := 3 * r) (by
      rw [show Qφ (projIcc 0 1 zero_le_one 0) = z from hQ0,
        show Qφ (projIcc 0 1 zero_le_one t₁) = Qφ τ₁ from hPτ₁]
      exact mem_uIcc.2 (Or.inr ⟨by rw [← hPτ₁]; exact ht₁T.2, hz.le⟩))
    have htT : t ∈ T := ⟨⟨ht.1, ht.2.trans ht₁T.1.2⟩, by show ‖P t‖ ≤ 3 * r; rw [hP]; simp only; rw [hPt]⟩
    have := csInf_le hTb htT
    have he : t = t₁ := le_antisymm ht.2 this
    rw [← hPτ₁, ← he]; exact hPt
  have hτ₁B : Qφ τ₁ ∈ closedBall (0 : ℂ) (3 * r) := by
    rw [mem_closedBall, dist_zero_right, hn₁]
  have hτ₁0 : (0 : unitInterval) < τ₁ := by
    by_contra h0
    have he : τ₁ = 0 := le_antisymm (not_lt.1 h0) τ₁.2.1
    rw [he, hQ.1] at hn₁
    linarith
  -- `D(𝕫, Qφ τ₁) ≤ D₁(𝕫, Qφ τ₁) = τ₁ L`
  have hloc : Dg.1 (z, Qφ τ₁) ≤ D₁.1 (z, Qφ τ₁) := by
    refine dist_le_weyl_of_geod_m2m3 hW hVo hfV (isGeod01_sub_m2m3 hQ τ₁) fun t ht => ?_
    have h := hbefore (mulMap01 τ₁ t) (by
      show (τ₁ : ℝ) * t < τ₁
      exact mul_lt_of_lt_one_right (show (0 : ℝ) < τ₁ from hτ₁0) (show (t : ℝ) < 1 from ht))
    simp only [hV, mem_compl_iff, mem_closedBall, dist_zero_right, not_le,
      ContinuousMap.comp_apply]
    exact h
  have hwloc : Dg.1 (w, y') ≤ D₁.1 (w, Qφ τ₁) := hit_ball_local_m2m2 hW hf0 hy (hy.2 _ hτ₁B)
  have hz₁ : Dg.1 (z, Qφ τ₁) ≤ Dg.1 (z, x') + Λ := by
    rw [hwτ] at hwloc
    rw [hzτ] at hloc
    nlinarith
  have hzx : Dg.1 (z, x') ≤ D₁.1 (z, Qφ τ₁) := hit_ball_local_m2m2 hW hf0 hx (hx.2 _ hτ₁B)
  refine ⟨τ₁, hn₁, ?_, fun τ hτ => hbefore τ hτ, fun τ hτ => ?_⟩
  · rcases hnear τ₁ hn₁ (hx.2 _ hτ₁B) (hy.2 _ hτ₁B) with h | h
    · exact h
    · exfalso
      have h5 := h4 _ hn₁ h
      have t1 := dist_triangle_m2m Dg z (Qφ τ₁) w
      have t2 := dist_triangle_m2m Dg (Qφ τ₁) y' w
      have t3 := dist_comm_m2m Dg w y'
      linarith
  · rw [hzτ] at hzx
    have h1 : (τ₁ : ℝ) * L ≤ τ * L := mul_le_mul_of_nonneg_right hτ hL0
    have h2 := hle z (Qφ τ)
    rw [hzτ] at h2
    linarith

end LQGMetric.GM
