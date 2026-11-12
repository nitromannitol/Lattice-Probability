/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.ShortcutHit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.EventDefs

/-!
# GM Lemma 5.12: the hitting points are `δr`-separated

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, Lemma 5.12 (`lem-hitpt-lower`,
l. 3391–3401), proof followed verbatim: a geodesic from `𝕫` to `𝕨` which enters `B_{2r}(0)` crosses
`𝔸_{2r,3r}(0)` twice after leaving the first metric ball and before reaching the second one, so
`D(𝕫,𝕨) ≥ σ_𝕫 + σ_𝕨 + 2 D(∂B_{2r},∂B_{3r})`; condition (4) of `E_r` gives
`D(𝕫,𝕨) ≤ σ_𝕫 + D(𝕩',𝕪') + σ_𝕨 ≤ σ_𝕫 + σ_𝕨 + Δ𝔠_r e^{ξh_r(0)}` if `|𝕩 − 𝕪| < δr`.
Deterministic statement for one continuous metric `D = D_h` (task P2-M2M).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the internal distance dominates the distance -/
lemma ofReal_le_internal_m2m (D : ContMetric) (U : Set ℂ) (a b : ℂ) :
    ENNReal.ofReal (D.1 (a, b)) ≤ D.internal U a b := by
  have := MetricGeometry.edist_le_internalEDist (X := D.Space) (D.pt '' U) (D.pt a) (D.pt b)
  rw [edist_dist] at this
  exact this

lemma nonneg_m2m (D : ContMetric) (a b : ℂ) : 0 ≤ D.1 (a, b) :=
  dist_nonneg (x := D.pt a) (y := D.pt b)

/-- the set distance is at most the distance of two points of the sets -/
lemma setDist_le_m2m (D : ContMetric) {A B : Set ℂ} {a b : ℂ} (ha : a ∈ A) (hb : b ∈ B) :
    setDist D A B ≤ ENNReal.ofReal (D.1 (a, b)) := by
  have := MetricGeometry.setEDist_le_edist (X := D.Space) (mem_image_of_mem D.pt ha)
    (mem_image_of_mem D.pt hb)
  rw [edist_dist] at this
  exact this

/-- intermediate values of `‖Q‖` along a path on `[0,1]` -/
lemma exists_norm_eq_m2m (Q : C(unitInterval, ℂ)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    {c : ℝ} (hc : c ∈ uIcc ‖Q (projIcc 0 1 zero_le_one a)‖ ‖Q (projIcc 0 1 zero_le_one b)‖) :
    ∃ t ∈ Icc a b, ‖Q (projIcc 0 1 zero_le_one t)‖ = c := by
  have hcont : Continuous fun t : ℝ => ‖Q (projIcc 0 1 zero_le_one t)‖ :=
    (Q.continuous.comp continuous_projIcc).norm
  obtain ⟨t, ht, hct⟩ := intermediate_value_uIcc (hcont.continuousOn) hc
  rw [uIcc_of_le hab] at ht
  exact ⟨t, ht, hct⟩

/-- **GM Lemma 5.12** (`lem-hitpt-lower`, l. 3391–3401), deterministic form: if `Q` is a
`D`-geodesic from `𝕫` to `𝕨` (`𝕫, 𝕨 ∉ B_{4r}(0)`) which enters `B_{2r}(0)`, `𝕩'`, `𝕪'` are
hitting points of `∂B_{3r}(0)` from `𝕫`, `𝕨`, and condition (4) of `E_r` holds with
`Δ' = Δ𝔠_r e^{ξh_r(0)} > 0`, then `|𝕩 − 𝕪| ≥ δr` for `𝕩 = 2𝕩'/3`, `𝕪 = 2𝕪'/3`. -/
theorem gm_L5_12 {D : ContMetric} {z w x' y' : ℂ} {r δ Δ' : ℝ} {Q : C(unitInterval, ℂ)}
    (hr : 0 < r) (hQ : IsGeod01 D z w Q) (hz : 4 * r ≤ ‖z‖) (hw : 4 * r ≤ ‖w‖)
    (hx : IsHitPt D z x' r) (hy : IsHitPt D w y' r)
    (hhit : (range Q ∩ Metric.ball (0 : ℂ) (2 * r)).Nonempty) (hΔ : 0 < Δ')
    (h4 : ∀ x ∈ Metric.sphere (0 : ℂ) (2 * r), ∀ y ∈ Metric.sphere (0 : ℂ) (2 * r),
      ‖x - y‖ < δ * r →
      D.internal (annulus 0 r (4 * r)) ((3 / 2 : ℂ) * x) ((3 / 2 : ℂ) * y) ≤ ENNReal.ofReal Δ' ∧
      ENNReal.ofReal Δ' ≤ setDist D (Metric.sphere 0 (2 * r)) (Metric.sphere 0 (3 * r))) :
    δ * r ≤ ‖(2 / 3 : ℂ) * x' - (2 / 3 : ℂ) * y'‖ := by
  by_contra hlt
  push_neg at hlt
  have hnx : ‖(2 / 3 : ℂ) * x'‖ = 2 * r := by
    rw [norm_mul, hx.1]; norm_num; ring
  have hny : ‖(2 / 3 : ℂ) * y'‖ = 2 * r := by
    rw [norm_mul, hy.1]; norm_num; ring
  obtain ⟨hint, hsep⟩ := h4 _ (by simpa using hnx) _ (by simpa using hny) hlt
  have e1 : (3 / 2 : ℂ) * ((2 / 3 : ℂ) * x') = x' := by ring
  have e2 : (3 / 2 : ℂ) * ((2 / 3 : ℂ) * y') = y' := by ring
  rw [e1, e2] at hint
  -- `D(𝕩', 𝕪') ≤ Δ'`
  have hxy : D.1 (x', y') ≤ Δ' :=
    (ENNReal.ofReal_le_ofReal_iff hΔ.le).1 ((ofReal_le_internal_m2m D _ _ _).trans hint)
  -- `Δ' ≤ D(p, q)` for `p ∈ ∂B_{2r}`, `q ∈ ∂B_{3r}`
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
  -- triangle inequality
  have htri : L ≤ D.1 (z, x') + D.1 (x', y') + D.1 (w, y') := by
    have a1 := D.2.triangle z x' w
    have a2 := D.2.triangle x' y' w
    have a3 := D.2.symm w y'
    linarith
  have hord : t₂ ≤ t₃ := ht₂.2.trans ht₃.1
  have hL0 : 0 ≤ L := nonneg_m2m D _ _
  nlinarith [mul_le_mul_of_nonneg_right hord hL0]

end LQGMetric.GM
