/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.IterateT42 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.IterateUnion
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodS46
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStab

/-!
# GM Theorem 4.2: the union bound with the grid count, and the far-witness lemma

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Theorem 4.2
(`thm-geo-iterate`, l. 2437–2446).

* `gm_T4_2_assembly`: "truncate on `ℰ_𝕣`, then take a union bound over all pairs
  `𝕫, 𝕨 ∈ (ε^q𝕣ℤ²) ∩ (𝕣U)`": if `P[ℰᶜ] ≤ η/2` and, for every admissible pair,
  `P[ℰ ∩ (no witness for (𝕫,𝕨))] ≤ C ε^{4q+1}` (Prop 4.17 gives `o^∞_ε(ε)`, here used with
  `M = 4q + 1`), then for `ε < ε₁(q, ρ, C, η)` the event of the theorem fails with probability
  `≤ η`, where `U ⊆ B_ρ(0)`. The number of pairs is `≤ 16(ρ+2)⁴ε^{-4q}`
  (`gm_grid_card_le`; implicit in the paper). `ε₁` depends only on `q, ρ, C, η`, uniformly in
  `𝕣` and the events (GM: "at a rate depending only on `U, q, ℓ, …`").
* `gm_T4_2_far`: the witness `(z, r) ∈ 𝒵_k` (GM (4.10)) satisfies `𝕫, 𝕨 ∉ B_{λ₃r}(z)` (the extra
  conjunct of the orchestrator's note / D74): `𝕫 ∈ 𝓑^•_{t_k}`, `dist(z, ∂𝓑^•_{t_k}) ≥ λ₄ε𝕣 ≥ λ₃r`,
  and `𝓑^•_{t_k} ⊆ B_{3ℓ𝕣}(𝕫)` on `ℰ_𝕣` (GM l. 2386) with `|𝕫 − 𝕨| ≥ 4ℓ𝕣` (own elementary
  argument, recorded as DV-M2K-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-! ## The witness is far from `𝕫` and `𝕨` -/

/-- **GM (4.10) ⇒ `𝕫, 𝕨 ∉ B_{λ₃r}(z)`** for `(z, r)` a candidate pair of `K = 𝓑^•_{t_k}`. -/
theorem gm_T4_2_far {K : Set ℂ} (hK : IsClosed K) {𝕫 𝕨 z : ℂ} {r lam1 lam3 lam4 ε ν 𝕣 L : ℝ}
    {Rads : Set ℝ} (hz : (z, r) ∈ candSet K lam1 lam4 ε ν 𝕣 Rads) (h𝕫 : 𝕫 ∈ K)
    (hpos : 0 < lam4 * ε * 𝕣) (hr : lam3 * r ≤ lam4 * ε * 𝕣)
    (hKL : frontier K ⊆ closedBall 𝕫 L)
    (hfar : L + 2 * lam4 * ε * 𝕣 + lam3 * r < ‖𝕫 - 𝕨‖) :
    𝕫 ∉ ball z (lam3 * r) ∧ 𝕨 ∉ ball z (lam3 * r) := by
  obtain ⟨-, hzK, -, hlo, hhi⟩ := hz
  dsimp only at hzK hlo hhi
  have hKne : K.Nonempty := ⟨𝕫, h𝕫⟩
  have hfr : (frontier K).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    simp only [hne, infDist_empty] at hlo
    linarith
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have h1 : infDist z K ≤ dist z 𝕫 := infDist_le_dist_of_mem h𝕫
    rw [← gm_infDist_frontier_eq hK hKne hzK] at h1
    rw [mem_ball, dist_comm] at hb
    linarith
  · obtain ⟨p, hp, hzp⟩ := (infDist_lt_iff hfr).1
      (lt_of_le_of_lt hhi (show 2 * lam4 * ε * 𝕣 < 2 * lam4 * ε * 𝕣 + (‖𝕫 - 𝕨‖ - L -
        2 * lam4 * ε * 𝕣 - lam3 * r) by linarith))
    have hp𝕫 := hKL hp
    rw [mem_closedBall, dist_comm] at hp𝕫
    rw [mem_ball, dist_comm] at hb
    have t1 := dist_triangle4 𝕫 p z 𝕨
    rw [dist_comm p z, dist_eq_norm 𝕫 𝕨] at t1
    linarith

/-! ## The grid is finite -/

/-- the points `(s : ℂ)(m₁ + m₂ i)` with `‖·‖ < L` form a finite set -/
theorem gm_grid_finite {s L : ℝ} (hs : 0 < s) :
    {a : ℂ | (∃ m : ℤ × ℤ, a = (s : ℂ) * (m.1 + m.2 * Complex.I)) ∧ ‖a‖ < L}.Finite := by
  set N : ℤ := ⌈L / s⌉
  refine ((((Finset.Icc (-N) N) ×ˢ (Finset.Icc (-N) N)).image
    (fun m : ℤ × ℤ => (s : ℂ) * (m.1 + m.2 * Complex.I))).finite_toSet).subset ?_
  rintro a ⟨⟨m, rfl⟩, ha⟩
  simp only [Finset.coe_image, Finset.coe_product, Finset.coe_Icc, mem_image, mem_prod, mem_Icc]
  refine ⟨m, ?_, rfl⟩
  have e1 : ((s : ℂ) * (m.1 + m.2 * Complex.I)).re = s * m.1 := by simp
  have e2 : ((s : ℂ) * (m.1 + m.2 * Complex.I)).im = s * m.2 := by simp
  have hre := Complex.abs_re_le_norm ((s : ℂ) * (m.1 + m.2 * Complex.I))
  have him := Complex.abs_im_le_norm ((s : ℂ) * (m.1 + m.2 * Complex.I))
  rw [e1, abs_mul, abs_of_pos hs] at hre
  rw [e2, abs_mul, abs_of_pos hs] at him
  have hN : L / s ≤ (N : ℝ) := Int.le_ceil _
  rw [div_le_iff₀ hs] at hN
  have h1 : |(m.1 : ℝ)| ≤ N := by
    by_contra h; push_neg at h; nlinarith
  have h2 : |(m.2 : ℝ)| ≤ N := by
    by_contra h; push_neg at h; nlinarith
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  exact ⟨⟨by exact_mod_cast a1.1, by exact_mod_cast a1.2⟩,
    ⟨by exact_mod_cast a2.1, by exact_mod_cast a2.2⟩⟩

/-! ## The assembly -/

open scoped Classical in
/-- **The union bound of the proof of GM Theorem 4.2** (l. 2441–2446), with the grid count and
the rate: `ε₁` depends only on `q, ρ, C, η`. -/
theorem gm_T4_2_assembly {q ρ C η : ℝ} (hq : 0 < q) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁, ∀ R : ℝ, 0 < R → ∀ U : Set ℂ,
      U ⊆ ball (0 : ℂ) ρ →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Reg : Set Ω)
      (Adm : ℂ → ℂ → Prop) (Good : ℂ → ℂ → Set Ω),
      P.real Regᶜ ≤ η / 2 →
      (∀ a b, a ∈ (fun x => (R : ℂ) * x) '' U → b ∈ (fun x => (R : ℂ) * x) '' U → Adm a b →
        P.real (Reg ∩ (Good a b)ᶜ) ≤ C * ε ^ (4 * q + 1)) →
      P {ω | ∀ a b : ℂ, (∃ m : ℤ × ℤ, a = ((ε ^ q * R : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
        (∃ m : ℤ × ℤ, b = ((ε ^ q * R : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
        a ∈ (fun x => (R : ℂ) * x) '' U → b ∈ (fun x => (R : ℂ) * x) '' U → Adm a b →
        ω ∈ Good a b}ᶜ ≤ ENNReal.ofReal η := by
  set A : ℝ := 16 * (ρ + 2) ^ 4 * C
  have hA : 0 ≤ A := by positivity
  refine ⟨min 1 (η / (2 * (A + 1))), lt_min one_pos (by positivity), ?_⟩
  intro ε hε R hR U hU Ω _ P _ Reg Adm Good hReg hpair
  have hε0 := hε.1
  have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
  have hεA : ε < η / (2 * (A + 1)) := hε.2.trans_le (min_le_right _ _)
  set s : ℝ := ε ^ q * R
  have hεq : 0 < ε ^ q := Real.rpow_pos_of_pos hε0 q
  have hεq1 : ε ^ q ≤ 1 := Real.rpow_le_one hε0.le hε1.le hq.le
  have hs : 0 < s := mul_pos hεq hR
  -- the finite set of grid points of `𝕣U`
  set G := {a : ℂ | (∃ m : ℤ × ℤ, a = (s : ℂ) * (m.1 + m.2 * Complex.I)) ∧ ‖a‖ < ρ * R}
  have hGf : G.Finite := gm_grid_finite hs
  set S0 : Finset ℂ := hGf.toFinset
  have hRU : ∀ a ∈ (fun x => (R : ℂ) * x) '' U, ‖a‖ < ρ * R := by
    rintro a ⟨x, hx, rfl⟩
    have := hU hx
    rw [mem_ball, dist_zero_right] at this
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le, mul_comm]
    exact mul_lt_mul_of_pos_right this hR
  have hS0 : (S0.card : ℝ) * s ^ 2 ≤ 4 * (ρ * R + 2 * s) ^ 2 :=
    gm_grid_card_le hs (by positivity) S0 fun z hz => by
      rw [Set.Finite.mem_toFinset] at hz
      exact ⟨gm_mem_gridPts_of_T42 hz.1, hz.2⟩
  -- `#S0 ≤ 4(ρ + 2)² ε^{-2q}`
  have hS0' : (S0.card : ℝ) * (ε ^ q) ^ 2 ≤ 4 * (ρ + 2) ^ 2 := by
    have e : 4 * (ρ * R + 2 * s) ^ 2 = 4 * (ρ + 2 * ε ^ q) ^ 2 * R ^ 2 := by
      simp only [s]; ring
    have e2 : (S0.card : ℝ) * s ^ 2 = (S0.card : ℝ) * (ε ^ q) ^ 2 * R ^ 2 := by
      simp only [s]; ring
    rw [e, e2] at hS0
    have h1 := le_of_mul_le_mul_right hS0 (by positivity)
    have : (ρ + 2 * ε ^ q) ^ 2 ≤ (ρ + 2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    linarith
  -- the pairs
  set S : Finset (ℂ × ℂ) := (S0 ×ˢ S0).filter (fun x => x.1 ∈ (fun x => (R : ℂ) * x) '' U ∧
    x.2 ∈ (fun x => (R : ℂ) * x) '' U ∧ Adm x.1 x.2)
  have hScard : (S.card : ℝ) * ε ^ (4 * q) ≤ 16 * (ρ + 2) ^ 4 := by
    have h1 : (S.card : ℝ) ≤ S0.card * S0.card := by
      have := Finset.card_filter_le (S0 ×ˢ S0) (fun x => x.1 ∈ (fun x => (R : ℂ) * x) '' U ∧
        x.2 ∈ (fun x => (R : ℂ) * x) '' U ∧ Adm x.1 x.2)
      rw [Finset.card_product] at this
      exact_mod_cast this
    have e : ε ^ (4 * q) = ((ε ^ q) ^ 2) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hε0.le,
        ← Real.rpow_mul (by positivity)]
      congr 1; push_cast; ring
    rw [e]
    have h2 : (S0.card : ℝ) * S0.card * ((ε ^ q) ^ 2) ^ 2 ≤ (4 * (ρ + 2) ^ 2) ^ 2 := by
      have := mul_le_mul hS0' hS0' (by positivity) (by positivity)
      nlinarith
    calc (S.card : ℝ) * ((ε ^ q) ^ 2) ^ 2 ≤ S0.card * S0.card * ((ε ^ q) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := by nlinarith
  -- reduction to `gm_T4_2_union`
  have hsub : {ω | ∀ a b : ℂ, (∃ m : ℤ × ℤ, a = (s : ℂ) * (m.1 + m.2 * Complex.I)) →
        (∃ m : ℤ × ℤ, b = (s : ℂ) * (m.1 + m.2 * Complex.I)) →
        a ∈ (fun x => (R : ℂ) * x) '' U → b ∈ (fun x => (R : ℂ) * x) '' U → Adm a b →
        ω ∈ Good a b}ᶜ ⊆ {ω | ∀ x ∈ S, ω ∈ Good x.1 x.2}ᶜ := by
    intro ω hω hS
    apply hω
    intro a b ha hb haU hbU hab
    refine hS (a, b) ?_
    simp only [S, Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset, S0]
    exact ⟨⟨⟨ha, hRU a haU⟩, ⟨hb, hRU b hbU⟩⟩, haU, hbU, hab⟩
  have hU' := gm_T4_2_union P Reg S (fun x => Good x.1 x.2) hReg (δ := C * ε ^ (4 * q + 1))
    fun x hx => by
      simp only [S, Finset.mem_filter] at hx
      exact hpair x.1 x.2 hx.2.1 hx.2.2.1 hx.2.2.2
  have hfin : (S.card : ℝ) * (C * ε ^ (4 * q + 1)) ≤ η / 2 := by
    have e : ε ^ (4 * q + 1) = ε ^ (4 * q) * ε := by
      rw [Real.rpow_add hε0, Real.rpow_one]
    rw [e]
    have h1 : (S.card : ℝ) * (C * (ε ^ (4 * q) * ε)) = ((S.card : ℝ) * ε ^ (4 * q)) * C * ε := by
      ring
    rw [h1]
    have h2 : ((S.card : ℝ) * ε ^ (4 * q)) * C * ε ≤ A * ε := by
      have := mul_le_mul_of_nonneg_right hScard hC
      have := mul_le_mul_of_nonneg_right this hε0.le
      simp only [A]; linarith
    have h3 : A * ε ≤ η / 2 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (A + 1))).1 hεA
      nlinarith
    linarith
  calc P _ ≤ P {ω | ∀ x ∈ S, ω ∈ Good x.1 x.2}ᶜ := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | ∀ x ∈ S, ω ∈ Good x.1 x.2}ᶜ) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)

end LQGMetric.GM
