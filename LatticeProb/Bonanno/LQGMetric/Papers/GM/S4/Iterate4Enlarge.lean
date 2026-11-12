/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate4Enlarge at commit fdb5cad; only the module paths of local imports are changed.
   Changed: docstring wording of the module. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4Pair
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4L420F

/-!
# GM Theorem 4.2 with `λ₃ = λ₄` (DEC-89, packet F)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Thm 4.2 (l. 1554–1571), which allows
`λ₃ = λ₄`. Decision `decisions/DEC-89.md` (D89c, own argument DV-D89c): the case `λ₃ = λ₄` follows
from the case `λ₃ < λ₄` by enlarging `λ₄` to `λ₄' ∈ (λ₄, min(λ₅, λ₄²/λ₁))` and using every other
radius of (1) (`μ' = μ/2`):
* (2): `σ(h|_{B_{λ₄r}}, P stopped at its last exit from B_{λ₄r}) ⊆ σ(h|_{B_{λ₄'r}}, P stopped at
  its last exit from B_{λ₄'r})` (`gm_stopLastExit_stop`: the first stopped path is a function of
  the second; `gm_comap_stop_le`);
* (4): fewer pairs `(𝕫, 𝕨)`; the conclusion for `λ₄'` implies the one for `λ₄`.

`T4_2Gt1E` = `T4_2Gt1` (D95: both carry `0 < ε₀`, GM l. 1557).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Pointwise

namespace LQGMetric.GM
open Blueprint

/-- since D95, `T4_2Gt1` itself carries `0 < ε₀` (GM l. 1557); `T4_2Gt1E` is kept as a name -/
def T4_2Gt1E : Prop := T4_2Gt1

/-- the path stopped at the last exit from `K` is a function of the path stopped at the last
exit from `K' ⊇ K` -/
theorem gm_stopLastExit_stop (η : C(unitInterval, ℂ)) {K K' : Set ℂ} (hKK' : K ⊆ K') :
    stopLastExit (⟨stopLastExit η K', gm_continuous_stopLastExit η K'⟩ : C(unitInterval, ℂ)) K =
      stopLastExit η K := by
  set ξ : C(unitInterval, ℂ) := ⟨stopLastExit η K', gm_continuous_stopLastExit η K'⟩ with hξ
  set T' := lastExitTime η K' with hT'
  have hT'0 : 0 ≤ T' := gm_lastExitTime_nonneg η K'
  have hT'1 : T' ≤ 1 := gm_lastExitTime_le_one η K'
  have hξv : ∀ v : unitInterval, ξ v = η (projIcc 0 1 zero_le_one ((v : ℝ) * T')) :=
    fun v => rfl
  have hle : ∀ u : unitInterval, η u ∈ K → (u : ℝ) ≤ T' :=
    fun u hu => gm_le_lastExitTime_of_mem (hKK' hu)
  funext u
  rw [gm_stopLastExit_apply, gm_stopLastExit_apply, hξv]
  rcases hT'0.eq_or_lt with h0 | hpos
  · -- `T' = 0`: both stopped paths are constant `η 0`
    have hT : lastExitTime η K = 0 := by
      refine le_antisymm ?_ (gm_lastExitTime_nonneg η K)
      refine Real.sSup_le ?_ le_rfl
      rintro _ ⟨v, rfl, hv⟩
      rw [h0]; exact hle v hv
    rw [hT, ← h0, mul_zero, mul_zero]
  · have hset : {t : ℝ | ∃ v : unitInterval, (v : ℝ) = t ∧ η v ∈ K} =
        T' • {t : ℝ | ∃ v : unitInterval, (v : ℝ) = t ∧ ξ v ∈ K} := by
      ext t
      simp only [Set.mem_smul_set, mem_setOf_eq, smul_eq_mul]
      constructor
      · rintro ⟨v, rfl, hv⟩
        have hvT := hle v hv
        refine ⟨v / T', ⟨⟨v / T', div_nonneg v.2.1 hpos.le, (div_le_one hpos).2 hvT⟩, rfl, ?_⟩,
          mul_div_cancel₀ _ hpos.ne'⟩
        rw [hξv]
        convert hv using 2
        rw [projIcc_of_mem _ ⟨mul_nonneg (div_nonneg v.2.1 hpos.le) hpos.le, by
          show (v : ℝ) / T' * T' ≤ 1
          rw [div_mul_cancel₀ _ hpos.ne']; exact v.2.2⟩]
        ext; simp only; rw [div_mul_cancel₀ _ hpos.ne']
      · rintro ⟨_, ⟨v, rfl, hv⟩, rfl⟩
        have hm : (v : ℝ) * T' ∈ Icc (0 : ℝ) 1 :=
          ⟨mul_nonneg v.2.1 hT'0, mul_le_one₀ v.2.2 hT'0 hT'1⟩
        refine ⟨⟨_, hm⟩, by simp only; ring, ?_⟩
        rw [hξv, projIcc_of_mem _ hm] at hv
        exact hv
    have hT : lastExitTime η K = T' * lastExitTime ξ K := by
      unfold lastExitTime
      rw [hset, Real.sSup_smul_of_nonneg hT'0, smul_eq_mul]
    have hm : (u : ℝ) * lastExitTime ξ K ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg u.2.1 (gm_lastExitTime_nonneg ξ K),
        mul_le_one₀ u.2.2 (gm_lastExitTime_nonneg ξ K) (gm_lastExitTime_le_one ξ K)⟩
    rw [projIcc_of_mem _ hm, hT]
    congr 2
    simp only
    ring

/-- `σ(P stopped at its last exit from K) ⊆ σ(P stopped at its last exit from K')` for `K ⊆ K'`,
`K` open -/
theorem gm_comap_stop_le {Ω : Type} (Y : Ω → C(unitInterval, ℂ)) {K K' : Set ℂ}
    (hK : IsOpen K) (hKK' : K ⊆ K') :
    MeasurableSpace.comap (fun ω => stopLastExit (Y ω) K) inferInstance ≤
      MeasurableSpace.comap (fun ω => stopLastExit (Y ω) K') inferInstance := by
  have hc : ∀ ω, Continuous (stopLastExit (Y ω) K') := fun ω => gm_continuous_stopLastExit _ _
  have hm := gm_measurable_contPath (fun ω => stopLastExit (Y ω) K') hc
  have hst : Measurable fun f : C(unitInterval, ℂ) => stopLastExit f K :=
    measurable_pi_iff.2 fun u => gm_measurable_stopLastExit_apply hK u
  have e : (fun ω => stopLastExit (Y ω) K) =
      (fun f : C(unitInterval, ℂ) => stopLastExit f K) ∘
        (fun ω => (⟨stopLastExit (Y ω) K', hc ω⟩ : C(unitInterval, ℂ))) :=
    funext fun ω => (gm_stopLastExit_stop (Y ω) hKK').symm
  rw [e]
  exact (hst.comp hm).comap_le

/-- every other radius: `k < ⌊y/2⌋ → 2k + 1 < ⌊y⌋` -/
theorem gm_floor_half {y : ℝ} {k : ℕ} (hk : k < ⌊y / 2⌋₊) : 2 * k + 1 < ⌊y⌋₊ := by
  have hpos : 0 < ⌊y / 2⌋₊ := lt_of_le_of_lt (Nat.zero_le k) hk
  have hy : 0 ≤ y / 2 := by
    by_contra hneg
    rw [Nat.floor_of_nonpos (le_of_lt (not_le.1 hneg))] at hpos
    exact lt_irrefl 0 hpos
  have h1 : ((k + 1 : ℕ) : ℝ) ≤ y / 2 :=
    le_trans (Nat.cast_le.2 hk) (Nat.floor_le hy)
  have h2 : ((2 * k + 2 : ℕ) : ℝ) ≤ y := by push_cast at h1 ⊢; linarith
  have h3 : 2 * k + 2 ≤ ⌊y⌋₊ := Nat.le_floor h2
  omega

/-- **enlarging `λ₄`** (D89c): the hypotheses of T4.2 for `λ` give those for
`λ' = (λ₁, λ₂, λ₃, λ₄', λ₅)` with `λ₄ ≤ λ₄'`, `λ₄'/λ₁ ≤ (λ₄/λ₁)²`, and `μ/2` (every other radius) -/
theorem gm_geoIterateHyp_enlarge {D : DistC → ContMetric}
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {μ ν : ℝ} {lam : Fin 5 → ℝ} {𝕡 R ε₀ Λ : ℝ}
    {Rad : Set ℝ} {E : ℝ → ℂ → Set DistC} {Ef : ℝ → ℂ → ℂ → ℂ → Set DistC}
    (H : GeoIterateHyp D sel μ ν lam 𝕡 R ε₀ Λ Rad E Ef) {l4 : ℝ} (hl : lam 3 ≤ l4)
    (hsq : l4 / lam 0 ≤ (lam 3 / lam 0) ^ 2) (h30 : 0 ≤ lam 3 / lam 0) :
    GeoIterateHyp D sel (μ / 2) ν ![lam 0, lam 1, lam 2, l4, lam 4] 𝕡 R ε₀ Λ Rad E Ef := by
  obtain ⟨hRad, hΛ, hE, hEf, h1, hP⟩ := H
  have hmono : ∀ r ∈ Rad, lam 3 * r ≤ l4 * r := fun r hr =>
    mul_le_mul_of_nonneg_right hl (hRad hr).1.le
  refine ⟨hRad, hΛ, hE, hEf, fun ε hε => ?_, fun {Ω} _ P _ h hh => ?_⟩
  · obtain ⟨rr, hr1, hr2⟩ := h1 ε hε
    refine ⟨fun k => rr (2 * k), fun k hk => hr1 (2 * k) ?_, fun k hk => ?_⟩
    · have : μ / 2 * Real.logb 8 ε⁻¹ = μ * Real.logb 8 ε⁻¹ / 2 := by ring
      rw [this] at hk
      have := gm_floor_half hk; omega
    · have : μ / 2 * Real.logb 8 ε⁻¹ = μ * Real.logb 8 ε⁻¹ / 2 := by ring
      rw [this] at hk
      have hk' := gm_floor_half hk
      have ha := hr2 (2 * k) (by omega)
      have hb := hr2 (2 * k + 1) (by omega)
      have hpos : 0 < rr (2 * k + 1) := (hRad (hr1 (2 * k + 1) (by omega)).2).1
      have hpos2 : 0 < rr (2 * k + 1 + 1) := (hRad (hr1 (2 * k + 1 + 1) (by omega)).2).1
      have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      show l4 / lam 0 ≤ rr (2 * k) / rr (2 * (k + 1))
      rw [e]
      calc l4 / lam 0 ≤ (lam 3 / lam 0) * (lam 3 / lam 0) := by rw [← sq]; exact hsq
        _ ≤ (rr (2 * k) / rr (2 * k + 1)) * (rr (2 * k + 1) / rr (2 * k + 1 + 1)) :=
          mul_le_mul ha hb h30 (h30.trans ha)
        _ = rr (2 * k) / rr (2 * k + 1 + 1) := by field_simp
  · obtain ⟨hg, h2, h2f, h3, h4⟩ := hP P h hh
    refine ⟨hg, fun z r hr => ?_, fun z r hr a b => ?_, h3, fun z r hr a b hab ha hb => ?_⟩
    · obtain ⟨F, hF, hEF⟩ := h2 z r hr
      refine ⟨F, fieldSigma_mono _ ?_ F hF, hEF⟩
      intro w hw
      exact ⟨hw.1, lt_of_lt_of_le hw.2 (hmono r hr)⟩
    · obtain ⟨F, hF, hEF⟩ := h2f z r hr a b
      refine ⟨F, sup_le_sup (fieldSigma_mono h ?_) (gm_comap_stop_le _ Metric.isOpen_ball
        (Metric.ball_subset_ball (hmono r hr))) F hF, hEF⟩
      exact Metric.ball_subset_ball (hmono r hr)
    · exact h4 z r hr a b hab (fun hm => ha (Metric.ball_subset_ball (hmono r hr) hm))
        (fun hm => hb (Metric.ball_subset_ball (hmono r hr) hm))

/-- **packet F** (D89c, own argument DV-D89c): T4.2 (`λ₄ > 1`, `0 < ε₀`) from the case `λ₃ < λ₄` -/
theorem gm_T4_2Gt1E_of_strict (H : T4_2Gt1S) : T4_2Gt1E := by
  intro γ D c hγ hγ2 hD sel hsel
  obtain ⟨νs, hνs, H1⟩ := H hγ hγ2 hD sel hsel
  refine ⟨νs, hνs, fun {μ ν} hμ hμν hν lam h0 h01 h12 h23 h34 h1l => ?_⟩
  by_cases hlt : lam 2 < lam 3
  · exact H1 hμ hμν hν lam h0 h01 h12 h23 h34 h1l hlt
  have h03 : lam 0 < lam 3 := by linarith
  set l4 : ℝ := min ((lam 3 + lam 4) / 2) (lam 3 ^ 2 / lam 0) with hl4
  have hl4a : lam 3 < l4 := lt_min (by linarith) (by rw [lt_div_iff₀ h0]; nlinarith)
  have hl4b : l4 < lam 4 := (min_le_left _ _).trans_lt (by linarith)
  have hsq : l4 / lam 0 ≤ (lam 3 / lam 0) ^ 2 := by
    rw [div_pow, sq (lam 0), ← div_div]
    exact div_le_div_of_nonneg_right (min_le_right _ _) h0.le
  have h30 : 0 ≤ lam 3 / lam 0 := div_nonneg (by linarith) h0.le
  obtain ⟨𝕡, h𝕡, H2⟩ := H1 (μ := μ / 2) (by positivity) (by linarith) hν
    ![lam 0, lam 1, lam 2, l4, lam 4] h0 h01 h12 (by show lam 2 ≤ l4; linarith)
    (show l4 < lam 4 from hl4b) (show 1 < l4 by linarith) (show lam 2 < l4 by linarith)
  refine ⟨𝕡, h𝕡, fun q ℓ U hq hℓ hU hUb ε₀ Λ η hε₀ hη => ?_⟩
  obtain ⟨ε₁, hε₁, H3⟩ := H2 q ℓ U hq hℓ hU hUb ε₀ Λ η hε₀ hη
  refine ⟨ε₁, hε₁, fun R Rad E Ef hR hGeo Ω _ P _ h hh ε hε => ?_⟩
  refine le_trans (measure_mono (compl_subset_compl.2 ?_))
    (H3 R Rad E Ef hR (gm_geoIterateHyp_enlarge hGeo hl4a.le hsq h30) P h hh ε hε)
  intro ω hω a b ha hb haU hbU hab
  obtain ⟨z, r, hr, hrI, hhit, hEf, ha', hb'⟩ := hω a b ha hb haU hbU hab
  have hr0 : 0 < r := (hGeo.1 hr).1
  have hsub : Metric.ball z (lam 3 * r) ⊆ Metric.ball z (l4 * r) :=
    Metric.ball_subset_ball (mul_le_mul_of_nonneg_right hl4a.le hr0.le)
  exact ⟨z, r, hr, hrI, hhit, hEf, fun hm => ha' (hsub hm), fun hm => hb' (hsub hm)⟩

end LQGMetric.GM
