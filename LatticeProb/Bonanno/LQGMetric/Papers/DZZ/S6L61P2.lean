/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61P2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61P1

/-!
# DZZ (eq-point-to-boundary-kappa), lower half: the estimate at one scale (P2-DZZ61P)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2593–2596 ("by Lemma 5.4 and a
similar derivation"), route of DEC-117 §2(b). For `v ∈ ∂𝕍̄_{u,α}`, `κ = (1−α)/20`, and the
similarity `θ = simMap (1−α) (v − (1−α) c₀)` sending the fixed L5.4 box `𝕍_{c₀,1/10}`
(`c₀ = (1/2,1/2)`) onto `𝕍_{v,2κ}`:

1. (eq-geodesic-range), l. 2340–2345 (`lgdMinSet_frontier_sqBox_eq_wall`, P2-DZZDB): on the
   big-ball event `BigBallsAt (κ/4) δ`, `min_{∂𝕍_{v,κ}} D(v,·) = min_{∂𝕍_{v,κ}} D̄^{v,2κ}(v,·)`;
2. lem-scaling-coupling, l. 611–624 (`dzzSimCoupleU_of_norm_le`, constant uniform in the
   translation `b`): on the coupling event,
   `D̄^{c₀,1/10}_{δ'}(c₀, x)[W₁] ≤ D̄^{v,2κ}_δ(v, θx)[W₂]`, `δ' = δ e^{λ}/(1−α)`;
3. off both events, the walled crude second moments (DZZ (eq-very-crude), l. 849–857, walled
   form `lintegral_sq_logMin_dzzWall_le`, uniform over the walls) and `Y ≤ t + Y²/t`
   (`integral_ge_of_ae_le_off`).

Result `ptBdry_key`: for all `v ∈ ∂𝕍̄_{u,α}`, `δ`, `λ ≥ 0`, `t₁, t₂ > 0`,
`E log D̄^{c₀,1/10}_{δ'}(c₀, ∂𝕍_{c₀,1/20}) − t₂ C e^{−λ²/C} − (a + b log² δ'⁻¹)/t₂
 − t₁ P(¬Big) − (a + b log² δ⁻¹)/t₁ ≤ E log min_{∂𝕍_{v,κ}} D_δ(v,·)`, with `C, a, b`
independent of `v` and `δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω]

/-- the centre `(1/2, 1/2)` of `𝕍`, where L5.4 is used -/
def ptCentre : ℂ := ⟨1 / 2, 1 / 2⟩

lemma ptCentre_mem_dzzVbar : ptCentre ∈ dzzVbar := by
  refine ⟨?_, ?_⟩ <;> simp [ptCentre] <;> norm_num

/-- `integral_ge_of_ae_le_off` with a bound on `P(Bd)` (fixes `Bd` by unification) -/
theorem integral_ge_of_ae_le_off' {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    [IsProbabilityMeasure P] {X Y : Ω' → ℝ} {Bd : Set Ω'} {c : ℝ} (hBd : P.real Bd ≤ c)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXi : Integrable X P) (hY : MemLp Y 2 P)
    (h : ∀ᵐ ω ∂P, ω ∉ Bd → Y ω ≤ X ω) {t : ℝ} (ht : 0 < t) :
    ∫ ω, Y ω ∂P - t * c - (∫ ω, Y ω ^ 2 ∂P) / t ≤ ∫ ω, X ω ∂P := by
  have := integral_ge_of_ae_le_off hX0 hXi hY h ht
  nlinarith [mul_le_mul_of_nonneg_left hBd ht.le]

set_option maxHeartbeats 1000000 in
/-- **(eq-point-to-boundary-kappa) at one scale** (DZZ l. 2593–2596, 2340–2345, 611–624). -/
theorem ptBdry_key {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {u : ℂ}
    (hu : u ∈ dzzVbar) :
    ∃ C a₁ b₁ : ℝ, 0 < C ∧ 0 ≤ a₁ ∧ 0 ≤ b₁ ∧ ∀ v ∈ frontier (sqBox u (α / 20)),
      ∀ δ lam t₁ t₂ : ℝ, 0 < δ → δ ≤ 1 / 2 → 0 ≤ lam → δ * Real.exp lam / (1 - α) ≤ 1 / 2 →
      0 < t₁ → 0 < t₂ →
      ∫ ω, logMinLGD (dzzWall (sqBox ptCentre (1 / 10)) (dzzMuIn γ W ω))
          (δ * Real.exp lam / (1 - α)) {ptCentre} (frontier (sqBox ptCentre (1 / 20))) ∂P
        - t₂ * (C * Real.exp (-lam ^ 2 / C))
        - (a₁ + b₁ * Real.log (δ * Real.exp lam / (1 - α))⁻¹ ^ 2) / t₂
        - t₁ * P.real {ω | ¬ BigBallsAt (dzzMuIn γ W ω) ((1 - α) / 20 / 4) δ}
        - (a₁ + b₁ * Real.log δ⁻¹ ^ 2) / t₁ ≤
      ∫ ω, logMinLGD (dzzMuIn γ W ω) δ {v} (frontier (sqBox v ((1 - α) / 20))) ∂P := by
  set κ := (1 - α) / 20 with hκdef
  have hr : 0 < 1 - α := by linarith
  have hκ : 0 < κ := by positivity
  have hκ1 : κ < 1 / 20 := by rw [hκdef]; linarith
  set ξ := min (1 / 100 : ℝ) κ with hξdef
  have hξ : 0 < ξ := lt_min (by norm_num) hκ
  have hξ1 : ξ ≤ 1 / 100 := min_le_left _ _
  have hξκ : ξ ≤ κ := min_le_right _ _
  set K := sqBox ptCentre (1 / 10) with hKdef
  have hKξ : K ⊆ dzzVXi ξ := fun z hz =>
    mem_dzzVXi_of_near (a := 1 / 20) (by have := hz.1; simp only [ptCentre] at this; linarith)
      (by have := hz.2; simp only [ptCentre] at this; linarith) (by linarith) hξ.le
  have ha0 : ((1 - α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hanorm : ‖((1 - α : ℝ) : ℂ)‖ = 1 - α := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  obtain ⟨C, hC, hcpl⟩ := dzzSimCoupleU_of_norm_le hγ hγ2 hξ (by linarith) (isClosed_sqBox _ _)
    hKξ ha0 (by rw [hanorm]; linarith)
  obtain ⟨a₁, b₁, ha₁, hb₁, hm⟩ := lintegral_sq_logMin_dzzWall_le hW hγ hγ2 hξ
  obtain ⟨a₂, b₂, ha₂, hb₂, hm2⟩ := lintegral_sq_logMin_dzzMuIn_le hW hγ hγ2 hξ
  refine ⟨C, a₁, b₁, hC, ha₁, hb₁, fun v hv δ lam t₁ t₂ hδ hδ2 hlam hδ'2 ht₁ ht₂ => ?_⟩
  haveI := hW.isProbabilityMeasure
  -- geometry of the moving centre
  have hvb : v ∈ sqBox u (α / 20) := (isClosed_sqBox _ _).closure_eq ▸ frontier_subset_closure hv
  obtain ⟨hu1, hu2⟩ := near_of_mem_dzzVbar hu
  obtain ⟨hv1, hv2⟩ := hvb
  have hvre : |v.re - 1 / 2| ≤ 1 / 20 := by
    have := abs_sub_le v.re u.re (1 / 2); linarith
  have hvim : |v.im - 1 / 2| ≤ 1 / 20 := by
    have := abs_sub_le v.im u.im (1 / 2); linarith
  have hθKξ' : sqBox v (2 * κ) ⊆ dzzVXi ξ := fun z hz =>
    mem_dzzVXi_of_near (a := 1 / 10)
      (by have := abs_sub_le z.re v.re (1 / 2); have := hz.1; linarith)
      (by have := abs_sub_le z.im v.im (1 / 2); have := hz.2; linarith) (by linarith) hξ.le
  have hVIn : ∀ z ∈ sqBox v (2 * κ), z ∈ dzzVIn ξ := fun z hz =>
    dzzVXi_sub_dzzVIn le_rfl (hθKξ' hz)
  have hKIn : ∀ z ∈ K, z ∈ dzzVIn ξ := fun z hz => dzzVXi_sub_dzzVIn le_rfl (hKξ hz)
  set y : ℂ := ⟨v.re + κ / 2, v.im⟩ with hydef
  have hy : y ∈ frontier (sqBox v κ) := right_mem_frontier_sqBox v hκ
  have hvv : v ∈ sqBox v (2 * κ) := ⟨by simp; positivity, by simp; positivity⟩
  have hyv : y ∈ sqBox v (2 * κ) := by
    refine ⟨?_, ?_⟩ <;> simp only [hydef, add_sub_cancel_left, sub_self, abs_zero]
    · rw [abs_of_pos (by positivity)]; linarith
    · positivity
  have hvy : v ≠ y := by
    intro h; have := congrArg Complex.re h; simp only [hydef] at this; linarith
  set y₀ : ℂ := ⟨ptCentre.re + 1 / 20 / 2, ptCentre.im⟩ with hy₀def
  have hy₀ : y₀ ∈ frontier (sqBox ptCentre (1 / 20)) :=
    right_mem_frontier_sqBox ptCentre (by norm_num)
  have hF₀K : frontier (sqBox ptCentre (1 / 20)) ⊆ K := fun z hz => by
    have hz' : z ∈ sqBox ptCentre (1 / 20) :=
      (isClosed_sqBox _ _).closure_eq ▸ frontier_subset_closure hz
    exact ⟨hz'.1.trans (by norm_num), hz'.2.trans (by norm_num)⟩
  have hcK : ptCentre ∈ K := ⟨by norm_num, by norm_num⟩
  have hc0 : ptCentre ≠ y₀ := by
    intro h; have := congrArg Complex.re h; simp only [hy₀def] at this; linarith
  have hsegK : ∀ t ∈ Icc (0 : ℝ) 1, Metric.ball (AffineMap.lineMap ptCentre y₀ t) (ξ / 2) ⊆ K :=
    fun t ht => by
      have h := ball_lineMap_subset_sqBox ptCentre (κ := 1 / 20) (ρ := ξ / 2) (by linarith) ht
      rwa [show (2 : ℝ) * (1 / 20) = 1 / 10 by norm_num] at h
  -- Step A: removing the wall `𝕍_{v,2κ}` on the big-ball event
  have hμm : ∀ (c : ℂ) (r : ℝ), AEMeasurable (fun ω => dzzMuIn γ W ω (Metric.ball c r)) P :=
    fun c r => by
      simp only [dzzMuIn, dzzWall, Measure.add_apply, Measure.smul_apply]
      exact (aemeasurable_wickQArea_ball hW hγ hγ2 c r).add aemeasurable_const
  have hfm := memLp_two_of_lintegral_sq (fun ω => logMinLGD_nonneg _ _ _ _)
    (aemeasurable_logMinLGD hμm δ {v} (frontier (sqBox v κ))) (by positivity)
    (hm2 {v} (frontier (sqBox v κ)) v y (mem_singleton v) hy (hVIn v hvv) (hVIn y hyv) hvy δ hδ
      hδ2)
  have hgB := hm (sqBox v (2 * κ)) {v} (frontier (sqBox v κ)) v y (mem_singleton v) hy
    (hVIn v hvv) (hVIn y hyv) hvy
    (fun t ht => ball_lineMap_subset_sqBox v (by linarith) ht) δ hδ hδ2
  have hgm := memLp_two_of_lintegral_sq (fun ω => logMinLGD_nonneg _ _ _ _)
    (aemeasurable_logMinLGD (fun c r => aemeasurable_dzzWall_dzzMuIn_ball hW hγ hγ2 _ c r) δ
      {v} (frontier (sqBox v κ))) (by positivity) hgB
  have hA := integral_ge_of_ae_le_off
    (X := fun ω => logMinLGD (dzzMuIn γ W ω) δ {v} (frontier (sqBox v κ)))
    (Y := fun ω => logMinLGD (dzzWall (sqBox v (2 * κ)) (dzzMuIn γ W ω)) δ {v}
      (frontier (sqBox v κ)))
    (Bd := {ω | ¬ BigBallsAt (dzzMuIn γ W ω) (κ / 4) δ})
    (fun ω => logMinLGD_nonneg _ _ _ _) (hfm.1.integrable one_le_two) hgm.1
    (Eventually.of_forall fun ω hω => by
      have hb : BigBallsAt (dzzMuIn γ W ω) (κ / 4) δ := not_not.mp hω
      apply le_of_eq
      simp only [logMinLGD]
      rw [show dzzMuIn γ W ω = dzzWall dzzV (wickQArea γ W ω) from rfl,
        lgdMinSet_frontier_sqBox_eq_wall hδ hκ hb v]) ht₁
  -- Step B: the scaling coupling from the fixed box `𝕍_{c₀,1/10}`
  set b := v - ((1 - α : ℝ) : ℂ) * ptCentre with hbdef
  have hθc : simMap ((1 - α : ℝ) : ℂ) b ptCentre = v := by simp [simMap, hbdef]
  have hθK : simMap ((1 - α : ℝ) : ℂ) b '' K = sqBox v (2 * κ) := by
    rw [hKdef, simMap_ofReal_image_sqBox hr, hθc, hκdef]; congr 1; ring
  have hθF : simMap ((1 - α : ℝ) : ℂ) b '' frontier (sqBox ptCentre (1 / 20)) =
      frontier (sqBox v κ) := by
    rw [simMap_image_frontier ha0, simMap_ofReal_image_sqBox hr, hθc, hκdef]; congr 2; ring
  have hθs : simMap ((1 - α : ℝ) : ℂ) b '' {ptCentre} = {v} := by rw [image_singleton, hθc]
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hcp⟩ := hcpl b (hθK ▸ hθKξ')
  haveI := hW₁.isProbabilityMeasure
  set δ' := δ * Real.exp lam / (1 - α) with hδ'def
  have hδ' : 0 < δ' := by positivity
  have hsc : ‖((1 - α : ℝ) : ℂ)‖ * δ' * Real.exp (-lam) = δ := by
    rw [hanorm, hδ'def, Real.exp_neg]; field_simp
  have hYB := hm K {ptCentre} (frontier (sqBox ptCentre (1 / 20))) ptCentre y₀
    (mem_singleton _) hy₀ (hKIn _ hcK) (hKIn _ (hF₀K hy₀)) hc0 hsegK δ' hδ' hδ'2
  have hY'm := memLp_logMinLGD_wall_of hW hW₁ hγ hγ2 K δ' {ptCentre}
    (frontier (sqBox ptCentre (1 / 20))) (by positivity) hYB
  have hX'm := memLp_logMinLGD_wall_of hW hW₂ hγ hγ2 (sqBox v (2 * κ)) δ {v}
    (frontier (sqBox v κ)) (by positivity) hgB
  have hvre' : |v.re - 1 / 2| + κ < 1 / 2 := by linarith
  have hvim' : |v.im - 1 / 2| + κ < 1 / 2 := by linarith
  have hB := integral_ge_of_ae_le_off' (hcp lam hlam)
    (X := fun ω => logMinLGD (dzzWall (sqBox v (2 * κ)) (dzzMuIn γ W₂ ω)) δ {v}
      (frontier (sqBox v κ)))
    (Y := fun ω => logMinLGD (dzzWall K (dzzMuIn γ W₁ ω)) δ' {ptCentre}
      (frontier (sqBox ptCentre (1 / 20))))
    (fun ω => logMinLGD_nonneg _ _ _ _) (hX'm.1.integrable one_le_two) hY'm.1
    (by
      filter_upwards [ae_lgdMinSet_wallSq_lt_top hW₂ hγ hγ2 hκ hvre' hvim' hδ] with ω hfin hω
      have hG := not_not.mp hω
      have hle : lgdMinSet (dzzWall K (dzzMuIn γ W₁ ω)) δ' {ptCentre}
          (frontier (sqBox ptCentre (1 / 20))) ≤
          lgdMinSet (dzzWall (simMap ((1 - α : ℝ) : ℂ) b '' K) (dzzMuIn γ W₂ ω)) δ
            (simMap ((1 - α : ℝ) : ℂ) b '' {ptCentre})
            (simMap ((1 - α : ℝ) : ℂ) b '' frontier (sqBox ptCentre (1 / 20))) :=
        lgdMinSet_le_image fun x hx z hz => by
          have h := (hG x (by rw [mem_singleton_iff.mp hx]; exact hcK) z (hF₀K hz) δ' hδ').2
          rwa [hsc] at h
      rw [hθK, hθs, hθF] at hle
      exact log_toNat_mono hle hfin.ne) ht₂
  have hTg := integral_logMinLGD_wall_eq hW hW₂ hγ hγ2 (sqBox v (2 * κ)) δ {v}
    (frontier (sqBox v κ))
  have hTY := integral_logMinLGD_wall_eq hW hW₁ hγ hγ2 K δ' {ptCentre}
    (frontier (sqBox ptCentre (1 / 20)))
  have hd1 := div_le_div_of_nonneg_right hgm.2 ht₁.le
  have hd2 := div_le_div_of_nonneg_right hY'm.2 ht₂.le
  linarith

end DZZ
end LQGMetric
