/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGoodL416 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422b
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
# GM Lemma 4.16, deterministic tools: competitors for `D(·,·;ℂ∖cl B_r(z))`-geodesics

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.16
(`lem-geodesic-diam`, l. 2572–2579): "By (4.39) and since `P'` is a
`D_h(·,·;ℂ∖cl B_r(z))`-geodesic, the `D_h`-length of `P'|_{[0,t']}` is at most
`t_k + cε^χ 𝔠_𝕣e^{ξh_𝕣(𝕫)}`", `t'` the last time `P'` hits `∂B_{2λ₄ε𝕣}(z)`.

* `gm_avoid_len_le_internal` — for a `D(·,·;ℂ∖cl B_r(z))`-geodesic `Q` (`IsAvoidGeod`, GM
  l. 1695) of finite length and any `V ⊆ ℂ ∖ B_r(z)`, `len(Q|_{[0,t']}) ≤ D(𝕫, Q(t'); V)`:
  replace `Q|_{[0,t']}` by any path in `V` (concatenation; GM's "since `P'` is a geodesic").
* `gm_exists_last_hit` — the last time `t'` at which `Q` hits the circle `∂B_ρ(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM proof of Lemma 4.16** (l. 2575–2576): competitors in `V ⊆ ℂ ∖ B_r(z)`. -/
theorem gm_avoid_len_le_internal {D : ContMetric} {𝕫 z x : ℂ} {r : ℝ} {Q : ℝ → ℂ} {T : ℝ}
    (hQ : IsAvoidGeod D 𝕫 z r x Q T) (hfin : D.len Q 0 T ≠ ⊤) {t' : ℝ} (ht' : t' ∈ Icc 0 T)
    {V : Set ℂ} (hV : V ⊆ (ball z r)ᶜ) :
    D.len Q 0 t' ≤ D.internal V 𝕫 (Q t') := by
  obtain ⟨hT0, hQc, hQ0, hQT, hxs, hQout, hmin⟩ := hQ
  refine le_iInf fun γ => ?_
  set φ : ℝ → ℝ := fun s => s - t' + 1 with hφ
  set Q' : ℝ → ℂ := fun s => if s ≤ t' then D.unpt (γ.1.extend (φ s)) else Q s with hQ'
  have ha : t' - 1 ≤ t' := by linarith
  have hφ1 : φ t' = 1 := by simp [hφ]
  have hφ0 : φ (t' - 1) = 0 := by simp [hφ]
  have hmatch : D.unpt (γ.1.extend (φ t')) = Q t' := by rw [hφ1, Path.extend_one]; rfl
  have hcont : ContinuousOn Q' (Icc (t' - 1) T) :=
    MetricGeometry.continuousOn_concat (X := ℂ) ha ht'.2 hmatch
      ((D.continuous_unpt.comp (γ.1.continuous_extend.comp
        (continuous_id.sub continuous_const |>.add continuous_const))).continuousOn)
      (hQc.mono (Icc_subset_Icc ht'.1 le_rfl))
  have hstart : Q' (t' - 1) = 𝕫 := by
    simp only [hQ', if_pos ha, hφ0, Path.extend_zero]; rfl
  have hend : Q' T = x := by
    by_cases hTt : T ≤ t'
    · have hTt' : T = t' := le_antisymm hTt ht'.2
      simp only [hQ', if_pos hTt]
      rw [hTt', hmatch, ← hTt', hQT]
    · simp only [hQ', if_neg hTt]; exact hQT
  have hmaps : MapsTo Q' (Icc (t' - 1) T) (ball z r)ᶜ := by
    intro s hs
    by_cases hst : s ≤ t'
    · simp only [hQ', if_pos hst]
      apply hV
      obtain ⟨u, hu⟩ : γ.1.extend (φ s) ∈ range γ.1 := by
        rw [← Path.extend_range]; exact mem_range_self _
      have h2 := γ.2 u
      rw [hu] at h2
      exact (D.mem_image_pt (z := D.unpt (γ.1.extend (φ s)))).1 h2
    · simp only [hQ', if_neg hst]
      rcases lt_or_eq_of_le hs.2 with hsT | hsT
      · exact fun h => hQout s ⟨by linarith [ht'.1, not_le.1 hst], hsT⟩ (ball_subset_closedBall h)
      · rw [hsT, hQT]
        intro h
        rw [mem_ball] at h; rw [mem_sphere] at hxs; linarith
  have hle := hmin Q' (t' - 1) T (by linarith [ht'.2]) hcont hstart hend hmaps
  -- the length of the competitor
  have hlenQ' : D.len Q' (t' - 1) T = MetricGeometry.pathLength γ.1 + D.len Q t' T := by
    have heq : D.pt ∘ Q' = fun s => if s ≤ t' then γ.1.extend (φ s) else D.pt (Q s) := by
      funext s; simp only [Function.comp_apply, hQ']; split_ifs <;> rfl
    unfold ContMetric.len
    rw [heq, MetricGeometry.curveLength_concat ha ht'.2 (by rw [hφ1, Path.extend_one])]
    congr 1
    have := MetricGeometry.curveLength_comp_of_continuousOn_monotoneOn γ.1.extend
      (φ := φ) ha (by fun_prop) (fun u _ v _ huv => by simp only [hφ]; linarith)
    rw [show (fun s => γ.1.extend (φ s)) = γ.1.extend ∘ φ from rfl, this, hφ0, hφ1]
    rfl
  have hsplit : D.len Q 0 T = D.len Q 0 t' + D.len Q t' T :=
    (MetricGeometry.curveLength_add _ ht'.1 ht'.2).symm
  rw [hlenQ', hsplit] at hle
  have hfin2 : D.len Q t' T ≠ ⊤ := by
    intro h; apply hfin; rw [hsplit, h, add_top]
  exact (ENNReal.add_le_add_iff_right hfin2).1 hle

end LQGMetric.GM
