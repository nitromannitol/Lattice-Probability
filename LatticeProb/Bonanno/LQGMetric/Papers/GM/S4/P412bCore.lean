/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412bCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bStab
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bEnter
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bFinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bScale

/-!
# GM Proposition 4.12: the deterministic core on `ℰ_𝕣` — (4.41) at `k` ⇒ `𝒵^E_k ≠ ∅`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Proposition 4.12,
l. 2229–2276.

* `p412b_ext_transfer`: GM proves (4.42) "for every `(z,r) ∈ 𝒵_k` with `P ∩ B_r(z) ≠ ∅`", while
  `𝒵^E_k` (GM (4.18)) and l. 2236 only provide `P ∩ B_{λ₂r}(z) ≠ ∅`. Reading (proposed
  DEVIATIONS entry): the external-distance bound at a point `p ∈ B_{λ₂r}(z)` transfers to the
  centre `z` at the cost `2λ₂r` (triangle inequality for `d^U`, `gm_dU_triangle`, through
  `B_{λ₂r}(z) ⊆ ℂ ∖ 𝓑^•_{t_k}`), after which `p412b_stab_of_ext` applies at `p = z`.
* `p412b_core`: on `ℰ_𝕣` (with the pointwise a.s. facts), for small dyadic `ε`, `k ≤ K`, a path
  `P` from `𝕫` to far away and `x₀ ∈ Conf(s_k,t_k)` such that every point of `P` outside
  `𝓑^•_{t_k}` satisfies (4.41) for `I_k = arcOf x₀`, there is `(z, r) ∈ 𝒵_k` with `E_r(z)`,
  `Stab_{k,r}(z)` and `P ∩ B_{λ₂r}(z) ≠ ∅`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- transfer of the external-distance bound from `p ∈ B_{R'}(z)` to the centre `z` -/
theorem p412b_ext_transfer {D : ContMetric} {𝕫 : ℂ} {t : ℝ} (ht : 0 < t) (hL : D.IsLength)
    (hbd : Bornology.IsBounded (ballM D 𝕫 t)) {z p : ℂ} {R' : ℝ}
    (hball : Disjoint (ball z R') (filledBall D 𝕫 t)) (hp : p ∈ ball z R') {I : Set ℂ} {ρ : ℝ}
    (hext : ∀ v ∈ frontier (filledBall D 𝕫 t) \ I,
      ENNReal.ofReal ρ ≤ dU (filledBall D 𝕫 t)ᶜ p v) :
    ∀ v ∈ frontier (filledBall D 𝕫 t) \ I,
      ENNReal.ofReal (ρ - 2 * R') ≤ dU (filledBall D 𝕫 t)ᶜ z v := by
  intro v hv
  have hR' : 0 < R' := lt_of_le_of_lt dist_nonneg (mem_ball.1 hp)
  have hzB : z ∈ ball z R' := mem_ball_self hR'
  have hzU : z ∈ (filledBall D 𝕫 t)ᶜ := fun h => disjoint_left.1 hball hzB h
  have htri := gm_dU_triangle ht hL hbd (gm_j1b D 𝕫 t ht hL hbd) p v (w := z) (Or.inl hzU)
  have hpz : dU (filledBall D 𝕫 t)ᶜ p z ≤ ENNReal.ofReal (2 * R') := by
    refine (dc_dU_le (fun y hy hyK => disjoint_left.1 hball hy hyK)
      (isConnected_ball hR') (subset_closure hp) (subset_closure hzB)).trans ?_
    refine Metric.ediam_le fun a ha b hb => ?_
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    have := dist_triangle_right a b z
    linarith [mem_ball.1 ha, mem_ball.1 hb]
  have h1 := (hext v hv).trans (htri.trans (add_le_add hpz le_rfl))
  rw [ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ 2 * R')]
  exact tsub_le_iff_left.2 h1

/-- `B_{R'}(z) ∩ K = ∅` for `(z, r) ∈ 𝒵_k` and `R' ≤ λ₄ε𝕣` -/
theorem p412b_ball_disj_of_cand {K : Set ℂ} (hK : IsClosed K) {lam1 lam4 ε ν 𝕣 : ℝ}
    {Rads : Set ℝ} {z : ℂ} {r R' : ℝ} (hc : (z, r) ∈ candSet K lam1 lam4 ε ν 𝕣 Rads)
    (hR' : R' ≤ lam4 * ε * 𝕣) : Disjoint (ball z R') K := by
  obtain ⟨-, hzK, -, hd⟩ := hc
  simp only at hzK hd
  rw [disjoint_left]
  intro w hw hwK
  have hKne : K.Nonempty := ⟨w, hwK⟩
  have h1 := infDist_le_dist_of_mem (x := z) hwK
  rw [← gm_infDist_frontier_eq hK hKne hzK] at h1
  have h2 := mem_ball'.1 hw
  linarith [hd.1]

/-- the output of `p412b_core` for the path `P = sel 𝕫 𝕨 (h ω)` (on `[0,1]`, extended by
`projIcc`) is `𝒵^E_k ≠ ∅` (GM (4.18)) -/
theorem p412b_zkE_nonempty {Ω : Type} [MeasurableSpace Ω] {D : DistC → ContMetric}
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)} {h : Ω → DistC} {R : RegPar} {𝕫 𝕨 : ℂ}
    {𝕣 ε β : ℝ} {k : ℕ} {ω : Ω}
    (H : ∃ z r, (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω))
        (R.lam 0) (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε) ∧
      h ω ∈ R.E r z ∧
      stabCond (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) z r ∧
      ∃ u ∈ Icc (0 : ℝ) 1,
        sel 𝕫 𝕨 (h ω) (Set.projIcc 0 1 zero_le_one u) ∈ ball z (R.lam 1 * r)) :
    (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty := by
  obtain ⟨z, r, hc, hE, hS, u, -, hu⟩ := H
  exact ⟨(z, r), hc, hE, hS, _, mem_range_self _, hu⟩

end LQGMetric.GM
