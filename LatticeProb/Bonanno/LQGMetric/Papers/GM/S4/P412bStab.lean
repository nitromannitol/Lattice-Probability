/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412bStab at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412Final
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL416b
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodS46

/-!
# GM Proposition 4.12, final step on `ℰ_𝕣`: (4.41) ⇒ `Stab_{k,r}(z)` (P4.12 assembly, piece (c))

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Proposition 4.12,
l. 2257–2276: given (4.41) `d^{ℂ∖𝓑^•_{t_k}}(P, ∂𝓑^•_{t_k} ∖ I_k) ≥ ρ` at a point `p` of
`P ∩ B_r(z)`, Lemma 4.16 (`gm_L4_16`) and the triangle inequality (4.42)
(`p412_hit_mem_of_dU`) give `Stab_{k,r}(z)` for `(z, r) ∈ 𝒵_k`, provided
`A + 2r < ρ` (`A` the bound of Lemma 4.16; GM: "for small enough `ε`").

`hdisj` (`cl B_r(z) ∩ 𝓑^•_{t_k} = ∅`) comes from (4.10): `dist(z, ∂𝓑^•_{t_k}) ≥ λ₄ε𝕣 > ε𝕣 ≥ r`
(`λ₄ > 1`, GM l. 2555). Open input `hfin`: avoid-geodesics `Q` have finite `D_h`-length (GM
takes the existence of these geodesics for granted, l. 1695).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `cl B_r(z) ∩ K = ∅` for `(z, r) ∈ 𝒵_k`, `r ≤ ε𝕣 < λ₄ε𝕣` -/
theorem p412b_disj_of_cand {K : Set ℂ} (hK : IsClosed K) {lam1 lam4 ε ν 𝕣 : ℝ}
    {Rads : Set ℝ} {z : ℂ} {r : ℝ} (hc : (z, r) ∈ candSet K lam1 lam4 ε ν 𝕣 Rads)
    (hr0 : 0 ≤ r) (hr : r < lam4 * ε * 𝕣) : Disjoint (closedBall z r) K := by
  obtain ⟨-, hzK, -, hd⟩ := hc
  simp only at hzK hd
  have hpos : 0 < infDist z (frontier K) := lt_of_lt_of_le (hr0.trans_lt hr) hd.1
  have hfne : (frontier K).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, infDist_empty] at hpos; exact lt_irrefl _ hpos
  have hKne : K.Nonempty := hfne.mono hK.frontier_subset
  rw [disjoint_left]
  intro w hw hwK
  have h1 := infDist_le_dist_of_mem (x := z) hwK
  rw [← gm_infDist_frontier_eq hK hKne hzK] at h1
  have h2 := mem_closedBall'.1 hw
  linarith [hd.1]

end LQGMetric.GM
