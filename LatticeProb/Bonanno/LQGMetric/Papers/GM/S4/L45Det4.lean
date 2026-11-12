/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L45Det4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Det3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45DetJ
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bFinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Meas

/-!
# GM Lemma 4.5: the point of `Conf_k` is determined by the hit pattern of its arc (task P2-E2R)

GM, arXiv:1905.00383, `uniqueness-final.tex` l. 1674–1675 ("this point is determined by which
arc of `𝓘_k` contains `P(t_k)`"): a.s., for all `0 < s < t`, distinct points of `Conf(s, t)` have
arcs `arcOf x` with distinct hit patterns on a fixed countable base `V` of the topology of `ℂ`
(`gm_conf_hitPattern_injOn`): the arcs are disjoint nonempty connected subsets of the Jordan
curve `∂𝓑^•_t` (GM.S4.1, `gm_S4_1`; `gm_filledBall_frontier_isJordanCurve'`), which have
different closures (`gm_hitPattern_ne`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM l. 1674–1675, deterministic part**: a.s., `x ↦ (hit pattern of arcOf x on V)` is
injective on `Conf(s, t)` for all `0 < s < t`. -/
theorem gm_conf_hitPattern_injOn (hC24 : CONFLem2_4) (hC27 : CONFLem2_7) (hC14 : CONFThm1_4)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P)
    (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ LocalEvent.lenSet) (𝕫 : ℂ) {V : ℕ → Set ℂ}
    (hV : ∀ (x : ℂ) (O : Set ℂ), IsOpen O → x ∈ O → ∃ n, x ∈ V n ∧ V n ⊆ O)
    (hVo : ∀ n, IsOpen (V n)) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 < s → s < t →
      InjOn (fun x n => (arcOf (D (h ω)) 𝕫 t x ∩ V n).Nonempty) (confPts (D (h ω)) 𝕫 s t) := by
  filter_upwards [gm_S4_1 hC24 hC27 hC14 hγ hγ2 hD P h hh 𝕫, hlen] with ω hS hl s t hs hst
  obtain ⟨-, harc, hdisj, -⟩ := hS s t hs hst
  have hJ := gm_filledBall_frontier_isJordanCurve' (hs.trans hst)
    (LocalEvent.isLength_of_mem_lenSet hl)
    ((gm_filledBall_isBounded_of_lenSet hl 𝕫 t).subset (subset_closure.trans subset_union_left))
  intro x hx x' hx' he
  by_contra hne
  have h1 := harc x hx
  have h2 := harc x' hx'
  exact gm_hitPattern_ne hV hVo hJ h1.1 h2.1 h1.2.isPreconnected h2.2.isPreconnected
    h1.2.nonempty h2.2.nonempty (hdisj hx hx' hne) he


/-- `σ(𝓑^•_{t_k}, h|_{𝓑^•_{t_k}})` at GM's `t_k` (4.6) is the local σ-algebra of
`gmKt D 𝕫 (ℓ𝕣) (1 + kε^β + ε^{2β})` -/
theorem gm_gmSigA_s4T {Ω : Type} [MeasurableSpace Ω] (D : DistC → ContMetric) (h : Ω → DistC)
    (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ) :
    gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k) =
      localSigma h (fun ω => gmKt D 𝕫 (ℓ * 𝕣) (1 + k * ε ^ β + ε ^ (2 * β)) (h ω)) := by
  unfold gmSigA gmKt
  congr 1
  funext ω
  rw [gm_s4T_eq]

end LQGMetric.GM
