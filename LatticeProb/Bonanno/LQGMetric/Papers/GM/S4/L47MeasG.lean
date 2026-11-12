/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L47MeasG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L47InputsZ
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L45Sel2
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasD5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Conditional
import LatticeProb.Bonanno.LQGMetric.Field.MarkovZBIndep
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBasic

/-!
# GM's event `G` is an event of `𝓕_k` (D70, `decisions/DEC-47.md`)

GM, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 4.7 (l. 1902): `G = {(z,r) ∈ 𝒵_k} ∩
{𝕨 ∉ B_R(𝓑^•_{t_k})}` is determined by `𝓑^•_{t_k}`, hence `G ∈ 𝓕_k` (GM use this without
comment). `gm_G0_measurableSet_sigF`: `gmG0 ∈ σ(𝓑^•_{t_k}) ⊆ 𝓕_k`, surely: `(z,r) ∈ 𝒵_k` is
`{𝓑^•_{t_k} ∩ B_a(z) = ∅} ∩ {𝓑^•_{t_k} ∩ cl B_{2a}(z) ≠ ∅}` (`a = λ₄ε𝕣`, `gm_candSet_iff`), with
`dist(z, ∂K) = dist(z, K)` for `z ∉ K` (`gm_infDist_frontier_eq'`, the proof of
`gm_infDist_frontier_eq` in `ManyGoodS46.lean`, repeated here so that this file does not depend on
that work-in-progress module).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent

/-- for `K` closed and `z ∉ K`, `dist(z, ∂K) = dist(z, K)` -/
theorem gm_infDist_frontier_eq' {K : Set ℂ} (hK : IsClosed K) (hne : K.Nonempty) {z : ℂ}
    (hz : z ∉ K) : infDist z (frontier K) = infDist z K := by
  have hseg : ∀ q ∈ K, ∃ p ∈ frontier K, dist z p ≤ dist z q := by
    intro q hq
    obtain ⟨p, hpseg, hpfr⟩ := jb_inter_frontier_nonempty hK (convex_segment z q).isPreconnected
      (left_mem_segment ℝ z q) hz (right_mem_segment ℝ z q) hq
    have hsub : segment ℝ z q ⊆ closedBall z (dist z q) :=
      (convex_closedBall z _).segment_subset (mem_closedBall_self dist_nonneg)
        (by rw [mem_closedBall, dist_comm])
    have := hsub hpseg
    rw [mem_closedBall, dist_comm] at this
    exact ⟨p, hpfr, this⟩
  obtain ⟨q₀, hq₀⟩ := hne
  obtain ⟨p₀, hp₀, -⟩ := hseg q₀ hq₀
  have hfne : (frontier K).Nonempty := ⟨p₀, hp₀⟩
  refine le_antisymm ?_ (infDist_le_infDist_of_subset hK.frontier_subset hfne)
  refine (le_infDist ⟨q₀, hq₀⟩).2 fun q hq => ?_
  obtain ⟨p, hp, hpq⟩ := hseg q hq
  exact (infDist_le_dist_of_mem hp).trans hpq

/-- the distance condition of `𝒵_k` as hit/miss events of a closed set -/
theorem gm_candDist_iff {K : Set ℂ} (hK : IsClosed K) {z : ℂ} {a b : ℝ} (ha : 0 < a) :
    (z ∉ K ∧ infDist z (frontier K) ∈ Icc a b) ↔
      (¬ (K ∩ ball z a).Nonempty ∧ (K ∩ closedBall z b).Nonempty) := by
  constructor
  · rintro ⟨hz, hlo, hhi⟩
    rcases K.eq_empty_or_nonempty with he | hne
    · rw [he, frontier_empty, infDist_empty] at hlo
      linarith
    rw [gm_infDist_frontier_eq' hK hne hz] at hlo hhi
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hxK, hx⟩
      have := infDist_le_dist_of_mem (x := z) hxK
      rw [mem_ball, dist_comm] at hx
      linarith
    · obtain ⟨y, hyK, hy⟩ := hK.exists_infDist_eq_dist hne z
      refine ⟨y, hyK, ?_⟩
      rw [mem_closedBall, dist_comm]
      linarith
  · rintro ⟨hmiss, y, hyK, hy⟩
    have hz : z ∉ K := fun hz => hmiss ⟨z, hz, mem_ball_self ha⟩
    refine ⟨hz, ?_⟩
    rw [gm_infDist_frontier_eq' hK ⟨y, hyK⟩ hz]
    refine ⟨(le_infDist ⟨y, hyK⟩).2 fun x hx => ?_, ?_⟩
    · by_contra hlt
      exact hmiss ⟨x, hx, by rw [mem_ball, dist_comm]; linarith⟩
    · rw [mem_closedBall, dist_comm] at hy
      exact (infDist_le_dist_of_mem hyK).trans hy

/-- **`G ∈ σ(𝓑^•_{t_k})`** -/
theorem gm_G0_measurableSet_setSigma {Ω : Type} [MeasurableSpace Ω] (D : DistC → ContMetric)
    (h : Ω → DistC) (𝕫 𝕨 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ) (lam1 lam4 ν : ℝ) (Rads : Set ℝ) (z : ℂ)
    (r R : ℝ) (ha : 0 < lam4 * ε * 𝕣) :
    MeasurableSet[setSigma (fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω))]
      (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R) := by
  set A : Ω → Set ℂ := fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k ω)
  have hA : ∀ ω, IsClosed (A ω) := fun ω => gm_filledBall_isClosed _ _ _
  have e : gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R =
      {_ω | z ∈ gridPts (lam1 * ε ^ (1 + ν) * 𝕣 / 4) ∧ r ∈ Rads} ∩
        ({ω | (A ω ∩ ball z (lam4 * ε * 𝕣)).Nonempty}ᶜ ∩
          {ω | (A ω ∩ closedBall z (2 * lam4 * ε * 𝕣)).Nonempty}) ∩
        {ω | (A ω ∩ ball 𝕨 R).Nonempty}ᶜ := by
    ext ω
    simp only [gmG0, candSet, mem_ofPred_eq, mem_inter_iff, mem_compl_iff,
      gm_notMem_thickening_iff]
    have := gm_candDist_iff (hA ω) (z := z) (b := 2 * lam4 * ε * 𝕣) ha
    simp only [A] at this
    tauto
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) (gm_setSigma_hit_open A isOpen_ball).compl
  · by_cases hc : z ∈ gridPts (lam1 * ε ^ (1 + ν) * 𝕣 / 4) ∧ r ∈ Rads
    · convert MeasurableSet.univ using 1
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact hc
    · convert MeasurableSet.empty using 1
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact hc
  · exact (gm_setSigma_hit_open A isOpen_ball).compl.inter
      (gm_setSigma_hit_closed hA isClosed_closedBall)

/-- **`G ∈ 𝓕_k`** (`hG₀F` of `gm_L4_7_of_null_G`), surely -/
theorem gm_G0_measurableSet_sigF {Ω : Type} [MeasurableSpace Ω] (D : DistC → ContMetric)
    (h : Ω → DistC) (𝕫 𝕨 : ℂ) (η : Ω → C(unitInterval, ℂ)) (ℓ 𝕣 ε β : ℝ) (k : ℕ)
    (lam1 lam4 ν : ℝ) (Rads : Set ℝ) (z : ℂ) (r R : ℝ) (ha : 0 < lam4 * ε * 𝕣) :
    MeasurableSet[gmSigF D h 𝕫 𝕨 η (s4S D h 𝕫 ℓ 𝕣 ε β k) (s4T D h 𝕫 ℓ 𝕣 ε β k)]
      (gmG0 D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4 ν Rads z r R) :=
  le_sup_left (a := gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β k)) _
    (gm_setSigma_le_localSigma h _ _ (gm_G0_measurableSet_setSigma D h 𝕫 𝕨 ℓ 𝕣 ε β k lam1 lam4
      ν Rads z r R ha))

end LQGMetric.GM
