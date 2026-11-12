/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5ProofAgree at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10ProofCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5: agreement of whole-plane and internal metrics (T:973–978)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`), proof of Lemma 2.5, display
`eqn-square-metric-agree` (T:973–978): on the event of Lemma 2.10 with `C = 2`,
"`sup_{u,v∈S_r(0)} D_h^ε(u,v) ≤ ½ D_h^ε(S_r(0), ∂S_{Rr}(0))` which implies
`D_h^ε(u,v) = D_h^ε(u,v; S_{Rr}(0))` for all `u, v ∈ S_r(0)`."

* `lfppDistE_eq_lfppDOn_of_lt`: if `D(u,v) < inf_{w∈∂K} D(u,w)` (`K` closed, `u, v ∈ K`), then
  `D(u,v) = D(u,v;K)`: a path of length `< inf_{w∈∂K} D(u,w)` cannot leave `K` (a path leaving
  `K` meets `∂K`; the sub-path up to that time is a competitor for `D(u, ∂K)`).
* `lfppDistE_eq_lfppDOn_of_sqBdyEvent`: the implication of T:974–977.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

theorem lfppDistE_self (ξ ε : ℝ) (x : DistC) (u : ℂ) : lfppDistE ξ ε x u u = 0 := by
  rw [lfppDistE_eq_lfppDOn, lfppDOn_self convex_univ (mem_univ u)]

/-- a path of `D`-length `< inf_{w ∈ ∂K} D(u, w)` from `u ∈ K` stays in the closed set `K` -/
theorem lfppDistE_eq_lfppDOn_of_lt {ξ ε : ℝ} {x : DistC} {K : Set ℂ} (hK : IsClosed K) {u v : ℂ}
    (hu : u ∈ K) (hlt : lfppDistE ξ ε x u v < ⨅ w ∈ frontier K, lfppDistE ξ ε x u w) :
    lfppDistE ξ ε x u v = lfppDOn ξ (heatMollify ε x) K u v := by
  refine le_antisymm (lfppDistE_le_lfppDOn ξ ε x K u v) ?_
  by_contra hne
  push_neg at hne
  obtain ⟨Q, hQ⟩ := iInf_lt_iff.1 (lt_min hne hlt)
  obtain ⟨P, hP⟩ := Q
  simp only at hQ
  by_cases hin : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ K
  · exact absurd ((lfppDOn_le hP hin).trans_lt (hQ.trans_le (min_le_left _ _))) (lt_irrefl _)
  push_neg at hin
  obtain ⟨t, ht, hPt⟩ := hin
  have hcon : IsPreconnected (P '' Icc 0 t) :=
    isPreconnected_Icc.image P (hP.continuousOn.mono (Icc_subset_Icc le_rfl ht.2))
  obtain ⟨w, ⟨t', ht', rfl⟩, hw⟩ := cut_inter_frontier_nonempty hK hcon
    ⟨t, ⟨ht.1, le_rfl⟩, rfl⟩ hPt ⟨0, ⟨le_rfl, ht.1⟩, rfl⟩ (by rw [hP.source]; exact hu)
  have hle : lfppDistE ξ ε x u (P t') ≤ lfppLen ξ (heatMollify ε x) P := by
    rcases ht'.1.eq_or_lt with h0 | h0
    · rw [← h0, hP.source, lfppDistE_self]; exact zero_le
    · have hsub := isPiecewiseC1Path_subPath hP le_rfl h0 (ht'.2.trans ht.2)
      rw [hP.source] at hsub
      calc lfppDistE ξ ε x u (P t') ≤ lfppLen ξ (heatMollify ε x) (subPath P 0 t') :=
            iInf_le_of_le ⟨_, hsub⟩ le_rfl
        _ = ∫⁻ s in Icc 0 t', lenDens ξ (heatMollify ε x) P s := lfppLen_subPath P h0
        _ ≤ ∫⁻ s in Icc 0 1, lenDens ξ (heatMollify ε x) P s :=
            lintegral_mono_set (Icc_subset_Icc le_rfl (ht'.2.trans ht.2))
        _ = lfppLen ξ (heatMollify ε x) P := (lfppLen_eq _ _ _).symm
  have := (iInf₂_le (f := fun w _ => lfppDistE ξ ε x u w) (P t') hw).trans hle
  exact absurd (this.trans_lt (hQ.trans_le (min_le_right _ _))) (lt_irrefl _)

/-- **DFGPS T:974–977**: on the event of (2.10) with `C = 2` (and `R ≥ 1`),
`D_h^ε(u,v) = D_h^ε(u,v;S_{Rr}(0))` for all `u, v ∈ S_r(0)`. -/
theorem lfppDistE_eq_lfppDOn_of_sqBdyEvent {ξ ε r R : ℝ} {x : DistC} (hr : 0 ≤ r) (hR : 1 ≤ R)
    (hE : sqBdyEvent ξ ε 2 r R x) {u v : ℂ} (hu : u ∈ sqC r 0) (hv : v ∈ sqC r 0) :
    lfppDistE ξ ε x u v = lfppDOn ξ (heatMollify ε x) (sqC (R * r) 0) u v := by
  have hsub : sqC r 0 ⊆ sqC (R * r) 0 := sqC_mono (le_mul_of_one_le_left hr hR)
  refine lfppDistE_eq_lfppDOn_of_lt (isCompact_sqC (by positivity)).isClosed (hsub hu) ?_
  unfold sqBdyEvent at hE
  set I := ⨅ u ∈ sqC r 0, ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε x u v
  have h1 : lfppDistE ξ ε x u v ≤ ⨆ u ∈ sqC r 0, ⨆ v ∈ sqC r 0, lfppDistE ξ ε x u v :=
    le_iSup₂_of_le (f := fun u _ => ⨆ v ∈ sqC r 0, lfppDistE ξ ε x u v) u hu
      (le_iSup₂_of_le (f := fun v _ => lfppDistE ξ ε x u v) v hv le_rfl)
  have h2 : I ≤ ⨅ w ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε x u w :=
    iInf₂_le_of_le (f := fun u _ => ⨅ v ∈ frontier (sqC (R * r) 0), lfppDistE ξ ε x u v) u hu
      le_rfl
  have h3 : ENNReal.ofReal 2⁻¹ * I ≤ I := by
    calc ENNReal.ofReal 2⁻¹ * I ≤ 1 * I := by
          gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
      _ = I := one_mul I
  exact h1.trans_lt (hE.trans_le (h3.trans h2))

end LQGMetric.DFGPS
