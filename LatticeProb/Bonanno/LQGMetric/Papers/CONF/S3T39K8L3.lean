/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8L3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8g
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8L2

/-!
# `hCtr`, `hGood` for `K` with nonempty interior, from `T39K8LocAccessI`

Copies of P2-T39K8's `k8_of_disc` (S3T39K8b), `k8CtrHit_iff` (S3T39K8f), `k8_hCtr`, `k8_hGood`
(S3T39K8g) with `(interior K).Nonempty` added to the class (right after `IsBounded K`) and
`T39K8LocAccess` replaced by `T39K8LocAccessI` (proved in S3T39K8L2, `t39k8_locAccessI`).
The proofs are those of the originals verbatim (only the extra hypothesis is threaded through).
`t39k8_hCtrI`, `t39k8_hGoodI` are the unconditional forms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory

namespace LQGMetric.CONF

/-- `DisconnectsFromInfty` implies `k8Disc` for Jordan `K` (uses `T39K8LocAccess`) -/
theorem k8_of_discI (hLA : T39K8LocAccessI) {K J : Set ℂ} (hK : IsClosed K)
    (hKb : Bornology.IsBounded K) (hKi : (interior K).Nonempty) (hJor : JordanMap.IsJordanCurve (frontier K))
    (hJK : J ⊆ frontier K) {c : ℂ} {a : ℝ} (h : DisconnectsFromInfty K (closedBall c a) J) :
    k8Disc K J c a := by
  obtain ⟨R, hR⟩ := h
  obtain ⟨M, hM⟩ := hKb.subset_closedBall 0
  obtain ⟨n, hn⟩ := exists_nat_gt (max R M + 1)
  have hnR : R < n := by linarith [le_max_left R M]
  have hKn : ∀ z ∈ K, ‖z‖ ≤ (n : ℝ) - 1 := fun z hz => by
    have := hM hz; rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_right R M]
  refine ⟨n, fun ⟨z, hz, hz'⟩ => by have := hKn z hz; simp only [mem_setOf_eq] at hz'; linarith,
    fun m => ?_⟩
  by_contra hk
  push_neg at hk
  choose q hW hJ hd using hk
  choose x' hx'J hx'b using hJ
  have hfb : IsCompact (closure J) := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
    exact hKb.subset ((closure_minimal hJK isClosed_frontier).trans
      (frontier_subset_closure.trans hK.closure_eq.subset))
  obtain ⟨x, hxJ, φ, hφ, hlim⟩ := hfb.tendsto_subseq (fun k => subset_closure (hx'J k))
  have hxK : x ∈ frontier K := closure_minimal hJK isClosed_frontier hxJ
  set ε : ℝ := 1 / (4 * ((m : ℝ) + 1)) with hε
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hε0 : 0 < ε := by positivity
  have hεm : 1 / ((m : ℝ) + 1) = 4 * ε := by rw [hε]; field_simp
  obtain ⟨δ, hδ, hLAx⟩ := hLA K hK hKb hKi hJor x hxK ε hε0
  set μ := min δ ε / 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have hμδ : 2 * μ ≤ δ := by have := min_le_left δ ε; rw [hμ]; linarith
  have hμε : 2 * μ ≤ ε := by have := min_le_right δ ε; rw [hμ]; linarith
  obtain ⟨k₁, hk₁⟩ := (Metric.tendsto_atTop.1 hlim) μ hμ0
  obtain ⟨k₂, hk₂⟩ := exists_nat_one_div_lt hμ0
  set k := max k₁ k₂
  have hφk : k₂ ≤ φ k := (le_max_right k₁ k₂).trans (hφ.id_le k)
  have h1 : dist (x' (φ k)) x < μ := hk₁ k (le_max_left _ _)
  have h2 : 1 / ((φ k : ℝ) + 1) < μ := by
    refine lt_of_le_of_lt ?_ hk₂
    gcongr
  have h3 : dist (k8Q (q (φ k))) (x' (φ k)) < μ := by
    have := hx'b (φ k); rw [mem_ball, dist_comm] at this; linarith
  have hwx : dist (k8Q (q (φ k))) x < δ := by
    linarith [dist_triangle (k8Q (q (φ k))) (x' (φ k)) x]
  have hwx' : dist (k8Q (q (φ k))) x < ε := by
    linarith [dist_triangle (k8Q (q (φ k))) (x' (φ k)) x]
  obtain ⟨y, hy, hjoin⟩ := k8W_joinedIn (hW (φ k))
  have hjoinK : JoinedIn Kᶜ y (k8Q (q (φ k))) :=
    hjoin.mono (compl_subset_compl.2 subset_union_left)
  obtain ⟨β, hβx, hβK⟩ := hLAx y _ hjoinK
    (fun z hz => by have := hKn z hz; linarith) hwx (x' (φ k)) (hJK (hx'J (φ k))) (by linarith)
  have hd' := hd (φ k)
  rw [hεm] at hd'
  have hxc : a + 3 * ε < dist x c := by
    linarith [dist_triangle (k8Q (q (φ k))) x c]
  obtain ⟨p, hp, hpc⟩ := hR y (x' (φ k)) (hjoin.somePath.trans β) (by linarith) (hx'J (φ k))
    (by
      rw [Path.trans_range]
      rintro z ⟨hz1 | hz2, hzK⟩
      · obtain ⟨t, rfl⟩ := hz1
        exact absurd (Or.inl hzK) (hjoin.somePath_mem t)
      · exact hβK ⟨hz2, hzK⟩)
  rw [Path.trans_range] at hp
  rcases hp with ⟨t, rfl⟩ | hp
  · exact hjoin.somePath_mem t (Or.inr hpc)
  · have := hβx hp
    rw [mem_ball] at this
    rw [mem_closedBall] at hpc
    linarith [dist_triangle x p c, dist_comm x p]

/-- **hit events of the centre set** -/
theorem k8CtrHit_iffI (hLA : T39K8LocAccessI) {K J : Set ℂ} (hK : IsClosed K)
    (hKb : Bornology.IsBounded K) (hKi : (interior K).Nonempty) (hJor : JordanMap.IsJordanCurve (frontier K))
    (hJK : J ⊆ frontier K) (r : ℝ) {U : Set ℂ} (hU : IsOpen U) :
    k8CtrHit K J r U ↔ (t39jCtrSet K J r ∩ U).Nonempty := by
  have hJK' : J ⊆ K := hJK.trans hK.frontier_subset
  rw [t39jCtrSet, closure_inter_open_nonempty_iff hU]
  constructor
  · rintro ⟨p, ρ, hρ, hFU, H⟩
    choose c' hc'p hfr hdisc using H
    have hz : ∀ j, (frontier K ∩ ball (k8Q (c' j)) (1 / ((j : ℝ) + 1))).Nonempty :=
      fun j => (k8FrHit_iff hK isOpen_ball).1 (hfr j)
    choose z hzf hzb using hz
    obtain ⟨M, hM⟩ := hKb.subset_closedBall 0
    obtain ⟨N, hN⟩ := exists_nat_gt (|M| + ‖k8Q p‖ + ρ + |r| + 4)
    have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg M, norm_nonneg (k8Q p), abs_nonneg r]
    have hKN : ∀ w ∈ K, ‖w‖ ≤ (N : ℝ) - 1 := fun w hw => by
      have := hM hw; rw [mem_closedBall, dist_zero_right] at this
      linarith [le_abs_self M, norm_nonneg (k8Q p), abs_nonneg r]
    have hR : ∀ j, k8DiscR K (closedBall (k8Q (c' j)) (r + 1 / ((j : ℝ) + 1))) J N := by
      intro j
      obtain ⟨n, -, Hn⟩ := hdisc j
      have hcN : ‖k8Q (c' j)‖ + (r + 1 / ((j : ℝ) + 1)) ≤ (N : ℝ) - 1 := by
        have h1 : ‖k8Q (c' j)‖ ≤ ‖k8Q p‖ + (ρ + 1) := by
          have := hc'p j
          have h1j : 1 / ((j : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
          linarith [norm_le_norm_add_norm_sub' (k8Q (c' j)) (k8Q p), dist_eq_norm (k8Q (c' j)) (k8Q p)]
        have h1j : 1 / ((j : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
        linarith [le_abs_self r, abs_nonneg M]
      refine k8_discR_of hK hJK' (fun ⟨w, hw, hw'⟩ => ?_) (fun m => ?_)
      · have := hKN w hw; simp only [mem_ofPred_eq] at hw'; linarith
      · obtain ⟨k, hk⟩ := Hn m
        exact ⟨k, fun q hq hJq => hk q (k8W_uniform hK hN1 hKN hcN hq n) hJq⟩
    obtain ⟨c₀, hc₀, φ, hφ, hlim⟩ := (t39j_isCompact_frontier hKb).tendsto_subseq hzf
    have hdj : Tendsto (fun j => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hc'lim : Tendsto (fun j => k8Q (c' (φ j))) atTop (𝓝 c₀) := by
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
        (by simpa using hdj.add (tendsto_iff_dist_tendsto_zero.1 hlim)))
      have := hzb (φ j)
      rw [mem_ball, dist_comm, one_div] at this
      show dist (k8Q (c' (φ j))) c₀ ≤ ((φ j : ℝ) + 1)⁻¹ + dist (z (φ j)) c₀
      linarith [dist_triangle (k8Q (c' (φ j))) (z (φ j)) c₀]
    have hrlim : Tendsto (fun j => r + 1 / ((φ j : ℝ) + 1)) atTop (𝓝 r) := by
      simpa using hdj.const_add r
    have hD := k8DiscR_limit hc'lim hrlim fun j => hR (φ j)
    have hc₀p : dist c₀ (k8Q p) ≤ ρ := by
      have hρlim : Tendsto (fun j => (ρ : ℝ) + 1 / ((φ j : ℝ) + 1)) atTop (𝓝 (ρ : ℝ)) := by
        simpa using hdj.const_add (ρ : ℝ)
      exact le_of_tendsto_of_tendsto' (hc'lim.dist tendsto_const_nhds) hρlim
        fun j => (hc'p (φ j)).le
    exact ⟨c₀, ⟨hc₀, N, hD⟩, hFU (mem_closedBall.2 hc₀p)⟩
  · rintro ⟨c, ⟨hcf, hcD⟩, hcU⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU c hcU
    obtain ⟨p, hp⟩ := k8_exists_rat c (show 0 < ε / 4 by linarith)
    have hp' : dist (k8Q p) c < ε / 4 := hp
    obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
    refine ⟨p, ρ, by linarith, fun w hw => hεU ?_, fun j => ?_⟩
    · rw [mem_closedBall] at hw; rw [mem_ball]; linarith [dist_triangle w (k8Q p) c]
    · obtain ⟨c', hc'⟩ := k8_exists_rat c (k8_one_div_pos j)
      have hc'' : dist (k8Q c') c < 1 / ((j : ℝ) + 1) := hc'
      refine ⟨c', ?_, (k8FrHit_iff hK isOpen_ball).2 ⟨c, hcf, ?_⟩, ?_⟩
      · rw [dist_comm] at hp'; linarith [dist_triangle (k8Q c') c (k8Q p)]
      · rw [mem_ball, dist_comm]; exact hc''
      · refine k8_of_discI hLA hK hKb hKi hJor hJK (hcD.mono fun w hw => ?_)
        rw [mem_closedBall] at hw ⊢
        linarith [dist_triangle w c (k8Q c'), dist_comm c (k8Q c')]

attribute [local instance] effrosSigma

/-- **`hCtr` of `t39k5_fields_at`** -/
theorem k8_hCtrI (hLA : T39K8LocAccessI) : ∃ Ψ : ℝ → Set ℂ × Set ℂ → ℂ,
    (∀ r, @Measurable _ _ (@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma) _ (Ψ r)) ∧
    ∀ (K J : Set ℂ) (r : ℝ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
      JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K → t39jCtr K J r = Ψ r (K, J) := by
  set C : Set (Set ℂ × Set ℂ) := {x | IsClosed x.1 ∧ Bornology.IsBounded x.1 ∧ (interior x.1).Nonempty ∧
    JordanMap.IsJordanCurve (frontier x.1) ∧ x.2 ⊆ frontier x.1}
  have H : ∀ r : ℝ, ∃ Ψ : Set ℂ × Set ℂ → ℂ, Measurable Ψ ∧
      ∀ x ∈ C, t39jLexMin (k8F r x) = Ψ x := by
    intro r
    refine k8_lexMin_meas C (k8F r) (fun x hx => ?_)
      (fun U => {x | k8CtrHit x.1 x.2 r univ ∧ k8CtrHit x.1 x.2 r U} ∪
        {x | ¬ k8CtrHit x.1 x.2 r univ ∧ k8FrHit x.1 U})
      (fun U _ => ((k8CtrHit_meas r univ).inter (k8CtrHit_meas r U)).union
        ((k8CtrHit_meas r univ).compl.inter (k8FrHit_meas U))) (fun U hU x hx => ?_)
    · obtain ⟨hK, hKb, -, hJor, -⟩ := hx
      unfold k8F
      split_ifs with h
      · exact ⟨t39j_isCompact_ctrSet hKb _ r, h⟩
      · exact ⟨t39j_isCompact_frontier hKb, k8_frontier_nonempty hJor⟩
    · obtain ⟨hK, hKb, hKi, hJor, hJK⟩ := hx
      have hu := k8CtrHit_iffI hLA hK hKb hKi hJor hJK r isOpen_univ
      have hU' := k8CtrHit_iffI hLA hK hKb hKi hJor hJK r hU
      rw [inter_univ] at hu
      simp only [mem_union, mem_ofPred_eq, hu, hU', k8FrHit_iff hK hU]
      unfold k8F
      split_ifs with h <;> simp [h]
  choose Ψ hΨ hΨeq using H
  exact ⟨Ψ, hΨ, fun K J r hK hKb hKi hJor hJK => hΨeq r (K, J) ⟨hK, hKb, hKi, hJor, hJK⟩⟩

/-- **`hGood` of `t39k5_fields_at`** -/
theorem k8_hGoodI (hLA : T39K8LocAccessI) (R : ℝ) : ∃ A : ℕ → Set (Set ℂ × Set ℂ),
    (∀ q, MeasurableSet[@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma] (A q)) ∧
    ∀ (K J : Set ℂ) (q : ℕ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
      JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K →
      (t39jGoodAct K J q R ↔ (K, J) ∈ A q) := by
  obtain ⟨Ψ, hΨ, hΨeq⟩ := k8_hCtrI hLA
  set ε : ℕ → ℝ := fun q => (2 : ℝ)⁻¹ ^ t39gExp q * R
  refine ⟨fun q => {_x | 1 ≤ t39gExp q} ∩ ({x | (x.2 ∩ univ).Nonempty} ∩
    {x | ∃ ρ : ℚ, 0 ≤ (ρ : ℝ) ∧ (ρ : ℝ) < ε q ∧ k8Disc x.1 x.2 (Ψ (ε q / 2) x) ρ}),
    fun q => ?_, fun K J q hK hKb hKi hJor hJK => ?_⟩
  · refine (MeasurableSet.const _).inter ((k8_hit2_meas isOpen_univ).inter ?_)
    simp only [ofPred_exists, ofPred_and]
    exact MeasurableSet.iUnion fun ρ => (MeasurableSet.const _).inter
      ((MeasurableSet.const _).inter (k8Disc_comp_meas (hΨ _) _))
  · have hc := hΨeq K J (ε q / 2) hK hKb hKi hJor hJK
    simp only [mem_inter_iff, mem_ofPred_eq, inter_univ, t39jGoodAct]
    rw [← hc]
    have hmem := k8_ctr_mem (J := J) hKb hJor (ε q / 2)
    constructor
    · rintro ⟨h1, h2, -, ρ, hρ0, hρε, hD⟩
      obtain ⟨ρ', hρ'₁, hρ'₂⟩ := exists_rat_btwn hρε
      refine ⟨h1, h2, ρ', by linarith, hρ'₂, k8_of_discI hLA hK hKb hKi hJor hJK
        (hD.mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hρ'₁.le)))⟩
    · rintro ⟨h1, h2, ρ', hρ'0, hρ'ε, hD⟩
      have hD' := k8_disc_of hK (hJK.trans hK.frontier_subset) hD
      refine ⟨h1, h2, hmem, ((ρ' : ℝ) + ε q) / 2, by linarith,
        by have := hρ'ε; simp only [ε] at this ⊢; linarith,
        hD'.mono (closedBall_subset_ball (by linarith))⟩

/-- **`hCtr`** for the class with nonempty interior, unconditional -/
theorem t39k8_hCtrI : ∃ Ψ : ℝ → Set ℂ × Set ℂ → ℂ,
    (∀ r, @Measurable _ _ (@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma) _ (Ψ r)) ∧
    ∀ (K J : Set ℂ) (r : ℝ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
      JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K → t39jCtr K J r = Ψ r (K, J) :=
  k8_hCtrI t39k8_locAccessI

/-- **`hGood`** for the class with nonempty interior, unconditional -/
theorem t39k8_hGoodI (R : ℝ) : ∃ A : ℕ → Set (Set ℂ × Set ℂ),
    (∀ q, MeasurableSet[@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma] (A q)) ∧
    ∀ (K J : Set ℂ) (q : ℕ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
      JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K →
      (t39jGoodAct K J q R ↔ (K, J) ∈ (A q)) :=
  k8_hGoodI t39k8_locAccessI R

end LQGMetric.CONF
