/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasDet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStab
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
# GM Lemma 4.6 (a), deterministic part: `{(z,r) ∈ 𝒵_k}` is local (task P2-E3a)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.6, l. 1705–1706: "Since `𝓑^•_{t_k}` is a local set for `h` and since balls
`B_r(z)` for `(z,r) ∈ 𝒵_k` are disjoint from `𝓑^•_{t_k}`, we find that `{(z,r) ∈ 𝒵_k}` is
determined by `h|_{ℂ∖B_r(z)}`."

Deterministic content (Axiom II reduces the random statement to it, `L46Meas.lean`): for two
length metrics `d₁, d₂` whose internal metrics agree on an open set `U ⊇ ℂ ∖ B_ρ(z)`, with
`ρ ≤ λ₄ε𝕣`, the event `(z,r) ∈ 𝒵_k` (GM (4.10), `candSet` at `𝓑^•_{t_k}`,
`t_k = τ_{ℓ𝕣} · (1 + kε^β + ε^{2β})`, D16) holds for `d₁` iff it holds for `d₂`.

* `gm_ballM_eq_of_internal_eq`: if `𝓑_s(𝕫; d₁) ⊆ U` then `𝓑_s(𝕫; d₂) = 𝓑_s(𝕫; d₁)` (GM S3.1,
  `ContMetric.internal_eq_of_lt_infEDist_frontier`, `infEDist_frontier_eq_of_internal_eq`);
* `gm_sInf_eq_of_agree`: the exit time `τ` only depends on the filled balls up to any time `> τ`;
* `gm_candEvD_of_internal_eq`: the main statement. On `(z,r) ∈ 𝒵_k` we have
  `dist(z, 𝓑^•_{t_k}) ≥ λ₄ε𝕣 ≥ ρ` (a segment from `z` to the hull crosses its boundary), so all
  filled balls up to `t_k` lie in `U`, where both metrics have the same balls.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the filled-ball exit time `τ_R(𝕫) = inf {s > 0 : 𝓑^•_s(𝕫) ⊄ B_R(𝕫)}` of one metric (CONF's
`tauR` at one sample) -/
def tauD (d : ContMetric) (𝕫 : ℂ) (R : ℝ) : ℝ :=
  sInf {s | 0 < s ∧ ¬ filledBall d 𝕫 s ⊆ Metric.ball 𝕫 R}

theorem gm_tauR_eq_tauD {Ω : Type} (D : DistC → ContMetric) (h : Ω → DistC) (𝕫 : ℂ) (R : ℝ)
    (ω : Ω) : tauR D h 𝕫 R ω = tauD (D (h ω)) 𝕫 R := rfl

/-- `t_k = τ_{ℓ𝕣} (1 + kε^β + ε^{2β})` -/
theorem gm_s4T_eq {Ω : Type} [MeasurableSpace Ω] (D : DistC → ContMetric) (h : Ω → DistC)
    (𝕫 : ℂ) (ℓ 𝕣 ε β : ℝ) (k : ℕ) (ω : Ω) :
    s4T D h 𝕫 ℓ 𝕣 ε β k ω = tauD (D (h ω)) 𝕫 (ℓ * 𝕣) * (1 + k * ε ^ β + ε ^ (2 * β)) := by
  simp only [s4T, s4S, s4Unit, gm_tauR_eq_tauD]
  ring

/-- the event `(z, r) ∈ 𝒵_k` (GM (4.10)) for one metric, with `t_k = τ_R · c` -/
def candEvD (d : ContMetric) (𝕫 : ℂ) (R c lam1 lam4 ε ν 𝕣 : ℝ) (Rads : Set ℝ) (z : ℂ) (r : ℝ) :
    Prop :=
  (z, r) ∈ candSet (filledBall d 𝕫 (tauD d 𝕫 R * c)) lam1 lam4 ε ν 𝕣 Rads

theorem gm_filledBall_congr {d₁ d₂ : ContMetric} {𝕫 : ℂ} {s : ℝ}
    (h : ballM d₁ 𝕫 s = ballM d₂ 𝕫 s) : filledBall d₁ 𝕫 s = filledBall d₂ 𝕫 s := by
  unfold filledBall
  rw [h]

theorem gm_ballM_nonpos (d : ContMetric) (𝕫 : ℂ) {s : ℝ} (hs : s ≤ 0) : ballM d 𝕫 s = ∅ := by
  ext w
  simp only [ballM, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
  exact hs.trans (gm_D_nonneg d 𝕫 w)

theorem gm_filledBall_nonpos (d : ContMetric) (𝕫 : ℂ) {s : ℝ} (hs : s ≤ 0) :
    filledBall d 𝕫 s = ∅ := by
  unfold filledBall
  rw [gm_ballM_nonpos d 𝕫 hs, closure_empty, compl_empty]
  ext x
  simp only [mem_union, mem_empty_iff_false, mem_ofPred_eq, false_or, iff_false, not_and,
    connectedComponentIn_univ]
  intro _
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact NormedSpace.unbounded_univ ℝ ℂ

/-- **GM S3.1 for balls centred at `𝕫`**: if `𝓑_s(𝕫; d₁) ⊆ U` and the internal metrics on `U`
agree, the two `s`-balls agree. -/
theorem gm_ballM_eq_of_internal_eq {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength)
    {U : Set ℂ} (hU : IsOpen U)
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y) {𝕫 : ℂ} {s : ℝ}
    (hs : 0 < s) (hsub : ballM d₁ 𝕫 s ⊆ U) : ballM d₂ 𝕫 s = ballM d₁ 𝕫 s := by
  have h𝕫 : 𝕫 ∈ U := hsub (show d₁.1 (𝕫, 𝕫) < s by rw [d₁.2.self_eq_zero]; exact hs)
  have hρ : ENNReal.ofReal s ≤ Metric.infEDist (d₁.pt 𝕫) (d₁.pt '' frontier U) := by
    refine Metric.le_infEDist.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hyU : y ∉ U := by
      intro h
      rw [frontier, hU.interior_eq] at hy
      exact hy.2 h
    have : ¬ d₁.1 (𝕫, y) < s := fun h => hyU (hsub h)
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (not_lt.1 this)
  have hρ₂ : ENNReal.ofReal s ≤ Metric.infEDist (d₂.pt 𝕫) (d₂.pt '' frontier U) := by
    rw [← ContMetric.infEDist_frontier_eq_of_internal_eq h₁ h₂ hU h𝕫 heq]
    exact hρ
  have key : ∀ {d d' : ContMetric}, d.IsLength →
      (∀ x ∈ U, ∀ y ∈ U, d.internal U x y = d'.internal U x y) →
      ENNReal.ofReal s ≤ Metric.infEDist (d.pt 𝕫) (d.pt '' frontier U) →
      ∀ v, d.1 (𝕫, v) < s → d'.1 (𝕫, v) < s := by
    intro d d' hd hdd' hρd v hv
    have hlt0 : edist (d.pt 𝕫) (d.pt v) < ENNReal.ofReal s := by
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff hs).2 hv
    obtain ⟨hvU, hint⟩ :=
      ContMetric.internal_eq_of_lt_infEDist_frontier hd hU h𝕫 (hlt0.trans_le hρd)
    have : edist (d'.pt 𝕫) (d'.pt v) < ENNReal.ofReal s :=
      calc edist (d'.pt 𝕫) (d'.pt v) ≤ d'.internal U 𝕫 v :=
            MetricGeometry.edist_le_internalEDist _ _ _
        _ = d.internal U 𝕫 v := (hdd' _ h𝕫 _ hvU).symm
        _ = edist (d.pt 𝕫) (d.pt v) := hint
        _ < ENNReal.ofReal s := hlt0
    rw [edist_dist] at this
    exact (ENNReal.ofReal_lt_ofReal_iff hs).1 this
  ext v
  exact ⟨key h₂ (fun x hx y hy => (heq x hx y hy).symm) hρ₂ v, key h₁ heq hρ v⟩

/-- the infimum of a set of positive reals is determined by the set below any level `T` larger
than the infimum -/
theorem gm_sInf_eq_of_agree {S₁ S₂ : Set ℝ} {T : ℝ} (h0₁ : ∀ s ∈ S₁, 0 < s)
    (h0₂ : ∀ s ∈ S₂, 0 < s) (hagree : ∀ s ≤ T, (s ∈ S₁ ↔ s ∈ S₂)) (hne : S₁.Nonempty)
    (hT : sInf S₁ < T) : sInf S₂ = sInf S₁ := by
  obtain ⟨s₀, hs₀, hs₀T⟩ := exists_lt_of_csInf_lt hne hT
  have hs₀' : s₀ ∈ S₂ := (hagree s₀ hs₀T.le).1 hs₀
  have aux : ∀ A B : Set ℝ, (∀ s ≤ T, (s ∈ A ↔ s ∈ B)) → (∀ s ∈ B, 0 < s) → s₀ ∈ B →
      A.Nonempty → sInf B ≤ sInf A := by
    intro A B hAB hB0 hs₀B hA
    have hbdd : BddBelow B := ⟨0, fun s hs => (hB0 s hs).le⟩
    refine le_csInf hA fun x hx => ?_
    by_cases hxT : x ≤ T
    · exact csInf_le hbdd ((hAB x hxT).1 hx)
    · exact (csInf_le hbdd hs₀B).trans (hs₀T.le.trans (not_le.1 hxT).le)
  exact le_antisymm (aux S₁ S₂ hagree h0₂ hs₀' hne)
    (aux S₂ S₁ (fun s hs => (hagree s hs).symm) h0₁ hs₀ ⟨s₀, hs₀'⟩)

/-- a point outside a set `K` is at distance `≥ dist(z, ∂K)` from every point of `K` -/
theorem gm_infDist_frontier_le_dist {K : Set ℂ} {z x : ℂ} (hz : z ∉ K) (hx : x ∈ K) :
    infDist z (frontier K) ≤ dist z x := by
  have hseg : IsPreconnected (segment ℝ z x) := (convex_segment z x).isPreconnected
  obtain ⟨p, hpseg, hpK⟩ : (segment ℝ z x ∩ frontier K).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hcov : segment ℝ z x ⊆ interior K ∪ (closure K)ᶜ := by
      intro y hy
      by_cases hyc : y ∈ closure K
      · left
        by_contra hyi
        exact (eq_empty_iff_forall_notMem.1 hemp) y ⟨hy, hyc, hyi⟩
      · exact Or.inr hyc
    obtain ⟨y, -, hy1, hy2⟩ := hseg (interior K) (closure K)ᶜ isOpen_interior
      isClosed_closure.isOpen_compl hcov
      (by
        refine ⟨x, right_mem_segment ℝ z x, ?_⟩
        rcases hcov (right_mem_segment ℝ z x) with h | h
        · exact h
        · exact absurd (subset_closure hx) h)
      (by
        refine ⟨z, left_mem_segment ℝ z x, ?_⟩
        rcases hcov (left_mem_segment ℝ z x) with h | h
        · exact absurd (interior_subset h) hz
        · exact h)
    exact hy2 (interior_subset_closure hy1)
  have hp : dist p z ≤ dist x z := by
    have := (convex_closedBall z (dist x z)).segment_subset (mem_closedBall_self dist_nonneg)
      (mem_closedBall.2 le_rfl) hpseg
    exact mem_closedBall.1 this
  calc infDist z (frontier K) ≤ dist z p := infDist_le_dist_of_mem hpK
    _ = dist p z := dist_comm _ _
    _ ≤ dist x z := hp
    _ = dist z x := dist_comm _ _

/-- **GM Lemma 4.6, first claim, deterministic form** (l. 1705–1706). -/
theorem gm_candEvD_of_internal_eq {d₁ d₂ : ContMetric} (h₁ : d₁.IsLength) (h₂ : d₂.IsLength)
    {𝕫 : ℂ} {R c lam1 lam4 ε ν 𝕣 : ℝ} {Rads : Set ℝ} {z : ℂ} {r ρ : ℝ} (hc : 1 < c)
    (ha : 0 < lam4 * ε * 𝕣) (hρ : ρ ≤ lam4 * ε * 𝕣) {U : Set ℂ} (hU : IsOpen U)
    (hUρ : (Metric.ball z ρ)ᶜ ⊆ U)
    (heq : ∀ x ∈ U, ∀ y ∈ U, d₁.internal U x y = d₂.internal U x y)
    (H : candEvD d₁ 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r) :
    candEvD d₂ 𝕫 R c lam1 lam4 ε ν 𝕣 Rads z r := by
  obtain ⟨hgrid, hzK, hrR, hdist⟩ := H
  set τ₁ := tauD d₁ 𝕫 R with hτ₁
  set K₁ := filledBall d₁ 𝕫 (τ₁ * c) with hK₁
  have hτpos : 0 < τ₁ := by
    by_contra hneg
    have hK : K₁ = ∅ := gm_filledBall_nonpos d₁ 𝕫
      (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (by linarith))
    have h0 := hdist.1
    rw [hK, frontier_empty, infDist_empty] at h0
    linarith
  have hT : 0 < τ₁ * c := mul_pos hτpos (by linarith)
  have hτT : τ₁ < τ₁ * c := by nlinarith
  have hKU : K₁ ⊆ U := by
    intro x hx
    refine hUρ fun hxb => ?_
    have h1 := gm_infDist_frontier_le_dist hzK hx
    rw [mem_ball, dist_comm] at hxb
    linarith [hdist.1]
  have hball : ∀ s ≤ τ₁ * c, ballM d₂ 𝕫 s = ballM d₁ 𝕫 s := by
    intro s hs
    rcases le_or_gt s 0 with hs0 | hs0
    · rw [gm_ballM_nonpos d₂ 𝕫 hs0, gm_ballM_nonpos d₁ 𝕫 hs0]
    · refine gm_ballM_eq_of_internal_eq h₁ h₂ hU heq hs0 ?_
      exact subset_closure.trans (subset_union_left.trans
        ((gm_filledBall_mono d₁ 𝕫 hs).trans hKU))
  have hfb : ∀ s ≤ τ₁ * c, filledBall d₂ 𝕫 s = filledBall d₁ 𝕫 s := fun s hs =>
    gm_filledBall_congr (hball s hs)
  have hne : {s | 0 < s ∧ ¬ filledBall d₁ 𝕫 s ⊆ Metric.ball 𝕫 R}.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have : τ₁ = 0 := by rw [hτ₁, tauD, hemp, Real.sInf_empty]
    linarith
  have hτ : tauD d₂ 𝕫 R = τ₁ := by
    refine gm_sInf_eq_of_agree (fun s hs => hs.1) (fun s hs => hs.1) ?_ hne hτT
    intro s hs
    simp only [mem_ofPred_eq, hfb s hs]
  have hK : filledBall d₂ 𝕫 (tauD d₂ 𝕫 R * c) = K₁ := by rw [hτ, hfb _ le_rfl]
  show (z, r) ∈ candSet (filledBall d₂ 𝕫 (tauD d₂ 𝕫 R * c)) lam1 lam4 ε ν 𝕣 Rads
  rw [hK]
  exact ⟨hgrid, hzK, hrR, hdist⟩

end LQGMetric.GM
