/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8

/-!
# CONF Theorem 3.9, packet J6d, node O2: `DisconnectsFromInfty` through countable data

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1586. For `K` closed, bounded, with Jordan frontier and `J ⊆ ∂K`, the event "`B̄_a(c)`
disconnects `J` from `∞` in `ℂ ∖ K`" (`DisconnectsFromInfty`) is expressed through countably many
hit events of `K` and `J` (**`k8_disc_iff`**): for some `n` with `K ⊆ B̄_{n-1}(0)` and every `m`
there is `k` such that every rational point `q` joined to `{‖·‖ > n}` by an admissible chain of
balls (`k8W`) and within `1/(k+1)` of `J` is within `a + 1/(m+1)` of `c`.

Topological input: `T39K8LocAccess`, the uniform local accessibility of a Jordan curve from the
unbounded complementary component (from Carathéodory's extension of the exterior conformal map to
the closed exterior disc; Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Thm 2.6 and
Prop. 2.3 — every Jordan domain is locally connected at its boundary). The proof of `k8_disc_iff`
from it is an own elementary argument (CONF gives none).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace LQGMetric.CONF

/-- `q` is joined to `{‖·‖ > n}` by a chain of balls avoiding `K ∪ B̄_a(c)` -/
def k8W (K : Set ℂ) (c : ℂ) (a : ℝ) (n : ℕ) (q : ℂ) : Prop :=
  ∃ l : List K8B, (∀ b ∈ l, k8Good K c a b) ∧ ∃ y : ℂ, (n : ℝ) < ‖y‖ ∧ k8G q l y

/-- the rational point `q` -/
def k8Q (q : ℚ × ℚ) : ℂ := ⟨(q.1 : ℝ), (q.2 : ℝ)⟩

/-- the countable condition replacing `DisconnectsFromInfty K (closedBall c a) J` -/
def k8Disc (K J : Set ℂ) (c : ℂ) (a : ℝ) : Prop :=
  ∃ n : ℕ, ¬ (K ∩ {z | (n : ℝ) - 1 < ‖z‖}).Nonempty ∧ ∀ m : ℕ, ∃ k : ℕ, ∀ q : ℚ × ℚ,
    k8W K c a n (k8Q q) → (J ∩ ball (k8Q q) (1 / ((k : ℝ) + 1))).Nonempty →
      dist (k8Q q) c ≤ a + 1 / ((m : ℝ) + 1)

theorem k8W_joinedIn {K : Set ℂ} {c : ℂ} {a : ℝ} {n : ℕ} {q : ℂ} (h : k8W K c a n q) :
    ∃ y : ℂ, (n : ℝ) < ‖y‖ ∧ JoinedIn (K ∪ closedBall c a)ᶜ y q := by
  obtain ⟨l, hl, y, hy, hG⟩ := h
  exact ⟨y, hy, (k8G_joinedIn (fun b hb => k8Good_subset (hl b hb)) hG).symm⟩

/-- `DisconnectsFromInfty` with a fixed radius `R` -/
def k8DiscR (K Y J : Set ℂ) (R : ℝ) : Prop :=
  ∀ (y x : ℂ) (γ : Path y x), R < ‖y‖ → x ∈ J → range γ ∩ K ⊆ {x} → (range γ ∩ Y).Nonempty

/-- the body of `k8Disc` at `n` implies `DisconnectsFromInfty` with radius `n` -/
theorem k8_discR_of {K J : Set ℂ} (hK : IsClosed K) (hJK : J ⊆ K) {c : ℂ} {a : ℝ} {n : ℕ}
    (hKn : ¬ (K ∩ {z | (n : ℝ) - 1 < ‖z‖}).Nonempty)
    (H : ∀ m : ℕ, ∃ k : ℕ, ∀ q : ℚ × ℚ,
      k8W K c a n (k8Q q) → (J ∩ ball (k8Q q) (1 / ((k : ℝ) + 1))).Nonempty →
        dist (k8Q q) c ≤ a + 1 / ((m : ℝ) + 1)) : k8DiscR K (closedBall c a) J n := by
  intro y x γ hy hx hγK
  by_contra hne
  have hrange : ∀ p ∈ range γ, p ∉ closedBall c a := fun p hp hpc => hne ⟨p, hp, hpc⟩
  have hxc : a < dist x c := by
    have := hrange x ⟨1, γ.target⟩
    simpa [mem_closedBall, not_le] using this
  set η := dist x c - a with hη
  have hη0 : 0 < η := by linarith
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < η / 2 by linarith)
  obtain ⟨k, hk⟩ := H m
  have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  set σ := min (1 / ((k : ℝ) + 1)) η / 4 with hσ
  have hσ0 : 0 < σ := by positivity
  have hxn : ‖x‖ ≤ (n : ℝ) - 1 := by
    by_contra hc; exact hKn ⟨x, hJK hx, by simpa using hc⟩
  -- first hitting time of `x`
  set T : Set ℝ := Icc 0 1 ∩ {t | γ.extend t = x} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_eq γ.continuous_extend continuous_const)
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by simp⟩
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set s₀ := sInf T with hs₀
  have hs₀T : s₀ ∈ T := hTc.csInf_mem ⟨1, h1T⟩ hTb
  have hs₀0 : 0 < s₀ := by
    rcases hs₀T.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have e : γ.extend s₀ = y := by rw [← h]; simp
      rw [hs₀T.2] at e
      rw [← e] at hy; linarith
  have hO : ∀ t ∈ Ico 0 s₀, γ.extend t ∈ (K ∪ closedBall c a)ᶜ := by
    intro t ht
    have hmem : γ.extend t ∈ range γ := by
      rw [← Path.extend_range]; exact ⟨t, rfl⟩
    have hne' : γ.extend t ≠ x := fun he =>
      (not_le.2 ht.2) (csInf_le hTb ⟨⟨ht.1, ht.2.le.trans hs₀T.1.2⟩, he⟩)
    simp only [mem_compl_iff, mem_union, not_or]
    exact ⟨fun hK' => hne' (hγK ⟨hmem, hK'⟩), hrange _ hmem⟩
  obtain ⟨δ', hδ', hδ'c⟩ := Metric.continuous_iff.1 γ.continuous_extend s₀ σ hσ0
  set t := max 0 (s₀ - δ' / 2) with ht
  have htI : t ∈ Ico 0 s₀ := ⟨le_max_left _ _, max_lt hs₀0 (by linarith)⟩
  have hwx : dist (γ.extend t) x < σ := by
    have hx' : γ.extend s₀ = x := hs₀T.2
    have := hδ'c t (by
      rw [Real.dist_eq, abs_lt]
      constructor <;> [skip; linarith [htI.2]]
      linarith [le_max_right 0 (s₀ - δ' / 2)])
    rwa [hx'] at this
  set w := γ.extend t
  have hwO := hO t htI
  simp only [mem_compl_iff, mem_union, not_or, mem_closedBall, not_le] at hwO
  obtain ⟨b, hb, hwb, hbr⟩ := k8_exists_good hK hwO.1 hwO.2 hσ0
  -- the chain from the centre of `b` to `y`
  set S := γ.extend '' Icc 0 t ∪ k8Ball b
  have hSc : IsPreconnected S := by
    refine IsPreconnected.union w ⟨t, ⟨htI.1, le_rfl⟩, rfl⟩ hwb
      (isPreconnected_Icc.image _ γ.continuous_extend.continuousOn) (convex_ball _ _).isPreconnected
  have hcov : ∀ z ∈ S, ∃ b', k8Good K c a b' ∧ z ∈ k8Ball b' := by
    rintro z (⟨u, hu, rfl⟩ | hz)
    · have := hO u ⟨hu.1, hu.2.trans_lt htI.2⟩
      simp only [mem_compl_iff, mem_union, not_or, mem_closedBall, not_le] at this
      obtain ⟨b', hb', hzb', -⟩ := k8_exists_good hK this.1 this.2 one_pos
      exact ⟨b', hb', hzb'⟩
    · exact ⟨b, hb, hz⟩
  have hctr : k8C b ∈ S := Or.inr (mem_ball_self hb.1)
  have hyS : y ∈ S := Or.inl ⟨0, ⟨le_rfl, htI.1⟩, by simp⟩
  obtain ⟨l, hl, hG⟩ := k8_preconn hSc (k8Good K c a) hcov hctr hyS
  have hq : k8Q (b.1, b.2.1) = k8C b := rfl
  have hW : k8W K c a n (k8Q (b.1, b.2.1)) := ⟨l, hl, y, hy, hq ▸ hG⟩
  have hdq : dist (k8C b) w < σ := by
    have := hwb; rw [k8Ball, mem_ball, dist_comm] at this; linarith
  have hqx : dist (k8C b) x < 2 * σ := by linarith [dist_triangle (k8C b) w x]
  have hσk : 2 * σ ≤ 1 / ((k : ℝ) + 1) := by
    have := min_le_left (1 / ((k : ℝ) + 1)) η; rw [hσ]; linarith
  have hση : 2 * σ ≤ η / 2 := by
    have := min_le_right (1 / ((k : ℝ) + 1)) η; rw [hσ]; linarith
  have hJ : (J ∩ ball (k8Q (b.1, b.2.1)) (1 / ((k : ℝ) + 1))).Nonempty :=
    ⟨x, hx, by rw [hq, mem_ball, dist_comm]; linarith⟩
  have h1 := hk _ hW hJ
  rw [hq] at h1
  have := dist_triangle x (k8C b) c
  rw [dist_comm x (k8C b)] at this
  linarith

/-- `k8Disc` implies `DisconnectsFromInfty` (no Jordan hypothesis needed) -/
theorem k8_disc_of {K J : Set ℂ} (hK : IsClosed K) (hJK : J ⊆ K) {c : ℂ} {a : ℝ}
    (h : k8Disc K J c a) : DisconnectsFromInfty K (closedBall c a) J := by
  obtain ⟨n, hKn, H⟩ := h
  exact ⟨n, k8_discR_of hK hJK hKn H⟩

end LQGMetric.CONF
