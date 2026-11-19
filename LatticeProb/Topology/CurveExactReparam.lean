import LatticeProb.Topology.CurveSpace

/-! # Exact reparametrization of pause-free curves at Fréchet distance zero

Two continuous curves on `[0,1]` that are nonconstant on every nondegenerate subinterval and are
approximated arbitrarily well in the supremum norm by increasing homeomorphic time changes of one
another are exact increasing reparametrizations of each other.  The proof takes a cluster point
`ψ` (in the product topology of `[0,1]^[0,1]`) of near-optimal time changes.  It is monotone and
satisfies `F = G ∘ ψ`; strict monotonicity comes from pause-freeness of `F`, and surjectivity,
which excludes jumps of `ψ`, from pause-freeness of `G`. -/

set_option autoImplicit false

open Filter Topology
open scoped unitInterval

namespace LatticeProb

/-- A function on `[0,1]` is pause-free if it is nonconstant on every nondegenerate subinterval. -/
def NoPause {X : Type*} (F : unitInterval → X) : Prop :=
  ∀ s t : unitInterval, s < t → ∃ u ∈ Set.Icc s t, F u ≠ F s

theorem exists_orderIso_of_approx {X : Type*} [MetricSpace X] {F G : unitInterval → X}
    (hFc : Continuous F) (hGc : Continuous G) (hF : NoPause F) (hG : NoPause G)
    (h : ∀ ε : ℝ, 0 < ε → ∃ e : unitInterval ≃o unitInterval, ∀ t, dist (F t) (G (e t)) < ε) :
    ∃ e : unitInterval ≃o unitInterval, ∀ s, F s = G (e s) := by
  choose e he using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨ψ, hψ⟩ := exists_clusterPt_of_compactSpace
    (Filter.map (fun n : ℕ => (⇑(e n) : unitInterval → unitInterval)) Filter.atTop)
  have hψ' : MapClusterPt ψ Filter.atTop
      (fun n : ℕ => (⇑(e n) : unitInterval → unitInterval)) := hψ
  have CP : ∀ (S : Finset unitInterval) (δ : ℝ), 0 < δ → ∀ N : ℕ,
      ∃ n, N ≤ n ∧ ∀ s ∈ S, dist (e n s) (ψ s) < δ := by
    intro S δ hδ N
    have hV : IsOpen {g : unitInterval → unitInterval | ∀ s ∈ S, dist (g s) (ψ s) < δ} := by
      have : {g : unitInterval → unitInterval | ∀ s ∈ S, dist (g s) (ψ s) < δ} =
          ⋂ s ∈ S, (fun g : unitInterval → unitInterval => g s) ⁻¹' Metric.ball (ψ s) δ := by
        ext g; simp [Metric.mem_ball]
      rw [this]
      exact isOpen_biInter_finset fun s _ => Metric.isOpen_ball.preimage (continuous_apply s)
    have hmem : ∀ᶠ g in 𝓝 ψ,
        g ∈ {g : unitInterval → unitInterval | ∀ s ∈ S, dist (g s) (ψ s) < δ} :=
      hV.mem_nhds (fun s _ => by simpa using hδ)
    obtain ⟨n, hn, hnN⟩ :=
      ((hψ'.frequently hmem).and_eventually (Filter.eventually_ge_atTop N)).exists
    exact ⟨n, hnN, hn⟩
  have small : ∀ (S : Finset unitInterval) (δ ε : ℝ), 0 < δ → 0 < ε →
      ∃ n : ℕ, 1 / ((n : ℝ) + 1) < ε ∧ ∀ s ∈ S, dist (e n s) (ψ s) < δ := by
    intro S δ ε hδ hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    obtain ⟨n, hn, h⟩ := CP S δ hδ N
    refine ⟨n, lt_of_le_of_lt ?_ hN, h⟩
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hFu := Metric.uniformContinuous_iff.1 (CompactSpace.uniformContinuous_of_continuous hFc)
  have hGu := Metric.uniformContinuous_iff.1 (CompactSpace.uniformContinuous_of_continuous hGc)
  have hd : ∀ (a b : unitInterval) (δ : ℝ), dist a b < δ → (a : ℝ) < b + δ ∧ (b : ℝ) < a + δ := by
    intro a b δ h
    rw [Subtype.dist_eq, Real.dist_eq, abs_lt] at h
    constructor <;> linarith [h.1, h.2]
  have shrink : ∀ (a : unitInterval) (η : ℝ), 0 < η → 0 < a →
      ∃ b : unitInterval, b < a ∧ (a : ℝ) < b + η := by
    intro a η hη ha
    have ha' : (0 : ℝ) < a := ha
    refine ⟨⟨max 0 ((a : ℝ) - η / 2), le_max_left _ _,
      max_le zero_le_one (by linarith [a.2.2])⟩, ?_, ?_⟩
    · show max 0 ((a : ℝ) - η / 2) < a
      exact max_lt ha' (by linarith)
    · show (a : ℝ) < max 0 ((a : ℝ) - η / 2) + η
      linarith [le_max_right 0 ((a : ℝ) - η / 2)]
  have grow : ∀ (a : unitInterval) (η : ℝ), 0 < η → a < 1 →
      ∃ b : unitInterval, a < b ∧ (b : ℝ) < a + η := by
    intro a η hη ha
    have ha' : (a : ℝ) < 1 := ha
    refine ⟨⟨min 1 ((a : ℝ) + η / 2), le_min zero_le_one (by linarith [a.2.1]),
      min_le_left _ _⟩, ?_, ?_⟩
    · show (a : ℝ) < min 1 ((a : ℝ) + η / 2)
      exact lt_min ha' (by linarith)
    · show min 1 ((a : ℝ) + η / 2) < a + η
      linarith [min_le_right 1 ((a : ℝ) + η / 2)]
  have hb : ∀ s, F s = G (ψ s) := by
    intro s
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨η, hη, hηG⟩ := hGu (ε / 2) (by positivity)
    obtain ⟨n, hn, hdist⟩ := small {s} η (ε / 2) hη (by positivity)
    have h1 := he n s
    have h2 := hηG (hdist s (Finset.mem_singleton_self s))
    calc dist (F s) (G (ψ s)) ≤ dist (F s) (G (e n s)) + dist (G (e n s)) (G (ψ s)) :=
          dist_triangle _ _ _
      _ ≤ ε := by linarith
  have hmono : Monotone ψ := by
    intro s t hst
    by_contra hlt
    have hlt' : (ψ t : ℝ) < ψ s := Subtype.coe_lt_coe.2 (not_le.1 hlt)
    obtain ⟨n, -, hn⟩ := small {s, t} (((ψ s : ℝ) - ψ t) / 3) 1 (by linarith) one_pos
    have h1 := hd _ _ _ (hn s (by simp))
    have h2 := hd _ _ _ (hn t (by simp))
    have h3 : (e n s : ℝ) ≤ e n t := Subtype.coe_le_coe.2 ((e n).monotone hst)
    linarith [h1.1, h1.2, h2.1, h2.2]
  have h0 : ψ 0 = 0 := by
    refine eq_of_forall_dist_le fun δ hδ => ?_
    obtain ⟨n, -, hn⟩ := small {0} δ 1 hδ one_pos
    have := hn 0 (Finset.mem_singleton_self _)
    rw [show e n 0 = 0 from map_bot (e n), dist_comm] at this
    exact this.le
  have h1 : ψ 1 = 1 := by
    refine eq_of_forall_dist_le fun δ hδ => ?_
    obtain ⟨n, -, hn⟩ := small {1} δ 1 hδ one_pos
    have := hn 1 (Finset.mem_singleton_self _)
    rw [show e n 1 = 1 from map_top (e n), dist_comm] at this
    exact this.le
  have hstrict : StrictMono ψ := by
    intro s t hst
    refine lt_of_le_of_ne (hmono hst.le) fun heq => ?_
    obtain ⟨u, hu, hne⟩ := hF s t hst
    apply hne
    have : ψ u = ψ s := le_antisymm ((hmono hu.2).trans heq.ge) (hmono hu.1)
    rw [hb u, hb s, this]
  have hsurj : Function.Surjective ψ := by
    intro v
    set A : Set unitInterval := {s | ψ s ≤ v} with hA
    set s0 := sSup A with hs0
    have hlt_s0 : ∀ s, s < s0 → ψ s ≤ v := by
      intro s hs
      obtain ⟨a, ha, hsa⟩ := lt_sSup_iff.1 hs
      exact (hmono hsa.le).trans ha
    have hgt_s0 : ∀ s, s0 < s → v < ψ s := by
      intro s hs
      by_contra hle
      exact absurd hs (not_lt.2 (le_sSup (not_lt.1 hle)))
    rcases lt_trichotomy (ψ s0) v with hlt | heq | hgt
    · exfalso
      have hs01 : s0 < 1 := by
        refine lt_of_le_of_ne unitInterval.le_one' fun h => ?_
        rw [h, h1] at hlt
        exact absurd hlt (not_lt.2 unitInterval.le_one')
      have jumpR : ∀ w : unitInterval, ψ s0 < w → w < v → G w = F s0 := by
        intro w hw1 hw2
        refine eq_of_forall_dist_le fun ε hε => ?_
        obtain ⟨η, hη, hηF⟩ := hFu (ε / 2) (by positivity)
        obtain ⟨s2, hs02, hs2η⟩ := grow s0 η hη hs01
        have hw1' : (ψ s0 : ℝ) < w := hw1
        have hw2' : (w : ℝ) < v := hw2
        have hdpos : 0 < min ((w : ℝ) - ψ s0) ((v : ℝ) - w) / 2 := by
          have := lt_min (sub_pos.2 hw1') (sub_pos.2 hw2')
          linarith
        have hdle1 : min ((w : ℝ) - ψ s0) ((v : ℝ) - w) / 2 ≤ ((w : ℝ) - ψ s0) / 2 := by
          linarith [min_le_left ((w : ℝ) - ψ s0) ((v : ℝ) - w)]
        have hdle2 : min ((w : ℝ) - ψ s0) ((v : ℝ) - w) / 2 ≤ ((v : ℝ) - w) / 2 := by
          linarith [min_le_right ((w : ℝ) - ψ s0) ((v : ℝ) - w)]
        obtain ⟨n, hn, hn2⟩ := small {s0, s2}
          (min ((w : ℝ) - ψ s0) ((v : ℝ) - w) / 2) (ε / 2) hdpos (by positivity)
        have e1 := hd _ _ _ (hn2 s0 (by simp))
        have e2 := hd _ _ _ (hn2 s2 (by simp))
        have hv2 : (v : ℝ) < ψ s2 := hgt_s0 s2 hs02
        have hlt1 : e n s0 < w := by
          have : (e n s0 : ℝ) < w := by linarith [e1.1]
          exact this
        have hlt2 : w < e n s2 := by
          have : (w : ℝ) < e n s2 := by linarith [e2.2]
          exact this
        set t := (e n).symm w with ht'
        have ht : e n t = w := (e n).apply_symm_apply w
        have hts0 : s0 < t := (e n).lt_iff_lt.1 (ht ▸ hlt1)
        have hts2 : t < s2 := (e n).lt_iff_lt.1 (ht ▸ hlt2)
        have hts0' : (s0 : ℝ) < t := hts0
        have hts2' : (t : ℝ) < s2 := hts2
        have hdt : dist t s0 < η := by
          rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
          constructor <;> linarith
        have h3 := hηF hdt
        have h4 := he n t
        rw [ht] at h4
        calc dist (G w) (F s0) ≤ dist (G w) (F t) + dist (F t) (F s0) := dist_triangle _ _ _
          _ ≤ ε := by rw [dist_comm (G w) (F t)]; linarith
      obtain ⟨w1, hw1, hw1v⟩ := exists_between hlt
      obtain ⟨u, hu, hne⟩ := hG (ψ s0) w1 hw1
      apply hne
      rcases eq_or_lt_of_le hu.1 with hu0 | hu0
      · rw [← hu0]
      · exact jumpR u hu0 (lt_of_le_of_lt hu.2 hw1v) |>.trans (hb s0 ▸ rfl)
    · exact ⟨s0, heq⟩
    · exfalso
      have hs0pos : 0 < s0 := by
        refine lt_of_le_of_ne unitInterval.nonneg' fun h => ?_
        rw [← h, h0] at hgt
        exact absurd hgt (not_lt.2 unitInterval.nonneg')
      have jumpL : ∀ w : unitInterval, v < w → w < ψ s0 → G w = F s0 := by
        intro w hw1 hw2
        refine eq_of_forall_dist_le fun ε hε => ?_
        obtain ⟨η, hη, hηF⟩ := hFu (ε / 2) (by positivity)
        obtain ⟨s1, hs1, hs1η⟩ := shrink s0 η hη hs0pos
        have hw1' : (v : ℝ) < w := hw1
        have hw2' : (w : ℝ) < ψ s0 := hw2
        have hdpos : 0 < min ((w : ℝ) - v) ((ψ s0 : ℝ) - w) / 2 := by
          have := lt_min (sub_pos.2 hw1') (sub_pos.2 hw2')
          linarith
        have hdle1 : min ((w : ℝ) - v) ((ψ s0 : ℝ) - w) / 2 ≤ ((w : ℝ) - v) / 2 := by
          linarith [min_le_left ((w : ℝ) - v) ((ψ s0 : ℝ) - w)]
        have hdle2 : min ((w : ℝ) - v) ((ψ s0 : ℝ) - w) / 2 ≤ ((ψ s0 : ℝ) - w) / 2 := by
          linarith [min_le_right ((w : ℝ) - v) ((ψ s0 : ℝ) - w)]
        obtain ⟨n, hn, hn2⟩ := small {s1, s0}
          (min ((w : ℝ) - v) ((ψ s0 : ℝ) - w) / 2) (ε / 2) hdpos (by positivity)
        have e1 := hd _ _ _ (hn2 s1 (by simp))
        have e2 := hd _ _ _ (hn2 s0 (by simp))
        have hv1 : (ψ s1 : ℝ) ≤ v := hlt_s0 s1 hs1
        have hlt1 : e n s1 < w := by
          have : (e n s1 : ℝ) < w := by linarith [e1.1]
          exact this
        have hlt2 : w < e n s0 := by
          have : (w : ℝ) < e n s0 := by linarith [e2.2]
          exact this
        set t := (e n).symm w with ht'
        have ht : e n t = w := (e n).apply_symm_apply w
        have hts1 : s1 < t := (e n).lt_iff_lt.1 (ht ▸ hlt1)
        have hts0 : t < s0 := (e n).lt_iff_lt.1 (ht ▸ hlt2)
        have hts1' : (s1 : ℝ) < t := hts1
        have hts0' : (t : ℝ) < s0 := hts0
        have hdt : dist t s0 < η := by
          rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
          constructor <;> linarith
        have h3 := hηF hdt
        have h4 := he n t
        rw [ht] at h4
        calc dist (G w) (F s0) ≤ dist (G w) (F t) + dist (F t) (F s0) := dist_triangle _ _ _
          _ ≤ ε := by rw [dist_comm (G w) (F t)]; linarith
      obtain ⟨w1, hw1, hw1v⟩ := exists_between hgt
      obtain ⟨u, hu, hne⟩ := hG w1 (ψ s0) hw1v
      apply hne
      have hGw1 : G w1 = F s0 := jumpL w1 hw1 hw1v
      rw [hGw1]
      rcases eq_or_lt_of_le hu.2 with hu0 | hu0
      · rw [hu0, ← hb s0]
      · exact jumpL u (lt_of_lt_of_le hw1 hu.1) hu0
  exact ⟨StrictMono.orderIsoOfSurjective ψ hstrict hsurj, fun s => hb s⟩

namespace NormalizedCurve

/-- Two pause-free normalized curves at Fréchet distance zero are exact increasing
reparametrizations of each other. -/
theorem exists_orderIso_of_frechetEDist_eq_zero {d : ℕ} (F G : NormalizedCurve d)
    (hF : NoPause F.path) (hG : NoPause G.path) (h0 : frechetEDist F G = 0) :
    ∃ e : TimeChange, ∀ s, F.path s = G.path (e s) := by
  refine exists_orderIso_of_approx F.path.continuous G.path.continuous hF hG fun ε hε => ?_
  have hlt : ⨅ e : TimeChange, timeChangeCost F G e < ENNReal.ofReal ε := by
    change frechetEDist F G < _
    rw [h0]
    exact ENNReal.ofReal_pos.2 hε
  obtain ⟨e, he⟩ := iInf_lt_iff.1 hlt
  refine ⟨e, fun t => ?_⟩
  exact edist_lt_ofReal.1
    (lt_of_le_of_lt (le_iSup (fun s => edist (F.path s) (G.path (e s))) t) he)

end NormalizedCurve

end LatticeProb
