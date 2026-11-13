import Mathlib.Topology.MetricSpace.Thickening
import LatticeProb.Topology.LocalAgreementChainsAt

/-!
# Fine chains through a dense subset

`HasFineChainsAt D d x y` allows chains with arbitrary points of `D`. If `d` is continuous on `D × D` and `S` is a
dense subset of the open set `D`, the intermediate points of a chain can be moved into `S`, at the price of an
arbitrarily small error in the sum, while the endpoints `x, y ∈ S` stay fixed, the steps stay below the mesh, and the
points stay in a compact window.

* `exists_chain_through_dense`: for `x, y ∈ S`, `ε > 0` there is an index `n` such that for every mesh `δ > 0` there is
  a chain `x = m 0, …, m N = y` of points of `S` in the `n`-th window `K n` with steps shorter than `δ` and
  `∑ d (m i) (m (i + 1)) ≤ d x y + ε`. Here `K` is an exhaustion of `D` by sets such that every compact subset of `D`
  lies in some `K n`.
-/

open Set Filter Metric Topology
open scoped ENNReal NNReal

namespace LatticeProb.Topology

variable {α : Type*} [PseudoMetricSpace α] [ProperSpace α]

/-- **Fine chains through a dense subset.** Let `D` be open, `S ⊆ D` dense in `D`, `d` continuous on `D × D`
(with values in `ℝ≥0∞`), and `K n` sets such that every compact subset of `D` lies in some `K n`. If `d` has fine
chains at `(x, y)` relative to `D` with `x, y ∈ S`, then for every `ε > 0` there is an `n` such that for every mesh
`δ > 0` there is a chain of points of `S` in `K n` from `x` to `y` with steps shorter than `δ` and
`∑ d (m i) (m (i + 1)) ≤ d x y + ε`. -/
theorem exists_chain_through_dense {D S : Set α} (hD : IsOpen D) (hSD : S ⊆ D) (hdense : D ⊆ closure S)
    {d : α → α → ℝ≥0∞} (hcont : ContinuousOn (fun q : α × α => d q.1 q.2) (D ×ˢ D))
    {K : ℕ → Set α} (hK : ∀ C : Set α, IsCompact C → C ⊆ D → ∃ n, C ⊆ K n)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hch : HasFineChainsAt D d x y) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∃ m : ℕ → α, m 0 = x ∧ m N = y ∧
      (∀ i ≤ N, m i ∈ S ∧ m i ∈ K n) ∧ (∀ i < N, dist (m i) (m (i + 1)) < δ) ∧
      ∑ i ∈ Finset.range N, d (m i) (m (i + 1)) ≤ d x y + ENNReal.ofReal ε := by
  classical
  have : Nonempty α := ⟨x⟩
  obtain ⟨K₀, hK₀D, hK₀c, hK₀⟩ := hch (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.2 (by linarith))
  obtain ⟨r, hr, hrD⟩ := IsCompact.exists_cthickening_subset_open hK₀c hD hK₀D
  obtain ⟨n, hn⟩ := hK _ (IsCompact.cthickening (r := r) hK₀c) hrD
  refine ⟨n, fun δ hδ => ?_⟩
  obtain ⟨N, m, hm0, hmN, hmK, hmδ, hmsum⟩ := hK₀ (δ / 2) (by linarith)
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (ε / (2 * ((N : ℝ) + 1))) with hc
  have hcpos : 0 < c := ENNReal.ofReal_pos.2 (div_pos hε (by positivity))
  -- continuity radii for the pairs `(m j, m (j + 1))`
  have hρ : ∀ j : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ (j < N → ∀ a' ∈ D, ∀ b' ∈ D, dist a' (m j) < ρ →
      dist b' (m (j + 1)) < ρ → d a' b' ≤ d (m j) (m (j + 1)) + c) := by
    intro j
    by_cases hj : j < N
    · by_cases htop : d (m j) (m (j + 1)) = ⊤
      · exact ⟨1, one_pos, fun _ a' _ b' _ _ _ => by simp [htop]⟩
      · have haD : m j ∈ D := hK₀D (hmK j hj.le)
        have hbD : m (j + 1) ∈ D := hK₀D (hmK (j + 1) hj)
        have hlt : d (m j) (m (j + 1)) < d (m j) (m (j + 1)) + c := ENNReal.lt_add_right htop hcpos.ne'
        have hev := (hcont (m j, m (j + 1)) ⟨haD, hbD⟩).eventually (gt_mem_nhds hlt)
        obtain ⟨ρ, hρ0, hρ⟩ := Metric.mem_nhdsWithin_iff.1 hev
        refine ⟨ρ, hρ0, fun _ a' ha' b' hb' h1 h2 => ?_⟩
        have hmem : (a', b') ∈ ball (m j, m (j + 1)) ρ ∩ (D ×ˢ D) := by
          refine ⟨?_, ha', hb'⟩
          rw [mem_ball, Prod.dist_eq]
          exact max_lt h1 h2
        exact (hρ hmem).le
    · exact ⟨1, one_pos, fun h => absurd h hj⟩
  choose ρ hρ0 hρc using hρ
  -- perturbation of the points of the chain into `S`
  have hp : ∀ i : ℕ, i ≤ N → ∃ p ∈ S, dist p (m i) < min (min r (δ / 4)) (min (ρ i) (ρ (i - 1))) ∧
      (i = 0 → p = x) ∧ (i = N → p = y) := by
    intro i hi
    have hpos : 0 < min (min r (δ / 4)) (min (ρ i) (ρ (i - 1))) :=
      lt_min (lt_min hr (by linarith)) (lt_min (hρ0 _) (hρ0 _))
    by_cases h0 : i = 0
    · refine ⟨x, hx, ?_, fun _ => rfl, fun hN => ?_⟩
      · have h00 : dist x (m i) = 0 := by rw [h0, hm0, dist_self]
        rw [h00]
        exact hpos
      · rw [← hmN, ← hN, h0, hm0]
    · by_cases hN : i = N
      · refine ⟨y, hy, ?_, fun h => absurd h h0, fun _ => rfl⟩
        have h00 : dist y (m i) = 0 := by rw [hN, hmN, dist_self]
        rw [h00]
        exact hpos
      · obtain ⟨p, hpS, hpd⟩ := Metric.mem_closure_iff.1 (hdense (hK₀D (hmK i hi))) _ hpos
        exact ⟨p, hpS, by rwa [dist_comm], fun h => absurd h h0, fun h => absurd h hN⟩
  choose! p hpS hpd hp0 hpN using hp
  refine ⟨N, p, hp0 0 (Nat.zero_le _) rfl, hpN N le_rfl rfl, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨hpS i hi, hn ?_⟩
    refine Metric.mem_cthickening_of_dist_le (p i) (m i) r K₀ (hmK i hi) ?_
    exact ((hpd i hi).trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  · intro i hi
    have h1 : dist (p i) (m i) < δ / 4 :=
      (hpd i hi.le).trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have h2 : dist (p (i + 1)) (m (i + 1)) < δ / 4 :=
      (hpd (i + 1) hi).trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have h3 := hmδ i hi
    calc dist (p i) (p (i + 1)) ≤ dist (p i) (m i) + dist (m i) (m (i + 1)) + dist (m (i + 1)) (p (i + 1)) :=
          dist_triangle4 _ _ _ _
      _ < δ := by rw [dist_comm (m (i + 1)) (p (i + 1))]; linarith
  · have hstep : ∀ i ∈ Finset.range N, d (p i) (p (i + 1)) ≤ d (m i) (m (i + 1)) + c := by
      intro i hiN
      have hi : i < N := Finset.mem_range.1 hiN
      have e1 : dist (p i) (m i) < ρ i :=
        (hpd i hi.le).trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have e2 : dist (p (i + 1)) (m (i + 1)) < ρ i := by
        have := (hpd (i + 1) hi).trans_le ((min_le_right _ _).trans (min_le_right _ _))
        simpa using this
      exact hρc i hi (p i) (hSD (hpS i hi.le)) (p (i + 1)) (hSD (hpS (i + 1) hi)) e1 e2
    have hNc : (N : ℝ≥0∞) * c ≤ ENNReal.ofReal (ε / 2) := by
      rw [← ENNReal.ofReal_natCast, hc, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      apply ENNReal.ofReal_le_ofReal
      have h2 : (N : ℝ) * (ε / (2 * ((N : ℝ) + 1))) = ε / 2 * ((N : ℝ) / ((N : ℝ) + 1)) := by
        field_simp
      rw [h2]
      have h1 : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by rw [div_le_one hN1]; linarith
      exact mul_le_of_le_one_right (by linarith) h1
    calc ∑ i ∈ Finset.range N, d (p i) (p (i + 1))
        ≤ ∑ i ∈ Finset.range N, (d (m i) (m (i + 1)) + c) := Finset.sum_le_sum hstep
      _ = ∑ i ∈ Finset.range N, d (m i) (m (i + 1)) + (N : ℝ≥0∞) * c := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (d x y + ENNReal.ofReal (ε / 2)) + ENNReal.ofReal (ε / 2) := add_le_add hmsum hNc
      _ = d x y + ENNReal.ofReal ε := by
          rw [add_assoc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 2
          ring

end LatticeProb.Topology
