import LatticeProb.Topology.LocalAgreementChains

/-!
# Gluing along fine chains, pair by pair

`LatticeProb.Topology.LocalAgreementChains` glues two locally agreeing distance functions `d₁, d₂` on a set `D`
from the fine-chain property `HasFineChains D d` at *all* pairs of `D`. The proof of the one-sided bound
`d₂ x y ≤ d₁ x y` uses the chains of `d₁` for the single pair `(x, y)` only. This module records that.

* `HasFineChainsAt D d x y`: the chain approximation for one pair; `HasFineChains D d` is its quantification over
  `x, y ∈ D` (`hasFineChains_iff`).
* `le_of_local_agreement_of_fineChainsAt`: the one-sided bound `d₂ x y ≤ d₁ x y` from chains of `d₁` at `(x, y)`.
* `eqOn_of_local_agreement_of_fineChainsAt`: `d₁ = d₂` on `S × S` when both have fine chains at the pairs of `S`
  (for instance a countable dense set, where the chains can be chosen through a countable family of points).
* `eqOn_of_eqOn_dense`: two functions continuous on `D × D` that agree on `S × S` with `S` dense in `D` agree on
  `D × D`.
-/

open Set Filter Metric Topology
open scoped ENNReal NNReal

namespace LatticeProb.Topology

variable {α : Type*} [PseudoMetricSpace α]

/-- `d` has **fine chains at the pair `(x, y)`** relative to `D`: for every `ε > 0` there is a compact `K ⊆ D`
such that for every mesh `δ > 0` some chain `x = m 0, …, m N = y` in `K` with steps shorter than `δ` has
`∑ d (m i) (m (i + 1)) ≤ d x y + ε`. -/
def HasFineChainsAt (D : Set α) (d : α → α → ℝ≥0∞) (x y : α) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K ⊆ D, IsCompact K ∧ ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∃ m : ℕ → α,
    m 0 = x ∧ m N = y ∧ (∀ i ≤ N, m i ∈ K) ∧ (∀ i < N, dist (m i) (m (i + 1)) < δ) ∧
      ∑ i ∈ Finset.range N, d (m i) (m (i + 1)) ≤ d x y + ε

/-- `HasFineChains D d` is the pairwise property at every pair of `D`. -/
theorem hasFineChains_iff {D : Set α} {d : α → α → ℝ≥0∞} :
    HasFineChains D d ↔ ∀ x ∈ D, ∀ y ∈ D, HasFineChainsAt D d x y := Iff.rfl

/-- **One-sided gluing at a pair.** If `d₂` satisfies the triangle inequality and is symmetric on `D` and tends
to `0` at the root `z ∈ D`, `d₁` has fine chains at `(x, y)`, and `d₁ = d₂` near every point of `D ∖ {z}`, then
`d₂ x y ≤ d₁ x y`. -/
theorem le_of_local_agreement_of_fineChainsAt {D : Set α} {z : α} (hz : z ∈ D) {d₁ d₂ : α → α → ℝ≥0∞}
    (htri₂ : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d₂ x w ≤ d₂ x y + d₂ y w)
    (hsymm₂ : ∀ x ∈ D, ∀ y ∈ D, d₂ x y = d₂ y x)
    (hroot₂ : Tendsto (fun w => d₂ w z) (𝓝[D] z) (𝓝 0))
    (hloc : ∀ q ∈ D, q ≠ z → ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s, d₁ u v = d₂ u v)
    {x y : α} (hch₁ : HasFineChainsAt D d₁ x y) : d₂ x y ≤ d₁ x y := by
  classical
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_
  obtain ⟨ε, hε, hthirds⟩ : ∃ ε : ℝ≥0∞, 0 < ε ∧ ε + ε + ε = ε' :=
    ⟨(ε' : ℝ≥0∞) / 3, ENNReal.div_pos_iff.2 ⟨ENNReal.coe_ne_zero.2 hε'.ne', by norm_num⟩,
      ENNReal.add_thirds _⟩
  -- a root radius
  obtain ⟨θ, hθ, hθε⟩ : ∃ θ > 0, ∀ w ∈ ball z θ, w ∈ D → d₂ w z < ε := by
    obtain ⟨θ, hθ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (hroot₂.eventually (Iio_mem_nhds hε))
    exact ⟨θ, hθ, fun w hw hwD => hsub ⟨hw, hwD⟩⟩
  obtain ⟨K, hKD, hKc, hK⟩ := hch₁ ε hε
  -- a Lebesgue number for the balls of local agreement covering `K ∖ B(z, θ)`
  have hK'c : IsCompact (K ∩ (ball z θ)ᶜ) := hKc.inter_right isOpen_ball.isClosed_compl
  have hloc' : ∀ q : ↥(K ∩ (ball z θ)ᶜ), ∃ s > 0,
      ∀ u ∈ ball (q : α) s, ∀ v ∈ ball (q : α) s, d₁ u v = d₂ u v := by
    rintro ⟨q, hqK, hqz⟩
    refine hloc q (hKD hqK) ?_
    rintro rfl
    exact hqz (mem_ball_self hθ)
  choose s hs hagree using hloc'
  obtain ⟨η, hη, hleb⟩ := lebesgue_number_lemma_of_metric hK'c
    (c := fun q : ↥(K ∩ (ball z θ)ᶜ) => ball (q : α) (s q)) (fun q => isOpen_ball)
    (fun q hq => mem_iUnion.2 ⟨⟨q, hq⟩, mem_ball_self (hs _)⟩)
  have agree : ∀ u ∈ K ∩ (ball z θ)ᶜ, ∀ v w, dist v u < η → dist w u < η → d₁ v w = d₂ v w := by
    intro u hu v w hv hw
    obtain ⟨q, hq⟩ := hleb u hu
    exact hagree q v (hq hv) w (hq hw)
  obtain ⟨N, m, hm0, hmN, hmK, hmδ, hmsum⟩ := hK η hη
  have hmD : ∀ i ≤ N, m i ∈ D := fun i hi => hKD (hmK i hi)
  have hη0 : ∀ u : α, dist u u < η := fun u => by simpa using hη
  have hterm_left : ∀ i < N, m i ∉ ball z θ → d₂ (m i) (m (i + 1)) = d₁ (m i) (m (i + 1)) := by
    intro i hi hout
    refine (agree (m i) ⟨hmK i hi.le, hout⟩ (m i) (m (i + 1)) (hη0 _) ?_).symm
    rw [dist_comm]
    exact hmδ i hi
  have hterm_right : ∀ i < N, m (i + 1) ∉ ball z θ →
      d₂ (m i) (m (i + 1)) = d₁ (m i) (m (i + 1)) := fun i hi hout =>
    (agree (m (i + 1)) ⟨hmK (i + 1) (Nat.succ_le_of_lt hi), hout⟩ (m i) (m (i + 1)) (hmδ i hi)
      (hη0 _)).symm
  by_cases hin : ∃ i, i ≤ N ∧ m i ∈ ball z θ
  · -- the chain visits the root ball: replace its middle part by two short legs to the root
    obtain ⟨i₁, hi₁N, hi₁, hbefore⟩ : ∃ i₁, i₁ ≤ N ∧ m i₁ ∈ ball z θ ∧ ∀ i < i₁, m i ∉ ball z θ :=
      ⟨Nat.find hin, (Nat.find_spec hin).1, (Nat.find_spec hin).2, fun i hi hmi =>
        Nat.find_min hin hi ⟨hi.le.trans (Nat.find_spec hin).1, hmi⟩⟩
    obtain ⟨i₂, hi₂N, hi₂, hi₁₂, hafter⟩ : ∃ i₂, i₂ ≤ N ∧ m i₂ ∈ ball z θ ∧ i₁ ≤ i₂ ∧
        ∀ i, i₂ < i → i ≤ N → m i ∉ ball z θ :=
      ⟨Nat.findGreatest (fun i => m i ∈ ball z θ) N, Nat.findGreatest_le N,
        Nat.findGreatest_spec (P := fun i => m i ∈ ball z θ) hi₁N hi₁,
        Nat.le_findGreatest (P := fun i => m i ∈ ball z θ) hi₁N hi₁,
        fun i hi hiN => Nat.findGreatest_is_greatest hi hiN⟩
    have hS₁ : ∑ i ∈ Finset.Ico 0 i₁, d₂ (m i) (m (i + 1)) =
        ∑ i ∈ Finset.Ico 0 i₁, d₁ (m i) (m (i + 1)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := (Finset.mem_Ico.1 hi).2
      exact hterm_left i (by omega) (hbefore i hi')
    have hS₂ : ∑ i ∈ Finset.Ico i₂ N, d₂ (m i) (m (i + 1)) =
        ∑ i ∈ Finset.Ico i₂ N, d₁ (m i) (m (i + 1)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
      exact hterm_right i hi2 (hafter (i + 1) (by omega) (by omega))
    have hleg₁ : d₂ (m i₁) z < ε := hθε _ hi₁ (hmD i₁ hi₁N)
    have hleg₂ : d₂ z (m i₂) < ε := by
      rw [hsymm₂ z hz _ (hmD i₂ hi₂N)]
      exact hθε _ hi₂ (hmD i₂ hi₂N)
    have hsplit : ∑ i ∈ Finset.Ico 0 i₁, d₁ (m i) (m (i + 1)) +
        ∑ i ∈ Finset.Ico i₂ N, d₁ (m i) (m (i + 1)) ≤ ∑ i ∈ Finset.range N, d₁ (m i) (m (i + 1)) := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le i₁) (hi₁₂.trans hi₂N),
        ← Finset.sum_Ico_consecutive _ hi₁₂ hi₂N, ← add_assoc]
      exact add_le_add le_self_add le_rfl
    calc d₂ x y = d₂ (m 0) (m N) := by rw [hm0, hmN]
      _ ≤ d₂ (m 0) z + d₂ z (m N) := htri₂ _ (hmD 0 (Nat.zero_le N)) _ hz _ (hmD N le_rfl)
      _ ≤ (∑ i ∈ Finset.Ico 0 i₁, d₂ (m i) (m (i + 1)) + d₂ (m i₁) z) +
          (d₂ z (m i₂) + ∑ i ∈ Finset.Ico i₂ N, d₂ (m i) (m (i + 1))) :=
        add_le_add (le_sum_add_of_chain htri₂ hmD hz (Nat.zero_le i₁) hi₁N)
          (le_add_sum_of_chain htri₂ hmD hz hi₂N le_rfl)
      _ ≤ (∑ i ∈ Finset.Ico 0 i₁, d₁ (m i) (m (i + 1)) + ε) +
          (ε + ∑ i ∈ Finset.Ico i₂ N, d₁ (m i) (m (i + 1))) := by
        rw [hS₁, hS₂]
        exact add_le_add (add_le_add le_rfl hleg₁.le) (add_le_add hleg₂.le le_rfl)
      _ = (∑ i ∈ Finset.Ico 0 i₁, d₁ (m i) (m (i + 1)) +
          ∑ i ∈ Finset.Ico i₂ N, d₁ (m i) (m (i + 1))) + (ε + ε) := by ring
      _ ≤ (d₁ x y + ε) + (ε + ε) := add_le_add (hsplit.trans hmsum) le_rfl
      _ = d₁ x y + ε' := by rw [← hthirds]; ring
  · -- the chain avoids the root ball: every step agrees
    simp only [not_exists, not_and] at hin
    have hS : ∑ i ∈ Finset.range N, d₂ (m i) (m (i + 1)) =
        ∑ i ∈ Finset.range N, d₁ (m i) (m (i + 1)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      exact hterm_left i hi' (hin i hi'.le)
    have hεε' : ε ≤ (ε' : ℝ≥0∞) := by
      rw [← hthirds]
      exact le_add_self
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have h0 : d₂ (m 0) (m 0) = d₁ (m 0) (m 0) :=
        (agree (m 0) ⟨hmK 0 le_rfl, hin 0 le_rfl⟩ (m 0) (m 0) (hη0 _) (hη0 _)).symm
      calc d₂ x y = d₁ x y := by rw [← hm0, ← hmN, h0]
        _ ≤ d₁ x y + ε' := le_self_add
    · calc d₂ x y = d₂ (m 0) (m N) := by rw [hm0, hmN]
        _ ≤ ∑ i ∈ Finset.Ico 0 N, d₂ (m i) (m (i + 1)) := le_sum_of_chain htri₂ hmD hN le_rfl
        _ = ∑ i ∈ Finset.range N, d₁ (m i) (m (i + 1)) := by rw [← Finset.range_eq_Ico, hS]
        _ ≤ d₁ x y + ε := hmsum
        _ ≤ d₁ x y + ε' := add_le_add le_rfl hεε'

/-- **Gluing along fine chains on a subset.** Two functions `d₁, d₂` that satisfy the triangle inequality and
are symmetric on `D`, tend to `0` at a root `z ∈ D`, agree near every point of `D ∖ {z}`, and have fine chains at
every pair of `S × S`, agree on `S × S`. -/
theorem eqOn_of_local_agreement_of_fineChainsAt {D S : Set α} {z : α} (hz : z ∈ D)
    {d₁ d₂ : α → α → ℝ≥0∞}
    (htri₁ : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d₁ x w ≤ d₁ x y + d₁ y w)
    (htri₂ : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d₂ x w ≤ d₂ x y + d₂ y w)
    (hsymm₁ : ∀ x ∈ D, ∀ y ∈ D, d₁ x y = d₁ y x) (hsymm₂ : ∀ x ∈ D, ∀ y ∈ D, d₂ x y = d₂ y x)
    (hroot₁ : Tendsto (fun w => d₁ w z) (𝓝[D] z) (𝓝 0))
    (hroot₂ : Tendsto (fun w => d₂ w z) (𝓝[D] z) (𝓝 0))
    (hch₁ : ∀ x ∈ S, ∀ y ∈ S, HasFineChainsAt D d₁ x y)
    (hch₂ : ∀ x ∈ S, ∀ y ∈ S, HasFineChainsAt D d₂ x y)
    (hloc : ∀ q ∈ D, q ≠ z → ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s, d₁ u v = d₂ u v) :
    ∀ x ∈ S, ∀ y ∈ S, d₁ x y = d₂ x y := fun _ hx _ hy =>
  le_antisymm
    (le_of_local_agreement_of_fineChainsAt hz htri₁ hsymm₁ hroot₁
      (fun q hq hqz => (hloc q hq hqz).imp fun _ ⟨hs, h⟩ => ⟨hs, fun u hu v hv => (h u hu v hv).symm⟩)
      (hch₂ _ hx _ hy))
    (le_of_local_agreement_of_fineChainsAt hz htri₂ hsymm₂ hroot₂ hloc (hch₁ _ hx _ hy))

/-- Two functions that are continuous on `D × D` and agree on `S × S`, with `S ⊆ D ⊆ closure S`, agree on
`D × D`. -/
theorem eqOn_of_eqOn_dense {D S : Set α} (hSD : S ⊆ D) (hdense : D ⊆ closure S) {d₁ d₂ : α → α → ℝ≥0∞}
    (h₁ : ContinuousOn (fun p : α × α => d₁ p.1 p.2) (D ×ˢ D))
    (h₂ : ContinuousOn (fun p : α × α => d₂ p.1 p.2) (D ×ˢ D))
    (heq : ∀ x ∈ S, ∀ y ∈ S, d₁ x y = d₂ x y) : ∀ x ∈ D, ∀ y ∈ D, d₁ x y = d₂ x y := by
  have hS : Set.EqOn (fun p : α × α => d₁ p.1 p.2) (fun p : α × α => d₂ p.1 p.2) (S ×ˢ S) :=
    fun p hp => heq p.1 hp.1 p.2 hp.2
  have hcl : D ×ˢ D ⊆ closure (S ×ˢ S) := by
    rw [closure_prod_eq]
    exact prod_mono hdense hdense
  exact fun x hx y hy => hS.of_subset_closure h₁ h₂ (prod_mono hSD hSD) hcl (mk_mem_prod hx hy)

end LatticeProb.Topology
