import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Gluing locally agreeing distance functions along fine chains

Let `D` be a set in a pseudometric space and `d₁, d₂ : α → α → ℝ≥0∞` two distance-like functions on `D`. Suppose
that they agree near every point of `D` other than one root point `z ∈ D`, that both satisfy the triangle inequality
on `D`, are symmetric on `D`, and tend to `0` at the root (`d w z → 0` as `w → z` in `D`), and that distances can
be approximated by sums along *fine chains*: for `x, y ∈ D` and `ε > 0` there is a compact `K ⊆ D` such that for
every mesh `δ > 0` some chain `x = m 0, m 1, …, m N = y` in `K` with steps shorter than `δ` has
`∑ d (m i) (m (i + 1)) ≤ d x y + ε`. Then `d₁ = d₂` on `D × D`.

For internal (length) metrics such chains come from near-geodesic paths; no length-space property of the two
functions is assumed beyond the chain approximation.

Proof of `d₂ x y ≤ d₁ x y`. Fix `ε > 0` and a radius `θ` with `d₂ w z < ε` on `D ∩ B(z, θ)`. The compact set
`K ∖ B(z, θ)` avoids `z`, so it is covered by balls of local agreement, with a Lebesgue number `η`. Take a chain for
`d₁` of mesh `η`. If it avoids `B(z, θ)`, every step has an endpoint in `K ∖ B(z, θ)`, so `d₁ = d₂` on every
step and the triangle inequality for `d₂` along the chain gives `d₂ x y ≤ d₁ x y + ε`. Otherwise, between the
first and the last visit of `B(z, θ)` the chain is replaced by two legs to the root, each of `d₂`-length `< ε`.

* `HasFineChains D d`: the chain approximation property.
* `le_sum_add_of_chain`, `le_add_sum_of_chain`, `le_sum_of_chain`: the triangle inequality along a chain.
* `le_of_local_agreement_of_fineChains`: the one-sided bound `d₂ ≤ d₁` (it uses the triangle inequality, symmetry
  and root continuity of `d₂` and the fine chains of `d₁` only).
* `eq_of_local_agreement_of_fineChains`: the two-sided gluing `d₁ = d₂` on `D × D`.
-/

open Set Filter Metric Topology
open scoped ENNReal NNReal

namespace LatticeProb.Topology

variable {α : Type*}

section Chain

variable {D : Set α} {d : α → α → ℝ≥0∞}

/-- Triangle inequality along a chain in `D`, ending at a point `w ∈ D`. -/
theorem le_sum_add_of_chain (htri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d x w ≤ d x y + d y w)
    {m : ℕ → α} {N : ℕ} (hmD : ∀ i ≤ N, m i ∈ D) {w : α} (hw : w ∈ D) {a b : ℕ} (hab : a ≤ b)
    (hbN : b ≤ N) :
    d (m a) w ≤ (∑ i ∈ Finset.Ico a b, d (m i) (m (i + 1))) + d (m b) w := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hb : b ≤ N := (Nat.le_succ b).trans hbN
    calc d (m a) w ≤ (∑ i ∈ Finset.Ico a b, d (m i) (m (i + 1))) + d (m b) w := ih hb
      _ ≤ (∑ i ∈ Finset.Ico a b, d (m i) (m (i + 1))) + (d (m b) (m (b + 1)) + d (m (b + 1)) w) :=
        add_le_add le_rfl (htri _ (hmD b hb) _ (hmD (b + 1) hbN) _ hw)
      _ = (∑ i ∈ Finset.Ico a (b + 1), d (m i) (m (i + 1))) + d (m (b + 1)) w := by
        rw [Finset.sum_Ico_succ_top hab, add_assoc]

/-- Triangle inequality along a chain in `D`, starting from a point `w ∈ D`. -/
theorem le_add_sum_of_chain (htri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d x w ≤ d x y + d y w)
    {m : ℕ → α} {N : ℕ} (hmD : ∀ i ≤ N, m i ∈ D) {w : α} (hw : w ∈ D) {a b : ℕ} (hab : a ≤ b)
    (hbN : b ≤ N) :
    d w (m b) ≤ d w (m a) + ∑ i ∈ Finset.Ico a b, d (m i) (m (i + 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hb : b ≤ N := (Nat.le_succ b).trans hbN
    calc d w (m (b + 1)) ≤ d w (m b) + d (m b) (m (b + 1)) :=
          htri _ hw _ (hmD b hb) _ (hmD (b + 1) hbN)
      _ ≤ (d w (m a) + ∑ i ∈ Finset.Ico a b, d (m i) (m (i + 1))) + d (m b) (m (b + 1)) :=
        add_le_add (ih hb) le_rfl
      _ = d w (m a) + ∑ i ∈ Finset.Ico a (b + 1), d (m i) (m (i + 1)) := by
        rw [Finset.sum_Ico_succ_top hab, add_assoc]

/-- Triangle inequality along a chain in `D` with at least one step. -/
theorem le_sum_of_chain (htri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d x w ≤ d x y + d y w)
    {m : ℕ → α} {N : ℕ} (hmD : ∀ i ≤ N, m i ∈ D) {a b : ℕ} (hab : a < b) (hbN : b ≤ N) :
    d (m a) (m b) ≤ ∑ i ∈ Finset.Ico a b, d (m i) (m (i + 1)) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hac : a ≤ c := Nat.lt_succ_iff.1 hab
  calc d (m a) (m (c + 1)) ≤ (∑ i ∈ Finset.Ico a c, d (m i) (m (i + 1))) + d (m c) (m (c + 1)) :=
        le_sum_add_of_chain htri hmD (hmD _ hbN) hac ((Nat.le_succ c).trans hbN)
    _ = ∑ i ∈ Finset.Ico a (c + 1), d (m i) (m (i + 1)) := (Finset.sum_Ico_succ_top hac _).symm

end Chain

variable [PseudoMetricSpace α]

/-- `d` has **fine chains** on `D`: every value `d x y` (`x, y ∈ D`) is approximated, up to any `ε > 0`, by the
sums of `d` along chains from `x` to `y` of arbitrarily small mesh inside one compact subset of `D`. -/
def HasFineChains (D : Set α) (d : α → α → ℝ≥0∞) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∀ ε : ℝ≥0∞, 0 < ε → ∃ K ⊆ D, IsCompact K ∧ ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∃ m : ℕ → α,
    m 0 = x ∧ m N = y ∧ (∀ i ≤ N, m i ∈ K) ∧ (∀ i < N, dist (m i) (m (i + 1)) < δ) ∧
      ∑ i ∈ Finset.range N, d (m i) (m (i + 1)) ≤ d x y + ε


/-- **One-sided gluing.** If `d₂` satisfies the triangle inequality and is symmetric on `D` and tends to `0` at the
root `z ∈ D`, `d₁` has fine chains on `D`, and `d₁ = d₂` near every point of `D ∖ {z}`, then `d₂ ≤ d₁` on
`D × D`. -/
theorem le_of_local_agreement_of_fineChains {D : Set α} {z : α} (hz : z ∈ D) {d₁ d₂ : α → α → ℝ≥0∞}
    (htri₂ : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d₂ x w ≤ d₂ x y + d₂ y w)
    (hsymm₂ : ∀ x ∈ D, ∀ y ∈ D, d₂ x y = d₂ y x)
    (hroot₂ : Tendsto (fun w => d₂ w z) (𝓝[D] z) (𝓝 0))
    (hch₁ : HasFineChains D d₁)
    (hloc : ∀ q ∈ D, q ≠ z → ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s, d₁ u v = d₂ u v)
    {x y : α} (hx : x ∈ D) (hy : y ∈ D) : d₂ x y ≤ d₁ x y := by
  classical
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_
  obtain ⟨ε, hε, hthirds⟩ : ∃ ε : ℝ≥0∞, 0 < ε ∧ ε + ε + ε = ε' :=
    ⟨(ε' : ℝ≥0∞) / 3, ENNReal.div_pos_iff.2 ⟨ENNReal.coe_ne_zero.2 hε'.ne', by norm_num⟩,
      ENNReal.add_thirds _⟩
  -- a root radius
  obtain ⟨θ, hθ, hθε⟩ : ∃ θ > 0, ∀ w ∈ ball z θ, w ∈ D → d₂ w z < ε := by
    obtain ⟨θ, hθ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (hroot₂.eventually (Iio_mem_nhds hε))
    exact ⟨θ, hθ, fun w hw hwD => hsub ⟨hw, hwD⟩⟩
  obtain ⟨K, hKD, hKc, hK⟩ := hch₁ x hx y hy ε hε
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

/-- **Gluing along fine chains.** Two functions `d₁, d₂ : α → α → ℝ≥0∞` that satisfy the triangle inequality and
are symmetric on `D`, tend to `0` at a root `z ∈ D`, have fine chains on `D`, and agree near every point of
`D ∖ {z}`, agree on `D × D`. -/
theorem eq_of_local_agreement_of_fineChains {D : Set α} {z : α} (hz : z ∈ D) {d₁ d₂ : α → α → ℝ≥0∞}
    (htri₁ : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d₁ x w ≤ d₁ x y + d₁ y w)
    (htri₂ : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d₂ x w ≤ d₂ x y + d₂ y w)
    (hsymm₁ : ∀ x ∈ D, ∀ y ∈ D, d₁ x y = d₁ y x) (hsymm₂ : ∀ x ∈ D, ∀ y ∈ D, d₂ x y = d₂ y x)
    (hroot₁ : Tendsto (fun w => d₁ w z) (𝓝[D] z) (𝓝 0))
    (hroot₂ : Tendsto (fun w => d₂ w z) (𝓝[D] z) (𝓝 0))
    (hch₁ : HasFineChains D d₁) (hch₂ : HasFineChains D d₂)
    (hloc : ∀ q ∈ D, q ≠ z → ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s, d₁ u v = d₂ u v) :
    ∀ x ∈ D, ∀ y ∈ D, d₁ x y = d₂ x y := fun _ hx _ hy =>
  le_antisymm
    (le_of_local_agreement_of_fineChains hz htri₁ hsymm₁ hroot₁ hch₂
      (fun q hq hqz => (hloc q hq hqz).imp fun _ ⟨hs, h⟩ => ⟨hs, fun u hu v hv => (h u hu v hv).symm⟩)
      hx hy)
    (le_of_local_agreement_of_fineChains hz htri₂ hsymm₂ hroot₂ hch₁ hloc hx hy)

end LatticeProb.Topology
