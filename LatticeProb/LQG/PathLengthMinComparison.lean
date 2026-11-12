import Mathlib
import LatticeProb.LQG.LengthMetricDerived

/-!
# Comparison of lengths for metrics that agree below a threshold

Let `E'` be a Euclidean length metric on `ℂ` and `E` a function `ℂ → ℂ → ℝ` such that `min c (E' x y) ≤ E x y` for
all `x, y` in a set `W` and some `c > 0`. Then the `E'`-length of every path with range in `W` is at most its `E`-length,
and consequently the internal metric of `E'` in a set `V ⊆ W` is at most that of `E`.

The proof refines partitions. A path `P` is continuous for the Euclidean topology, which is the `E'`-topology, hence
uniformly continuous for `E'` on `[0, 1]`: consecutive points of a fine enough subdivision are at `E'`-distance `< c`,
where `E'` is bounded by `E`. The triangle inequality for `E'` then bounds the `E'`-distance between the endpoints of
each step of the original partition by an inscribed `E`-sum of the step, and the lengths on adjacent intervals add up
(superadditivity of `curveLength`), see `curveLength_add_le`.
-/

namespace LatticeProb.LQG

open Set Filter Topology
open scoped ENNReal unitInterval Uniformity

/-- The length of a curve on a subinterval is at most its length on a larger interval. -/
private theorem curveLength_mono_interval (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {a b a' b' : ℝ} (ha : a' ≤ a)
    (hb : b ≤ b') : curveLength D p a b ≤ curveLength D p a' b' := by
  unfold curveLength
  refine iSup_le fun q => ?_
  exact le_iSup_of_le (⟨q.1, q.2.1, q.2.2.1, fun i => ⟨ha.trans (q.2.2.2 i).1,
    (q.2.2.2 i).2.trans hb⟩⟩ : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a' b' }) le_rfl

/-- **Superadditivity of length.** The lengths of a curve on `[a, m]` and `[m, b]` add up to at most its length on
`[a, b]`. No property of `D` is needed: two partitions are concatenated, the gap contributing a nonnegative term. -/
theorem curveLength_add_le (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b) :
    curveLength D p a m + curveLength D p m b ≤ curveLength D p a b := by
  have : Nonempty (ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a m }) :=
    ⟨(0, ⟨fun _ => a, monotone_const, fun _ => ⟨le_rfl, ham⟩⟩)⟩
  have : Nonempty (ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc m b }) :=
    ⟨(0, ⟨fun _ => m, monotone_const, fun _ => ⟨le_rfl, hmb⟩⟩)⟩
  unfold curveLength
  refine ENNReal.iSup_add_iSup_le ?_
  rintro ⟨n₁, u₁, hu₁, hI₁⟩ ⟨n₂, u₂, hu₂, hI₂⟩
  let w : ℕ → ℝ := fun k => if k ≤ n₁ then u₁ k else u₂ (k - (n₁ + 1))
  have hw_mem : ∀ k, w k ∈ Icc a b := by
    intro k
    simp only [w]
    split_ifs
    · exact ⟨(hI₁ k).1, (hI₁ k).2.trans hmb⟩
    · exact ⟨ham.trans (hI₂ _).1, (hI₂ _).2⟩
  have hw_mono : Monotone w := by
    refine monotone_nat_of_le_succ fun k => ?_
    simp only [w]
    by_cases h1 : k + 1 ≤ n₁
    · have h2 : k ≤ n₁ := by omega
      simp only [h1, h2, ↓reduceIte]
      exact hu₁ (Nat.le_succ k)
    · by_cases h2 : k ≤ n₁
      · simp only [h1, h2, ↓reduceIte]
        have hk : k = n₁ := by omega
        rw [hk, Nat.sub_self]
        exact (hI₁ n₁).2.trans (hI₂ 0).1
      · simp only [h1, h2, ↓reduceIte]
        have e : k + 1 - (n₁ + 1) = (k - (n₁ + 1)) + 1 := by omega
        rw [e]
        exact hu₂ (Nat.le_succ _)
  refine le_trans ?_ (le_iSup_of_le (⟨n₁ + 1 + n₂, w, hw_mono, hw_mem⟩ :
    ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b }) le_rfl)
  show _ ≤ ∑ k ∈ Finset.range (n₁ + 1 + n₂), ENNReal.ofReal (D (p (w (k + 1))) (p (w k)))
  rw [Finset.sum_range_add, Finset.sum_range_succ]
  have h1 : ∑ i ∈ Finset.range n₁, ENNReal.ofReal (D (p (u₁ (i + 1))) (p (u₁ i))) =
      ∑ k ∈ Finset.range n₁, ENNReal.ofReal (D (p (w (k + 1))) (p (w k))) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have hk1 : k + 1 ≤ n₁ := by omega
    have hk2 : k ≤ n₁ := by omega
    simp only [w, hk1, hk2, ↓reduceIte]
  have h2 : ∑ i ∈ Finset.range n₂, ENNReal.ofReal (D (p (u₂ (i + 1))) (p (u₂ i))) =
      ∑ x ∈ Finset.range n₂, ENNReal.ofReal (D (p (w (n₁ + 1 + x + 1))) (p (w (n₁ + 1 + x)))) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx1 : ¬ (n₁ + 1 + x + 1 ≤ n₁) := by omega
    have hx2 : ¬ (n₁ + 1 + x ≤ n₁) := by omega
    simp only [w, hx1, hx2, ↓reduceIte]
    have e1 : n₁ + 1 + x + 1 - (n₁ + 1) = x + 1 := by omega
    have e2 : n₁ + 1 + x - (n₁ + 1) = x := by omega
    rw [e1, e2]
  rw [h1, h2]
  gcongr
  exact le_self_add

/-- Lengths on the consecutive intervals of a monotone sequence add up to at most the length on the hull. -/
theorem sum_curveLength_le (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {u : ℕ → ℝ} (hu : Monotone u) (N : ℕ) :
    ∑ i ∈ Finset.range N, curveLength D p (u i) (u (i + 1)) ≤ curveLength D p (u 0) (u N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    calc _ ≤ curveLength D p (u 0) (u N) + curveLength D p (u N) (u (N + 1)) := by gcongr
      _ ≤ _ := curveLength_add_le D p (hu (Nat.zero_le N)) (hu (Nat.le_succ N))

/-- Triangle inequality along a chain, in `[0, ∞]`. -/
theorem ofReal_le_sum_range_of_triangle {E : ℂ → ℂ → ℝ} (htri : ∀ x y z, E x z ≤ E x y + E y z)
    (hE0 : ∀ x, E x x = 0) (f : ℕ → ℂ) (n : ℕ) :
    ENNReal.ofReal (E (f n) (f 0)) ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (E (f (i + 1)) (f i)) := by
  induction n with
  | zero => simp [hE0]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc ENNReal.ofReal (E (f (n + 1)) (f 0))
        ≤ ENNReal.ofReal (E (f (n + 1)) (f n) + E (f n) (f 0)) := ENNReal.ofReal_le_ofReal (htri _ _ _)
      _ ≤ ENNReal.ofReal (E (f (n + 1)) (f n)) + ENNReal.ofReal (E (f n) (f 0)) := ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal (E (f (n + 1)) (f n)) + ∑ i ∈ Finset.range n, ENNReal.ofReal (E (f (i + 1)) (f i)) := by
        gcongr
      _ = _ := add_comm _ _

/-- A path is uniformly continuous for a Euclidean length metric: for every `c > 0` there is `δ > 0` such that
`E (P t) (P s) < c` whenever `s, t ∈ [0, 1]` and `|t - s| < δ`. -/
theorem exists_dist_lt_of_isEuclideanLengthMetric {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E)
    {x y : ℂ} (P : Path x y) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| < δ →
      E (P.extend t) (P.extend s) < c := by
  have hball : ∀ (z : ℂ) (r : ℝ), 0 < r → {w | E z w < r} ∈ 𝓝 z := by
    intro z r hr
    have hopen : IsOpen {w | E z w < r} := by
      rw [hE.isOpen_iff]
      intro w hw
      have hw' : E z w < r := hw
      refine ⟨r - E z w, by linarith, fun v hv => ?_⟩
      show E z v < r
      have := hE.triangle z w v
      linarith
    refine hopen.mem_nhds ?_
    show E z z < r
    rw [hE.self_eq_zero]
    exact hr
  let U : Set (unitInterval × unitInterval) := {q | E (P q.2) (P q.1) < c}
  have hUnhds : U ∈ 𝓝ˢ (Set.diagonal unitInterval) := by
    rw [mem_nhdsSet_iff_forall]
    rintro ⟨a, b⟩ hab
    have hab' : a = b := hab
    subst hab'
    have hB : P ⁻¹' {w | E (P a) w < c / 2} ∈ 𝓝 a :=
      P.continuous.continuousAt.preimage_mem_nhds (hball _ _ (half_pos hc))
    filter_upwards [prod_mem_nhds hB hB] with q hq
    obtain ⟨hs, ht⟩ := hq
    have hs' : E (P a) (P q.1) < c / 2 := hs
    have ht' : E (P a) (P q.2) < c / 2 := ht
    show E (P q.2) (P q.1) < c
    have h1 := hE.triangle (P q.2) (P a) (P q.1)
    have h2 := hE.symm (P q.2) (P a)
    linarith
  have hUnif : U ∈ 𝓤 unitInterval := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    exact hUnhds
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_uniformity_dist.mp hUnif
  refine ⟨δ, hδ, fun s t hs ht hst => ?_⟩
  have hd : dist (⟨s, hs⟩ : unitInterval) ⟨t, ht⟩ < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    exact hst
  have hmem := @hδU ⟨s, hs⟩ ⟨t, ht⟩ hd
  have hmem' : E (P ⟨t, ht⟩) (P ⟨s, hs⟩) < c := hmem
  rwa [Path.extend_extends' P ⟨t, ht⟩, Path.extend_extends' P ⟨s, hs⟩]

/-- If `min c (E' x y) ≤ E x y` on `W` and the path has range in `W`, the `E'`-distance between two points of the
path, at parameters `s ≤ t` in `[0, 1]`, is at most the `E`-length of the path on `[s, t]`. -/
theorem ofReal_le_curveLength_of_min_le {E E' : ℂ → ℂ → ℝ} (hE' : IsEuclideanLengthMetric E') {c : ℝ}
    (hc : 0 < c) {W : Set ℂ} (hmin : ∀ x ∈ W, ∀ y ∈ W, min c (E' x y) ≤ E x y) {x y : ℂ} (P : Path x y)
    (hP : ∀ t, P t ∈ W) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ENNReal.ofReal (E' (P.extend t) (P.extend s)) ≤ curveLength E P.extend s t := by
  obtain ⟨δ, hδ, hδ'⟩ := exists_dist_lt_of_isEuclideanLengthMetric hE' P hc
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hmpos : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have hmδ : 1 / (m : ℝ) < δ := by
    rw [div_lt_iff₀ hmpos]
    have := (div_lt_iff₀ hδ).1 hm
    linarith
  let sg : ℕ → ℝ := fun j => s + (t - s) * ((min j m : ℕ) : ℝ) / m
  have hsg0 : sg 0 = s := by simp [sg]
  have hsgm : sg m = t := by
    simp only [sg, min_self]
    field_simp
    ring
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  have hsgmono : Monotone sg := by
    intro i j hij
    have : ((min i m : ℕ) : ℝ) ≤ ((min j m : ℕ) : ℝ) := by exact_mod_cast min_le_min_right m hij
    simp only [sg]
    have h : (t - s) * ((min i m : ℕ) : ℝ) / m ≤ (t - s) * ((min j m : ℕ) : ℝ) / m := by gcongr
    linarith
  have hsgmem : ∀ j, sg j ∈ Icc s t := by
    intro j
    have h0 : (0 : ℝ) ≤ ((min j m : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : ((min j m : ℕ) : ℝ) ≤ m := by exact_mod_cast min_le_right j m
    have hq : (t - s) * ((min j m : ℕ) : ℝ) / m ≤ t - s := by
      rw [div_le_iff₀ hmpos]
      nlinarith
    have hq0 : 0 ≤ (t - s) * ((min j m : ℕ) : ℝ) / m := by positivity
    exact ⟨by simp only [sg]; linarith, by simp only [sg]; linarith⟩
  have hsgI : ∀ j, sg j ∈ Icc (0 : ℝ) 1 := fun j => ⟨hs.trans (hsgmem j).1, (hsgmem j).2.trans ht⟩
  have hstep : ∀ j, |sg (j + 1) - sg j| < δ := by
    intro j
    have hmono := hsgmono (Nat.le_succ j)
    have hnat : min (j + 1) m ≤ min j m + 1 := by omega
    have hcast : ((min (j + 1) m : ℕ) : ℝ) ≤ ((min j m : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
    rw [abs_of_nonneg (sub_nonneg.2 hmono)]
    have e : sg (j + 1) - sg j =
        (t - s) * (((min (j + 1) m : ℕ) : ℝ) - ((min j m : ℕ) : ℝ)) / m := by
      simp only [sg]; ring
    rw [e]
    have hts1 : t - s ≤ 1 := by linarith
    have hnn : (0 : ℝ) ≤ ((min (j + 1) m : ℕ) : ℝ) - ((min j m : ℕ) : ℝ) := by
      have : ((min j m : ℕ) : ℝ) ≤ ((min (j + 1) m : ℕ) : ℝ) := by
        exact_mod_cast min_le_min_right m (Nat.le_succ j)
      linarith
    calc (t - s) * (((min (j + 1) m : ℕ) : ℝ) - ((min j m : ℕ) : ℝ)) / m
        ≤ 1 * 1 / m := by
          gcongr
          · linarith
        _ = 1 / m := by ring
        _ < δ := hmδ
  have hextW : ∀ r ∈ Icc (0 : ℝ) 1, P.extend r ∈ W := by
    intro r hr
    rw [Path.extend_extends' P ⟨r, hr⟩]
    exact hP _
  have hle : ∀ j, E' (P.extend (sg (j + 1))) (P.extend (sg j)) ≤ E (P.extend (sg (j + 1))) (P.extend (sg j)) := by
    intro j
    have hlt := hδ' (sg j) (sg (j + 1)) (hsgI j) (hsgI (j + 1)) (hstep j)
    calc E' (P.extend (sg (j + 1))) (P.extend (sg j)) = min c (E' (P.extend (sg (j + 1))) (P.extend (sg j))) :=
          (min_eq_right hlt.le).symm
      _ ≤ _ := hmin _ (hextW _ (hsgI _)) _ (hextW _ (hsgI _))
  calc ENNReal.ofReal (E' (P.extend t) (P.extend s))
      = ENNReal.ofReal (E' (P.extend (sg m)) (P.extend (sg 0))) := by rw [hsgm, hsg0]
    _ ≤ ∑ j ∈ Finset.range m, ENNReal.ofReal (E' (P.extend (sg (j + 1))) (P.extend (sg j))) :=
        ofReal_le_sum_range_of_triangle hE'.triangle hE'.self_eq_zero (fun j => P.extend (sg j)) m
    _ ≤ ∑ j ∈ Finset.range m, ENNReal.ofReal (E (P.extend (sg (j + 1))) (P.extend (sg j))) :=
        Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal (hle j)
    _ ≤ curveLength E P.extend s t := by
        unfold curveLength
        exact le_iSup (fun q : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc s t } =>
          ∑ i ∈ Finset.range q.1, ENNReal.ofReal (E (P.extend (q.2.1 (i + 1))) (P.extend (q.2.1 i))))
          ⟨m, sg, hsgmono, hsgmem⟩

/-- **Length comparison.** If `E'` is a Euclidean length metric, `c > 0`, and `min c (E' x y) ≤ E x y` for `x, y` in `W`,
then the `E'`-length of every path with range in `W` is at most its `E`-length. -/
theorem pathLength_le_of_min_le {E E' : ℂ → ℂ → ℝ} (hE' : IsEuclideanLengthMetric E') {c : ℝ} (hc : 0 < c)
    {W : Set ℂ} (hmin : ∀ x ∈ W, ∀ y ∈ W, min c (E' x y) ≤ E x y) {x y : ℂ} (P : Path x y)
    (hP : ∀ t, P t ∈ W) : pathLength E' P ≤ pathLength E P := by
  unfold pathLength
  refine curveLength_le_of_partition_bound fun N u hu hI => ?_
  calc ∑ i ∈ Finset.range N, ENNReal.ofReal (E' (P.extend (u (i + 1))) (P.extend (u i)))
      ≤ ∑ i ∈ Finset.range N, curveLength E P.extend (u i) (u (i + 1)) :=
        Finset.sum_le_sum fun i _ => ofReal_le_curveLength_of_min_le hE' hc hmin P hP (hI i).1
          (hu (Nat.le_succ i)) (hI (i + 1)).2
    _ ≤ curveLength E P.extend (u 0) (u N) := sum_curveLength_le E _ hu N
    _ ≤ curveLength E P.extend 0 1 := curveLength_mono_interval E _ (hI 0).1 (hI N).2

/-- **Internal metric comparison.** Under the hypotheses of `pathLength_le_of_min_le`, the internal metric of `E'` in
a subset `V ⊆ W` is at most the internal metric of `E` in `V`. -/
theorem internalMetric_le_of_min_le {E E' : ℂ → ℂ → ℝ} (hE' : IsEuclideanLengthMetric E') {c : ℝ} (hc : 0 < c)
    {W V : Set ℂ} (hmin : ∀ x ∈ W, ∀ y ∈ W, min c (E' x y) ≤ E x y) (hV : V ⊆ W) {x y : ℂ} :
    internalMetric E' V x y ≤ internalMetric E V x y := by
  unfold internalMetric
  refine le_iInf₂ fun P hP => ?_
  exact (iInf₂_le P hP).trans (pathLength_le_of_min_le hE' hc hmin P fun t => hV (hP t))

end LatticeProb.LQG
