/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Meas.Internal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Meas.Geod
import LatticeProb.Bonanno.LQGMetric.Meas.CR
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Measurability of internal metrics (LM S-int (a), CR4 of decision D30)

For `V ⊆ ℂ` open and a continuous **length** metric `D`, the internal metric `D(z, w; V)` is given
by a countable formula (`ContMetric.internal_eq_chainInf`):
`D(z, w; V) = inf` over finite chains `z = x₀, x₁, …, x_n, x_{n+1} = w` with interior points in a
fixed countable dense set and each step shorter than the `D`-distance from its start to `∂V`
(`D(x_i, x_{i+1}) < D(x_i, Vᶜ)`) of `∑ D(x_i, x_{i+1})`. The right side (`ContMetric.chainInf`) is
jointly measurable in `(D, z, w) ∈ ContMetric × ℂ × ℂ` for every `D` (CR1 for the distance to
`Vᶜ`), so `(D, z, w) ↦ D(z, w; V)` agrees on length metrics with a Borel function
(`measurable_internal`, LM S-int (a)), and `ω ↦ D_ω(z, w; V)` is a.e.-measurable for a random length
metric (`aemeasurable_internal`).

Source: blueprint/LocalMetrics.md, row LM.S-int: "(a) is an own argument, best via a countable
formula … the idea is LM's own (proof of Lemma 2.2(2), tex:507–517, and of Lemma 1.1,
tex:213–214)" (Gwynne–Miller, *Local metrics of the Gaussian free field*, arXiv:1905.00379).
Steps: `≤` by locality (`internalEDist_eq_edist_of_ball_subset`, LM tex:213–214) and the triangle
inequality; `≥` by sampling a near-minimal path at a fine uniform partition and moving the sample
points to the dense set (uniform continuity, positive distance of the path to `Vᶜ`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric

open MetricGeometry

namespace ContMetric

/-- `D`-distance from `x` to the complement of `V` -/
noncomputable def bdDist (D : ContMetric) (V : Set ℂ) (x : ℂ) : ℝ≥0∞ :=
  Metric.infEDist (D.pt x) (D.pt '' V)ᶜ

/-- an admissible chain step (length `D(x, y)` if `D(x, y) < D(x, Vᶜ)`, else `∞`) -/
noncomputable def chainStep (D : ContMetric) (V : Set ℂ) (x y : ℂ) : ℝ≥0∞ :=
  if edist (D.pt x) (D.pt y) < D.bdDist V x then edist (D.pt x) (D.pt y) else ⊤

/-- the value of the chain `x, l, y` -/
noncomputable def chainVal (D : ContMetric) (V : Set ℂ) : ℂ → List ℂ → ℂ → ℝ≥0∞
  | x, [], y => D.chainStep V x y
  | x, q :: l, y => D.chainStep V x q + D.chainVal V q l y

/-- infimum over chains with interior points in the dense sequence of `ℂ` -/
noncomputable def chainInf (D : ContMetric) (V : Set ℂ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ l : List ℕ, D.chainVal V z (l.map (TopologicalSpace.denseSeq ℂ)) w

theorem mem_compl_image_pt (D : ContMetric) {V : Set ℂ} {y : ℂ} :
    D.pt y ∈ (D.pt '' V)ᶜ ↔ y ∉ V := by
  rw [mem_compl_iff, mem_image_pt]

theorem bdDist_eq (D : ContMetric) (V : Set ℂ) (x : ℂ) :
    D.bdDist V x = ⨅ y ∈ Vᶜ, ENNReal.ofReal (D.1 (x, y)) := by
  refine le_antisymm (le_iInf₂ fun y hy => ?_) (Metric.le_infEDist.2 fun y hy => ?_)
  · exact (Metric.infEDist_le_edist_of_mem (D.mem_compl_image_pt.2 hy)).trans_eq (edist_pt D x y)
  · refine (biInf_le _ (show D.unpt y ∈ Vᶜ from D.mem_compl_image_pt.1 hy)).trans_eq ?_
    exact (edist_pt D x (D.unpt y)).symm

/-! ### Measurability of the chain formula -/

theorem measurable_edist_pt :
    Measurable fun p : ContMetric × ℂ × ℂ => edist (p.1.pt p.2.1) (p.1.pt p.2.2) := by
  have : (fun p : ContMetric × ℂ × ℂ => edist (p.1.pt p.2.1) (p.1.pt p.2.2)) =
      fun p => ENNReal.ofReal (p.1.1 p.2) := funext fun p => edist_pt p.1 p.2.1 p.2.2
  rw [this]
  exact (ENNReal.continuous_ofReal.comp continuous_contMetric_apply).measurable

theorem measurable_bdDist (V : Set ℂ) : Measurable fun p : ContMetric × ℂ => p.1.bdDist V p.2 := by
  simp_rw [bdDist_eq]
  refine measurable_biInf_of_continuous (f := fun (p : ContMetric × ℂ) (y : ℂ) =>
    ENNReal.ofReal (p.1.1 (p.2, y))) (fun p => ?_) (fun y => ?_) Vᶜ
  · exact ENNReal.continuous_ofReal.comp (p.1.1.continuous.comp
      (continuous_const.prodMk continuous_id))
  · have h1 : Continuous fun p : ContMetric × ℂ => ((p.1, (p.2, y)) : ContMetric × (ℂ × ℂ)) :=
      continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
    have h2 : Continuous fun p : ContMetric × ℂ => ENNReal.ofReal (p.1.1 (p.2, y)) :=
      ENNReal.continuous_ofReal.comp (continuous_contMetric_apply.comp h1)
    exact h2.measurable

theorem measurable_chainStep (V : Set ℂ) :
    Measurable fun p : ContMetric × ℂ × ℂ => p.1.chainStep V p.2.1 p.2.2 := by
  have hg : Measurable fun p : ContMetric × ℂ × ℂ => ((p.1, p.2.1) : ContMetric × ℂ) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hB : Measurable fun p : ContMetric × ℂ × ℂ => p.1.bdDist V p.2.1 :=
    fun s hs => hg ((measurable_bdDist V) hs)
  exact Measurable.ite (measurableSet_lt measurable_edist_pt hB) measurable_edist_pt
    measurable_const

theorem measurable_chainVal (V : Set ℂ) (l : List ℂ) :
    Measurable fun p : ContMetric × ℂ × ℂ => p.1.chainVal V p.2.1 l p.2.2 := by
  induction l with
  | nil => exact measurable_chainStep V
  | cons q l ih =>
    simp only [chainVal]
    refine Measurable.add ?_ ?_
    · exact (measurable_chainStep V).comp
        (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const))
    · exact ih.comp (measurable_fst.prodMk (measurable_const.prodMk
        (measurable_snd.comp measurable_snd)))

/-- the chain formula is Borel in `(D, z, w)` -/
theorem measurable_chainInf (V : Set ℂ) :
    Measurable fun p : ContMetric × ℂ × ℂ => p.1.chainInf V p.2.1 p.2.2 :=
  Measurable.iInf fun l => measurable_chainVal V (l.map (TopologicalSpace.denseSeq ℂ))

/-! ### `D(·,·;V) ≤` chain values -/

theorem internal_le_chainStep (D : ContMetric) (hD : D.IsLength) (V : Set ℂ) (x y : ℂ) :
    D.internal V x y ≤ D.chainStep V x y := by
  unfold chainStep
  split_ifs with h
  · refine (internalEDist_eq_edist_of_ball_subset hD (r := D.bdDist V x) ?_ h).le
    intro y' hy'
    by_contra hc
    have h1 := Metric.infEDist_le_edist_of_mem (x := D.pt x) (show y' ∈ (D.pt '' V)ᶜ from hc)
    rw [Metric.mem_eball, edist_comm] at hy'
    exact absurd (hy'.trans_le h1) (lt_irrefl _)
  · exact le_top

theorem internal_le_chainVal (D : ContMetric) (hD : D.IsLength) (V : Set ℂ) (l : List ℂ) :
    ∀ x y : ℂ, D.internal V x y ≤ D.chainVal V x l y := by
  induction l with
  | nil => exact fun x y => D.internal_le_chainStep hD V x y
  | cons q l ih =>
    intro x y
    simp only [chainVal]
    exact (internalEDist_triangle _ _ (D.pt q) _).trans
      (add_le_add (D.internal_le_chainStep hD V x q) (ih q y))

theorem internal_le_chainInf (D : ContMetric) (hD : D.IsLength) (V : Set ℂ) (z w : ℂ) :
    D.internal V z w ≤ D.chainInf V z w :=
  le_iInf fun l => D.internal_le_chainVal hD V (l.map (TopologicalSpace.denseSeq ℂ)) z w

/-! ### Chain values along a sampled path -/

/-- a chain given by a sequence of points is the sum of its steps -/
theorem chainVal_eq_sum (D : ContMetric) (V : Set ℂ) (n : ℕ) :
    ∀ c : ℕ → ℂ, D.chainVal V (c 0) ((List.range n).map fun k => c (k + 1)) (c (n + 1)) =
      ∑ k ∈ Finset.range (n + 1), D.chainStep V (c k) (c (k + 1)) := by
  induction n with
  | zero => intro c; simp [chainVal]
  | succ n ih =>
    intro c
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, chainVal, Finset.sum_range_succ',
      add_comm]
    congr 1
    exact ih (fun k => c (k + 1))

/-! ### Chain values `≤` lengths of paths in `V` -/

/-- a path in an open set stays at positive distance from its complement -/
theorem exists_pos_le_infEDist (D : ContMetric) {V : Set ℂ} (hV : IsOpen V) {x y : D.Space}
    (γ : Path x y) (hγ : ∀ t, γ t ∈ D.pt '' V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal δ ≤ Metric.infEDist (γ.extend t) (D.pt '' V)ᶜ := by
  have hY : IsClosed (D.pt '' V)ᶜ := (D.isOpen_image_pt hV).isClosed_compl
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < Metric.infEDist (γ.extend t) (D.pt '' V)ᶜ := by
    intro t ht
    rw [Metric.infEDist_pos_iff_notMem_closure, hY.closure_eq, notMem_compl_iff,
      Path.extend_apply γ ht]
    exact hγ _
  have hc : ContinuousOn (fun t => Metric.infEDist (γ.extend t) (D.pt '' V)ᶜ) (Icc 0 1) :=
    (Metric.continuous_infEDist.comp γ.continuous_extend).continuousOn
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hc
  obtain ⟨δ, -, hδ0, hδ⟩ := ENNReal.lt_iff_exists_real_btwn.1 (hpos t0 ht0)
  exact ⟨δ, ENNReal.ofReal_pos.1 hδ0, fun t ht => hδ.le.trans (hmin ht)⟩

/-- sampling a path in `V` at a fine partition and moving the sample points to the dense
sequence gives an admissible chain of value `≤ length + ε` -/
theorem chainInf_le_pathLength (D : ContMetric) {V : Set ℂ} (hV : IsOpen V) (z w : ℂ)
    (γ : Path (D.pt z) (D.pt w)) (hγ : ∀ t, γ t ∈ D.pt '' V) {ε : ℝ} (hε : 0 < ε) :
    D.chainInf V z w ≤ pathLength γ + ENNReal.ofReal ε := by
  classical
  obtain ⟨δ, hδ, hδY⟩ := D.exists_pos_le_infEDist hV γ hγ
  have huc : UniformContinuousOn γ.extend (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous γ.continuous_extend.continuousOn
  obtain ⟨η, hη, hηγ⟩ := Metric.uniformContinuousOn_iff.1 huc (δ / 4) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  set ρ : ℝ := min (δ / 8) (ε / (2 * (n + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρδ : ρ ≤ δ / 8 := min_le_left _ _
  set u : ℕ → ℝ := fun k => min ((k : ℝ) / (n + 1)) 1 with hu
  have hu_mono : Monotone u := fun a b hab =>
    min_le_min_right _ (div_le_div_of_nonneg_right (Nat.cast_le.2 hab) (by positivity))
  have hu_mem : ∀ k, u k ∈ Icc (0 : ℝ) 1 := fun k =>
    ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hu_eq : ∀ k, k ≤ n + 1 → u k = k / (n + 1) := fun k hk =>
    min_eq_left ((div_le_one (by positivity)).2 (by exact_mod_cast hk))
  have hdense : DenseRange (D.pt ∘ TopologicalSpace.denseSeq ℂ) :=
    D.ptHomeomorph.surjective.denseRange.comp (TopologicalSpace.denseRange_denseSeq ℂ)
      D.continuous_pt
  choose m hm using fun k => hdense.exists_dist_lt (γ.extend (u k)) hρ0
  set c : ℕ → ℂ := fun k => if k = 0 then z else if k = n + 1 then w else
    TopologicalSpace.denseSeq ℂ (m k) with hc
  have hce : ∀ k, k ≤ n + 1 → dist (D.pt (c k)) (γ.extend (u k)) < ρ := by
    intro k hk
    by_cases h0 : k = 0
    · subst h0
      have : u 0 = 0 := by simp [u]
      simp only [c, if_pos rfl, this, Path.extend_zero, dist_self]
      exact hρ0
    · by_cases h1 : k = n + 1
      · subst h1
        have : u (n + 1) = 1 := by rw [hu_eq _ le_rfl]; push_cast; exact div_self (by positivity)
        rw [show c (n + 1) = w by simp [c], this, Path.extend_one, dist_self]
        exact hρ0
      · simp only [c, if_neg h0, if_neg h1]
        rw [dist_comm]
        exact hm k
  have hγstep : ∀ k, k ≤ n → dist (γ.extend (u k)) (γ.extend (u (k + 1))) < δ / 4 := by
    intro k hk
    refine hηγ _ (hu_mem k) _ (hu_mem (k + 1)) ?_
    rw [Real.dist_eq, hu_eq k (by omega), hu_eq (k + 1) (by omega)]
    push_cast
    rw [show (k : ℝ) / (n + 1) - (k + 1) / (n + 1) = -(1 / (n + 1)) by ring, abs_neg,
      abs_of_pos (by positivity)]
    exact hn
  have hstep : ∀ k, k ≤ n → dist (D.pt (c k)) (D.pt (c (k + 1))) ≤
      dist (γ.extend (u k)) (γ.extend (u (k + 1))) + 2 * ρ := by
    intro k hk
    have h1 := hce k (by omega)
    have h2 := hce (k + 1) (by omega)
    rw [dist_comm] at h2
    linarith [dist_triangle4 (D.pt (c k)) (γ.extend (u k)) (γ.extend (u (k + 1)))
      (D.pt (c (k + 1)))]
  have hvalid : ∀ k, k ≤ n →
      D.chainStep V (c k) (c (k + 1)) = edist (D.pt (c k)) (D.pt (c (k + 1))) := by
    intro k hk
    unfold chainStep
    rw [if_pos]
    by_contra hcon
    rw [not_lt] at hcon
    have h1 := hδY (u k) (hu_mem k)
    have h2 := Metric.infEDist_le_infEDist_add_edist (x := γ.extend (u k)) (y := D.pt (c k))
      (s := (D.pt '' V)ᶜ)
    have h3 : ENNReal.ofReal δ ≤ ENNReal.ofReal (dist (D.pt (c k)) (D.pt (c (k + 1))) +
        dist (γ.extend (u k)) (D.pt (c k))) := by
      rw [ENNReal.ofReal_add dist_nonneg dist_nonneg, ← edist_dist, ← edist_dist]
      exact h1.trans (h2.trans (add_le_add (show Metric.infEDist _ _ ≤ _ from hcon) le_rfl))
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    have h4 := hstep k hk
    have h5 := hγstep k hk
    have h6 := hce k (by omega)
    rw [dist_comm] at h6
    linarith
  have hlist : (List.map (TopologicalSpace.denseSeq ℂ) ((List.range n).map fun k => m (k + 1))) =
      (List.range n).map fun k => c (k + 1) := by
    rw [List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk' : k < n := List.mem_range.1 hk
    simp only [Function.comp_apply, c, if_neg (Nat.succ_ne_zero k),
      if_neg (show k + 1 ≠ n + 1 by omega)]
  have hc0 : c 0 = z := by simp [c]
  have hcn : c (n + 1) = w := by simp [c]
  have hlen : ∑ k ∈ Finset.range (n + 1), edist (γ.extend (u k)) (γ.extend (u (k + 1))) ≤
      pathLength γ := by
    refine (Finset.sum_le_sum fun k _ => ?_).trans
      (sum_internalEDist_le_curveLength (Y := univ) γ.continuous_extend.continuousOn
        (mapsTo_univ _ _) hu_mono hu_mem (n + 1))
    rw [edist_comm]
    exact edist_le_internalEDist univ _ _
  have hpert : ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * ρ) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : ρ ≤ ε / (2 * (n + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    push_cast
    linarith
  calc D.chainInf V z w
      ≤ D.chainVal V z (List.map (TopologicalSpace.denseSeq ℂ)
          ((List.range n).map fun k => m (k + 1))) w := iInf_le _ _
    _ = D.chainVal V (c 0) ((List.range n).map fun k => c (k + 1)) (c (n + 1)) := by
        rw [hlist, hc0, hcn]
    _ = ∑ k ∈ Finset.range (n + 1), D.chainStep V (c k) (c (k + 1)) := D.chainVal_eq_sum V n c
    _ = ∑ k ∈ Finset.range (n + 1), edist (D.pt (c k)) (D.pt (c (k + 1))) :=
        Finset.sum_congr rfl fun k hk => hvalid k (by have := Finset.mem_range.1 hk; omega)
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          (edist (γ.extend (u k)) (γ.extend (u (k + 1))) + ENNReal.ofReal (2 * ρ)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
        rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hstep k hk')
    _ = ∑ k ∈ Finset.range (n + 1), edist (γ.extend (u k)) (γ.extend (u (k + 1))) +
          ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * ρ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ pathLength γ + ENNReal.ofReal ε := add_le_add hlen hpert

theorem chainInf_le_internal (D : ContMetric) {V : Set ℂ} (hV : IsOpen V) (z w : ℂ) :
    D.chainInf V z w ≤ D.internal V z w := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  unfold ContMetric.internal internalEDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun γ => ?_
  have := D.chainInf_le_pathLength hV z w γ.1 γ.2 (ε := ε) (by exact_mod_cast hε)
  rwa [ENNReal.ofReal_coe_nnreal] at this

/-- **The countable formula for internal metrics** (LM S-int (a), own argument following the
blueprint's suggestion): for a length metric `D` and `V` open, `D(z, w; V)` is the infimum over
admissible chains with interior points in a fixed countable dense set. -/
theorem internal_eq_chainInf (D : ContMetric) (hD : D.IsLength) {V : Set ℂ} (hV : IsOpen V)
    (z w : ℂ) : D.internal V z w = D.chainInf V z w :=
  le_antisymm (D.internal_le_chainInf hD V z w) (D.chainInf_le_internal hV z w)

end ContMetric

/-- **LM S-int (a)** (CR4): for `V` open, `(D, z, w) ↦ D(z, w; V)` agrees on continuous length
metrics with a Borel function on `ContMetric × ℂ × ℂ`. -/
theorem measurable_internal {V : Set ℂ} (hV : IsOpen V) :
    ∃ F : ContMetric × ℂ × ℂ → ℝ≥0∞, Measurable F ∧
      ∀ D : ContMetric, D.IsLength → ∀ z w : ℂ, D.internal V z w = F (D, z, w) :=
  ⟨fun p => p.1.chainInf V p.2.1 p.2.2, ContMetric.measurable_chainInf V,
    fun D hD z w => D.internal_eq_chainInf hD hV z w⟩

end LQGMetric
