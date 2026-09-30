import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityCovering

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# The maximal inequality: double counting and the conclusion (Step 4, part B, DEEP)

The combinatorial core of the theorem. Double counting over offsets `u` in the cube of side `2 ^ J`:
each bad site is covered, at a heavy cell, for at least half the offsets, and the heavy cells at a
fixed offset are pairwise disjoint and lie in `dyBig u J N`, so the count of bad sites is controlled
by the average of `r (dyBig u J N)`. Letting `N → ∞` then `K → ∞` gives the maximal inequality: the
probability that some cube `Q_k` (`k ≥ 1`) is `α k ^ d`-heavy is at most `akMaxConst d * ρ / α`,
where `ρ` bounds the normalised means.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For a witness `k ≤ K` with `2 d K ≤ 2 ^ J`, there is a scale `j ≤ J` with `2 d k ≤ 2 ^ j < 4 d
k`. -/
theorem exists_le_two_pow_and_lt_of_le {d : ℕ} (hd : 1 ≤ d) {k K J : ℕ} (hk : 1 ≤ k) (hK : k
    ≤ K)
    (hKJ : 2 * d * K ≤ 2 ^ J) : ∃ j, j ≤ J ∧ 2 * d * k ≤ 2 ^ j ∧ 2 ^ j < 4 * d * k := by
  have h1 : 1 ≤ 2 * d * k := by
    have h2 : 1 ≤ 2 * d := by omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp h2)
        (Nat.one_le_iff_ne_zero.mp hk))
  obtain ⟨j, hj⟩ := exists_pow_two_le_lt_two_mul (2 * d * k) h1
  have h2 : 2 ^ j < 4 * d * k := by
    have : 2 * (2 * d * k) = 4 * d * k := by ring
    omega
  refine ⟨j, ?_, hj.1, h2⟩
  have h3 : 2 * (2 * d * k) ≤ 2 * (2 * d * K) := by
    have : 2 * d * k ≤ 2 * d * K := Nat.mul_le_mul_left (2 * d) hK
    omega
  have h4 : 2 * (2 * d * K) ≤ 2 * 2 ^ J := by
    have : 2 * d * K ≤ 2 ^ J := hKJ
    omega
  have h5 : 2 * 2 ^ J = 2 ^ (J + 1) := by rw [pow_succ]; ring
  have h6 : 2 ^ j < 2 ^ (J + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h6
  omega

open Classical in
/-- Choice functions `kf, jf` assigning to each bad site `x` a witness `k = kf x` and matching scale
`j = jf x ≤ J` with `2 d kf x ≤ 2 ^ jf x < 4 d kf x`. -/
theorem exists_kf_jf_of_bad {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ) {α : ℝ} {K J : ℕ}
    (hKJ : 2 * d * K ≤ 2 ^ J) (N : ℕ) :
    ∃ kf jf : Site d → ℕ, ∀ x ∈ (latticeCube d N).filter (fun x => ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < r ((latticeCube d k).map (Equiv.addRight x).toEmbedding)),
      1 ≤ kf x ∧ jf x ≤ J ∧ 2 * d * kf x ≤ 2 ^ jf x ∧ 2 ^ jf x < 4 * d * kf x ∧
        α * (kf x : ℝ) ^ d < r ((latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding) := by
  have hchoice : ∀ x : Site d, ∃ p : ℕ × ℕ,
      x ∈ (latticeCube d N).filter (fun x => ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < r ((latticeCube d k).map (Equiv.addRight x).toEmbedding)) →
      1 ≤ p.1 ∧ p.2 ≤ J ∧ 2 * d * p.1 ≤ 2 ^ p.2 ∧ 2 ^ p.2 < 4 * d * p.1 ∧
        α * (p.1 : ℝ) ^ d < r ((latticeCube d p.1).map (Equiv.addRight x).toEmbedding) := by
    intro x
    by_cases hx : x ∈ (latticeCube d N).filter (fun x => ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < r ((latticeCube d k).map (Equiv.addRight x).toEmbedding))
    · obtain ⟨k, hk1, hkK, hkr⟩ := (Finset.mem_filter.mp hx).2
      obtain ⟨j, hjJ, hjk, hjk2⟩ := exists_le_two_pow_and_lt_of_le hd hk1 hkK hKJ
      exact ⟨(k, j), fun _ => ⟨hk1, hjJ, hjk, hjk2, hkr⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hx⟩
  choose g hg using hchoice
  exact ⟨fun x => (g x).1, fun x => (g x).2, fun x hx => hg x hx⟩

/-- A site `x` lies in the translated cube of side `k ≥ 1` at `x`. -/
theorem self_mem_map_addRight_cube {d : ℕ} (x : Site d) {k : ℕ} (hk : 1 ≤ k) :
    x ∈ (latticeCube d k).map (Equiv.addRight x).toEmbedding := by
  rw [map_addRight_latticeCube_eq_latticeBox, mem_latticeBox_iff]
  intro i
  constructor <;> omega

open Classical in
/-- For a fixed offset `u`, `α / (4d) ^ d` times the count of bad sites of `S` whose witness cube
lies in a level-`jf x` cell of offset `u` is at most `r (dyBig u J N)`. -/
theorem mul_card_filter_le_apply_dyBig {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B)
    (hrmono : ∀ a b a' b', a ≤ a' → b' ≤ b → r (latticeBox a' b') ≤ r (latticeBox a b))
    {α : ℝ} (hα : 0 < α) {J N : ℕ} (u : Site d) (hu : u ∈ latticeCube d (2 ^ J))
    (S : Finset (Site d)) (hS : S ⊆ latticeCube d N) (kf jf : Site d → ℕ)
    (hw : ∀ x ∈ S, 1 ≤ kf x ∧ jf x ≤ J ∧ 2 ^ jf x < 4 * d * kf x ∧
      α * (kf x : ℝ) ^ d < r ((latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding)) :
    α / (4 * (d : ℝ)) ^ d *
        ((S.filter fun x => ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell
            u (jf x) c).card : ℝ) ≤
      r (dyBig u J N) := by
  refine mul_card_le_apply_dyBig_of_forall_sel hd r hrnn hrsup u J N (div_nonneg hα.le (by
      positivity)) _
    (fun x => (jf x, if h : ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell
        u (jf x) c
      then h.choose else 0)) ?_
  intro x hx
  obtain ⟨hxS, hex⟩ := Finset.mem_filter.1 hx
  obtain ⟨hk, hjJ, hj, hbad⟩ := hw x hxS
  simp only [dif_pos hex]
  have hc := hex.choose_spec
  have hxc := hc (self_mem_map_addRight_cube x hk)
  exact ⟨hxc, hjJ, dyCell_subset_dyBig_of_mem hu hjJ (hS hxS) hxc,
    heavy_dyCell_of_heavy_cube hd r hrmono x hk hj u _ hc hα hbad⟩

/-- Double counting: summing `card (S.filter (P u ·))` over `u ∈ U` equals summing `card (U.filter
(P · x))` over `x ∈ S`. -/
theorem sum_card_filter_comm {α β : Type*} (S : Finset α) (U : Finset β) (P : β → α → Prop)
    [∀ u x, Decidable (P u x)] :
    ∑ u ∈ U, (S.filter fun x => P u x).card = ∑ x ∈ S, (U.filter fun u => P u x).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-- If every `x ∈ S` satisfies `P ≤ 2 * b x`, then `S.card * P ≤ 2 * ∑ x ∈ S, b x`. -/
theorem card_mul_le_two_mul_sum_of_forall_le {α : Type*} (S : Finset α) (b : α → ℝ) {P : ℝ}
    (h : ∀ x ∈ S, P ≤ 2 * b x) : (S.card : ℝ) * P ≤ 2 * ∑ x ∈ S, b x := by
  have h1 : (S.card : ℝ) * P = ∑ _x ∈ S, P := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1, Finset.mul_sum]
  exact Finset.sum_le_sum h

/-- If `γ * a u ≤ R u` for every `u ∈ U`, then `γ * ∑ u ∈ U, a u ≤ ∑ u ∈ U, R u`. -/
theorem mul_sum_le_sum_of_forall_le {β : Type*} (U : Finset β) (a R : β → ℝ) {γ : ℝ}
    (h : ∀ u ∈ U, γ * a u ≤ R u) : γ * ∑ u ∈ U, a u ≤ ∑ u ∈ U, R u := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum h

/-- Real-algebra step combining `s * P ≤ 2 * A` and `α / D * A ≤ R'` into `s ≤ 2 * D / α * (R' /
P)`. -/
theorem le_two_mul_div_mul_div_of_le {s P A R' α D : ℝ} (hα : 0 < α) (hD : 0 < D) (hP : 0 <
    P)
    (h1 : s * P ≤ 2 * A) (h2 : α / D * A ≤ R') : s ≤ 2 * D / α * (R' / P) := by
  have h3 : A ≤ D * R' / α := by
    rw [le_div_iff₀ hα]
    have h2' : α * A ≤ R' * D := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hD] at h2
      linarith
    linarith
  have h4 : s * P ≤ 2 * (D * R' / α) := by linarith
  have h5 : s ≤ 2 * (D * R' / α) / P := by
    rw [le_div_iff₀ hP]
    linarith
  have h6 : 2 * (D * R' / α) / P = 2 * D / α * (R' / P) := by ring
  linarith [h5, h6.le, h6.ge]

open Classical in
/-- Double-counting bound: the number of bad sites of the cube of side `N` (with witness `k ≤ K`) is
at most `akMaxConst d / α` times the average of `r (dyBig u J N)` over offsets `u`. -/
theorem card_filter_bad_le_akMaxConst_mul_avg_dyBig {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site
    d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B)
    (hrmono : ∀ a b a' b', a ≤ a' → b' ≤ b → r (latticeBox a' b') ≤ r (latticeBox a b))
    {α : ℝ} (hα : 0 < α) {K J : ℕ} (hKJ : 2 * d * K ≤ 2 ^ J) (N : ℕ) :
    (((latticeCube d N).filter fun x => ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < r ((latticeCube d k).map (Equiv.addRight x).toEmbedding)).card : ℝ) ≤
      akMaxConst d / α *
        ((∑ u ∈ latticeCube d (2 ^ J), r (dyBig u J N)) / ((2 ^ J : ℕ) : ℝ) ^ d) := by
  obtain ⟨kf, jf, hw⟩ := exists_kf_jf_of_bad hd r (α := α) hKJ N
  set S := (latticeCube d N).filter (fun x => ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < r ((latticeCube d k).map (Equiv.addRight x).toEmbedding)) with hSdef
  have hSN : S ⊆ latticeCube d N := Finset.filter_subset _ _
  have hA : ∀ u ∈ latticeCube d (2 ^ J), α / (4 * (d : ℝ)) ^ d *
      ((S.filter fun x => ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u
          (jf x) c).card : ℝ) ≤
        r (dyBig u J N) :=
    fun u hu => mul_card_filter_le_apply_dyBig hd r hrnn hrsup hrmono hα u hu S hSN kf jf
      (fun x hx => ⟨(hw x hx).1, (hw x hx).2.1, (hw x hx).2.2.2.1, (hw x hx).2.2.2.2⟩)
  have hB : ∀ x ∈ S, ((2 ^ J : ℕ) : ℝ) ^ d ≤ 2 * ((((latticeCube d (2 ^ J)).filter fun u =>
      ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c).card : ℕ)
          : ℝ) :=
    fun x hx => pow_le_two_mul_card_filter_dyCell x (hw x hx).1 (hw x hx).2.1 (hw x hx).2.2.1
  have hswap := sum_card_filter_comm S (latticeCube d (2 ^ J))
    (fun u x => ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c)
  have hswapR : ∑ u ∈ latticeCube d (2 ^ J),
      ((S.filter fun x => ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u
          (jf x) c).card : ℝ) =
      ∑ x ∈ S, ((((latticeCube d (2 ^ J)).filter fun u =>
        ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c).card :
            ℕ) : ℝ) := by
    exact_mod_cast hswap
  have h7 := mul_sum_le_sum_of_forall_le (latticeCube d (2 ^ J)) _ _ hA
  rw [hswapR] at h7
  have h6 := card_mul_le_two_mul_sum_of_forall_le S _ hB
  have hP : (0 : ℝ) < ((2 ^ J : ℕ) : ℝ) ^ d := by positivity
  have hD : (0 : ℝ) < (4 * (d : ℝ)) ^ d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact pow_pos (by linarith) d
  unfold akMaxConst
  exact le_two_mul_div_mul_div_of_le hα hD hP h6 h7

/-- `dyBig u J N` is a translate of a cube, so `∫ R (dyBig u J N) ≤ ρ` times its volume, given the
volume bound on cubes. -/
theorem integral_apply_dyBig_le_mul_pow {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] (τ
    : Site d → Ω → Ω)
    (hτ : ∀ z, MeasurePreserving (τ z) μ μ) (R : Finset (Site d) → Ω → ℝ)
    (hRm : ∀ B, Measurable (R B))
    (hRstat : ∀ (B : Finset (Site d)) (z : Site d) (ω : Ω),
      R (B.map (Equiv.addRight z).toEmbedding) ω = R B (τ z ω))
    {ρ : ℝ} (hρ : ∀ N : ℕ, 1 ≤ N → ∫ ω, R (latticeCube d N) ω ∂μ ≤ ρ * (N : ℝ) ^ d)
    (u : Site d) (J N : ℕ) :
    ∫ ω, R (dyBig u J N) ω ∂μ ≤ ρ * (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d := by
  have hM : 1 ≤ (N / 2 ^ J + 4) * 2 ^ J :=
    one_le_mul (le_trans (by norm_num) (Nat.le_add_left 4 (N / 2 ^ J))) Nat.one_le_two_pow
  have hEq : ∫ ω, R (dyBig u J N) ω ∂μ =
      ∫ ω, R (latticeCube d ((N / 2 ^ J + 4) * 2 ^ J))
        (τ (u - fun _ => 2 * (2 ^ J : ℤ)) ω) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [dyBig]
      exact hRstat (latticeCube d ((N / 2 ^ J + 4) * 2 ^ J))
        (u - fun _ => 2 * (2 ^ J : ℤ)) ω)
  have hInt : ∫ ω, R (latticeCube d ((N / 2 ^ J + 4) * 2 ^ J))
        (τ (u - fun _ => 2 * (2 ^ J : ℤ)) ω) ∂μ =
      ∫ ω, R (latticeCube d ((N / 2 ^ J + 4) * 2 ^ J)) ω ∂μ
  · have hmap : ∫ y, R (latticeCube d ((N / 2 ^ J + 4) * 2 ^ J)) y
          ∂(Measure.map (τ (u - fun _ => 2 * (2 ^ J : ℤ))) μ) =
        ∫ ω, R (latticeCube d ((N / 2 ^ J + 4) * 2 ^ J))
          (τ (u - fun _ => 2 * (2 ^ J : ℤ)) ω) ∂μ :=
      integral_map (hτ (u - fun _ => 2 * (2 ^ J : ℤ))).measurable.aemeasurable
        (hRm (latticeCube d ((N / 2 ^ J + 4) * 2 ^ J))).aestronglyMeasurable
    rw [MeasurePreserving.map_eq (hτ (u - fun _ => 2 * (2 ^ J : ℤ)))] at hmap
    exact hmap.symm
  rw [hEq, hInt]
  exact hρ _ hM


open Classical in
omit [MeasurableSpace Ω] in
/-- The count of bad sites of the cube of side `N` at `ω` equals a sum, over those sites, of the
indicator of the bad event composed with the action. -/
theorem card_filter_bad_eq_sum_indicator_comp_action {d : ℕ} (τ : Site d → Ω → Ω) (R :
    Finset (Site d) → Ω → ℝ)
    (hRstat : ∀ (B : Finset (Site d)) (z : Site d) (ω : Ω),
      R (B.map (Equiv.addRight z).toEmbedding) ω = R B (τ z ω)) (α : ℝ) (K N : ℕ) (ω : Ω) :
    (((latticeCube d N).filter fun x => ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < R ((latticeCube d k).map (Equiv.addRight x).toEmbedding) ω).card : ℝ) =
      ∑ x ∈ latticeCube d N,
        {ω' | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω'}.indicator
          (fun _ => (1 : ℝ)) (τ x ω) := by
  classical
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hiff : (τ x ω ∈ {ω' : Ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < R (latticeCube d k) ω'}) ↔
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < R ((latticeCube d k).map (Equiv.addRight x).toEmbedding) ω) :=
    ⟨fun ⟨k, h1, h2, h3⟩ => ⟨k, h1, h2, (hRstat (latticeCube d k) x ω) ▸ h3⟩,
     fun ⟨k, h1, h2, h3⟩ => ⟨k, h1, h2, (hRstat (latticeCube d k) x ω).symm ▸ h3⟩⟩
  rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator_apply]
  exact if_congr hiff.symm rfl rfl


/-- The event `{ω | ∃ k ≤ K, α k ^ d < R (cube k) ω}` is measurable, being a finite union of
measurable sets. -/
theorem measurableSet_bad_le_K {d : ℕ} (R : Finset (Site d) → Ω → ℝ) (hRm : ∀ B, Measurable
    (R B))
    (α : ℝ) (K : ℕ) :
    MeasurableSet {ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω} := by
  have hset : {ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω} =
      ⋃ k ∈ Finset.Icc 1 K, {ω | α * (k : ℝ) ^ d < R (latticeCube d k) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨k, h1, h2, h3⟩
      exact ⟨k, ⟨h1, h2⟩, h3⟩
    · rintro ⟨k, ⟨h1, h2⟩, h3⟩
      exact ⟨k, h1, h2, h3⟩
  rw [hset]
  exact Finset.measurableSet_biUnion _ (fun k _ =>
    measurableSet_lt measurable_const (hRm (latticeCube d k)))

/-- `R (dyBig u J N)` is integrable, being nonnegative and bounded by a multiple of its cardinality.
-/
theorem integrable_apply_dyBig {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Finset (Site d) → Ω → ℝ) (hRm : ∀ B, Measurable (R B))
    (hRnn : ∀ a b ω, 0 ≤ R (latticeBox a b) ω) {M : ℝ} (hRbd : ∀ B ω, R B ω ≤ M * B.card)
    (u : Site d) (J N : ℕ) : Integrable (R (dyBig u J N)) μ := by
  have hab : dyBig u J N = latticeBox (u - fun _ => 2 * (2 ^ J : ℤ))
      (fun i => (u i - 2 * (2 ^ J : ℤ)) + (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℤ) - 1) := by
    rw [dyBig, map_addRight_latticeCube_eq_latticeBox]
    congr 1
  refine Integrable.of_bound (hRm _).aestronglyMeasurable (M * (dyBig u J N).card) ?_
  filter_upwards with ω
  have h1 : 0 ≤ R (dyBig u J N) ω := by
    rw [hab]
    exact hRnn _ _ ω
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact hRbd _ ω

/-- The integral of the sum of `R (dyBig u J N)` over offsets `u` in the cube of side `2 ^ J` is at
most `(2 ^ J) ^ d` times `ρ` times the volume of `dyBig`. -/
theorem integral_sum_apply_dyBig_le {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (R : Finset (Site d) → Ω → ℝ) (hRm : ∀ B, Measurable (R B))
    (hRstat : ∀ (B : Finset (Site d)) (z : Site d) (ω : Ω),
      R (B.map (Equiv.addRight z).toEmbedding) ω = R B (τ z ω))
    (hRnn : ∀ a b ω, 0 ≤ R (latticeBox a b) ω) {M : ℝ} (hRbd : ∀ B ω, R B ω ≤ M * B.card)
    {ρ : ℝ} (hρ : ∀ N : ℕ, 1 ≤ N → ∫ ω, R (latticeCube d N) ω ∂μ ≤ ρ * (N : ℝ) ^ d)
    (J N : ℕ) :
    ∫ ω, (∑ u ∈ latticeCube d (2 ^ J), R (dyBig u J N) ω) ∂μ ≤
      ((2 ^ J : ℕ) : ℝ) ^ d * (ρ * (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d) := by
  rw [integral_finsetSum _ (fun u _ => integrable_apply_dyBig R hRm hRnn hRbd u J N)]
  have h1 : ∑ u ∈ latticeCube d (2 ^ J), ∫ ω, R (dyBig u J N) ω ∂μ ≤
      ∑ _u ∈ latticeCube d (2 ^ J), ρ * (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d :=
    Finset.sum_le_sum (fun u _ => integral_apply_dyBig_le_mul_pow τ hτ R hRm hRstat hρ u J N)
  rw [Finset.sum_const, card_latticeCube_eq_pow', nsmul_eq_mul] at h1
  simpa only [Nat.cast_pow] using h1

/-- Real-algebra step combining two averaged bounds into `X ≤ c * ρ * (Nd' / Nd)`. -/
theorem le_mul_div_of_le_mul_div_and_le {X c S P Nd Nd' ρ : ℝ} (hc : 0 ≤ c) (hP : 0 < P) (hN
    : 0 < Nd)
    (h1 : Nd * X ≤ c * (S / P)) (h2 : S ≤ P * (ρ * Nd')) : X ≤ c * ρ * (Nd' / Nd) := by
  have h3 : S / P ≤ ρ * Nd' := by
    rw [div_le_iff₀ hP]
    linarith
  have h4 : Nd * X ≤ c * (ρ * Nd') := le_trans h1 (mul_le_mul_of_nonneg_left h3 hc)
  have h5 : X ≤ c * (ρ * Nd') / Nd := by
    rw [le_div_iff₀ hN]
    linarith
  have h6 : c * (ρ * Nd') / Nd = c * ρ * (Nd' / Nd) := by ring
  linarith [h5, h6.le, h6.ge]

/-- Finite-`N` form of the maximal inequality: the measure of the bad event with witness `k ≤ K` is
at most `akMaxConst d / α * ρ` times the volume ratio `((N / 2^J + 4) 2^J) ^ d / N ^ d`. -/
theorem measureReal_bad_le_K_le_akMaxConst_div_mul_pow_div_pow {d : ℕ} (hd : 1 ≤ d) {μ :
    Measure Ω} [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (R : Finset (Site d) → Ω → ℝ) (hRm : ∀ B, Measurable (R B))
    (hRstat : ∀ (B : Finset (Site d)) (z : Site d) (ω : Ω),
      R (B.map (Equiv.addRight z).toEmbedding) ω = R B (τ z ω))
    (hRnn : ∀ a b ω, 0 ≤ R (latticeBox a b) ω) {M : ℝ} (hRbd : ∀ B ω, R B ω ≤ M * B.card)
    (hRsup : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → R B₁ ω + R B₂ ω ≤ R B ω)
    (hRmono : ∀ a b a' b' ω, a ≤ a' → b' ≤ b → R (latticeBox a' b') ω ≤ R (latticeBox a b) ω)
    {ρ : ℝ} (hρ : ∀ N : ℕ, 1 ≤ N → ∫ ω, R (latticeCube d N) ω ∂μ ≤ ρ * (N : ℝ) ^ d)
    {α : ℝ} (hα : 0 < α) {K J : ℕ} (hKJ : 2 * d * K ≤ 2 ^ J) {N : ℕ} (hN : 1 ≤ N) :
    μ.real {ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω} ≤
      akMaxConst d / α * ρ * ((((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d) := by
  have hEm := measurableSet_bad_le_K (d := d) R hRm α K
  have h17 := integral_sum_indicator_comp_action_eq_pow_mul_measureReal τ hτ hEm N
  have hc : 0 ≤ akMaxConst d / α := div_nonneg (akMaxConst_pos hd).le hα.le
  have hpt : ∀ ω, (∑ x ∈ latticeCube d N,
      {ω' | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω'}.indicator
        (fun _ => (1 : ℝ)) (τ x ω)) ≤
      akMaxConst d / α * ((∑ u ∈ latticeCube d (2 ^ J), R (dyBig u J N) ω) /
        ((2 ^ J : ℕ) : ℝ) ^ d) := by
    intro ω
    rw [← card_filter_bad_eq_sum_indicator_comp_action τ R hRstat α K N ω]
    exact card_filter_bad_le_akMaxConst_mul_avg_dyBig hd (fun B => R B ω) (fun a b => hRnn a b ω)
      (fun B B₁ B₂ h => hRsup B B₁ B₂ ω h) (fun a b a' b' ha hb => hRmono a b a' b' ω ha hb) hα hKJ
          N
  have hint1 : Integrable (fun ω => ∑ x ∈ latticeCube d N,
      {ω' | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω'}.indicator
        (fun _ => (1 : ℝ)) (τ x ω)) μ :=
    integrable_finsetSum _ (fun x _ => integrable_indicator_comp_action τ hτ hEm x)
  have hint2 : Integrable (fun ω => akMaxConst d / α *
      ((∑ u ∈ latticeCube d (2 ^ J), R (dyBig u J N) ω) / ((2 ^ J : ℕ) : ℝ) ^ d)) μ :=
    ((integrable_finsetSum _ (fun u _ =>
      integrable_apply_dyBig R hRm hRnn hRbd u J N)).div_const _).const_mul _
  have hmono := integral_mono hint1 hint2 hpt
  rw [h17, integral_const_mul, integral_div] at hmono
  have hNpos : (0 : ℝ) < (N : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr (by omega)) d
  exact le_mul_div_of_le_mul_div_and_le hc (by positivity) hNpos hmono
    (integral_sum_apply_dyBig_le τ hτ R hRm hRstat hRnn hRbd hρ J N)

/-- `N ≥ 1` casts to a positive real. -/
theorem cast_pos_of_one_le {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : (0 : ℕ) < N)

/-- `N ≤ (N / 2 ^ J + 4) * 2 ^ J`. -/
theorem le_div_add_four_mul_pow_two {J N : ℕ} : N ≤ (N / 2 ^ J + 4) * 2 ^ J := by
    rw [Nat.add_mul]; exact le_trans (le_of_lt (Nat.lt_div_mul_add (b := 2 ^ J) (pow_pos (by
        norm_num) J))) (Nat.add_le_add_left (Nat.le_mul_of_pos_left (n := 4) (2 ^ J) (by
            norm_num)) _)

/-- `(N / 2 ^ J + 4) * 2 ^ J ≤ N + 4 * 2 ^ J`. -/
theorem mul_pow_two_le_add_four_mul_pow_two {J N : ℕ} : (N / 2 ^ J + 4) * 2 ^ J ≤ N + 4 * 2
    ^ J := by
    rw [Nat.add_mul]; exact Nat.add_le_add_right (Nat.div_mul_le_self N (2 ^ J)) (4 * 2 ^ J)

/-- `((N + 4 * 2 ^ J : ℕ) : ℝ) = N + 4 * 2 ^ J` after casting. -/
theorem cast_add_four_mul_pow_two_eq {J N : ℕ} : ((N + 4 * 2 ^ J : ℕ) : ℝ) = (N : ℝ) + 4 *
    ((2 ^ J : ℕ) : ℝ) := by
    push_cast; ring

/-- `1 ≤ ((N / 2^J + 4) * 2^J) ^ d / N ^ d`, from the lower bound `le_div_add_four_mul_pow_two`. -/
theorem one_le_pow_div_pow_of_le {d J N : ℕ} (hN : 1 ≤ N) : (1 : ℝ) ≤ (((N / 2 ^ J + 4) * 2
    ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d := (le_div_iff₀ (pow_pos (cast_pos_of_one_le hN) d)).mpr (by
    rw [one_mul]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by
        exact_mod_cast le_div_add_four_mul_pow_two (J := J) (N := N)) d)

/-- `(N + 4 * 2 ^ J) / N = 1 + 4 * 2 ^ J / N`. -/
theorem add_four_mul_pow_two_div_eq {J N : ℕ} (hN : 1 ≤ N) : ((N + 4 * 2 ^ J : ℕ) : ℝ) / (N
    : ℝ) = 1 + 4 * ((2 ^ J : ℕ) : ℝ) / (N : ℝ) := by
    rw [cast_add_four_mul_pow_two_eq (J := J) (N := N), add_div, div_self (ne_of_gt
        (cast_pos_of_one_le hN))]

/-- `((N / 2^J + 4) * 2^J) ^ d / N ^ d ≤ ((N + 4 * 2^J) / N) ^ d`, from the upper bound
`mul_pow_two_le_add_four_mul_pow_two`. -/
theorem pow_div_pow_le_pow_add_four_mul_pow_two_div {d J N : ℕ} (hN : 1 ≤ N) : (((N / 2 ^ J
    + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d ≤ (((N + 4 * 2 ^ J : ℕ) : ℝ) / (N : ℝ)) ^ d := by
    rw [div_pow]; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (by
        exact_mod_cast mul_pow_two_le_add_four_mul_pow_two (J := J) (N := N)) d) (pow_nonneg
            (cast_pos_of_one_le hN).le d)

/-- `((N / 2^J + 4) * 2^J) ^ d / N ^ d ≤ (1 + 4 * 2^J / N) ^ d`. -/
theorem pow_div_pow_le_one_add_four_mul_pow_two_div_pow {d J N : ℕ} (hN : 1 ≤ N) : (((N / 2
    ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d ≤ (1 + 4 * ((2 ^ J : ℕ) : ℝ) / (N : ℝ)) ^ d := by
    have h := pow_div_pow_le_pow_add_four_mul_pow_two_div (d := d) (J := J) (N := N) hN; rwa
        [add_four_mul_pow_two_div_eq hN] at h

/-- `(1 + 4 * 2 ^ J / N) ^ d → 1` as `N → ∞`. -/
theorem tendsto_one_add_four_mul_pow_two_div_pow_one {d J : ℕ} : Tendsto (fun N : ℕ => (1 +
    4 * ((2 ^ J : ℕ) : ℝ) / (N : ℝ)) ^ d) atTop (𝓝 1) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (4 * ((2 ^ J : ℕ) : ℝ))).const_add 1).pow d

/-- Eventually in `N`, `1 ≤ ((N / 2^J + 4) * 2^J) ^ d / N ^ d`. -/
theorem eventually_one_le_pow_div_pow {d J : ℕ} : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (((N / 2 ^ J
    + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d := eventually_atTop.mpr ⟨1, fun N hN =>
        one_le_pow_div_pow_of_le (d := d) (J := J) (N := N) hN⟩

/-- Eventually in `N`, `((N / 2^J + 4) * 2^J) ^ d / N ^ d ≤ (1 + 4 * 2^J / N) ^ d`. -/
theorem eventually_pow_div_pow_le_pow {d J : ℕ} : ∀ᶠ N : ℕ in atTop, (((N / 2 ^ J + 4) * 2 ^
    J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d ≤ (1 + 4 * ((2 ^ J : ℕ) : ℝ) / (N : ℝ)) ^ d :=
        eventually_atTop.mpr ⟨1, fun N hN => pow_div_pow_le_one_add_four_mul_pow_two_div_pow (d :=
            d) (J := J) (N := N) hN⟩

/-- The volume ratio `((N / 2 ^ J + 4) * 2 ^ J) ^ d / N ^ d` tends to `1` as `N → ∞`, squeezed
between `1` and `tendsto_one_add_four_mul_pow_two_div_pow_one`'s bound. -/
theorem tendsto_pow_dyBig_volume_div_pow_one (d J : ℕ) :
    Tendsto (fun N : ℕ => ((((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d)) atTop (𝓝 1) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_one_add_four_mul_pow_two_div_pow_one (d := d) (J := J))
          (eventually_one_le_pow_div_pow (d := d) (J := J)) (eventually_pow_div_pow_le_pow (d := d)
              (J := J))


/-- The maximal inequality: `μ.real {ω | ∃ k ≥ 1, α k ^ d < R (cube k) ω} ≤ akMaxConst d * ρ / α`.
-/
theorem measureReal_exists_heavy_le_akMaxConst_mul_div {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (R : Finset (Site d) → Ω → ℝ) (hRm : ∀ B, Measurable (R B))
    (hRstat : ∀ (B : Finset (Site d)) (z : Site d) (ω : Ω),
      R (B.map (Equiv.addRight z).toEmbedding) ω = R B (τ z ω))
    (hRnn : ∀ a b ω, 0 ≤ R (latticeBox a b) ω) {M : ℝ} (hRbd : ∀ B ω, R B ω ≤ M * B.card)
    (hRsup : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → R B₁ ω + R B₂ ω ≤ R B ω)
    (hRmono : ∀ a b a' b' ω, a ≤ a' → b' ≤ b → R (latticeBox a' b') ω ≤ R (latticeBox a b) ω)
    {ρ : ℝ} (hρ : ∀ N : ℕ, 1 ≤ N → ∫ ω, R (latticeCube d N) ω ∂μ ≤ ρ * (N : ℝ) ^ d)
    {α : ℝ} (hα : 0 < α) :
    μ.real {ω | ∃ k : ℕ, 1 ≤ k ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω} ≤
      akMaxConst d * ρ / α := by
  have hset : ({ω : Ω | ∃ k : ℕ, 1 ≤ k ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω} : Set Ω) =
      ⋃ K, {ω : Ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω} :=
    Set.ext fun ω => by
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk1, hk⟩
        exact ⟨k, ⟨k, hk1, le_rfl, hk⟩⟩
      · rintro ⟨K, k, hk1, -, hk⟩
        exact ⟨k, hk1, hk⟩
  rw [hset]
  refine measureReal_iUnion_le_of_le (S := fun K => {ω : Ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
      α * (k : ℝ) ^ d < R (latticeCube d k) ω}) (monotone_nat_of_le_succ fun K => ?_) ?_
  · intro ω hω
    obtain ⟨k, hk1, hkK, hk⟩ := hω
    exact ⟨k, hk1, Nat.le_succ_of_le hkK, hk⟩
  · intro K
    have h' : μ.real {ω : Ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < R (latticeCube d k) ω} ≤ (akMaxConst d / α * ρ) * 1 :=
      ge_of_tendsto ((tendsto_pow_dyBig_volume_div_pow_one d (2 * d * K)).const_mul (akMaxConst d /
          α * ρ))
        (Filter.eventually_atTop.2 ⟨1, fun N hN =>
            measureReal_bad_le_K_le_akMaxConst_div_mul_pow_div_pow hd τ hτ R hRm hRstat hRnn
          hRbd hRsup hRmono hρ hα (le_of_lt Nat.lt_two_pow_self) hN⟩)
    rwa [mul_one, div_mul_eq_mul_div] at h'

end LatticeProb
