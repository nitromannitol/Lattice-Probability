import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityPartition

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# The maximal inequality: random-offset covering (Step 4, part B, the covering step)

At least half of the `(2 ^ J) ^ d` offsets `u` of a grid of side `2 ^ J` place a witness cube of
side `k` at a bad site inside a single dyadic cell of side `2 ^ j ∈ [2 d k, 4 d k)`; such a cell is
then heavy, since a bad cube inside a cell of comparable side makes the cell's normalised value
exceed a fixed fraction of `α`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- One-coordinate dyadic covering: if `(x - u) mod L ≤ L - k` there is a cell index `c` with `u +
Lc ≤ x` and `x + k - 1 ≤ u + Lc + L - 1`. -/
theorem exists_dyadic_index_of_mod_le (x u L k : ℤ) (hL : 0 < L) (h : (x - u) % L ≤ L - k) :
    ∃ c : ℤ, u + L * c ≤ x ∧ x + (k - 1) ≤ u + L * c + (L - 1) := by
  refine ⟨(x - u) / L, ?_, ?_⟩
  · have h1 := Int.mul_ediv_add_emod (x - u) L
    have h2 := Int.emod_nonneg (x - u) hL.ne'
    linarith
  · have h1 := Int.mul_ediv_add_emod (x - u) L
    linarith

/-- If every coordinate satisfies the containment inequalities, the translated cube of side `k` at
`x` is contained in the dyadic cell of level `j`, offset `u`, index `c`. -/
theorem map_addRight_cube_subset_dyCell_of_forall {d : ℕ} (x u c : Site d) (j k : ℕ)
    (h : ∀ i, u i + 2 ^ j * c i ≤ x i ∧ x i + (k : ℤ) - 1 ≤ u i + 2 ^ j * c i + (2 ^ j - 1)) :
    (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c := by
  intro y hy
  rw [map_addRight_latticeCube_eq_latticeBox, mem_latticeBox_iff] at hy
  rw [dyCell, mem_latticeBox_iff]
  intro i
  have h1 := hy i
  have h2 := h i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  constructor <;> linarith

/-- If every coordinate of `x - u` satisfies the modular bound, there is a cell index `c` with the
translated cube at `x` contained in the level-`j` cell of offset `u`. -/
theorem exists_dyCell_containing_map_addRight_cube {d : ℕ} (x u : Site d) {j k : ℕ}
    (h : ∀ i, (x i - u i) % 2 ^ j ≤ 2 ^ j - (k : ℤ)) :
    ∃ c, (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c := by
  choose c hc using fun i => exists_dyadic_index_of_mod_le (x i) (u i) (2 ^ j) k (by
      positivity) (h i)
  exact ⟨c, map_addRight_cube_subset_dyCell_of_forall x u c j k fun i => ⟨(hc i).1, by
      linarith [(hc i).2]⟩⟩

/-- The offsets `u` in the cube of side `n` satisfying the coordinatewise modular condition form a
product set, one interval-filter per coordinate. -/
theorem filter_latticeCube_eq_piFinset_filter {d : ℕ} (x : Site d) (j k n : ℕ) :
    (latticeCube d n).filter (fun u => ∀ i, (x i - u i) % 2 ^ j ≤ 2 ^ j - (k : ℤ)) =
      Fintype.piFinset (fun i => (Finset.Icc (0 : ℤ) ((n : ℤ) - 1)).filter
        (fun v => (x i - v) % 2 ^ j ≤ 2 ^ j - (k : ℤ))) := by
  ext u
  simp only [Finset.mem_filter, Fintype.mem_piFinset, latticeCube, Finset.mem_Icc, Pi.le_def,
    Pi.zero_apply]
  constructor
  · rintro ⟨hu, hc⟩ i
    exact ⟨⟨hu.1 i, hu.2 i⟩, hc i⟩
  · intro h
    exact ⟨⟨fun i => (h i).1.1, fun i => (h i).1.2⟩, fun i => (h i).2⟩

/-- Shifting the offset by a multiple of `L` does not change `(y - v) mod L`. -/
theorem sub_add_mul_emod_eq (y v L q : ℤ) : (y - (v + L * q)) % L = (y - v) % L := by
  have h : y - (v + L * q) = (y - v) + L * (-q) := by ring
  rw [h, Int.add_mul_emod_self_left]

/-- The count of `v` in a shifted length-`L` interval with `(y - v) mod L ≤ t` equals the same count
over `[0, L)`. -/
theorem card_filter_Ico_shift_eq (y L t q : ℤ) (_unused_hL : 0 < L) :
    ((Finset.Ico (L * q) (L * q + L)).filter (fun v => (y - v) % L ≤ t)).card =
      ((Finset.Ico 0 L).filter (fun v => (y - v) % L ≤ t)).card := by
  refine Finset.card_bij (fun v _ => v - L * q) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h : y - (a - L * q) = (y - a) + L * q := by ring
    rw [h, Int.add_mul_emod_self_left]
    exact ha.2
  · intro a₁ ha₁ a₂ ha₂ h
    omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Ico] at hb
    refine ⟨b + L * q, ?_, by ring⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h : y - (b + L * q) = (y - b) + L * (-q) := by ring
    rw [h, Int.add_mul_emod_self_left]
    exact hb.2

/-- The count of `v ∈ [0, Lm)` with `(y - v) mod L ≤ t` is `m` times the count over `[0, L)`, by
induction on `m` and the shift invariance `card_filter_Ico_shift_eq`. -/
theorem card_filter_Ico_mul_eq_mul_card_filter_Ico (y L t : ℤ) (hL : 0 < L) (m : ℕ) :
    ((Finset.Ico 0 (L * m)).filter (fun v => (y - v) % L ≤ t)).card =
      m * ((Finset.Ico 0 L).filter (fun v => (y - v) % L ≤ t)).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hLm : (0:ℤ) ≤ L * ↑m := by positivity
    have hsplit : Finset.Ico 0 (L * ↑(m+1)) = Finset.Ico 0 (L * ↑m) ∪ Finset.Ico (L * ↑m) (L * ↑m +
        L) := by
      have h : L * ↑(m+1) = L * ↑m + L := by push_cast; ring
      rw [h]
      exact (Finset.Ico_union_Ico_eq_Ico hLm (by linarith)).symm
    have hdisj' : Disjoint ((Finset.Ico 0 (L * ↑m)).filter (fun v => (y - v) % L ≤ t))
                           ((Finset.Ico (L * ↑m) (L * ↑m + L)).filter (fun v => (y - v) % L ≤ t)) :=
                               by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [Finset.mem_filter, Finset.mem_Ico] at hv1 hv2
      linarith
    have hshift : ((Finset.Ico (L * ↑m) (L * ↑m + L)).filter (fun v => (y - v) % L ≤ t)).card =
                  ((Finset.Ico 0 L).filter (fun v => (y - v) % L ≤ t)).card := by
      apply Finset.card_bij (fun v _ => v - L * ↑m)
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_Ico] at hv ⊢
        obtain ⟨⟨h1, h2⟩, h3⟩ := hv
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        have heq : y - (v - L * ↑m) = (y - v) + L * ↑m := by ring
        rw [heq, Int.add_mul_emod_self_left]
        exact h3
      · intro v1 hv1 v2 hv2 heq
        simp only [Finset.mem_filter, Finset.mem_Ico] at hv1 hv2
        linarith
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_Ico] at hw
        obtain ⟨⟨h1, h2⟩, h3⟩ := hw
        refine ⟨w + L * ↑m, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by linarith, by linarith⟩, ?_⟩
          have heq : y - (w + L * ↑m) = (y - w) + L * (-(↑m)) := by ring
          rw [heq, Int.add_mul_emod_self_left]
          exact h3
        · ring
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj']
    rw [ih, hshift]
    ring

/-- `v ↦ (y - v) mod L` is an involution on `[0, L)`. -/
theorem sub_mod_mod_eq_self (y v L : ℤ) (_unused_hL : 0 < L) (hv0 : 0 ≤ v) (hvL : v < L) :
    (y - (y - v) % L) % L = v := by
  have h : y - (y - v) % L = (y - v) - (y - v) % L + v := by ring
  rw [h]
  have h1 : ((y - v) - (y - v) % L) % L = 0 := by
    rw [Int.sub_emod, Int.emod_emod]
    simp
  rw [Int.add_emod, h1]
  simp [Int.emod_eq_of_lt (a := v) (b := L) hv0 hvL]

/-- The count of `v ∈ [0, L)` with `(y - v) mod L ≤ t` equals the count of `r ∈ [0, L)` with `r ≤
t`, via the involution `sub_mod_mod_eq_self`. -/
theorem card_filter_Ico_mod_eq_card_filter_Ico (y L t : ℤ) (hL : 0 < L) :
    ((Finset.Ico 0 L).filter (fun v => (y - v) % L ≤ t)).card =
      ((Finset.Ico 0 L).filter (fun r => r ≤ t)).card := by
  refine Finset.card_bij (fun v _ => (y - v) % L) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_Ico] at hv ⊢
    exact ⟨⟨Int.emod_nonneg _ hL.ne', Int.emod_lt_of_pos _ hL⟩, hv.2⟩
  · intro v₁ hv₁ v₂ hv₂ h
    simp only [Finset.mem_filter, Finset.mem_Ico] at hv₁ hv₂
    have hsub : (v₂ - v₁) % L = 0 := by
      have h1 := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp h
      have h2 : y - v₁ - (y - v₂) = v₂ - v₁ := by ring
      rwa [h2] at h1
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hsub
    have hk' : v₂ - v₁ = L * k := hk
    have hk0 : k = 0 := by
      have hlt : |L * k| < L := by
        rw [← hk']
        rw [abs_lt]
        constructor <;> omega
      have hk1 : |k| < 1 := by
        rw [abs_mul, abs_of_pos hL] at hlt
        nlinarith [abs_nonneg k]
      rw [abs_lt] at hk1
      omega
    rw [hk0, mul_zero] at hk'
    omega
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Ico] at hr
    have hr0 : 0 ≤ r := hr.1.1
    have hrL : r < L := hr.1.2
    have hrt : r ≤ t := hr.2
    have heq : (y - (y - r) % L) % L = r := by
      have h1 : y - (y - r) % L = (y - r) - (y - r) % L + r := by ring
      rw [h1]
      have h2 : ((y - r) - (y - r) % L) % L = 0 := by
        rw [Int.sub_emod, Int.emod_emod]
        simp
      rw [Int.add_emod, h2, Int.zero_add, Int.emod_emod]
      exact Int.emod_eq_of_lt hr0 hrL
    refine ⟨(y - r) % L, ?_, heq⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Int.emod_nonneg _ hL.ne', Int.emod_lt_of_pos _ hL⟩, by rw [heq]; exact hrt⟩

/-- For `0 ≤ t < L`, the count of `r ∈ [0, L)` with `r ≤ t` is `(t + 1).toNat`. -/
theorem card_filter_Ico_le_eq_toNat_add_one (L t : ℤ) (_unused_h0 : 0 ≤ t) (ht : t < L) :
    ((Finset.Ico 0 L).filter (fun r => r ≤ t)).card = (t + 1).toNat := by
  have h : (Finset.Ico 0 L).filter (fun r => r ≤ t) = Finset.Ico 0 (t + 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [h, Int.card_Ico]
  simp

/-- `Icc 0 (n - 1) = Ico 0 n` for integers. -/
theorem Icc_zero_sub_one_eq_Ico (n : ℤ) : Finset.Icc (0 : ℤ) (n - 1) = Finset.Ico 0 n := by
  ext v
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- The count of offsets `v` in `[0, 2 ^ J)` with `(y - v) mod 2 ^ j ≤ 2 ^ j - k` is `2 ^ (J - j) *
(2 ^ j - k + 1)`. -/
theorem card_filter_mod_le_eq_mul (y : ℤ) {k j J : ℕ} (hk : 1 ≤ k) (hkj : k ≤ 2 ^ j) (hjJ :
    j ≤ J) :
    ((Finset.Icc (0 : ℤ) (((2 ^ J : ℕ) : ℤ) - 1)).filter
      (fun v => (y - v) % 2 ^ j ≤ 2 ^ j - (k : ℤ))).card = 2 ^ (J - j) * (2 ^ j - k + 1) := by
  have hL : (0 : ℤ) < 2 ^ j := by positivity
  have hkj' : (k : ℤ) ≤ 2 ^ j := by exact_mod_cast hkj
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hJ : ((2 ^ J : ℕ) : ℤ) = 2 ^ j * ((2 ^ (J - j) : ℕ) : ℤ) := by
    push_cast; rw [← pow_add, Nat.add_sub_cancel' hjJ]
  rw [Icc_zero_sub_one_eq_Ico, hJ, card_filter_Ico_mul_eq_mul_card_filter_Ico y _ _ hL,
      card_filter_Ico_mod_eq_card_filter_Ico y _ _ hL,
    card_filter_Ico_le_eq_toNat_add_one _ _ (by linarith) (by linarith)]
  congr 1
  have e : (2 : ℤ) ^ j - k + 1 = ((2 ^ j - k + 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub hkj]; ring
  rw [e, Int.toNat_natCast]

/-- A Bernoulli-type bound: if `d * a ≥ -1/2` and `a ≥ -1`, then `(1 + a) ^ d ≥ 1/2`. -/
theorem half_le_one_add_pow_of_mul_ge (d : ℕ) {a : ℝ} (ha : -1 ≤ a) (h : -1 / 2 ≤ (d : ℝ) *
    a) :
    1 / 2 ≤ (1 + a) ^ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    norm_num
  · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have h2 : (1 : ℝ) + (d : ℝ) * a ≤ (1 + a) ^ d := by
      have := one_add_mul_le_pow (a := a) (n := d) (by linarith)
      simpa using this
    have h3 : (1 : ℝ) / 2 ≤ 1 + (d : ℝ) * a := by linarith
    linarith

/-- If `2 d (A - B) ≤ A` with `0 < A`, `0 ≤ B`, then `A ^ d ≤ 2 B ^ d`. -/
theorem pow_le_two_mul_pow_of_le (d : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (h : 2 * (d : ℝ) * (A - B) ≤ A) : A ^ d ≤ 2 * B ^ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    norm_num
  · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hBpos : 0 < B := by
      by_contra hcon
      push Not at hcon
      have hzero : B = 0 := le_antisymm hcon hB
      subst hzero
      have h1 : 2 * (d : ℝ) * A ≤ A := by simpa using h
      have h4 : 2 * (d : ℝ) ≤ 1 := by
        have h5 : 2 * (d : ℝ) * A ≤ 1 * A := by linarith [h1]
        exact le_of_mul_le_mul_right h5 hA
      have h6 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have ha : -1 ≤ B / A - 1 := by
      have : 0 ≤ B / A := div_nonneg hB hA.le
      linarith
    have hda : -1 / 2 ≤ (d : ℝ) * (B / A - 1) := by
      have h2 : (d : ℝ) * (B / A - 1) = ((d : ℝ) * B - (d : ℝ) * A) / A := by
        field_simp
      rw [h2, le_div_iff₀ hA]
      nlinarith
    have h13 := half_le_one_add_pow_of_mul_ge d ha hda
    have hBA : (1 : ℝ) + (B / A - 1) = B / A := by ring
    rw [hBA] at h13
    rw [div_pow] at h13
    rw [le_div_iff₀ (pow_pos hA d)] at h13
    linarith

/-- If `2 d k ≤ 2 ^ j` with `j ≤ J`, `k ≥ 1`, then `(2 ^ J) ^ d ≤ 2 (2 ^ (J-j) (2^j - k + 1)) ^ d`.
-/
theorem pow_le_two_mul_pow_of_mul_le {d k j J : ℕ} (hk : 1 ≤ k) (hjJ : j ≤ J) (hkj : 2 * d *
    k ≤ 2 ^ j) :
    ((2 ^ J : ℕ) : ℝ) ^ d ≤ 2 * ((2 ^ (J - j) * (2 ^ j - k + 1) : ℕ) : ℝ) ^ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    norm_num
  · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hkj' : k ≤ 2 ^ j := by
      have : k ≤ 2 * d * k := by nlinarith [hd]
      omega
    have hJ : ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ (J - j) * 2 ^ j := by
      push_cast
      rw [← pow_add, Nat.sub_add_cancel hjJ]
    have hB : ((2 ^ (J - j) * (2 ^ j - k + 1) : ℕ) : ℝ)
        = (2 : ℝ) ^ (J - j) * ((2 : ℝ) ^ j - k + 1) := by
      push_cast [Nat.cast_sub hkj']
      ring
    rw [hJ, hB]
    have hA : (0 : ℝ) < (2 : ℝ) ^ (J - j) * 2 ^ j := by positivity
    have hBnn : (0 : ℝ) ≤ (2 : ℝ) ^ (J - j) * ((2 : ℝ) ^ j - k + 1) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ j - k + 1 := by
        have hkR : (k : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hkj'
        linarith
      positivity
    have hmain : 2 * (d : ℝ) * ((2 : ℝ) ^ (J - j) * 2 ^ j
        - (2 : ℝ) ^ (J - j) * ((2 : ℝ) ^ j - k + 1))
        ≤ (2 : ℝ) ^ (J - j) * 2 ^ j := by
      have hdiff : (2 : ℝ) ^ (J - j) * 2 ^ j
          - (2 : ℝ) ^ (J - j) * ((2 : ℝ) ^ j - k + 1)
          = (2 : ℝ) ^ (J - j) * ((k : ℝ) - 1) := by ring
      rw [hdiff]
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have h2 : 2 * (d : ℝ) * ((k : ℝ) - 1) ≤ (2 : ℝ) ^ j := by
        have h3 : (2 : ℝ) * (d : ℝ) * (k : ℝ) ≤ (2 : ℝ) ^ j := by
          have h4 : ((2 * d * k : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hkj
          push_cast at h4
          linarith
        nlinarith [h3, hkR, hdR]
      have h4 : (2 : ℝ) ^ (J - j) * (2 * (d : ℝ) * ((k : ℝ) - 1))
          ≤ (2 : ℝ) ^ (J - j) * (2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith [h4]
    have := pow_le_two_mul_pow_of_le d hA hBnn hmain
    linarith [this]

open Classical in
/-- At least half of the `(2 ^ J) ^ d` offsets `u` in the cube of side `2 ^ J` place the cube of
side `k` at `x` inside a single level-`j` cell, when `2 d k ≤ 2 ^ j ≤ 2 ^ J`. -/
theorem pow_le_two_mul_card_filter_dyCell {d : ℕ} (x : Site d) {k j J : ℕ} (hk : 1 ≤ k) (hjJ
    : j ≤ J)
    (hkj : 2 * d * k ≤ 2 ^ j) :
    ((2 ^ J : ℕ) : ℝ) ^ d ≤
      2 * (((latticeCube d (2 ^ J)).filter fun u =>
        ∃ c, (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c).card : ℝ) := by
  have hsubset : (latticeCube d (2 ^ J)).filter
        (fun u => ∀ i, (x i - u i) % 2 ^ j ≤ 2 ^ j - (k : ℤ)) ⊆
      (latticeCube d (2 ^ J)).filter (fun u => ∃ c, (latticeCube d k).map (Equiv.addRight
          x).toEmbedding ⊆ dyCell u j c) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
    exact Finset.mem_filter.2 ⟨hu1, exists_dyCell_containing_map_addRight_cube x u hu2⟩
  have hmono := Finset.card_le_card hsubset
  rw [filter_latticeCube_eq_piFinset_filter x j k (2 ^ J), Fintype.card_piFinset] at hmono
  have hcount : ∀ i : Fin d, ((Finset.Icc (0 : ℤ) (((2 ^ J : ℕ) : ℤ) - 1)).filter
      (fun v => (x i - v) % 2 ^ j ≤ 2 ^ j - (k : ℤ))).card = 2 ^ (J - j) * (2 ^ j - k + 1) :=
    fun i => card_filter_mod_le_eq_mul (x i) hk (le_trans (by have := i.pos; nlinarith) hkj) hjJ
  simp only [hcount, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hmono
  have hX : (((2 ^ (J - j) * (2 ^ j - k + 1) : ℕ) : ℝ)) ^ d ≤
      (((latticeCube d (2 ^ J)).filter fun u => ∃ c, (latticeCube d k).map (Equiv.addRight
          x).toEmbedding ⊆ dyCell u j c).card : ℝ) := by
    exact_mod_cast hmono
  linarith [pow_le_two_mul_pow_of_mul_le (d := d) hk hjJ hkj]

/-- For a box-monotone `r`, if the translated cube at `x` is contained in a dyadic cell, `r` of the
cube is at most `r` of the cell. -/
theorem apply_map_addRight_cube_le_apply_dyCell_of_mono {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrmono : ∀ a b a' b', a ≤ a' → b' ≤ b → r (latticeBox a' b') ≤ r (latticeBox a b))
    (x : Site d) {k j : ℕ} (hk : 1 ≤ k) (u c : Site d)
    (hsub : (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c) :
    r ((latticeCube d k).map (Equiv.addRight x).toEmbedding) ≤ r (dyCell u j c) := by
  have hcube : (latticeCube d k).map (Equiv.addRight x).toEmbedding =
      latticeBox x (fun i => x i + (k : ℤ) - 1) := map_addRight_latticeCube_eq_latticeBox d k x
  have hcell : dyCell u j c = latticeBox (fun l => u l + 2 ^ j * c l)
      (fun l => u l + 2 ^ j * c l + 2 ^ j - 1) := by
    rw [dyCell]
    congr 1 <;> funext l <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [hcube, hcell]
  refine hrmono _ _ _ _ ?_ ?_
  · rw [hcell] at hsub
    rw [hcube] at hsub
    have hmem : x ∈ latticeBox x (fun i => x i + (k : ℤ) - 1) := by
      rw [mem_latticeBox_iff]
      intro i
      constructor <;> omega
    have h1 := hsub hmem
    rw [mem_latticeBox_iff] at h1
    intro i
    exact (h1 i).1
  · rw [hcell] at hsub
    rw [hcube] at hsub
    have hmem : (fun i => x i + (k : ℤ) - 1) ∈ latticeBox x (fun i => x i + (k : ℤ) - 1) := by
      rw [mem_latticeBox_iff]
      intro i
      constructor <;> omega
    have h1 := hsub hmem
    rw [mem_latticeBox_iff] at h1
    intro i
    exact (h1 i).2

/-- Real-algebra bound: if `P ≤ D k` and `α k ^ d < R ≤ R'`, then `α / D ^ d * P ^ d ≤ R'`. -/
theorem mul_pow_le_of_le_mul_and_lt (d : ℕ) {α D k P R R' : ℝ} (hα : 0 ≤ α) (hD : 0 < D)
    (hP0 : 0 ≤ P)
    (hP : P ≤ D * k) (hbad : α * k ^ d < R) (hRR : R ≤ R') : α / D ^ d * P ^ d ≤ R' := by
  have h1 : P ^ d ≤ (D * k) ^ d := pow_le_pow_left₀ hP0 hP d
  have h2 : α / D ^ d * (D * k) ^ d = α * k ^ d := by
    rw [mul_pow]
    field_simp
  have h3 : α / D ^ d * P ^ d ≤ α / D ^ d * (D * k) ^ d :=
    mul_le_mul_of_nonneg_left h1 (div_nonneg hα (pow_nonneg hD.le d))
  linarith [h3, h2.le, h2.ge, hbad, hRR]

/-- If a cube of side `k` with `r`-value exceeding `α k ^ d` sits inside a cell of side `2 ^ j < 4 d
k`, that cell is heavy: `α / (4d) ^ d` times its cardinality is at most `r` of the cell. -/
theorem heavy_dyCell_of_heavy_cube {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrmono : ∀ a b a' b', a ≤ a' → b' ≤ b → r (latticeBox a' b') ≤ r (latticeBox a b))
    (x : Site d) {k j : ℕ} (hk : 1 ≤ k) (hj : 2 ^ j < 4 * d * k) (u c : Site d)
    (hsub : (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c)
    {α : ℝ} (hα : 0 < α)
    (hbad : α * (k : ℝ) ^ d < r ((latticeCube d k).map (Equiv.addRight x).toEmbedding)) :
    α / (4 * (d : ℝ)) ^ d * ((dyCell u j c).card : ℝ) ≤ r (dyCell u j c) := by
  rw [card_dyCell_eq_pow u j c]
  have hD : (0 : ℝ) < 4 * (d : ℝ) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hP : (2 : ℝ) ^ j ≤ 4 * (d : ℝ) * (k : ℝ) := by exact_mod_cast hj.le
  have h := mul_pow_le_of_le_mul_and_lt d hα.le hD (by positivity) hP hbad
    (apply_map_addRight_cube_le_apply_dyCell_of_mono r hrmono x hk u c hsub)
  push_cast
  exact h

/-- If every point of `S` can be assigned a heavy cell of level `≤ J` inside `dyBig u J N`, then `β
* S.card ≤ r (dyBig u J N)`. -/
theorem mul_card_le_apply_dyBig_of_forall_sel {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (J N : ℕ)
    {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Site d)) (sel : Site d → ℕ × Site d)
    (hsel : ∀ x ∈ S, x ∈ dyCell u (sel x).1 (sel x).2 ∧ (sel x).1 ≤ J ∧
      dyCell u (sel x).1 (sel x).2 ⊆ dyBig u J N ∧
      β * ((dyCell u (sel x).1 (sel x).2).card : ℝ) ≤ r (dyCell u (sel x).1 (sel x).2)) :
    β * (S.card : ℝ) ≤ r (dyBig u J N) := by
  have hsub : (S : Finset (Site d)) ⊆ (S.image sel).biUnion (fun p => dyCell u p.1 p.2) :=
    fun x hx => Finset.mem_biUnion.2 ⟨sel x, Finset.mem_image.2 ⟨x, hx, rfl⟩, (hsel x hx).1⟩
  refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub)) hβ) ?_
  exact mul_card_biUnion_le_apply_dyBig_of_heavy hd r hrnn hrsup u J N hβ (S.image sel)
    (fun p hp => (Finset.mem_image.1 hp).elim fun x hx => hx.2 ▸ (hsel x hx.1).2.1)
    (fun p hp => (Finset.mem_image.1 hp).elim fun x hx => hx.2 ▸ (hsel x hx.1).2.2.1)
    (fun p hp => (Finset.mem_image.1 hp).elim fun x hx => hx.2 ▸ (hsel x hx.1).2.2.2)


/-- A cell of level `j ≤ J`, offset `u` in the cube of side `2 ^ J`, meeting the cube of side `N`,
is contained in `dyBig u J N`. -/
theorem dyCell_subset_dyBig_of_mem {d : ℕ} {u x c : Site d} {j J N : ℕ} (hu : u ∈
    latticeCube d (2 ^ J))
    (hjJ : j ≤ J) (hx : x ∈ latticeCube d N) (hxc : x ∈ dyCell u j c) :
    dyCell u j c ⊆ dyBig u J N := by
  have hc2 : ∀ n : ℕ, ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := fun n => (by
    rw [Nat.cast_pow]
    norm_num)
  have hL : (2 : ℤ) ^ j ≤ (2 : ℤ) ^ J :=
    pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hjJ
  have hu' : ∀ i, 0 ≤ u i ∧ u i ≤ (2 : ℤ) ^ J - 1 := (by
    intro i
    have h := (mem_latticeBox_iff (0 : Site d) (fun _ => ((2 ^ J : ℕ) : ℤ) - 1) u).1 hu i
    rw [hc2 J] at h
    simpa only [Pi.zero_apply] using h)
  have hx' : ∀ i, 0 ≤ x i ∧ x i ≤ (N : ℤ) - 1 := (by
    intro i
    simpa only [Pi.zero_apply] using
      (mem_latticeBox_iff (0 : Site d) (fun _ => (N : ℤ) - 1) x).1 hx i)
  have hxc' : ∀ i, u i + (2 : ℤ) ^ j • c i ≤ x i ∧
      x i ≤ u i + (2 : ℤ) ^ j • c i + ((2 : ℤ) ^ j - 1) := (by
    intro i
    simpa only [Pi.add_apply, Pi.smul_apply] using
      (mem_latticeBox_iff (u + (2 ^ j : ℤ) • c)
        (u + (2 ^ j : ℤ) • c + fun _ => (2 ^ j : ℤ) - 1) x).1 hxc i)
  have hcast : (((N / 2 ^ J) * 2 ^ J + 2 ^ J : ℕ) : ℤ) =
      (((N / 2 ^ J) * 2 ^ J : ℕ) : ℤ) + (2 : ℤ) ^ J := (by
    rw [Nat.cast_add, hc2 J])
  have hlt : (N : ℤ) < (((N / 2 ^ J) * 2 ^ J : ℕ) : ℤ) + (2 : ℤ) ^ J := (by
    have hnat : N < (N / 2 ^ J) * 2 ^ J + 2 ^ J :=
      Nat.lt_div_mul_add (pow_pos (by norm_num : (0 : ℕ) < 2) J)
    rw [← hcast]
    exact Int.ofNat_lt.2 hnat)
  have hK : (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℤ) =
      (((N / 2 ^ J) * 2 ^ J : ℕ) : ℤ) + 4 * (2 : ℤ) ^ J := (by
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, hc2 J]
    ring)
  have h3k : (N : ℤ) + (2 : ℤ) ^ J - 1 ≤
      (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℤ) - 2 * (2 : ℤ) ^ J := (by
    rw [hK]
    linarith)
  rw [dyBig, map_addRight_latticeCube_eq_latticeBox]
  intro y hy
  have hy' : ∀ i, u i + (2 : ℤ) ^ j • c i ≤ y i ∧
      y i ≤ u i + (2 : ℤ) ^ j • c i + ((2 : ℤ) ^ j - 1) := (by
    intro i
    simpa only [Pi.add_apply, Pi.smul_apply] using
      (mem_latticeBox_iff (u + (2 ^ j : ℤ) • c)
        (u + (2 ^ j : ℤ) • c + fun _ => (2 ^ j : ℤ) - 1) y).1 hy i)
  rw [mem_latticeBox_iff]
  intro i
  simp only [Pi.sub_apply]
  constructor
  · linarith [hy' i, hxc' i, hu' i, hx' i, hL]
  · linarith [hy' i, hxc' i, hx' i, hu' i, hL, h3k]

end LatticeProb
