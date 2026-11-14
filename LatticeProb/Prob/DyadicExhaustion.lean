import LatticeProb.Prob.DyadicCellMass
import LatticeProb.Prob.DyadicOffGrid

/-!
# Exhaustion of the plane by the dyadic squares containing a point

In the uniform dyadic system of the line (Gwynne, Miller and Sheffield, *An invariance principle
for ergodic scale-free random environments*, arXiv 1807.07515, Section 2.1) the interval of
generation `k` containing the origin is `[-o k, 2^k - o k)`, where `o k = x + ∑_{j<k} 2^j e j`
with `x` uniform on `[0, 1)` and independent fair bits `e j`. Both ends of these intervals escape
to infinity as soon as the bit sequence takes each value infinitely often, which holds almost
surely. Once the intervals at the origin exhaust the line, the interval of a large generation
containing any given point is the one containing the origin; hence, for every scale coordinate
and every point `w`, the squares of the dyadic system of the plane containing `w` exhaust the
plane. Together with the dyadic form of Lemma 2.2 of the paper cited above, this shows that the
capped square `S_m^w` of (2.1) there exists almost surely for every mass `m ∈ (0, ∞)`.

## Main statements

* `LatticeProb.DyadicOffset.ae_frequently_bitLaw`: a sequence of fair bits takes each value
  infinitely often, almost surely.
* `LatticeProb.DyadicOffset.ae_isExhaustive_offsetLaw`: almost every offset sequence is
  exhaustive (`IsExhaustive`).
* `LatticeProb.DyadicOffset.iUnion_squareAt_eq_univ`: for exhaustive offset sequences, the squares
  containing any point exhaust the plane, for every scale coordinate.
* `LatticeProb.DyadicOffset.ae_iUnion_squareAt_eq_univ`: almost surely, for every point `w`, the
  squares of the uniform dyadic system of the plane containing `w` exhaust the plane.
* `LatticeProb.DyadicOffset.ae_exists_isCappedSquare_squareAt_cellMass`: for a fixed point `w` and
  a countable locally finite cover of the plane by compact cells of positive area, almost surely
  the capped square of every mass `m ∈ (0, ∞)` around `w` exists and is a square of the chain
  at `w`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LatticeProb.DyadicOffset

/-! ### Fair bits take each value infinitely often -/

theorem bitProb_singleton (b : Bool) : bitProb {b} = 2⁻¹ := by
  cases b <;> rw [bitProb, uniformOn_univ] <;> simp

/-- The probability that `m` consecutive fair bits all equal `b` is `2^{-m}`. -/
theorem bitLaw_forall_Ico_eq (N m : ℕ) (b : Bool) :
    bitLaw {e : ℕ → Bool | ∀ j ∈ Finset.Ico N (N + m), e j = b} = 2⁻¹ ^ m := by
  have h : {e : ℕ → Bool | ∀ j ∈ Finset.Ico N (N + m), e j = b} =
      Set.pi (↑(Finset.Ico N (N + m))) fun _ => {b} := by
    ext e
    simp [Set.mem_pi]
  rw [h, bitLaw, Measure.infinitePi_pi (fun _ : ℕ => bitProb) fun _ _ => measurableSet_singleton b]
  simp [bitProb_singleton]

/-- A sequence of fair bits is constant from some index on with probability zero. -/
theorem bitLaw_forall_ge_eq (N : ℕ) (b : Bool) :
    bitLaw {e : ℕ → Bool | ∀ j, N ≤ j → e j = b} = 0 := by
  refine nonpos_iff_eq_zero.mp (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)) fun m => ?_)
  rw [← bitLaw_forall_Ico_eq N m b]
  exact measure_mono fun e he j hj => he j (Finset.mem_Ico.1 hj).1

/-- **Fair bits take each value infinitely often**, almost surely. -/
theorem ae_frequently_bitLaw : ∀ᵐ e ∂bitLaw, ∀ (b : Bool) (N : ℕ), ∃ j, N ≤ j ∧ e j = b := by
  rw [ae_all_iff]
  intro b
  rw [ae_all_iff]
  intro N
  rw [ae_iff]
  refine measure_mono_null ?_ (bitLaw_forall_ge_eq N (!b))
  intro e he
  have he' : ¬∃ j, N ≤ j ∧ e j = b := he
  show ∀ j, N ≤ j → e j = !b
  intro j hj
  have hne : e j ≠ b := fun h => he' ⟨j, hj, h⟩
  cases b <;> simpa using hne

/-! ### Exhaustive offset sequences -/

/-- The offset sequence `o` is exhaustive: both ends of the interval `[-o k, 2^k - o k)` of
generation `k` containing the origin escape to infinity. -/
def IsExhaustive (o : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → (n : ℝ) ≤ o k ∧ (n : ℝ) ≤ 2 ^ k - o k

theorem measurableSet_isExhaustive : MeasurableSet {o : ℕ → ℝ | IsExhaustive o} := by
  simp only [IsExhaustive, ofPred_forall, ofPred_exists, ofPred_and]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun K => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => ?_
  exact (measurableSet_le measurable_const (measurable_pi_apply k)).inter
    (measurableSet_le measurable_const (measurable_const.sub (measurable_pi_apply k)))

theorem sum_range_two_pow (k : ℕ) : ∑ j ∈ Finset.range k, (2 : ℝ) ^ j = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- The offsets built from a base point in `[0, 1)` and a bit sequence taking each value
infinitely often are exhaustive. -/
theorem isExhaustive_offsetsL {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) {e : ℕ → Bool}
    (he : ∀ (b : Bool) (N : ℕ), ∃ j, N ≤ j ∧ e j = b) : IsExhaustive (offsetsL 1 x e) := by
  intro n
  obtain ⟨j₁, hj₁, he₁⟩ := he true n
  obtain ⟨j₀, hj₀, he₀⟩ := he false n
  have hpow : ∀ j, n ≤ j → (n : ℝ) ≤ 2 ^ j := fun j hj => by
    have : n < 2 ^ j := lt_of_le_of_lt hj Nat.lt_two_pow_self
    exact_mod_cast this.le
  refine ⟨max j₁ j₀ + 1, fun k hk => ⟨?_, ?_⟩⟩
  · have hle := Finset.single_le_sum (f := fun j => (1 : ℝ) * 2 ^ j * bit (e j))
      (fun j _ => mul_nonneg (by positivity) (bit_nonneg _))
      (Finset.mem_range.2 (show j₁ < k by omega))
    beta_reduce at hle
    have h1 : (1 : ℝ) * 2 ^ j₁ * bit (e j₁) = 2 ^ j₁ := by rw [he₁]; simp [bit]
    have := hpow j₁ hj₁
    rw [offsetsL]
    linarith [hx.1]
  · have hsum : (2 : ℝ) ^ k - offsetsL 1 x e k =
        ∑ j ∈ Finset.range k, 2 ^ j * (1 - bit (e j)) + (1 - x) := by
      rw [offsetsL]
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_range_two_pow, one_mul]
      ring
    have hle := Finset.single_le_sum (f := fun j => (2 : ℝ) ^ j * (1 - bit (e j)))
      (fun j _ => mul_nonneg (by positivity) (sub_nonneg.2 (bit_le_one _)))
      (Finset.mem_range.2 (show j₀ < k by omega))
    beta_reduce at hle
    have h0 : (2 : ℝ) ^ j₀ * (1 - bit (e j₀)) = 2 ^ j₀ := by rw [he₀]; simp [bit]
    have := hpow j₀ hj₀
    rw [hsum]
    linarith [hx.2]

theorem ae_mem_Ico_unifIco : ∀ᵐ x ∂unifIco 1, x ∈ Ico (0 : ℝ) 1 := by
  rw [unifIco]
  exact Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem measurableSet_Ico)

/-- Almost every offset sequence of the uniform dyadic system is exhaustive. -/
theorem ae_isExhaustive_offsetLaw : ∀ᵐ o ∂offsetLaw, IsExhaustive o := by
  rw [offsetLaw, ae_map_iff (measurable_offsetsL 1).aemeasurable measurableSet_isExhaustive]
  have h₁ : ∀ᵐ q ∂(unifIco 1).prod bitLaw, q.1 ∈ Ico (0 : ℝ) 1 :=
    ae_iff.mpr (measure_mono_null (t := {x | x ∉ Ico (0 : ℝ) 1} ×ˢ univ)
      (fun _ hq => ⟨hq, trivial⟩)
      (by rw [Measure.prod_prod, ae_iff.mp ae_mem_Ico_unifIco, zero_mul]))
  have h₂ : ∀ᵐ q ∂(unifIco 1).prod bitLaw, ∀ (b : Bool) (N : ℕ), ∃ j, N ≤ j ∧ q.2 j = b :=
    ae_iff.mpr (measure_mono_null
      (t := univ ×ˢ {e : ℕ → Bool | ¬∀ (b : Bool) (N : ℕ), ∃ j, N ≤ j ∧ e j = b})
      (fun _ hq => ⟨trivial, hq⟩)
      (by rw [Measure.prod_prod, ae_iff.mp ae_frequently_bitLaw, mul_zero]))
  filter_upwards [h₁, h₂] with q hq₁ hq₂
  exact isExhaustive_offsetsL hq₁ hq₂

/-! ### Deterministic exhaustion of the chain at a point -/

/-- For an exhaustive offset sequence, every point `y` lies in the closed grid interval of
generation `j` containing `x`, for all large `j`. -/
theorem exists_forall_ge_mem_gridInterval {o : ℕ → ℝ} (ho : IsExhaustive o) (s x y : ℝ) :
    ∃ K : ℕ, ∀ j : ℤ, (K : ℤ) ≤ j →
      gridFloor s o j x ≤ y ∧ y ≤ gridFloor s o j x + (2 : ℝ) ^ (s + (j : ℝ)) := by
  have hs : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos two_pos s
  obtain ⟨n, hn⟩ := exists_nat_gt ((|x| + |y|) / 2 ^ s)
  obtain ⟨K, hK⟩ := ho n
  refine ⟨K, fun j hj => ?_⟩
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (by positivity) hj)
  have hk : K ≤ k := by exact_mod_cast hj
  obtain ⟨h₁, h₂⟩ := hK k hk
  have hside : (2 : ℝ) ^ (s + ((k : ℤ) : ℝ)) = 2 ^ s * 2 ^ k := by
    rw [Int.cast_natCast, Real.rpow_add two_pos, Real.rpow_natCast]
  have hn' : |x| + |y| < 2 ^ s * n := by rwa [div_lt_iff₀ hs, mul_comm] at hn
  have hlo : 2 ^ s * (n : ℝ) ≤ 2 ^ s * o k := mul_le_mul_of_nonneg_left h₁ hs.le
  have hhi : 2 ^ s * (n : ℝ) ≤ 2 ^ s * 2 ^ k - 2 ^ s * o k := by
    rw [← mul_sub]; exact mul_le_mul_of_nonneg_left h₂ hs.le
  have hfl : gridFloor s o (k : ℤ) x = -(2 ^ s * o k) := by
    rw [gridFloor, Int.toNat_natCast, hside]
    refine (eq_latticeFloor (by positivity) ⟨0, by simp⟩ ?_ ?_).symm
    · linarith [neg_abs_le x, abs_nonneg y]
    · linarith [le_abs_self x, abs_nonneg y]
  rw [hfl, hside]
  constructor
  · linarith [neg_abs_le y, abs_nonneg x]
  · linarith [le_abs_self y, abs_nonneg x]

/-- **Exhaustion of the plane**: for exhaustive offset sequences in both coordinates, the
squares of the dyadic system containing any point `w` exhaust the plane, for every scale
coordinate `s`. -/
theorem iUnion_squareAt_eq_univ {o₁ o₂ : ℕ → ℝ} (h₁ : IsExhaustive o₁) (h₂ : IsExhaustive o₂)
    (s : ℝ) (w : ℂ) : ⋃ j, squareAt s o₁ o₂ j w = univ := by
  refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
  obtain ⟨K₁, hK₁⟩ := exists_forall_ge_mem_gridInterval h₁ s w.re z.re
  obtain ⟨K₂, hK₂⟩ := exists_forall_ge_mem_gridInterval h₂ s w.im z.im
  refine ⟨((max K₁ K₂ : ℕ) : ℤ), ?_⟩
  obtain ⟨a₁, b₁⟩ := hK₁ _ (Nat.cast_le.mpr (le_max_left K₁ K₂))
  obtain ⟨a₂, b₂⟩ := hK₂ _ (Nat.cast_le.mpr (le_max_right K₁ K₂))
  exact ⟨a₁, b₁, a₂, b₂⟩

/-- Almost surely, for every point `w`, the squares of the uniform dyadic system of the plane
containing `w` exhaust the plane. -/
theorem ae_iUnion_squareAt_eq_univ :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw),
      ∀ w : ℂ, ⋃ j, squareAt q.1 q.2.1 q.2.2 j w = univ := by
  have h := ae_iff.mp ae_isExhaustive_offsetLaw
  have h₁ : ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), IsExhaustive q.2.1 :=
    ae_iff.mpr (measure_mono_null (t := univ ×ˢ ({o | ¬IsExhaustive o} ×ˢ univ))
      (fun _ hq => ⟨trivial, hq, trivial⟩)
      (by rw [Measure.prod_prod, Measure.prod_prod, h, zero_mul, mul_zero]))
  have h₂ : ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), IsExhaustive q.2.2 :=
    ae_iff.mpr (measure_mono_null (t := univ ×ˢ (univ ×ˢ {o | ¬IsExhaustive o}))
      (fun _ hq => ⟨trivial, trivial, hq⟩)
      (by rw [Measure.prod_prod, Measure.prod_prod, h, mul_zero, mul_zero]))
  filter_upwards [h₁, h₂] with q hq₁ hq₂
  exact fun w => iUnion_squareAt_eq_univ hq₁ hq₂ q.1 w

/-! ### Existence of the capped squares -/

section CappedSquare

open CellMass CappedSquare

variable {ι : Type*} [Countable ι] {c : ι → Set ℂ}

/-- **Existence of `S_m^w`** (Gwynne, Miller and Sheffield, arXiv 1807.07515, (2.1) and
Lemma 2.2, for the cell mass of Lebesgue measure): for a fixed point `w` and a countable locally
finite cover of the plane by compact cells of positive area, almost surely, for every mass
`m ∈ (0, ∞)`, the square `squareAt j w` with `m` between the masses of generations `j` and `j + 1`
is the capped square of mass `m` around `w`. -/
theorem ae_exists_isCappedSquare_squareAt_cellMass (w : ℂ) (hc : LocallyFinite c)
    (hcover : ⋃ i, c i = univ) (hcpt : ∀ i, IsCompact (c i)) (hpos : ∀ i, volume (c i) ≠ 0) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∃ j, cellMass volume c (squareAt q.1 q.2.1 q.2.2 j w) ≤ m ∧
        m < cellMass volume c (squareAt q.1 q.2.1 q.2.2 (j + 1) w) ∧
        IsCappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (cellMass volume c) m w
          (squareAt q.1 q.2.1 q.2.2 j w) := by
  filter_upwards [ae_isCompatible_isOffGrid_system w, ae_iUnion_squareAt_eq_univ] with q hq hexh
  exact fun m hm0 hmtop => exists_isCappedSquare_squareAt_cellMass hq.1 hq.2.1 hq.2.2 (hexh w)
    hc hcover hcpt hpos hm0 hmtop

end CappedSquare

end LatticeProb.DyadicOffset
