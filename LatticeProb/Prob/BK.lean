/-
The van den Berg-Kesten inequality on the discrete cube.

Two increasing events occur disjointly at a configuration when two disjoint sets
of coordinates certify them separately.  Under a product measure the probability
of a disjoint occurrence is at most the product of the probabilities.  This is
the opposite direction to Harris, and it is not a consequence of it.

The proof is van den Berg and Kesten's.  It runs on a doubled configuration
`σ : ι → Bool × Bool`, two independent copies of the cube at once.  For a set
`S` of coordinates, `DEv A B S` asks for the two certificates, the one for `A`
read off the second copy on `S` and the first copy off `S`, the one for `B` read
off the first copy throughout, and required to be disjoint only outside `S`.  At
`S = ∅` this is the disjoint occurrence in the first copy; at `S = univ` the two
certificates live in different copies and no longer interact, so its probability
is the product.  The whole content is that adding one coordinate to `S` does not
decrease the probability, and that is a four-case comparison at that coordinate.

Everything here is a finite sum; no measure theory is used until the last
section, which transports the inequality to `Measure.pi` of Bernoulli measures.
-/
import Mathlib

namespace LatticeProb

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The weighted cube -/

/-- The weight of one coordinate: `t` for `true`, `1 - t` for `false`. -/
def wgt (t : ℝ) (b : Bool) : ℝ := if b then t else 1 - t

theorem wgt_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (b : Bool) : 0 ≤ wgt t b := by
  cases b <;> simp [wgt] <;> linarith

theorem sum_wgt (t : ℝ) : ∑ b : Bool, wgt t b = 1 := by
  simp [wgt]

/-- The weight of a configuration under the product measure with parameters `p`. -/
def weight (p : ι → ℝ) (ω : ι → Bool) : ℝ := ∏ i, wgt (p i) (ω i)

omit [DecidableEq ι] in
theorem weight_nonneg {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) (ω : ι → Bool) :
    0 ≤ weight p ω :=
  Finset.prod_nonneg fun i _ => wgt_nonneg (h0 i) (h1 i) _

/-- The probability of an event of the cube. -/
noncomputable def prob (p : ι → ℝ) (A : Set (ι → Bool)) : ℝ :=
  ∑ ω : ι → Bool, A.indicator (weight p) ω

/-- The weight of a doubled configuration: the two copies are independent. -/
def weight₂ (p : ι → ℝ) (σ : ι → Bool × Bool) : ℝ :=
  ∏ i, (wgt (p i) (σ i).1 * wgt (p i) (σ i).2)

omit [DecidableEq ι] in
theorem weight₂_nonneg {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1)
    (σ : ι → Bool × Bool) : 0 ≤ weight₂ p σ :=
  Finset.prod_nonneg fun i _ =>
    mul_nonneg (wgt_nonneg (h0 i) (h1 i) _) (wgt_nonneg (h0 i) (h1 i) _)

/-- The probability of an event of the doubled cube. -/
noncomputable def prob₂ (p : ι → ℝ) (X : Set (ι → Bool × Bool)) : ℝ :=
  ∑ σ : ι → Bool × Bool, X.indicator (weight₂ p) σ

/-! ### Splitting off one coordinate -/

/-- The configuration with value `v` at `j` and `rest` elsewhere. -/
def fill {α : Type*} (j : ι) (v : α) (rest : {i : ι // i ≠ j} → α) : ι → α :=
  fun i => if h : i = j then v else rest ⟨i, h⟩

omit [Fintype ι] in
@[simp] theorem fill_self {α : Type*} (j : ι) (v : α) (rest : {i : ι // i ≠ j} → α) :
    fill j v rest j = v := by simp [fill]

omit [Fintype ι] in
theorem fill_of_ne {α : Type*} {j i : ι} (h : i ≠ j) (v : α)
    (rest : {i : ι // i ≠ j} → α) : fill j v rest i = rest ⟨i, h⟩ := by
  simp [fill, h]

omit [Fintype ι] in
/-- Changing the value at `j` changes nothing elsewhere. -/
theorem fill_congr_of_ne {α : Type*} {j i : ι} (h : i ≠ j) (v v' : α)
    (rest : {i : ι // i ≠ j} → α) : fill j v rest i = fill j v' rest i := by
  rw [fill_of_ne h, fill_of_ne h]

omit [Fintype ι] in
/-- Splitting a configuration into its value at `j` and the rest. -/
def splitEquiv {α : Type*} (j : ι) : (α × ({i : ι // i ≠ j} → α)) ≃ (ι → α) where
  toFun q := fill j q.1 q.2
  invFun ω := (ω j, fun i => ω i)
  left_inv := by
    rintro ⟨v, rest⟩
    refine Prod.ext (by simp) ?_
    funext i
    show fill j v rest i = rest i
    exact fill_of_ne i.2 v rest
  right_inv := by
    intro ω
    funext i
    show fill j (ω j) (fun i => ω i) i = ω i
    by_cases h : i = j
    · subst h; simp
    · rw [fill_of_ne h]

theorem sum_split {α : Type*} [Fintype α] [DecidableEq α] (j : ι) (f : (ι → α) → ℝ) :
    ∑ ω : ι → α, f ω
      = ∑ v : α, ∑ rest : {i : ι // i ≠ j} → α, f (fill j v rest) := by
  classical
  rw [← Equiv.sum_comp (splitEquiv (α := α) j) f, Fintype.sum_prod_type]
  rfl

theorem sum_split' {α : Type*} [Fintype α] [DecidableEq α] (j : ι) (f : (ι → α) → ℝ) :
    ∑ ω : ι → α, f ω
      = ∑ rest : {i : ι // i ≠ j} → α, ∑ v : α, f (fill j v rest) := by
  rw [sum_split j f, Finset.sum_comm]

/-- The weight of a doubled configuration splits at any coordinate. -/
theorem weight₂_fill (p : ι → ℝ) (j : ι) (v : Bool × Bool)
    (rest : {i : ι // i ≠ j} → Bool × Bool) :
    weight₂ p (fill j v rest)
      = (wgt (p j) v.1 * wgt (p j) v.2)
        * ∏ i ∈ ({j}ᶜ : Finset ι),
            (wgt (p i) (fill j v rest i).1 * wgt (p i) (fill j v rest i).2) := by
  rw [weight₂, Fintype.prod_eq_mul_prod_compl j]
  simp

theorem sum_weight (p : ι → ℝ) : ∑ ω : ι → Bool, weight p ω = 1 := by
  have h : ∑ ω : ι → Bool, ∏ i, wgt (p i) (ω i) = ∏ i, ∑ b : Bool, wgt (p i) b :=
    (Fintype.prod_sum fun i (b : Bool) => wgt (p i) b).symm
  have h2 : ∀ i : ι, wgt (p i) true + wgt (p i) false = 1 := by
    intro i; simp [wgt]
  simp only [weight]
  rw [h]
  simp only [Fintype.sum_bool, h2]
  simp

/-- Splitting a doubled configuration into its two copies. -/
def pairEquiv : (ι → Bool × Bool) ≃ ((ι → Bool) × (ι → Bool)) where
  toFun σ := (fun i => (σ i).1, fun i => (σ i).2)
  invFun q := fun i => (q.1 i, q.2 i)
  left_inv σ := by funext i; exact Prod.ext rfl rfl
  right_inv q := by refine Prod.ext ?_ ?_ <;> rfl

omit [DecidableEq ι] in
theorem weight₂_eq (p : ι → ℝ) (σ : ι → Bool × Bool) :
    weight₂ p σ = weight p (fun i => (σ i).1) * weight p (fun i => (σ i).2) := by
  rw [weight₂, weight, weight, ← Finset.prod_mul_distrib]

theorem sum_pair {M : Type*} [AddCommMonoid M] (f : (ι → Bool) → (ι → Bool) → M) :
    ∑ σ : ι → Bool × Bool, f (fun i => (σ i).1) (fun i => (σ i).2)
      = ∑ ω : ι → Bool, ∑ η : ι → Bool, f ω η := by
  classical
  rw [← Fintype.sum_prod_type (fun q : (ι → Bool) × (ι → Bool) => f q.1 q.2)]
  exact Equiv.sum_comp pairEquiv fun q => f q.1 q.2

/-! ### Disjoint occurrence -/

/-- The configuration that is `true` exactly on `K`. -/
def indic (K : Finset ι) : ι → Bool := fun i => decide (i ∈ K)

omit [Fintype ι] in
theorem indic_le {K : Finset ι} {ω : ι → Bool} (h : ∀ i ∈ K, ω i = true) : indic K ≤ ω := by
  intro i
  by_cases hi : i ∈ K
  · rw [indic, decide_eq_true hi, h i hi]
  · simp [indic, hi]

/-- Two events occur disjointly at `ω` when two disjoint sets of coordinates
certify them separately: reading only the coordinates in `K` forces `A`, and
reading only those in `L` forces `B`. -/
def disjointOcc (A B : Set (ι → Bool)) : Set (ι → Bool) :=
  {ω | ∃ K L : Finset ι, Disjoint K L ∧
        (∀ ω', (∀ i ∈ K, ω' i = ω i) → ω' ∈ A) ∧
        (∀ ω', (∀ i ∈ L, ω' i = ω i) → ω' ∈ B)}

/-- The witness form of the disjoint occurrence: two disjoint sets of coordinates
on which `ω` is `true`, whose indicators lie in the two events. -/
def wit (A B : Set (ι → Bool)) : Set (ι → Bool) :=
  {ω | ∃ K L : Finset ι, Disjoint K L ∧ (∀ i ∈ K, ω i = true) ∧ (∀ i ∈ L, ω i = true) ∧
        indic K ∈ A ∧ indic L ∈ B}

omit [Fintype ι] in
/-- For increasing events the two forms agree: the smallest configuration a
cylinder contains is the indicator of the part of the cylinder where `ω` is
`true`. -/
theorem disjointOcc_eq_wit {A B : Set (ι → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    disjointOcc A B = wit A B := by
  classical
  ext ω
  constructor
  · rintro ⟨K, L, hKL, hA', hB'⟩
    refine ⟨K.filter fun i => ω i = true, L.filter fun i => ω i = true, ?_, ?_, ?_, ?_, ?_⟩
    · exact hKL.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · intro i hi; exact (Finset.mem_filter.mp hi).2
    · intro i hi; exact (Finset.mem_filter.mp hi).2
    · refine hA' _ fun i hi => ?_
      by_cases hw : ω i = true
      · rw [indic, decide_eq_true (Finset.mem_filter.mpr ⟨hi, hw⟩), hw]
      · have : i ∉ K.filter fun i => ω i = true := fun hc => hw (Finset.mem_filter.mp hc).2
        simp only [indic, decide_eq_false this]
        simpa using hw
    · refine hB' _ fun i hi => ?_
      by_cases hw : ω i = true
      · rw [indic, decide_eq_true (Finset.mem_filter.mpr ⟨hi, hw⟩), hw]
      · have : i ∉ L.filter fun i => ω i = true := fun hc => hw (Finset.mem_filter.mp hc).2
        simp only [indic, decide_eq_false this]
        simpa using hw
  · rintro ⟨K, L, hKL, hKw, hLw, hKA, hLB⟩
    refine ⟨K, L, hKL, fun ω' hω' => ?_, fun ω' hω' => ?_⟩
    · refine hA (fun i => ?_) hKA
      by_cases hi : i ∈ K
      · rw [indic, decide_eq_true hi, hω' i hi, hKw i hi]
      · simp [indic, hi]
    · refine hB (fun i => ?_) hLB
      by_cases hi : i ∈ L
      · rw [indic, decide_eq_true hi, hω' i hi, hLw i hi]
      · simp [indic, hi]

/-- An increasing event is the union of the cylinders of its indicators. -/
theorem mem_iff_exists_indic {A : Set (ι → Bool)} (hA : IsUpperSet A) (ω : ι → Bool) :
    ω ∈ A ↔ ∃ K : Finset ι, (∀ i ∈ K, ω i = true) ∧ indic K ∈ A := by
  classical
  constructor
  · intro hω
    refine ⟨Finset.univ.filter fun i => ω i = true, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
    have : indic (Finset.univ.filter fun i => ω i = true) = ω := by
      funext i
      by_cases hw : ω i = true
      · rw [indic, decide_eq_true (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hw⟩), hw]
      · have : i ∉ Finset.univ.filter fun i => ω i = true := fun hc =>
          hw (Finset.mem_filter.mp hc).2
        simp only [indic, decide_eq_false this]
        simpa using hw
    rwa [this]
  · rintro ⟨K, hK, hKA⟩
    exact hA (indic_le hK) hKA

/-! ### The interpolating events on the doubled cube -/

/-- The certificate for `A` reads the second copy on `S` and the first copy off
`S`. -/
def mixAt (S : Finset ι) (σ : ι → Bool × Bool) : ι → Bool :=
  fun i => if i ∈ S then (σ i).2 else (σ i).1

omit [Fintype ι] in
theorem mixAt_empty (σ : ι → Bool × Bool) : mixAt ∅ σ = fun i => (σ i).1 := by
  funext i; simp [mixAt]

theorem mixAt_univ (σ : ι → Bool × Bool) : mixAt Finset.univ σ = fun i => (σ i).2 := by
  funext i; simp [mixAt]

/-- The interpolating event.  `K` certifies `A` against the mixed copy, `L`
certifies `B` against the first copy, and the two are required to be disjoint
only outside `S`. -/
def DEv (A B : Set (ι → Bool)) (S : Finset ι) : Set (ι → Bool × Bool) :=
  {σ | ∃ K L : Finset ι,
        (∀ i ∈ K, mixAt S σ i = true) ∧ (∀ i ∈ L, (σ i).1 = true) ∧
        indic K ∈ A ∧ indic L ∈ B ∧ ∀ i, i ∉ S → i ∈ K → i ∈ L → False}

omit [Fintype ι] in
theorem DEv_empty (A B : Set (ι → Bool)) :
    DEv A B ∅ = {σ : ι → Bool × Bool | (fun i => (σ i).1) ∈ wit A B} := by
  ext σ
  simp only [DEv, wit, Set.mem_setOf_eq, mixAt_empty, Finset.notMem_empty, not_false_iff,
    forall_true_left]
  constructor
  · rintro ⟨K, L, hK, hL, hKA, hLB, hd⟩
    exact ⟨K, L, Finset.disjoint_left.mpr fun i hi hj => hd i hi hj, hK, hL, hKA, hLB⟩
  · rintro ⟨K, L, hKL, hK, hL, hKA, hLB⟩
    exact ⟨K, L, hK, hL, hKA, hLB, fun i hi hj => (Finset.disjoint_left.mp hKL) hi hj⟩

theorem DEv_univ {A B : Set (ι → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    DEv A B Finset.univ
      = {σ : ι → Bool × Bool | (fun i => (σ i).2) ∈ A ∧ (fun i => (σ i).1) ∈ B} := by
  ext σ
  simp only [DEv, Set.mem_setOf_eq, mixAt_univ]
  constructor
  · rintro ⟨K, L, hK, hL, hKA, hLB, -⟩
    exact ⟨(mem_iff_exists_indic hA _).mpr ⟨K, hK, hKA⟩,
      (mem_iff_exists_indic hB _).mpr ⟨L, hL, hLB⟩⟩
  · rintro ⟨hAm, hBm⟩
    obtain ⟨K, hK, hKA⟩ := (mem_iff_exists_indic hA _).mp hAm
    obtain ⟨L, hL, hLB⟩ := (mem_iff_exists_indic hB _).mp hBm
    exact ⟨K, L, hK, hL, hKA, hLB, fun i hi => absurd (Finset.mem_univ i) hi⟩

/-! ### The two endpoints -/

theorem prob₂_DEv_empty (p : ι → ℝ) (A B : Set (ι → Bool)) :
    prob₂ p (DEv A B ∅) = prob p (wit A B) := by
  classical
  rw [prob₂, prob, DEv_empty]
  have h : ∀ σ : ι → Bool × Bool,
      Set.indicator {σ : ι → Bool × Bool | (fun i => (σ i).1) ∈ wit A B} (weight₂ p) σ
        = Set.indicator (wit A B) (weight p) (fun i => (σ i).1)
          * weight p (fun i => (σ i).2) := by
    intro σ
    by_cases hσ : (fun i => (σ i).1) ∈ wit A B
    · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem (show σ ∈ _ from hσ), weight₂_eq]
    · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem (show σ ∉ _ from hσ), zero_mul]
  refine (Finset.sum_congr rfl fun σ _ => h σ).trans ?_
  rw [sum_pair fun ω η => Set.indicator (wit A B) (weight p) ω * weight p η,
    ← Finset.sum_mul_sum]
  simp [sum_weight]

theorem prob₂_DEv_univ (p : ι → ℝ) {A B : Set (ι → Bool)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    prob₂ p (DEv A B Finset.univ) = prob p A * prob p B := by
  classical
  rw [prob₂, DEv_univ hA hB]
  have h : ∀ σ : ι → Bool × Bool,
      Set.indicator {σ : ι → Bool × Bool | (fun i => (σ i).2) ∈ A ∧ (fun i => (σ i).1) ∈ B}
          (weight₂ p) σ
        = Set.indicator B (weight p) (fun i => (σ i).1)
          * Set.indicator A (weight p) (fun i => (σ i).2) := by
    intro σ
    by_cases h1 : (fun i => (σ i).2) ∈ A
    · by_cases h2 : (fun i => (σ i).1) ∈ B
      · have hm : σ ∈ {σ : ι → Bool × Bool |
            (fun i => (σ i).2) ∈ A ∧ (fun i => (σ i).1) ∈ B} := ⟨h1, h2⟩
        rw [Set.indicator_of_mem hm, Set.indicator_of_mem h2,
          Set.indicator_of_mem h1, weight₂_eq]
      · rw [Set.indicator_of_notMem (show σ ∉ _ from fun hc => h2 hc.2),
          Set.indicator_of_notMem h2, zero_mul]
    · rw [Set.indicator_of_notMem (show σ ∉ _ from fun hc => h1 hc.1),
        Set.indicator_of_notMem h1, mul_zero]
  refine (Finset.sum_congr rfl fun σ _ => h σ).trans ?_
  rw [sum_pair fun ω η => Set.indicator B (weight p) ω * Set.indicator A (weight p) η,
    ← Finset.sum_mul_sum, prob, prob]
  ring

/-! ### The arithmetic of one coordinate -/

open scoped Classical in
/-- The four-case comparison at one coordinate.  `P0` and `P1` are the two values
of the interpolating event before the coordinate is added, `Q` the four values
after; the hypotheses are the transfers proved below. -/
theorem bk_step_arith {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    {P0 P1 Q00 Q01 Q10 Q11 : Prop}
    (f1a : P0 → Q00) (f1b : P0 → Q01) (f2 : P1 → Q11)
    (f3 : P1 → Q10 ∨ Q01) (f4 : P0 → P1 ∧ Q10) :
    q * (if P0 then (1 : ℝ) else 0) + p * (if P1 then (1 : ℝ) else 0)
      ≤ q * q * (if Q00 then (1 : ℝ) else 0) + q * p * (if Q01 then (1 : ℝ) else 0)
        + p * q * (if Q10 then (1 : ℝ) else 0) + p * p * (if Q11 then (1 : ℝ) else 0) := by
  have hz : ∀ R : Prop, (0 : ℝ) ≤ if R then (1 : ℝ) else 0 := by
    intro R; split <;> norm_num
  have e00 : (0 : ℝ) ≤ q * q * (if Q00 then (1 : ℝ) else 0) :=
    mul_nonneg (mul_nonneg hq hq) (hz Q00)
  have e01 : (0 : ℝ) ≤ q * p * (if Q01 then (1 : ℝ) else 0) :=
    mul_nonneg (mul_nonneg hq hp) (hz Q01)
  have e10 : (0 : ℝ) ≤ p * q * (if Q10 then (1 : ℝ) else 0) :=
    mul_nonneg (mul_nonneg hp hq) (hz Q10)
  have e11 : (0 : ℝ) ≤ p * p * (if Q11 then (1 : ℝ) else 0) :=
    mul_nonneg (mul_nonneg hp hp) (hz Q11)
  have hsq : q * q + q * p + p * q + p * p = 1 := by nlinarith [hpq]
  have hpsum : p * q * 1 + p * p * 1 = p := by nlinarith [hpq]
  have hqsum : q * p * 1 + p * p * 1 = p := by nlinarith [hpq]
  by_cases h0 : P0
  · obtain ⟨h1, h10⟩ := f4 h0
    rw [if_pos h0, if_pos h1, if_pos (f1a h0), if_pos (f1b h0), if_pos h10, if_pos (f2 h1)]
    linarith
  · rw [if_neg h0]
    by_cases h1 : P1
    · rw [if_pos h1, if_pos (f2 h1)]
      rcases f3 h1 with h | h
      · rw [if_pos h]
        linarith
      · rw [if_pos h]
        linarith
    · rw [if_neg h1]
      linarith

/-! ### Adding one coordinate to `S` -/

section Step

variable {A B : Set (ι → Bool)} {S : Finset ι} {j : ι}

omit [Fintype ι] in
theorem mixAt_fill_self (hj : j ∉ S) (v : Bool × Bool)
    (rest : {i : ι // i ≠ j} → Bool × Bool) :
    mixAt S (fill j v rest) j = v.1 := by
  simp [mixAt, hj]

omit [Fintype ι] in
theorem mixAt_insert_fill_self (v : Bool × Bool)
    (rest : {i : ι // i ≠ j} → Bool × Bool) :
    mixAt (insert j S) (fill j v rest) j = v.2 := by
  simp [mixAt]

omit [Fintype ι] in
theorem mixAt_fill_congr {i : ι} (h : i ≠ j) {T T' : Finset ι} (hT : i ∈ T ↔ i ∈ T')
    (v v' : Bool × Bool) (rest : {i : ι // i ≠ j} → Bool × Bool) :
    mixAt T (fill j v rest) i = mixAt T' (fill j v' rest) i := by
  simp only [mixAt, fill_of_ne h]
  by_cases hi : i ∈ T
  · rw [if_pos hi, if_pos (hT.mp hi)]
  · rw [if_neg hi, if_neg fun hc => hi (hT.mpr hc)]

omit [Fintype ι] in
theorem fst_fill_of_ne {i : ι} (h : i ≠ j) (v v' : Bool × Bool)
    (rest : {i : ι // i ≠ j} → Bool × Bool) :
    ((fill j v rest) i).1 = ((fill j v' rest) i).1 := by
  rw [fill_of_ne h, fill_of_ne h]

omit [Fintype ι] in
/-- Transferring a pair of certificates from `S` to a set `T` that differs from
it only at `j`.  Away from `j` nothing changes; at `j` the two hypotheses say
what has to hold if `j` is used by one of the certificates. -/
theorem DEv_transfer {T : Finset ι} (hTS : ∀ i, i ≠ j → (i ∈ T ↔ i ∈ S))
    (hTd : ∀ i, i ∉ T → i ∉ S) {v v' : Bool × Bool}
    {rest : {i : ι // i ≠ j} → Bool × Bool} {K L : Finset ι}
    (hK : ∀ i ∈ K, mixAt S (fill j v rest) i = true)
    (hL : ∀ i ∈ L, ((fill j v rest) i).1 = true)
    (hKA : indic K ∈ A) (hLB : indic L ∈ B)
    (hd : ∀ i, i ∉ S → i ∈ K → i ∈ L → False)
    (hKj : j ∈ K → mixAt T (fill j v' rest) j = true)
    (hLj : j ∈ L → ((fill j v' rest) j).1 = true) :
    fill j v' rest ∈ DEv A B T := by
  refine ⟨K, L, fun i hi => ?_, fun i hi => ?_, hKA, hLB, fun i hi hiK hiL => ?_⟩
  · by_cases h : i = j
    · subst h; exact hKj hi
    · rw [mixAt_fill_congr h (hTS i h) v' v rest]; exact hK i hi
  · by_cases h : i = j
    · subst h; exact hLj hi
    · rw [fst_fill_of_ne h v' v rest]; exact hL i hi
  · exact hd i (hTd i hi) hiK hiL

omit [Fintype ι] in
theorem insert_iff_of_ne {i : ι} (h : i ≠ j) : i ∈ insert j S ↔ i ∈ S := by
  simp [Finset.mem_insert, h]

omit [Fintype ι] in
/-- Whether the interpolating event holds does not depend on the second copy at
`j`, because `j` is not in `S`. -/
theorem DEv_fill_snd (hj : j ∉ S) {s t t' : Bool}
    {rest : {i : ι // i ≠ j} → Bool × Bool}
    (h : fill j (s, t) rest ∈ DEv A B S) : fill j (s, t') rest ∈ DEv A B S := by
  obtain ⟨K, L, hK, hL, hKA, hLB, hd⟩ := h
  refine DEv_transfer (fun _ _ => Iff.rfl) (fun _ hi => hi) hK hL hKA hLB hd
    (fun hjK => ?_) (fun hjL => ?_)
  · have := hK j hjK
    rw [mixAt_fill_self hj] at this ⊢
    exact this
  · have := hL j hjL
    rw [fill_self] at this ⊢
    exact this

omit [Fintype ι] in
/-- If the first copy is `false` at `j`, neither certificate uses `j`, so the
event transfers to `insert j S` whatever the second copy does there. -/
theorem transfer_false (hj : j ∉ S) {t t' : Bool}
    {rest : {i : ι // i ≠ j} → Bool × Bool}
    (h : fill j (false, t) rest ∈ DEv A B S) :
    fill j (false, t') rest ∈ DEv A B (insert j S) := by
  obtain ⟨K, L, hK, hL, hKA, hLB, hd⟩ := h
  refine DEv_transfer (fun i hi => insert_iff_of_ne hi) (fun i hi hc =>
    hi (Finset.mem_insert_of_mem hc)) hK hL hKA hLB hd (fun hjK => ?_) (fun hjL => ?_)
  · exfalso
    have := hK j hjK
    rw [mixAt_fill_self hj] at this
    exact Bool.noConfusion this
  · exfalso
    have := hL j hjL
    rw [fill_self] at this
    exact Bool.noConfusion this

omit [Fintype ι] in
/-- If the first copy is `true` at `j`, the event transfers to `insert j S` with
the second copy `true` at `j`, whichever certificate uses `j`. -/
theorem transfer_true_true (_hj : j ∉ S) {t : Bool}
    {rest : {i : ι // i ≠ j} → Bool × Bool}
    (h : fill j (true, t) rest ∈ DEv A B S) :
    fill j (true, true) rest ∈ DEv A B (insert j S) := by
  obtain ⟨K, L, hK, hL, hKA, hLB, hd⟩ := h
  exact DEv_transfer (fun i hi => insert_iff_of_ne hi) (fun i hi hc =>
    hi (Finset.mem_insert_of_mem hc)) hK hL hKA hLB hd
    (fun _ => by rw [mixAt_insert_fill_self]) (fun _ => by rw [fill_self])

omit [Fintype ι] in
/-- If the first copy is `true` at `j`, then `j` is used by at most one of the
two certificates, and whichever it is, one of the two mixed configurations
carries the event. -/
theorem transfer_true_split (hj : j ∉ S) {t : Bool}
    {rest : {i : ι // i ≠ j} → Bool × Bool}
    (h : fill j (true, t) rest ∈ DEv A B S) :
    fill j (true, false) rest ∈ DEv A B (insert j S)
      ∨ fill j (false, true) rest ∈ DEv A B (insert j S) := by
  obtain ⟨K, L, hK, hL, hKA, hLB, hd⟩ := h
  by_cases hjK : j ∈ K
  · right
    exact DEv_transfer (fun i hi => insert_iff_of_ne hi) (fun i hi hc =>
      hi (Finset.mem_insert_of_mem hc)) hK hL hKA hLB hd
      (fun _ => by rw [mixAt_insert_fill_self]) (fun hjL => (hd j hj hjK hjL).elim)
  · left
    exact DEv_transfer (fun i hi => insert_iff_of_ne hi) (fun i hi hc =>
      hi (Finset.mem_insert_of_mem hc)) hK hL hKA hLB hd
      (fun hc => absurd hc hjK) (fun _ => by rw [fill_self])

omit [Fintype ι] in
/-- If the first copy is `false` at `j`, neither certificate uses `j`, so
turning it to `true` keeps the event, and it also transfers to `insert j S` with
the second copy `false`. -/
theorem transfer_false_up (hj : j ∉ S) {t t' : Bool}
    {rest : {i : ι // i ≠ j} → Bool × Bool}
    (h : fill j (false, t) rest ∈ DEv A B S) :
    fill j (true, t') rest ∈ DEv A B S := by
  obtain ⟨K, L, hK, hL, hKA, hLB, hd⟩ := h
  refine DEv_transfer (fun _ _ => Iff.rfl) (fun _ hi => hi) hK hL hKA hLB hd
    (fun hjK => ?_) (fun _ => by rw [fill_self])
  · rw [mixAt_fill_self hj]

omit [Fintype ι] in
/-- From a `false` first copy at `j`, the event transfers to `insert j S` with a
`true` first copy: neither certificate used `j`. -/
theorem transfer_false_insert (hj : j ∉ S) {t t' : Bool}
    {rest : {i : ι // i ≠ j} → Bool × Bool}
    (h : fill j (false, t) rest ∈ DEv A B S) :
    fill j (true, t') rest ∈ DEv A B (insert j S) := by
  obtain ⟨K, L, hK, hL, hKA, hLB, hd⟩ := h
  refine DEv_transfer (fun i hi => insert_iff_of_ne hi) (fun i hi hc =>
    hi (Finset.mem_insert_of_mem hc)) hK hL hKA hLB hd (fun hjK => ?_)
    (fun _ => by rw [fill_self])
  exfalso
  have := hK j hjK
  rw [mixAt_fill_self hj] at this
  exact Bool.noConfusion this

theorem prod_compl_fill_congr (p : ι → ℝ) (v v' : Bool × Bool)
    (rest : {i : ι // i ≠ j} → Bool × Bool) :
    (∏ i ∈ ({j}ᶜ : Finset ι),
        (wgt (p i) ((fill j v rest) i).1 * wgt (p i) ((fill j v rest) i).2))
      = ∏ i ∈ ({j}ᶜ : Finset ι),
        (wgt (p i) ((fill j v' rest) i).1 * wgt (p i) ((fill j v' rest) i).2) := by
  refine Finset.prod_congr rfl fun i hi => ?_
  have h : i ≠ j := by simpa using hi
  rw [fill_of_ne h, fill_of_ne h]

/-- **The step.**  Adding one coordinate to `S` does not decrease the
probability of the interpolating event. -/
theorem prob₂_DEv_le_insert {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1)
    (hj : j ∉ S) :
    prob₂ p (DEv A B S) ≤ prob₂ p (DEv A B (insert j S)) := by
  classical
  have expand4 : ∀ g : Bool × Bool → ℝ,
      ∑ v : Bool × Bool, g v
        = g (true, true) + g (true, false) + (g (false, true) + g (false, false)) := by
    intro g
    rw [Fintype.sum_prod_type]
    simp
  rw [prob₂, prob₂, sum_split' j, sum_split' j]
  refine Finset.sum_le_sum fun rest _ => ?_
  set C : ℝ := ∏ i ∈ ({j}ᶜ : Finset ι),
      (wgt (p i) ((fill j (false, false) rest) i).1
        * wgt (p i) ((fill j (false, false) rest) i).2) with hCdef
  have hCnn : 0 ≤ C := Finset.prod_nonneg fun i _ =>
    mul_nonneg (wgt_nonneg (h0 i) (h1 i) _) (wgt_nonneg (h0 i) (h1 i) _)
  have hw : ∀ v : Bool × Bool,
      weight₂ p (fill j v rest) = (wgt (p j) v.1 * wgt (p j) v.2) * C := by
    intro v
    rw [weight₂_fill, hCdef, prod_compl_fill_congr p v (false, false) rest]
  have expand : ∀ X : Set (ι → Bool × Bool),
      ∑ v : Bool × Bool, Set.indicator X (weight₂ p) (fill j v rest)
        = C * ∑ v : Bool × Bool, (wgt (p j) v.1 * wgt (p j) v.2) *
            (if fill j v rest ∈ X then (1 : ℝ) else 0) := by
    intro X
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Set.indicator_apply]
    by_cases hv : fill j v rest ∈ X
    · rw [if_pos hv, if_pos hv, hw v]; ring
    · rw [if_neg hv, if_neg hv]; ring
  rw [expand, expand]
  refine mul_le_mul_of_nonneg_left ?_ hCnn
  rw [expand4, expand4]
  set pp : ℝ := wgt (p j) true with hpp
  set qq : ℝ := wgt (p j) false with hqq
  have hppnn : 0 ≤ pp := wgt_nonneg (h0 j) (h1 j) true
  have hqqnn : 0 ≤ qq := wgt_nonneg (h0 j) (h1 j) false
  have hsum : pp + qq = 1 := by rw [hpp, hqq]; simp [wgt]
  have hTT : (fill j (true, true) rest ∈ DEv A B S)
      ↔ (fill j (true, false) rest ∈ DEv A B S) :=
    ⟨fun h => DEv_fill_snd hj h, fun h => DEv_fill_snd hj h⟩
  have hFT : (fill j (false, true) rest ∈ DEv A B S)
      ↔ (fill j (false, false) rest ∈ DEv A B S) :=
    ⟨fun h => DEv_fill_snd hj h, fun h => DEv_fill_snd hj h⟩
  rw [if_congr hTT rfl rfl, if_congr hFT rfl rfl]
  have harith := bk_step_arith (p := pp) (q := qq) hppnn hqqnn (by linarith)
    (P0 := fill j (false, false) rest ∈ DEv A B S)
    (P1 := fill j (true, false) rest ∈ DEv A B S)
    (Q00 := fill j (false, false) rest ∈ DEv A B (insert j S))
    (Q01 := fill j (false, true) rest ∈ DEv A B (insert j S))
    (Q10 := fill j (true, false) rest ∈ DEv A B (insert j S))
    (Q11 := fill j (true, true) rest ∈ DEv A B (insert j S))
    (fun h => transfer_false hj h) (fun h => transfer_false hj h)
    (fun h => transfer_true_true hj h) (fun h => transfer_true_split hj h)
    (fun h => ⟨transfer_false_up hj h, transfer_false_insert hj h⟩)
  have hLHS : ((pp * pp * if fill j (true, false) rest ∈ DEv A B S then (1:ℝ) else 0) +
        pp * qq * if fill j (true, false) rest ∈ DEv A B S then (1:ℝ) else 0) +
      ((qq * pp * if fill j (false, false) rest ∈ DEv A B S then (1:ℝ) else 0) +
        qq * qq * if fill j (false, false) rest ∈ DEv A B S then (1:ℝ) else 0)
      = qq * (if fill j (false, false) rest ∈ DEv A B S then (1:ℝ) else 0)
        + pp * (if fill j (true, false) rest ∈ DEv A B S then (1:ℝ) else 0) := by
    linear_combination (pp * (if fill j (true, false) rest ∈ DEv A B S then (1:ℝ) else 0)
      + qq * (if fill j (false, false) rest ∈ DEv A B S then (1:ℝ) else 0)) * hsum
  rw [hLHS]
  linarith [harith]

end Step

/-! ### The inequality on the finite cube -/

theorem prob₂_DEv_le_univ_aux {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1)
    (A B : Set (ι → Bool)) : ∀ (n : ℕ) (S : Finset ι), Sᶜ.card = n →
      prob₂ p (DEv A B S) ≤ prob₂ p (DEv A B Finset.univ) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS
    by_cases hSu : S = Finset.univ
    · rw [hSu]
    · obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
        by_contra hc
        push Not at hc
        exact hSu (Finset.eq_univ_iff_forall.mpr hc)
      have hjc : j ∈ Sᶜ := Finset.mem_compl.mpr hj
      have hins : (insert j S)ᶜ = Sᶜ.erase j := by
        ext i
        simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_erase, not_or]
      have hlt : (insert j S)ᶜ.card < n := by
        rw [← hS, hins]
        exact Finset.card_erase_lt_of_mem hjc
      exact le_trans (prob₂_DEv_le_insert h0 h1 hj) (ih _ hlt (insert j S) rfl)

/-- **The van den Berg-Kesten inequality on the finite cube.**  For a product
measure with parameters `p` and two increasing events, the probability that they
occur disjointly is at most the product of their probabilities. -/
theorem prob_disjointOcc_le {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1)
    {A B : Set (ι → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    prob p (disjointOcc A B) ≤ prob p A * prob p B := by
  rw [disjointOcc_eq_wit hA hB, ← prob₂_DEv_empty p A B, ← prob₂_DEv_univ p hA hB]
  exact prob₂_DEv_le_univ_aux h0 h1 A B _ ∅ rfl

/-! ### The inequality for a product of Bernoulli measures -/

open MeasureTheory

/-- The disjoint occurrence with the certificates given as sets of coordinates.
Over a finite index type this is `disjointOcc`. -/
def disjointOccSet (A B : Set (ι → Bool)) : Set (ι → Bool) :=
  {ω | ∃ K L : Set ι, Disjoint K L ∧
        (∀ ω', (∀ i ∈ K, ω' i = ω i) → ω' ∈ A) ∧
        (∀ ω', (∀ i ∈ L, ω' i = ω i) → ω' ∈ B)}

omit [DecidableEq ι] in
theorem disjointOccSet_eq (A B : Set (ι → Bool)) :
    disjointOccSet A B = disjointOcc A B := by
  classical
  ext ω
  constructor
  · rintro ⟨K, L, hKL, hA, hB⟩
    refine ⟨Finset.univ.filter (· ∈ K), Finset.univ.filter (· ∈ L), ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi hj
      rw [Finset.mem_filter] at hi hj
      exact (Set.disjoint_left.mp hKL) hi.2 hj.2
    · exact fun ω' h => hA ω' fun i hi =>
        h i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    · exact fun ω' h => hB ω' fun i hi =>
        h i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  · rintro ⟨K, L, hKL, hA, hB⟩
    exact ⟨↑K, ↑L, Finset.disjoint_coe.mpr hKL, fun ω' h => hA ω' fun i hi => h i hi,
      fun ω' h => hB ω' fun i hi => h i hi⟩

theorem measure_singleton_bool (ν : Measure Bool) [IsProbabilityMeasure ν] (b : Bool) :
    (ν {b}).toReal = wgt ((ν {true}).toReal) b := by
  cases b
  · have hsplit : ν {false} + ν {true} = 1 := by
      have : ({false} ∪ {true} : Set Bool) = Set.univ := by
        ext b; cases b <;> simp
      have hd : Disjoint ({false} : Set Bool) {true} := by
        simp
      rw [← measure_union hd (MeasurableSet.singleton _), this, measure_univ]
    have h1 : ν {false} ≠ ⊤ := measure_ne_top _ _
    have h2 : ν {true} ≠ ⊤ := measure_ne_top _ _
    have := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add h1 h2] at this
    simp only [ENNReal.toReal_one] at this
    simp [wgt]
    linarith
  · simp [wgt]

omit [DecidableEq ι] in
theorem measure_pi_singleton (μ : ι → Measure Bool) [∀ i, IsProbabilityMeasure (μ i)]
    (ω : ι → Bool) : Measure.pi μ {ω} = ∏ i, μ i {ω i} := by
  have h : ({ω} : Set (ι → Bool)) = Set.univ.pi fun i => ({ω i} : Set Bool) := by
    ext η
    simp only [Set.mem_singleton_iff, Set.mem_univ_pi, Set.mem_singleton_iff]
    exact ⟨fun h i => by rw [h], fun h => funext h⟩
  rw [h, Measure.pi_pi]

theorem measure_pi_toReal_eq_prob (μ : ι → Measure Bool) [∀ i, IsProbabilityMeasure (μ i)]
    (X : Set (ι → Bool)) :
    (Measure.pi μ X).toReal = prob (fun i => (μ i {true}).toReal) X := by
  classical
  have hX : ((Finset.univ.filter fun ω : ι → Bool => ω ∈ X : Finset (ι → Bool)) : Set (ι → Bool))
      = X := by
    ext ω; simp
  have h1 : Measure.pi μ X = ∑ ω ∈ Finset.univ.filter fun ω : ι → Bool => ω ∈ X,
      Measure.pi μ {ω} := by
    rw [sum_measure_singleton, hX]
  rw [h1, ENNReal.toReal_sum fun ω _ => measure_ne_top _ _]
  rw [prob]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω ∈ X
  · rw [if_pos hω, Set.indicator_of_mem hω, measure_pi_singleton,
      ENNReal.toReal_prod, weight]
    exact Finset.prod_congr rfl fun i _ => measure_singleton_bool (μ i) (ω i)
  · rw [if_neg hω, Set.indicator_of_notMem hω]

/-- **The van den Berg-Kesten inequality** for a product of Bernoulli measures on
a finite product of two-point spaces: two increasing measurable events occur
disjointly with probability at most the product of their probabilities. -/
theorem measure_pi_disjointOccSet_le (μ : ι → Measure Bool) [∀ i, IsProbabilityMeasure (μ i)]
    {A B : Set (ι → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    Measure.pi μ (disjointOccSet A B) ≤ Measure.pi μ A * Measure.pi μ B := by
  classical
  have h0 : ∀ i, 0 ≤ (μ i {true}).toReal := fun i => ENNReal.toReal_nonneg
  have h1 : ∀ i, (μ i {true}).toReal ≤ 1 := by
    intro i
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by norm_num) (by simpa using prob_le_one)
  rw [disjointOccSet_eq]
  have hcore := prob_disjointOcc_le (p := fun i => (μ i {true}).toReal) h0 h1 hA hB
  rw [← measure_pi_toReal_eq_prob, ← measure_pi_toReal_eq_prob,
    ← measure_pi_toReal_eq_prob, ← ENNReal.toReal_mul] at hcore
  have hfin : Measure.pi μ A * Measure.pi μ B ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) hfin).mp hcore

end LatticeProb
