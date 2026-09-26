/-
Strassen's coupling theorem for `{0,1}`-valued fields on a countable set.

`IsIncreasingSet A` says that `A` is closed under increasing a `{0,1}`-valued field coordinatewise.
`exists_monotone_coupling` (Strassen's theorem, in the domination form used by the percolation
literature) states: if `μ` and `ν` are probability measures on `S → Bool` for a countable `S` and
every measurable increasing event is at least as likely under `μ` as under `ν`, then there is a
probability measure `π` on the product with first marginal `μ`, second marginal `ν`, and
`p.2 ≤ p.1` for `π`-almost every `p`.  `domination_of_monotone_coupling` is the converse.

Route (no Kolmogorov extension, no LP duality: Mathlib has Farkas only for closed cones and no
closedness of finitely generated cones, so the finite stage goes through Hall instead).
A. Integer Strassen on a finite poset `P` via Hall (`Fintype.all_card_le_filter_rel_iff_exists_injective`)
   on "copies" `Σ y, Fin (n y)` → `Σ x, Fin (m x)`; up-set domination is Hall's condition.
B. Rounding with denominator `D`: the small law is rounded down (excess to `⊥`), the large law
   rounded up (excess to `⊤`); this preserves up-set domination exactly and errs by at most
   `|P|/D` per set.
C. Weights of the finite-dimensional marginals on `P_F = (F → Bool)`, `F : Finset S`.
D. The discrete coupling on `(S → Bool)²` (extend by `false` off `F`), supported on `{p.2 ≤ p.1}`.
E. Level-`N` coupling with `F_N ↑ S`, `D_N = (N+1)|P_{F_N}|`: cylinder marginals within `1/(N+1)`.
F. Limit: `ProbabilityMeasure ((S → Bool)²)` is compact (Mathlib `instCompactSpaceProbabilityMeasure`,
   Prokhorov); take a limit along an ultrafilter `≤ atTop`; the closed support set passes by
   portmanteau (`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`), clopen cylinder masses
   pass by `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`, and cylinders form a
   generating π-system (`generateFrom_measurableCylinders`, `isPiSystem_measurableCylinders`).

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
import Mathlib

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- Verbatim copy of `Exploding.IsIncreasingSet`. -/
def IsIncreasingSet {S : Type} (A : Set (S → Bool)) : Prop :=
  ∀ ω ω' : S → Bool, ω ∈ A → (∀ s, ω s = true → ω' s = true) → ω' ∈ A

/-- The support set of a monotone coupling: second coordinate below the first. -/
def couplingSupport (S : Type) : Set ((S → Bool) × (S → Bool)) :=
  {p | ∀ s, p.2 s = true → p.1 s = true}

/-! ### 0. Order basics -/

-- Pi order on Bool: `Pi.le_def`, `Bool.le_iff_imp`.
private theorem aux_strassen_1 {ι : Type*} (ω ω' : ι → Bool) :
    (∀ s, ω s = true → ω' s = true) ↔ ω ≤ ω' := by
  simp only [Pi.le_def, Bool.le_iff_imp]


/-! ### A. Integer Strassen on a finite poset (Hall) -/

-- A ⊆ (A.image Sigma.fst).sigma (fun _ => univ); `Finset.card_le_card`, `Finset.card_sigma`,
-- `Finset.card_univ`, `Fintype.card_fin`.
private theorem aux_strassen_2 {P : Type*} [Fintype P] (n : P → ℕ) (A : Finset (Σ y : P, Fin (n y))) :
    A.card ≤ ∑ y ∈ A.image Sigma.fst, n y := by
  classical
  have hsub : A ⊆ (A.image Sigma.fst).sigma (fun y => (Finset.univ : Finset (Fin (n y)))) :=
    fun a ha => by
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_image_of_mem Sigma.fst ha, Finset.mem_univ a.snd⟩
  calc A.card
      ≤ ((A.image Sigma.fst).sigma (fun y => (Finset.univ : Finset (Fin (n y))))).card :=
        Finset.card_le_card hsub
    _ = ∑ y ∈ A.image Sigma.fst, (Finset.univ : Finset (Fin (n y))).card :=
        Finset.card_sigma _ _
    _ = ∑ y ∈ A.image Sigma.fst, n y :=
        Finset.sum_congr rfl (fun y _ => by simp)


-- The filter equals `U.sigma (fun _ => univ)`; `Finset.card_sigma`, `Finset.card_univ`,
-- `Fintype.card_fin`.
private theorem aux_strassen_3 {P : Type*} [Fintype P] (m : P → ℕ) (U : Finset P) :
    (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 ∈ U)).card = ∑ x ∈ U, m x := by
  rw [show (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 ∈ U)) = U.sigma (fun _ => Finset.univ) from ?_]
  · rw [Finset.card_sigma]
    simp [Finset.card_univ, Fintype.card_fin]
  · ext b
    simp [Finset.mem_sigma]


-- The up-closure of a finset is an upper set: `le_trans`.
private theorem aux_strassen_4 {P : Type*} [Fintype P] [PartialOrder P] (Y : Finset P) :
    IsUpperSet ((Finset.univ.filter (fun x : P => ∃ y ∈ Y, y ≤ x) : Finset P) : Set P) := by
  intro a b hab ha
  rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
  obtain ⟨-, y, hyY, hya⟩ := ha
  exact ⟨Finset.mem_univ b, y, hyY, le_trans hya hab⟩


-- Hall's condition on copies. U := up-closure of A.image fst (aux 4);
-- card A ≤ ∑_{A.image fst} n (aux 2) ≤ ∑_U n (`Finset.sum_le_sum_of_subset`, y ≤ y)
-- ≤ ∑_U m (hup) = card {b | b.1 ∈ U} (aux 3), and that filter equals the target filter.
private theorem aux_strassen_5 {P : Type*} [Fintype P] [PartialOrder P] (m n : P → ℕ)
    (hup : ∀ U : Finset P, IsUpperSet (U : Set P) → ∑ y ∈ U, n y ≤ ∑ x ∈ U, m x)
    (A : Finset (Σ y : P, Fin (n y))) :
    A.card ≤ (Finset.univ.filter
      (fun b : Σ x : P, Fin (m x) => ∃ a ∈ A, a.1 ≤ b.1)).card := by
  classical
  set Y : Finset P := A.image Sigma.fst with hY
  set U : Finset P := Finset.univ.filter (fun x : P => ∃ y ∈ Y, y ≤ x) with hU
  have h1 : A.card ≤ ∑ y ∈ Y, n y := aux_strassen_2 n A
  have hYU : Y ⊆ U := fun y hy => by
    rw [hU]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨y, hy, le_rfl⟩⟩
  have h2 : ∑ y ∈ Y, n y ≤ ∑ y ∈ U, n y :=
    Finset.sum_le_sum_of_subset_of_nonneg hYU (fun i _ _ => Nat.zero_le _)
  have h3 : ∑ y ∈ U, n y ≤ ∑ x ∈ U, m x := hup U (aux_strassen_4 Y)
  have h4 : ∑ x ∈ U, m x =
      (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 ∈ U)).card :=
    (aux_strassen_3 m U).symm
  have hsub : (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 ∈ U)) ⊆
      (Finset.univ.filter
        (fun b : Σ x : P, Fin (m x) => ∃ a ∈ A, a.1 ≤ b.1)) := fun b hb => by
    rw [Finset.mem_filter] at hb
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ b, ?_⟩
    obtain ⟨-, hbU⟩ := hb
    rw [hU] at hbU
    obtain ⟨-, y, hy, hyb⟩ := Finset.mem_filter.mp hbU
    obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp hy
    exact ⟨a, ha, haeq ▸ hyb⟩
  calc A.card ≤ ∑ y ∈ Y, n y := h1
    _ ≤ ∑ y ∈ U, n y := h2
    _ ≤ ∑ x ∈ U, m x := h3
    _ = (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 ∈ U)).card := h4
    _ ≤ (Finset.univ.filter
        (fun b : Σ x : P, Fin (m x) => ∃ a ∈ A, a.1 ≤ b.1)).card :=
        Finset.card_le_card hsub


-- `Fintype.all_card_le_filter_rel_iff_exists_injective` with r a b := a.1 ≤ b.1, and aux 5.
private theorem aux_strassen_6 {P : Type*} [Fintype P] [PartialOrder P] (m n : P → ℕ)
    (hup : ∀ U : Finset P, IsUpperSet (U : Set P) → ∑ y ∈ U, n y ≤ ∑ x ∈ U, m x) :
    ∃ f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x)),
      Function.Injective f ∧ ∀ a, a.1 ≤ (f a).1 := by
  have h := (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun a : Σ y : P, Fin (n y) => fun b : Σ x : P, Fin (m x) => a.1 ≤ b.1)).mp
  exact h (fun A => aux_strassen_5 m n hup A)


-- Equal cardinalities: `Fintype.card_sigma`, `Fintype.card_fin`; then
-- `Fintype.bijective_iff_injective_and_card`.
private theorem aux_strassen_7 {P : Type*} [Fintype P] (m n : P → ℕ)
    (hsum : ∑ x, m x = ∑ y, n y) (f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x)))
    (hf : Function.Injective f) : Function.Bijective f := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hf, ?_⟩
  rw [Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact hsum.symm


/-- Number of copies of `y` sent to copies of `x`. -/
noncomputable def transportCount {P : Type*} [Fintype P] {m n : P → ℕ}
    (f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x))) (y x : P) : ℕ :=
  (Finset.univ.filter (fun i : Fin (n y) => (f ⟨y, i⟩).1 = x)).card

-- Row sums: `Finset.card_eq_sum_card_fiberwise` (map i ↦ (f ⟨y,i⟩).1 into univ),
-- `Finset.card_univ`, `Fintype.card_fin`.
private theorem aux_strassen_8 {P : Type*} [Fintype P] {m n : P → ℕ}
    (f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x))) (y : P) :
    ∑ x, transportCount f y x = n y := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin (n y))))
    (t := (Finset.univ : Finset P))
    (f := fun i : Fin (n y) => (f ⟨y, i⟩).1) (fun i _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  simp only [transportCount]
  rw [← h]


-- ∑_y #{i | (f⟨y,i⟩).1 = x} = #{a | (f a).1 = x}: the filter is
-- `univ.sigma (fun y => filter ..)`, `Finset.card_sigma`.
private theorem aux_strassen_9 {P : Type*} [Fintype P] {m n : P → ℕ}
    (f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x))) (x : P) :
    ∑ y, transportCount f y x = (Finset.univ.filter (fun a => (f a).1 = x)).card := by
  have h : (Finset.univ.filter (fun a : Σ y : P, Fin (n y) => (f a).1 = x)) = Finset.univ.sigma (fun y : P => Finset.univ.filter (fun i : Fin (n y) => (f ⟨y, i⟩).1 = x)) := Finset.ext (fun a => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma])
  rw [h, Finset.card_sigma]
  simp [transportCount]


-- Bijection transports the fibre: `Finset.card_bij (fun a _ => f a)` (surjectivity from hf).
private theorem aux_strassen_10 {P : Type*} [Fintype P] {m n : P → ℕ}
    (f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x))) (hf : Function.Bijective f) (x : P) :
    (Finset.univ.filter (fun a => (f a).1 = x)).card
      = (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 = x)).card := by
  apply Finset.card_bij (fun a _ => f a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a1 _ a2 _ h
    exact hf.1 h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨a, ha⟩ := hf.2 b
    exact ⟨a, by rw [ha]; exact hb, ha⟩


-- The fibre over x is `{x}.sigma (fun _ => univ)` up to reindexing: aux 3 with U = {x},
-- `Finset.sum_singleton` (or directly `Finset.card_sigma`).
private theorem aux_strassen_11 {P : Type*} [Fintype P] (m : P → ℕ) (x : P) :
    (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 = x)).card = m x := by
  suffices h : (Finset.univ.filter (fun b : Sigma (fun y : P => Fin (m y)) => b.1 = x))
      = ({x} : Finset P).sigma (fun y => (Finset.univ : Finset (Fin (m y)))) by
    rw [h, Finset.card_sigma, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin]
  ext b
  simp [Finset.mem_sigma]


-- Nonzero count gives some i with (f⟨y,i⟩).1 = x (`Finset.card_ne_zero`, `Finset.mem_filter`);
-- then hmono ⟨y,i⟩.
private theorem aux_strassen_12 {P : Type*} [Fintype P] [PartialOrder P] {m n : P → ℕ}
    (f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x))) (hmono : ∀ a, a.1 ≤ (f a).1)
    (y x : P) (h : transportCount f y x ≠ 0) : y ≤ x := by
  rw [transportCount] at h
  obtain ⟨i, hi⟩ := Finset.card_ne_zero.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  calc y ≤ (f ⟨y, i⟩).1 := hmono ⟨y, i⟩
    _ = x := hi


-- Integer finite Strassen: k := transportCount f with f from aux 6; aux 7–12.
private theorem aux_strassen_13 {P : Type*} [Fintype P] [PartialOrder P] (m n : P → ℕ)
    (hsum : ∑ x, m x = ∑ y, n y)
    (hup : ∀ U : Finset P, IsUpperSet (U : Set P) → ∑ y ∈ U, n y ≤ ∑ x ∈ U, m x) :
    ∃ k : P → P → ℕ, (∀ y, ∑ x, k y x = n y) ∧ (∀ x, ∑ y, k y x = m x) ∧
      ∀ y x, k y x ≠ 0 → y ≤ x := by
  obtain ⟨f, hf_inj, hf_mono⟩ := aux_strassen_6 m n hup
  have hf_bij : Function.Bijective f := aux_strassen_7 m n hsum f hf_inj
  refine ⟨transportCount f, ?_, ?_, ?_⟩
  · intro y
    exact aux_strassen_8 f y
  · intro x
    rw [aux_strassen_9 f x, aux_strassen_10 f hf_bij x, aux_strassen_11 m x]
  · intro y x h
    exact aux_strassen_12 f hf_mono y x h


/-! ### B. Rounding real weights to denominator `D` -/

/-- Round down off `⊥`, give the remainder to `⊥` (keeps up-set masses from growing). -/
noncomputable def roundLow {P : Type*} [Fintype P] [PartialOrder P] [OrderBot P]
    (a : P → ℝ) (D : ℕ) (y : P) : ℕ :=
  if y = ⊥ then D - ∑ z ∈ Finset.univ.erase ⊥, ⌊(D : ℝ) * a z⌋₊ else ⌊(D : ℝ) * a y⌋₊

/-- Round down off `⊤`, give the remainder to `⊤` (keeps up-set masses from shrinking). -/
noncomputable def roundHigh {P : Type*} [Fintype P] [PartialOrder P] [OrderTop P]
    (b : P → ℝ) (D : ℕ) (x : P) : ℕ :=
  if x = ⊤ then D - ∑ z ∈ Finset.univ.erase ⊤, ⌊(D : ℝ) * b z⌋₊ else ⌊(D : ℝ) * b x⌋₊

-- `Nat.floor_le` (0 ≤ D a z), `Nat.lt_floor_add_one`, `Finset.sum_le_sum`, `Finset.mul_sum`,
-- `Nat.cast_sum`, `Finset.card_eq_sum_ones`.
private theorem aux_strassen_14 {P : Type*} (a : P → ℝ) (ha : ∀ z, 0 ≤ a z) (D : ℕ) (s : Finset P) :
    ((∑ z ∈ s, ⌊(D : ℝ) * a z⌋₊ : ℕ) : ℝ) ≤ D * ∑ z ∈ s, a z ∧
      (D : ℝ) * ∑ z ∈ s, a z - s.card ≤ ((∑ z ∈ s, ⌊(D : ℝ) * a z⌋₊ : ℕ) : ℝ) := by
  constructor
  · rw [Nat.cast_sum, Finset.mul_sum]; exact Finset.sum_le_sum (fun z _ => Nat.floor_le (mul_nonneg (Nat.cast_nonneg D) (ha z)))
  · rw [Nat.cast_sum, Finset.mul_sum, show (s.card : ℝ) = ∑ _z ∈ s, (1 : ℝ) by rw [Finset.sum_const, nsmul_eq_mul, mul_one], ← Finset.sum_sub_distrib]; exact Finset.sum_le_sum (fun z _ => by have hlt := Nat.lt_floor_add_one ((D : ℝ) * a z); linarith)


-- aux 14 upper half, ∑_s a ≤ ∑_univ a = 1 (`Finset.sum_le_sum_of_subset_of_nonneg`),
-- `Nat.cast_le`.
private theorem aux_strassen_15 {P : Type*} [Fintype P] (a : P → ℝ) (ha : ∀ z, 0 ≤ a z)
    (ha1 : ∑ z, a z = 1) (D : ℕ) (s : Finset P) :
    ∑ z ∈ s, ⌊(D : ℝ) * a z⌋₊ ≤ D := by
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have h2 : (∑ z ∈ s, a z) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ => ha i)).trans (le_of_eq ha1)
  refine (Nat.cast_le (α := ℝ)).mp ?_
  exact (Nat.cast_sum s (fun z => ⌊(D : ℝ) * a z⌋₊)).trans_le
    (((Finset.sum_le_sum (fun z _ => Nat.floor_le (mul_nonneg hD0 (ha z)))).trans
      (le_of_eq (Finset.mul_sum s a (D : ℝ)).symm)).trans
      ((mul_le_mul_of_nonneg_left h2 hD0).trans (le_of_eq (mul_one (D : ℝ)))))


-- Generic rounding error: r agrees with the floor off one point p and sums to D.
-- Case p ∉ E: aux 14 with card E ≤ card P (`Finset.card_le_univ`).
private theorem aux_strassen_16 {P : Type*} [Fintype P] (a : P → ℝ) (ha : ∀ z, 0 ≤ a z)
    (D : ℕ) (r : P → ℕ) (p : P) (hr : ∀ z, z ≠ p → r z = ⌊(D : ℝ) * a z⌋₊)
    (E : Finset P) (hpE : p ∉ E) :
    |((∑ z ∈ E, r z : ℕ) : ℝ) - D * ∑ z ∈ E, a z| ≤ Fintype.card P := by
  have hlow : ∀ z ∈ E, (-1:ℝ) ≤ (r z : ℝ) - (D:ℝ) * a z := fun z hz => by
    have hzr : r z = ⌊(D:ℝ) * a z⌋₊ := hr z (fun h => hpE (h ▸ hz))
    rw [hzr]
    have hlt := Nat.lt_floor_add_one ((D:ℝ) * a z)
    linarith
  have hhigh : ∀ z ∈ E, (r z : ℝ) - (D:ℝ) * a z ≤ 1 := fun z hz => by
    have hzr : r z = ⌊(D:ℝ) * a z⌋₊ := hr z (fun h => hpE (h ▸ hz))
    rw [hzr]
    have hle := Nat.floor_le (show (0:ℝ) ≤ (D:ℝ) * a z by
      exact mul_nonneg (Nat.cast_nonneg D) (ha z))
    linarith
  have habs : ∀ z ∈ E, |(r z : ℝ) - (D:ℝ) * a z| ≤ (1:ℝ) :=
    fun z hz => abs_le.mpr ⟨hlow z hz, hhigh z hz⟩
  have h1 : |∑ z ∈ E, ((r z : ℝ) - (D:ℝ) * a z)| ≤ ∑ z ∈ E, (1:ℝ) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum habs)
  have h2 : (∑ z ∈ E, (1:ℝ)) = (E.card : ℝ) := by simp
  have h3 : (E.card : ℝ) ≤ (Fintype.card P : ℝ) := by exact_mod_cast Finset.card_le_univ E
  rw [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  linarith


-- Case p ∈ E: ∑_E r = D − ∑_{Eᶜ} r and ∑_E a = 1 − ∑_{Eᶜ} a (`Finset.sum_add_sum_compl`),
-- then aux 16 on Eᶜ (p ∉ Eᶜ).
private theorem aux_strassen_17 {P : Type*} [Fintype P] (a : P → ℝ) (ha : ∀ z, 0 ≤ a z)
    (ha1 : ∑ z, a z = 1) (D : ℕ) (r : P → ℕ) (hrD : ∑ z, r z = D) (p : P)
    (hr : ∀ z, z ≠ p → r z = ⌊(D : ℝ) * a z⌋₊) (E : Finset P) :
    |((∑ z ∈ E, r z : ℕ) : ℝ) - D * ∑ z ∈ E, a z| ≤ Fintype.card P := by
  classical
  have hmain : ∀ T : Finset P, p ∉ T → |((∑ z ∈ T, r z : ℕ) : ℝ) - (D : ℝ) * ∑ z ∈ T, a z| ≤ (Fintype.card P : ℝ) := fun T hT => aux_strassen_16 a ha D r p hr T hT
  by_cases hpE : p ∈ E
  · have hT : p ∉ Eᶜ := (Finset.notMem_compl).mpr hpE
    have h16 := hmain Eᶜ hT
    have hsum : ((∑ z ∈ E, r z : ℕ) : ℝ) + ((∑ z ∈ Eᶜ, r z : ℕ) : ℝ) = (D : ℝ) := (by exact_mod_cast (Finset.sum_add_sum_compl E r).trans (by rw [hrD]))
    have ha0 : (∑ z ∈ E, a z) + (∑ z ∈ Eᶜ, a z) = 1 := (Finset.sum_add_sum_compl E a).trans (by rw [ha1])
    have hU : ((∑ z ∈ Eᶜ, r z : ℕ) : ℝ) = (D : ℝ) - ((∑ z ∈ E, r z : ℕ) : ℝ) := (by linarith)
    have hV : ∑ z ∈ Eᶜ, a z = 1 - ∑ z ∈ E, a z := (by linarith)
    have key : ((∑ z ∈ E, r z : ℕ) : ℝ) - (D : ℝ) * ∑ z ∈ E, a z = -(((∑ z ∈ Eᶜ, r z : ℕ) : ℝ) - (D : ℝ) * ∑ z ∈ Eᶜ, a z) := (by rw [hU, hV]; ring)
    rw [key, abs_neg]
    exact h16
  · exact hmain E hpE


-- `Finset.add_sum_erase` at ⊥, `if_pos`/`if_neg` via `Finset.sum_congr`, `Nat.sub_add_cancel`
-- with aux 15.
private theorem aux_strassen_18 {P : Type*} [Fintype P] [PartialOrder P] [OrderBot P] (a : P → ℝ)
    (ha : ∀ z, 0 ≤ a z) (ha1 : ∑ z, a z = 1) (D : ℕ) : ∑ y, roundLow a D y = D := by
  have h1 : roundLow a D (⊥ : P) = D - ∑ z ∈ Finset.univ.erase (⊥ : P), ⌊(D : ℝ) * a z⌋₊ := (by simp [roundLow])
  have h2 : ∑ y ∈ Finset.univ.erase (⊥ : P), roundLow a D y = ∑ y ∈ Finset.univ.erase (⊥ : P), ⌊(D : ℝ) * a y⌋₊ := (by
    apply Finset.sum_congr rfl
    intro y hy
    simp only [roundLow, if_neg (Finset.ne_of_mem_erase hy)])
  rw [← Finset.add_sum_erase (Finset.univ : Finset P) (fun y => roundLow a D y) (Finset.mem_univ (⊥ : P))]
  rw [h1, h2]
  exact Nat.sub_add_cancel (aux_strassen_15 a ha ha1 D _)


-- Same with ⊤.
private theorem aux_strassen_19 {P : Type*} [Fintype P] [PartialOrder P] [OrderTop P] (b : P → ℝ)
    (hb : ∀ z, 0 ≤ b z) (hb1 : ∑ z, b z = 1) (D : ℕ) : ∑ x, roundHigh b D x = D := by
  have hsplit := Finset.add_sum_erase (s := (Finset.univ : Finset P)) (f := roundHigh b D)
    (a := ⊤) (Finset.mem_univ _)
  have htop : roundHigh b D (⊤ : P) = D - ∑ x ∈ (Finset.univ.erase (⊤ : P)), ⌊(D : ℝ) * b x⌋₊ :=
    if_pos rfl
  have hoff : ∀ x ∈ (Finset.univ.erase (⊤ : P)),
      roundHigh b D x = ⌊(D : ℝ) * b x⌋₊ :=
    fun x hx => if_neg (Finset.ne_of_mem_erase hx)
  have hsum_off : ∑ x ∈ (Finset.univ.erase (⊤ : P)), roundHigh b D x
      = ∑ x ∈ (Finset.univ.erase (⊤ : P)), ⌊(D : ℝ) * b x⌋₊ :=
    Finset.sum_congr rfl hoff
  have hle : ∑ x ∈ (Finset.univ.erase (⊤ : P)), ⌊(D : ℝ) * b x⌋₊ ≤ D :=
    aux_strassen_15 b hb hb1 D (Finset.univ.erase (⊤ : P))
  rw [← hsplit, htop, hsum_off, Nat.sub_add_cancel hle]


-- An upper set containing ⊥ is everything: `bot_le`, `Finset.eq_univ_iff_forall`.
private theorem aux_strassen_20 {P : Type*} [Fintype P] [PartialOrder P] [OrderBot P] (U : Finset P)
    (hU : IsUpperSet (U : Set P)) (h : ⊥ ∈ U) : U = Finset.univ := by
  ext z
  simp only [Finset.mem_univ, iff_true]
  exact hU bot_le h


-- A nonempty upper set contains ⊤: `le_top`.
private theorem aux_strassen_21 {P : Type*} [Fintype P] [PartialOrder P] [OrderTop P] (U : Finset P)
    (hU : IsUpperSet (U : Set P)) (h : U.Nonempty) : ⊤ ∈ U := by
  obtain ⟨y, hy⟩ := h
  exact hU le_top hy


-- Rounding down never raises an upper set's mass. ⊥ ∈ U: aux 20, aux 18, ha1.
-- ⊥ ∉ U: roundLow = floor on U (`if_neg`), aux 14.
private theorem aux_strassen_22 {P : Type*} [Fintype P] [PartialOrder P] [OrderBot P] (a : P → ℝ)
    (ha : ∀ z, 0 ≤ a z) (ha1 : ∑ z, a z = 1) (D : ℕ) (U : Finset P)
    (hU : IsUpperSet (U : Set P)) :
    ((∑ y ∈ U, roundLow a D y : ℕ) : ℝ) ≤ D * ∑ y ∈ U, a y := by
  exact if hbot : (⊥ : P) ∈ U then (by rw [aux_strassen_20 U hU hbot]; rw [aux_strassen_18 a ha ha1 D]; simp [ha1]) else (by have hsum : ∑ y ∈ U, roundLow a D y = ∑ y ∈ U, ⌊(D:ℝ) * a y⌋₊ := Finset.sum_congr rfl (fun y hy => by simp only [roundLow, if_neg (show ¬(y = ⊥) from fun h => hbot (h ▸ hy))]); rw [hsum]; exact (aux_strassen_14 a ha D U).1)


-- Rounding up never lowers an upper set's mass. U = ∅ trivial; else ⊤ ∈ U (aux 21), so on Uᶜ
-- roundHigh = floor; ∑_U roundHigh = D − ∑_{Uᶜ} floor (aux 19, `Finset.sum_add_sum_compl`)
-- ≥ D − D∑_{Uᶜ} b (aux 14) = D ∑_U b.
private theorem aux_strassen_roundup {P : Type*} [Fintype P] [PartialOrder P] [OrderTop P] (b : P → ℝ)
    (hb : ∀ z, 0 ≤ b z) (hb1 : ∑ z, b z = 1) (D : ℕ) (U : Finset P)
    (hU : IsUpperSet (U : Set P)) :
    (D : ℝ) * ∑ x ∈ U, b x ≤ ((∑ x ∈ U, roundHigh b D x : ℕ) : ℝ) := by
  classical
  by_cases hUne : U.Nonempty
  · have htop : ⊤ ∈ U := aux_strassen_21 U hU hUne
    have hcompl : ∀ x : P, x ∉ U → roundHigh b D x = ⌊(D : ℝ) * b x⌋₊ := by
      intro x hxU
      have hxne : x ≠ ⊤ := fun h => hxU (h.symm ▸ htop)
      rw [roundHigh, if_neg hxne]
    have hCeq : (∑ x ∈ Uᶜ, roundHigh b D x) = ∑ x ∈ Uᶜ, ⌊(D : ℝ) * b x⌋₊ := by
      exact Finset.sum_congr rfl (fun x hx => hcompl x (Finset.mem_compl.mp hx))
    have hC : ((∑ x ∈ Uᶜ, roundHigh b D x : ℕ) : ℝ) ≤ (D : ℝ) * ∑ x ∈ Uᶜ, b x := by
      rw [hCeq]
      exact (aux_strassen_14 b hb D Uᶜ).1
    have hsum_all : (∑ x, roundHigh b D x) = D := aux_strassen_19 b hb hb1 D
    have h1 : ((∑ x ∈ U, roundHigh b D x : ℕ) : ℝ)
        + ((∑ x ∈ Uᶜ, roundHigh b D x : ℕ) : ℝ) = (D : ℝ) := by
      rw [← Nat.cast_add, Finset.sum_add_sum_compl U (roundHigh b D), hsum_all]
    have h3 : ∑ x ∈ U, b x + ∑ x ∈ Uᶜ, b x = 1 := by
      rw [Finset.sum_add_sum_compl U b, hb1]
    have h4 : (D : ℝ) * ∑ x ∈ U, b x = (D : ℝ) - (D : ℝ) * ∑ x ∈ Uᶜ, b x := by
      have h5 : ∑ x ∈ U, b x = 1 - ∑ x ∈ Uᶜ, b x := by linarith
      rw [h5]; ring
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hUne]
    simp

private theorem aux_strassen_23 {P : Type*} [Fintype P] [PartialOrder P] [OrderTop P] (b : P → ℝ)
    (hb : ∀ z, 0 ≤ b z) (hb1 : ∑ z, b z = 1) (D : ℕ) (U : Finset P)
    (hU : IsUpperSet (U : Set P)) :
    (D : ℝ) * ∑ x ∈ U, b x ≤ ((∑ x ∈ U, roundHigh b D x : ℕ) : ℝ) := by
  exact aux_strassen_roundup b hb hb1 D U hU


-- Error bounds: aux 17 with p = ⊥ (resp. ⊤), r = roundLow (resp. roundHigh); `if_neg`; aux 18/19.
private theorem aux_strassen_24 {P : Type*} [Fintype P] [PartialOrder P] [BoundedOrder P]
    (a : P → ℝ) (ha : ∀ z, 0 ≤ a z) (ha1 : ∑ z, a z = 1) (D : ℕ) (E : Finset P) :
    |((∑ z ∈ E, roundLow a D z : ℕ) : ℝ) - D * ∑ z ∈ E, a z| ≤ Fintype.card P ∧
      |((∑ z ∈ E, roundHigh a D z : ℕ) : ℝ) - D * ∑ z ∈ E, a z| ≤ Fintype.card P := by
  constructor
  · exact aux_strassen_17 a ha ha1 D (roundLow a D) (aux_strassen_18 a ha ha1 D) ⊥
      (fun z hz => by simp only [roundLow]; exact if_neg hz) E
  · exact aux_strassen_17 a ha ha1 D (roundHigh a D) (aux_strassen_19 a ha ha1 D) ⊤
      (fun z hz => by simp only [roundHigh]; exact if_neg hz) E


/-! ### C. Finite-dimensional marginal weights -/

/-- Weight of the finite pattern `y` on `F` under `μ`. -/
noncomputable def wt {S : Type} (μ : Measure (S → Bool)) (F : Finset S) (y : F → Bool) : ℝ :=
  (μ (F.restrict ⁻¹' {y})).toReal

-- `Finset.measurable_restrict` and `MeasurableSet.of_discrete` (Bool pi over a finite type is
-- discrete-measurable) — or `measurableSet_preimage` of `measurable_pi_lambda`.
private theorem aux_strassen_25 {S : Type} (F : Finset S) (T : Set (F → Bool)) :
    MeasurableSet (F.restrict ⁻¹' T : Set (S → Bool)) := by
  haveI : DiscreteMeasurableSpace (F → Bool) := inferInstance
  exact (MeasurableSet.of_discrete (α := F → Bool)).preimage (Finset.measurable_restrict F)


-- `MeasureTheory.sum_measure_preimage_singleton` (aux 25), `ENNReal.toReal_sum`
-- (`measure_ne_top`).
private theorem aux_strassen_26 {S : Type} (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (F : Finset S) (U : Finset (F → Bool)) :
    ∑ y ∈ U, wt μ F y = (μ (F.restrict ⁻¹' (U : Set (F → Bool)))).toReal := by
  have hg : Measurable (F.restrict : (S → Bool) → (↥F → Bool)) := Finset.measurable_restrict F
  have hmeas : ∀ y ∈ U,
      MeasurableSet ((F.restrict : (S → Bool) → (↥F → Bool)) ⁻¹' ({y} : Set (↥F → Bool))) :=
    fun y _ => (measurableSet_singleton y).preimage hg
  have hsum := sum_measureReal_preimage_singleton (μ := μ) U
    (f := (F.restrict : (S → Bool) → (↥F → Bool))) hmeas
  simp only [measureReal_def] at hsum
  simp only [wt]
  exact hsum


-- `ENNReal.toReal_nonneg`; aux 26 with U = univ, `Finset.coe_univ`, `Set.preimage_univ`,
-- `measure_univ`.
private theorem aux_strassen_27 {S : Type} (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (F : Finset S) : (∀ y, 0 ≤ wt μ F y) ∧ ∑ y, wt μ F y = 1 := by
  refine ⟨fun y => ENNReal.toReal_nonneg, ?_⟩
  rw [aux_strassen_26 μ F (Finset.univ : Finset (F → Bool))]
  simp


-- ω ≤ ω' (aux 1) ⇒ F.restrict ω ≤ F.restrict ω' (pointwise), then upper-set property.
private theorem aux_strassen_28 {S : Type} (F : Finset S) (U : Set (F → Bool)) (hU : IsUpperSet U) :
    IsIncreasingSet (F.restrict ⁻¹' U : Set (S → Bool)) := by
  intro ω ω' hω h
  refine hU ?_ hω
  rw [Pi.le_def]
  intro i
  exact Bool.le_iff_imp.mpr (h (i : S))


-- Domination transfers to up-sets of patterns: aux 26 (twice), hdom with aux 25, 28,
-- `ENNReal.toReal_mono` (`measure_ne_top`).
private theorem aux_strassen_29 {S : Type} (μ ν : Measure (S → Bool)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A)
    (F : Finset S) (U : Finset (F → Bool)) (hU : IsUpperSet (U : Set (F → Bool))) :
    ∑ y ∈ U, wt ν F y ≤ ∑ x ∈ U, wt μ F x := by
  rw [aux_strassen_26 ν F U, aux_strassen_26 μ F U]
  exact ENNReal.toReal_mono (measure_ne_top μ _)
    (hdom _ (aux_strassen_25 F (U : Set (F → Bool)))
      (aux_strassen_28 F (U : Set (F → Bool)) hU))


/-! ### D. The discrete coupling on the full space -/

/-- Extend a pattern on `F` by `false`. -/
noncomputable def ext {S : Type} (F : Finset S) (ω : F → Bool) : S → Bool :=
  fun s => if h : s ∈ F then ω ⟨s, h⟩ else false

-- `funext`, `dif_pos`.
private theorem aux_strassen_30 {S : Type} (F : Finset S) (ω : F → Bool) : F.restrict (ext F ω) = ω := by
  funext i
  simp [Finset.restrict, ext, i.2]


-- `dite` cases; aux 1 for the Pi order on `F → Bool`.
private theorem aux_strassen_31 {S : Type} (F : Finset S) (ω ω' : F → Bool) (h : ω ≤ ω') :
    ∀ s, ext F ω s = true → ext F ω' s = true := by
  intro s hs
  have hle : ∀ t, ω t ≤ ω' t := (Pi.le_def.mp h)
  rw [ext] at hs ⊢
  by_cases hF : s ∈ F
  · rw [dif_pos hF] at hs ⊢
    exact (Bool.le_iff_imp.mp (hle ⟨s, hF⟩)) hs
  · rw [dif_neg hF] at hs
    exact absurd hs (by simp)


-- Membership in a cylinder over G ⊆ F only sees F-coordinates: `mem_cylinder`,
-- G.restrict (ext F (F.restrict ω)) = G.restrict ω (`funext`, `dif_pos (hGF i.2)`).
private theorem aux_strassen_32 {S : Type} (F G : Finset S) (hGF : G ⊆ F) (T : Set (G → Bool))
    (ω : S → Bool) : ω ∈ cylinder G T ↔ ext F (F.restrict ω) ∈ cylinder G T := by
  have h : G.restrict (ext F (F.restrict ω)) = G.restrict ω := funext fun i => by
    simp only [StrassenAux.ext, Finset.restrict_def]
    exact dif_pos (hGF i.2)
  simp only [cylinder, Set.mem_preimage, h]


-- Cylinder mass as a pattern sum: the cylinder equals F.restrict ⁻¹' ↑E with
-- E = {x | ext F x ∈ C} (aux 32, aux 30), then aux 26.
private theorem aux_strassen_33 {S : Type} (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (F G : Finset S) (hGF : G ⊆ F) (T : Set (G → Bool)) :
    (μ (cylinder G T)).toReal
      = ∑ x ∈ Finset.univ.filter (fun x : F → Bool => ext F x ∈ cylinder G T), wt μ F x := by
  have h26 := aux_strassen_26 μ F (Finset.univ.filter (fun x : F → Bool => ext F x ∈ cylinder G T))
  rw [h26]
  apply congrArg (fun s => (μ s).toReal)
  apply Set.ext
  intro ω
  simp only [MeasureTheory.cylinder, Set.mem_preimage, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact aux_strassen_32 F G hGF T ω


/-- The discrete coupling: mass `k y x / D` at `(ext x, ext y)` (first coordinate = large law). -/
noncomputable def cplMeasure {S : Type} (F : Finset S) (D : ℕ) (k : (F → Bool) → (F → Bool) → ℕ) :
    Measure ((S → Bool) × (S → Bool)) :=
  ∑ y, ∑ x, ((k y x : ENNReal) / D) • Measure.dirac (ext F x, ext F y)

-- Total mass: `cplMeasure`, `Measure.finsetSum_apply`, `Measure.smul_apply`, `measure_univ`
-- (dirac is a probability measure), `smul_eq_mul`, `mul_one`.
private theorem aux_aux_strassen_34_1 {S : Type} (F : Finset S) (D : ℕ)
    (k : (F → Bool) → (F → Bool) → ℕ) :
    cplMeasure F D k Set.univ = ∑ y, ∑ x, (k y x : ENNReal) / D := by
  simp only [cplMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]

-- `div_eq_mul_inv`, `Finset.sum_mul` (twice), `Nat.cast_sum` (twice).
private theorem aux_aux_strassen_34_2 {ι κ : Type} [Fintype ι] [Fintype κ] (k : ι → κ → ℕ) (D : ℕ) :
    ∑ y, ∑ x, (k y x : ENNReal) / D = ((∑ y, ∑ x, k y x : ℕ) : ENNReal) / D := by
  simp only [ENNReal.div_eq_inv_mul, ← Finset.mul_sum, ← Nat.cast_sum]

-- `Measure.coe_finsetSum`, `Measure.smul_apply`, `measure_univ` of dirac;
-- ∑∑ k/D = (∑∑ k)/D (`ENNReal.sum_div`? — or `Finset.sum_div` in ENNReal via `div_eq_mul_inv`,
-- `Finset.sum_mul`), `ENNReal.div_self`.
private theorem aux_strassen_34 {S : Type} (F : Finset S) (D : ℕ) (hD : D ≠ 0)
    (k : (F → Bool) → (F → Bool) → ℕ) (hk : ∑ y, ∑ x, k y x = D) :
    IsProbabilityMeasure (cplMeasure F D k) := by
  constructor
  rw [aux_aux_strassen_34_1, aux_aux_strassen_34_2, hk]
  exact ENNReal.div_self (Nat.cast_ne_zero.mpr hD) (ENNReal.natCast_ne_top D)

-- Each atom is in couplingSupport or has weight 0 (aux 31); `Measure.dirac_apply'`
-- (couplingSupportᶜ measurable: aux 43 below gives closedness; or directly a countable
-- intersection of measurable sets), `Finset.sum_eq_zero`.
private theorem aux_strassen_35 {S : Type} [Countable S] (F : Finset S) (D : ℕ) (k : (F → Bool) → (F → Bool) → ℕ)
    (hk : ∀ y x, k y x ≠ 0 → y ≤ x) : cplMeasure F D k (couplingSupport S)ᶜ = 0 := by
  rw [cplMeasure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun x _ => ?_
  by_cases hkxy : k y x = 0
  · simp [hkxy]
  · have hle : y ≤ x := hk y x hkxy
    have hmem : (ext F x, ext F y) ∈ couplingSupport S := by
      intro s hs
      simp only [ext] at hs ⊢
      by_cases hF : s ∈ F
      · rw [dif_pos hF] at hs ⊢
        exact Bool.le_iff_imp.mp (Pi.le_def.mp hle ⟨s, hF⟩) hs
      · rw [dif_neg hF] at hs
        exact absurd hs (by simp)
    simp [Set.mem_compl_iff, hmem]

-- First marginal: `Measure.coe_finsetSum`, `Measure.dirac_apply'` (`measurableSet_prod`),
-- `Finset.sum_comm`, `Finset.sum_filter`, `Finset.sum_div`/`ENNReal.sum_div`, `Nat.cast_sum`.
private theorem aux_strassen_36 {S : Type} (F : Finset S) (D : ℕ) (k : (F → Bool) → (F → Bool) → ℕ)
    (A : Set (S → Bool)) (hA : MeasurableSet A) :
    cplMeasure F D k (A ×ˢ Set.univ)
      = ∑ x ∈ Finset.univ.filter (fun x => ext F x ∈ A), ((∑ y, k y x : ℕ) : ENNReal) / D := by
  rw [cplMeasure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hA.prod MeasurableSet.univ), Set.indicator_apply,
    Set.mem_prod, Set.mem_univ, and_true, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ext F x ∈ A
  · simp only [hx, if_true, ENNReal.div_eq_inv_mul, ← Finset.mul_sum, ← Nat.cast_sum]
  · simp only [hx, if_false, Finset.sum_const_zero]


-- Second marginal: same, without `Finset.sum_comm`.
private theorem aux_strassen_37 {S : Type} (F : Finset S) (D : ℕ) (k : (F → Bool) → (F → Bool) → ℕ)
    (A : Set (S → Bool)) (hA : MeasurableSet A) :
    cplMeasure F D k (Set.univ ×ˢ A)
      = ∑ y ∈ Finset.univ.filter (fun y => ext F y ∈ A), ((∑ x, k y x : ℕ) : ENNReal) / D := by
  classical
  have hprod : MeasurableSet (Set.univ ×ˢ A : Set ((S → Bool) × (S → Bool))) :=
    MeasurableSet.univ.prod hA
  have hterm : ∀ (y x : F → Bool),
      (((k y x : ENNReal) / D) • Measure.dirac (ext F x, ext F y)) (Set.univ ×ˢ A)
        = (if ext F y ∈ A then ((k y x : ENNReal) / D) else 0) := fun y x => by
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hprod, Set.indicator_apply]
    by_cases hy : ext F y ∈ A
    · simp [hy, Set.mem_prod]
    · simp [hy]
  unfold cplMeasure
  rw [Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Measure.coe_finsetSum, Finset.sum_apply, hterm]
  split_ifs with hy
  · simp only [ENNReal.div_eq_inv_mul]
    rw [← Finset.mul_sum, ← Nat.cast_sum]
  · simp


/-! ### E. The level-`F` approximate coupling -/

-- Integer data: m := roundHigh (wt μ F) D, n := roundLow (wt ν F) D; hsum from aux 18, 19;
-- hup from aux 22, 29, 23 and `Nat.cast_le`; then aux 13.
private theorem aux_strassen_38 {S : Type} (μ ν : Measure (S → Bool)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A)
    (F : Finset S) (D : ℕ) :
    ∃ k : (F → Bool) → (F → Bool) → ℕ,
      (∀ y, ∑ x, k y x = roundLow (wt ν F) D y) ∧
      (∀ x, ∑ y, k y x = roundHigh (wt μ F) D x) ∧ ∀ y x, k y x ≠ 0 → y ≤ x := by
  obtain ⟨hμ0, hμ1⟩ := aux_strassen_27 μ F
  obtain ⟨hν0, hν1⟩ := aux_strassen_27 ν F
  refine aux_strassen_13 (m := roundHigh (wt μ F) D) (n := roundLow (wt ν F) D) ?_ ?_
  · rw [aux_strassen_19 (wt μ F) hμ0 hμ1 D, aux_strassen_18 (wt ν F) hν0 hν1 D]
  · intro U hU
    have hA : ((∑ y ∈ U, roundLow (wt ν F) D y : ℕ) : ℝ) ≤ D * ∑ y ∈ U, wt ν F y :=
      aux_strassen_22 (wt ν F) hν0 hν1 D U hU
    have hB : D * ∑ y ∈ U, wt ν F y ≤ D * ∑ y ∈ U, wt μ F y :=
      mul_le_mul_of_nonneg_left (aux_strassen_29 μ ν hdom F U hU) (Nat.cast_nonneg D)
    have hC : D * ∑ y ∈ U, wt μ F y ≤ ((∑ y ∈ U, roundHigh (wt μ F) D y : ℕ) : ℝ) :=
      aux_strassen_23 (wt μ F) hμ0 hμ1 D U hU
    exact_mod_cast le_trans hA (le_trans hB hC)


-- Marginal error on a cylinder over G ⊆ F: aux 36 with the column sums, `ENNReal.toReal_sum`,
-- `ENNReal.toReal_div`; aux 33; |∑_E m/D − ∑_E wt| = |∑_E m − D∑_E wt|/D ≤ |P|/D (aux 24, 27).
private theorem aux_strassen_39 {S : Type} (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (F G : Finset S) (hGF : G ⊆ F) (T : Set (G → Bool)) (_hT : MeasurableSet T)
    (D : ℕ) (hD : D ≠ 0) (k : (F → Bool) → (F → Bool) → ℕ)
    (hcol : ∀ x, ∑ y, k y x = roundHigh (wt μ F) D x) :
    |(cplMeasure F D k (cylinder G T ×ˢ Set.univ)).toReal - (μ (cylinder G T)).toReal|
      ≤ Fintype.card (F → Bool) / D := by
  classical
  let E : Finset (↥F → Bool) := Finset.univ.filter (fun x => ext F x ∈ G.restrict ⁻¹' T)
  have hcyl : (μ (G.restrict ⁻¹' T)).toReal = ∑ x ∈ E, wt μ F x := aux_strassen_33 μ F G hGF T
  have hwt := aux_strassen_27 μ F
  have h24 := (aux_strassen_24 (wt μ F) hwt.1 hwt.2 D E).2
  have h24' : |(∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) - D * ∑ x ∈ E, wt μ F x|
      ≤ (Fintype.card (↥F → Bool) : ℝ) := (by simpa only [Nat.cast_sum] using h24)
  have hD0 : (0 : ℝ) < D := (by exact_mod_cast Nat.pos_of_ne_zero hD)
  have hDnz : (D : ℝ) ≠ 0 := ne_of_gt hD0
  have hDenn : (D : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (by exact_mod_cast hD)
  have hfin : ∀ x ∈ E, ((∑ y, k y x : ℕ) : ENNReal) / D ≠ ⊤ := fun x _ =>
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hDenn
  have hnum : (∑ x ∈ E, ((∑ y, k y x : ℕ) : ℝ))
      = (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) :=
    Finset.sum_congr rfl (fun x _ => (by rw [hcol x]))
  have hmeas : MeasurableSet (G.restrict ⁻¹' T) := (by exact aux_strassen_25 (F := G) T)
  have hmarg : (cplMeasure F D k ((G.restrict ⁻¹' T) ×ˢ Set.univ)).toReal
      = (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) / (D : ℝ) := (by
    rw [aux_strassen_36 F D k (G.restrict ⁻¹' T) hmeas]
    rw [ENNReal.toReal_sum hfin]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
    rw [← Finset.sum_div, hnum])
  have hAub : (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) - D * ∑ x ∈ E, wt μ F x
      ≤ (Fintype.card (↥F → Bool) : ℝ) := le_trans (le_abs_self _) h24'
  have hBub : D * ∑ x ∈ E, wt μ F x - (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ))
      ≤ (Fintype.card (↥F → Bool) : ℝ) := (by
    have h := neg_le_abs ((∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ))
      - D * ∑ x ∈ E, wt μ F x)
    rw [neg_sub] at h
    exact le_trans h h24')
  have hkey1 : (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) / (D : ℝ) - ∑ x ∈ E, wt μ F x
      = ((∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) - D * ∑ x ∈ E, wt μ F x) / (D : ℝ) := (by
    rw [sub_div, mul_div_cancel_left₀ _ hDnz])
  have hkey2 : ∑ x ∈ E, wt μ F x - (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ)) / (D : ℝ)
      = (D * ∑ x ∈ E, wt μ F x - (∑ x ∈ E, ((roundHigh (wt μ F) D x : ℕ) : ℝ))) / (D : ℝ) := (by
    rw [sub_div, mul_div_cancel_left₀ _ hDnz])
  change |(cplMeasure F D k ((G.restrict ⁻¹' T) ×ˢ Set.univ)).toReal
      - (μ (G.restrict ⁻¹' T)).toReal| ≤ (Fintype.card (↥F → Bool) : ℝ) / (D : ℝ)
  rw [hmarg, hcyl, abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · rw [hkey1]; exact div_le_div_of_nonneg_right hAub (le_of_lt hD0)
  · rw [hkey2]; exact div_le_div_of_nonneg_right hBub (le_of_lt hD0)


-- Same for the second coordinate: aux 37 with the row sums, aux 33, aux 24 (roundLow half).
private theorem aux_strassen_40 {S : Type} (ν : Measure (S → Bool)) [IsProbabilityMeasure ν]
    (F G : Finset S) (hGF : G ⊆ F) (T : Set (G → Bool)) (_hT : MeasurableSet T)
    (D : ℕ) (hD : D ≠ 0) (k : (F → Bool) → (F → Bool) → ℕ)
    (hrow : ∀ y, ∑ x, k y x = roundLow (wt ν F) D y) :
    |(cplMeasure F D k (Set.univ ×ˢ cylinder G T)).toReal - (ν (cylinder G T)).toReal|
      ≤ Fintype.card (F → Bool) / D := by
  classical
  have hDne : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD)
  have hD0 : (D : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have hCyl : MeasurableSet (cylinder G T : Set (S → Bool)) := aux_strassen_25 (S := S) G T
  have h1 : (cplMeasure F D k (Set.univ ×ˢ cylinder G T)).toReal
      = ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
          (roundLow (wt ν F) D y : ℝ) / (D : ℝ) := (by
    rw [aux_strassen_37 (S := S) F D k (cylinder G T) hCyl]
    rw [ENNReal.toReal_sum (fun y _ => ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hD0)]
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hrow y])
  obtain ⟨ha, ha1⟩ := aux_strassen_27 (S := S) ν F
  have h24 : |(∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
        (roundLow (wt ν F) D y : ℝ))
      - (D : ℝ) * ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
        wt ν F y| ≤ ((Fintype.card (F → Bool) : ℕ) : ℝ) := (by
    have h := (aux_strassen_24 (P := F → Bool) (wt ν F) ha ha1 D
      (Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T))).1
    rw [Nat.cast_sum] at h
    exact h)
  have h2 : (ν (cylinder G T)).toReal
      = ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T), wt ν F y :=
    aux_strassen_33 (S := S) ν F G hGF T
  have h3 : |(∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
        (roundLow (wt ν F) D y : ℝ) / (D : ℝ))
      - ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T), wt ν F y|
      = |(∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
          (roundLow (wt ν F) D y : ℝ))
        - (D : ℝ) * ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
          wt ν F y| / (D : ℝ) := (by
    rw [← Finset.sum_div]
    have hX : (∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
          (roundLow (wt ν F) D y : ℝ)) / (D : ℝ)
        - ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T), wt ν F y
        = ((∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
            (roundLow (wt ν F) D y : ℝ))
          - (D : ℝ) * ∑ y ∈ Finset.univ.filter (fun y : F → Bool => ext F y ∈ cylinder G T),
            wt ν F y) / (D : ℝ) := (by
      rw [eq_div_iff hDne, sub_mul, div_mul_cancel₀ _ hDne]
      ring)
    rw [hX, abs_div, abs_of_pos hDpos])
  rw [h1, h2, h3]
  exact div_le_div_of_nonneg_right h24 (le_of_lt hDpos)


-- Package: aux 38, then aux 34 (∑∑ k = ∑_y roundLow = D by aux 18, 27), 35, 39, 40.
private theorem aux_strassen_41 {S : Type} [Countable S] (μ ν : Measure (S → Bool)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A)
    (F : Finset S) (D : ℕ) (hD : D ≠ 0) :
    ∃ π : Measure ((S → Bool) × (S → Bool)), IsProbabilityMeasure π ∧
      π (couplingSupport S)ᶜ = 0 ∧
      ∀ G : Finset S, G ⊆ F → ∀ T : Set (G → Bool), MeasurableSet T →
        |(π (cylinder G T ×ˢ Set.univ)).toReal - (μ (cylinder G T)).toReal|
            ≤ Fintype.card (F → Bool) / D ∧
        |(π (Set.univ ×ˢ cylinder G T)).toReal - (ν (cylinder G T)).toReal|
            ≤ Fintype.card (F → Bool) / D := by
  obtain ⟨kk, hrw, hcl, hmn⟩ := aux_strassen_38 μ ν hdom F D
  exact ⟨cplMeasure F D kk, aux_strassen_34 F D hD kk (by
      rw [Finset.sum_congr rfl (fun y _ => hrw y)]
      exact aux_strassen_18 (wt ν F) (aux_strassen_27 ν F).1 (aux_strassen_27 ν F).2 D),
    aux_strassen_35 F D kk hmn, fun G hGF T hT =>
      ⟨aux_strassen_39 μ F G hGF T hT D hD kk hcl,
       aux_strassen_40 ν F G hGF T hT D hD kk hrw⟩⟩


/-! ### F. Passage to the limit -/

-- letI := Encodable.ofCountable S; F N := (Finset.range N).preimage Encodable.encode
-- (Encodable.encode_injective.injOn); N0 := G.sup encode + 1 (`Finset.le_sup`).
private theorem aux_strassen_42 {S : Type} [Countable S] :
    ∃ F : ℕ → Finset S, ∀ G : Finset S, ∃ N0, ∀ N, N0 ≤ N → G ⊆ F N := by
  classical
  letI := Encodable.ofCountable S
  refine ⟨fun N => (Finset.range N).preimage Encodable.encode
      (Encodable.encode_injective.injOn), ?_⟩
  intro G
  refine ⟨G.sup Encodable.encode + 1, fun N hN => ?_⟩
  intro x hx
  rw [Finset.mem_preimage, Finset.mem_range]
  exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup hx)) hN


-- couplingSupport = ⋂ s, (fun p => (p.1 s, p.2 s)) ⁻¹' {q | q.2 = true → q.1 = true};
-- `isClosed_iInter`, `(isClosed_discrete _).preimage` (continuity: `continuous_apply`,
-- `Continuous.prodMk`, `continuous_fst`, `continuous_snd`).
private theorem aux_strassen_43_eq (S : Type) :
    couplingSupport S = ⋂ s : S,
      (fun p : (S → Bool) × (S → Bool) => (p.1 s, p.2 s)) ⁻¹'
        {q : Bool × Bool | q.2 = true → q.1 = true} := by
  ext p
  simp [couplingSupport]

private theorem aux_strassen_43 (S : Type) : IsClosed (couplingSupport S) := by
  rw [aux_strassen_43_eq S]
  exact isClosed_iInter fun s =>
    IsClosed.preimage
      (Continuous.prodMk ((continuous_apply s).comp continuous_fst)
        ((continuous_apply s).comp continuous_snd)) (isClosed_discrete _)


-- `mem_measurableCylinders` gives C = cylinder s T; cylinder = s.restrict ⁻¹' T (`cylinder`
-- is defeq); `(isClopen_discrete T).preimage (Finset.continuous_restrict s)`.
private theorem aux_strassen_44 {S : Type} (C : Set (S → Bool))
    (hC : C ∈ measurableCylinders (fun _ : S => Bool)) : IsClopen C := by
  obtain ⟨s, T, hT, rfl⟩ := (mem_measurableCylinders _).mp hC
  haveI : DiscreteTopology (↥s → Bool) := Pi.discreteTopology
  exact IsClopen.preimage (isClopen_discrete T) (Finset.continuous_restrict s)


-- Compactness: `Ultrafilter.of atTop`, `Ultrafilter.of_le`, and
-- `isCompact_univ.ultrafilter_le_nhds (U.map Ps)` (instance `instCompactSpaceProbabilityMeasure`).
private theorem aux_strassen_45 {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    [OpensMeasurableSpace Y] [CompactSpace (ProbabilityMeasure Y)]
    (Ps : ℕ → ProbabilityMeasure Y) :
    ∃ (U : Ultrafilter ℕ) (P₀ : ProbabilityMeasure Y),
      (U : Filter ℕ) ≤ atTop ∧ Tendsto Ps (U : Filter ℕ) (𝓝 P₀) := by
  obtain ⟨P₀, -, hP₀⟩ := isCompact_univ.ultrafilter_le_nhds
    (Ultrafilter.map Ps (Ultrafilter.of atTop)) (by rw [le_principal_iff]; exact Filter.univ_mem)
  refine ⟨Ultrafilter.of atTop, P₀, Ultrafilter.of_le atTop, ?_⟩
  rw [Ultrafilter.coe_map] at hP₀
  exact hP₀


-- Closed full-mass sets pass to the limit: `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`,
-- `Filter.limsup_const`, `ProbabilityMeasure.apply_le_one`, `le_antisymm`.
private theorem aux_strassen_46 {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    [OpensMeasurableSpace Y] [HasOuterApproxClosed Y] (U : Ultrafilter ℕ)
    (Ps : ℕ → ProbabilityMeasure Y) (P₀ : ProbabilityMeasure Y)
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀)) (K : Set Y) (hK : IsClosed K)
    (h1 : ∀ n, Ps n K = 1) : P₀ K = 1 := by
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hK
  have hfn : (fun i : ℕ => ((Ps i : ProbabilityMeasure Y) : Measure Y) K)
      = (fun _ : ℕ => (1 : ENNReal)) :=
    funext (fun n =>
      ((ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (Ps n) K).symm).trans
        ((congrArg (fun r : NNReal => (r : ENNReal)) (h1 n)).trans ENNReal.coe_one))
  rw [hfn, limsup_const] at h
  exact le_antisymm (ProbabilityMeasure.apply_le_one P₀ K)
    (ENNReal.coe_le_coe.mp (by simpa using h))


-- Clopen masses pass: `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto` with
-- `IsClopen.frontier_eq`, `measure_empty`; `tendsto_nhds_unique` against `hc.mono_left hU`.
private theorem aux_strassen_47 {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    [OpensMeasurableSpace Y] [HasOuterApproxClosed Y] (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop)
    (Ps : ℕ → ProbabilityMeasure Y) (P₀ : ProbabilityMeasure Y)
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀)) (E : Set Y) (hE : IsClopen E) (c : NNReal)
    (hc : Tendsto (fun n => Ps n E) atTop (𝓝 c)) : P₀ E = c := by
  exact tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hlim hE) (hc.mono_left hU)


-- Marginal identification: `ext_of_generate_finite` with `generateFrom_measurableCylinders.symm`,
-- `isPiSystem_measurableCylinders`; `Measure.map_apply measurable_fst
-- (MeasurableSet.of_mem_measurableCylinders hC)`, `Set.prod_univ` (fst ⁻¹' C = C ×ˢ univ).
private theorem aux_strassen_48 {S : Type} (π : Measure ((S → Bool) × (S → Bool)))
    [IsProbabilityMeasure π] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (h : ∀ C ∈ measurableCylinders (fun _ : S => Bool), π (C ×ˢ Set.univ) = μ C) :
    π.map Prod.fst = μ := by
  haveI : IsFiniteMeasure (π.map Prod.fst) := inferInstance
  refine ext_of_generate_finite (measurableCylinders (fun _ : S => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    rw [Measure.map_apply measurable_fst (MeasurableSet.of_mem_measurableCylinders hC),
      ← Set.prod_univ]
    exact h C hC
  · rw [Measure.map_apply measurable_fst MeasurableSet.univ]
    simp


-- Same with `measurable_snd`, `Set.univ_prod`.
private theorem aux_strassen_49 {S : Type} (π : Measure ((S → Bool) × (S → Bool)))
    [IsProbabilityMeasure π] (ν : Measure (S → Bool)) [IsProbabilityMeasure ν]
    (h : ∀ C ∈ measurableCylinders (fun _ : S => Bool), π (Set.univ ×ˢ C) = ν C) :
    π.map Prod.snd = ν := by
  refine ext_of_generate_finite (measurableCylinders (fun _ : S => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    rw [Measure.map_apply measurable_snd (MeasurableSet.of_mem_measurableCylinders hC),
      ← Set.univ_prod]
    exact h C hC
  · rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ,
      measure_univ, measure_univ]


-- Real error → NNReal convergence: `NNReal.tendsto_coe`, `ProbabilityMeasure.coeFn_def`-style
-- `ENNReal.coe_toNNReal`, squeeze: |x_N − c| ≤ e N eventually and e → 0
-- (`squeeze_zero'`, `tendsto_sub_nhds_zero_iff`, `abs_sub_lt_iff`).
private theorem aux_strassen_50 (x : ℕ → NNReal) (c : NNReal) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hx : ∀ᶠ N in atTop, |(x N : ℝ) - c| ≤ e N) : Tendsto x atTop (𝓝 c) := by
  rw [← NNReal.tendsto_coe]
  refine (tendsto_iff_norm_sub_tendsto_zero).mpr ?_
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _)
      (hx.mono fun N hN => le_trans hN (le_abs_self _)) (by simpa using he.abs)


-- Error sequence: card P_N / ((N+1) card P_N) = 1/(N+1) (card P_N ≥ 1: `Fintype.card_pos`),
-- `tendsto_one_div_add_atTop_nhds_zero_nat`.
private theorem aux_strassen_51 (c : ℕ → ℕ) (hc : ∀ N, 0 < c N) :
    Tendsto (fun N => (c N : ℝ) / ((N + 1) * c N : ℕ)) atTop (𝓝 0) := by
  have hcN : ∀ N : ℕ, (c N : ℝ) ≠ 0 := fun N => Nat.cast_ne_zero.mpr (ne_of_gt (hc N))
  have hfun : ∀ N : ℕ, (c N : ℝ) / ((N + 1) * c N : ℕ) = 1 / ((N : ℝ) + 1) := fun N => by
    have h1 : (↑(c N) : ℝ) ≠ 0 := hcN N
    push_cast
    field_simp
  simp only [hfun]
  exact tendsto_one_div_add_atTop_nhds_zero_nat


-- Limit lemma. Ps N := ⟨π_N, _⟩; aux 45; mass on couplingSupport is 1 (`prob_compl_eq_zero_iff`,
-- aux 43, aux 46); for each cylinder C: C ×ˢ univ and univ ×ˢ C are clopen (aux 44,
-- `IsClopen.prod`, `isClopen_univ`), aux 47 with the hypotheses; aux 48, 49; the a.e. statement
-- from `measure_compl` / `ae_iff`.
private theorem aux_strassen_52d {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (A : Set Ω) (r : NNReal) (h : P A = r) : (P : Measure Ω) A = (r : ENNReal) := by
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P A, h]

private theorem aux_cyl_fst {S : Type} [Countable S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (P₀ : ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀))
    (hfst : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (C ×ˢ Set.univ)) atTop (𝓝 (μ C).toNNReal))
    (G : Finset S) (T : Set (G → Bool)) (hT : MeasurableSet T) :
    (↑P₀ : Measure ((S → Bool) × (S → Bool)))
        ((cylinder (α := fun _ : S => Bool) G T) ×ˢ (Set.univ : Set (S → Bool)))
      = μ (cylinder (α := fun _ : S => Bool) G T) := by
  have hmem : (cylinder (α := fun _ : S => Bool) G T) ∈ measurableCylinders (fun _ : S => Bool) :=
    (mem_measurableCylinders _).mpr ⟨G, T, hT, rfl⟩
  have hE : IsClopen ((cylinder (α := fun _ : S => Bool) G T) ×ˢ (Set.univ : Set (S → Bool))) :=
    IsClopen.prod (aux_strassen_44 _ hmem) isClopen_univ
  have hfront : P₀ (frontier ((cylinder (α := fun _ : S => Bool) G T) ×ˢ (Set.univ : Set (S → Bool)))) = 0 := by
    rw [hE.frontier_eq]
    simp
  have h1 : Tendsto (fun N => Ps N ((cylinder (α := fun _ : S => Bool) G T) ×ˢ Set.univ)) (U : Filter ℕ)
      (𝓝 ((μ (cylinder (α := fun _ : S => Bool) G T)).toNNReal)) :=
    (hfst _ hmem).mono_left hU
  have h2 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hlim hfront
  have h3 : P₀ ((cylinder (α := fun _ : S => Bool) G T) ×ˢ Set.univ)
      = (μ (cylinder (α := fun _ : S => Bool) G T)).toNNReal := tendsto_nhds_unique h2 h1
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P₀
      ((cylinder (α := fun _ : S => Bool) G T) ×ˢ Set.univ), h3,
    ENNReal.coe_toNNReal (measure_ne_top μ _)]

private theorem aux_cyl_snd {S : Type} [Countable S] (ν : Measure (S → Bool)) [IsProbabilityMeasure ν]
    (Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (P₀ : ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀))
    (hsnd : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (Set.univ ×ˢ C)) atTop (𝓝 (ν C).toNNReal))
    (G : Finset S) (T : Set (G → Bool)) (hT : MeasurableSet T) :
    (↑P₀ : Measure ((S → Bool) × (S → Bool)))
        ((Set.univ : Set (S → Bool)) ×ˢ (cylinder (α := fun _ : S => Bool) G T))
      = ν (cylinder (α := fun _ : S => Bool) G T) := by
  have hmem : (cylinder (α := fun _ : S => Bool) G T) ∈ measurableCylinders (fun _ : S => Bool) :=
    (mem_measurableCylinders _).mpr ⟨G, T, hT, rfl⟩
  have hE : IsClopen ((Set.univ : Set (S → Bool)) ×ˢ (cylinder (α := fun _ : S => Bool) G T)) :=
    IsClopen.prod isClopen_univ (aux_strassen_44 _ hmem)
  have hfront : P₀ (frontier ((Set.univ : Set (S → Bool)) ×ˢ (cylinder (α := fun _ : S => Bool) G T))) = 0 := by
    rw [hE.frontier_eq]
    simp
  have h1 : Tendsto (fun N => Ps N (Set.univ ×ˢ (cylinder (α := fun _ : S => Bool) G T))) (U : Filter ℕ)
      (𝓝 ((ν (cylinder (α := fun _ : S => Bool) G T)).toNNReal)) :=
    (hsnd _ hmem).mono_left hU
  have h2 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hlim hfront
  have h3 : P₀ (Set.univ ×ˢ (cylinder (α := fun _ : S => Bool) G T))
      = (ν (cylinder (α := fun _ : S => Bool) G T)).toNNReal := tendsto_nhds_unique h2 h1
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P₀
      (Set.univ ×ˢ (cylinder (α := fun _ : S => Bool) G T)), h3,
    ENNReal.coe_toNNReal (measure_ne_top ν _)]

private theorem aux_strassen_52e {S : Type} [Countable S]
    (Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hK : IsClosed (couplingSupport S))
    (hsupp : ∀ N, (↑(Ps N) : Measure ((S → Bool) × (S → Bool))) (couplingSupport S)ᶜ = 0)
    (U : Ultrafilter ℕ) (P₀ : ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hlim : Tendsto Ps (U : Filter ℕ) (𝓝 P₀)) :
    (↑P₀ : Measure ((S → Bool) × (S → Bool))) (couplingSupport S) = 1 := by
  have hPsK : ∀ N, (↑(Ps N) : Measure ((S → Bool) × (S → Bool))) (couplingSupport S) = (1 : ENNReal) :=
    fun N => (prob_compl_eq_zero_iff (μ := (↑(Ps N) : Measure ((S → Bool) × (S → Bool)))) hK.measurableSet).mp (hsupp N)
  have hlimsup : limsup (fun N => (↑(Ps N) : Measure ((S → Bool) × (S → Bool))) (couplingSupport S)) (U : Filter ℕ) = (1 : ENNReal) := by
    rw [show (fun N => (↑(Ps N) : Measure ((S → Bool) × (S → Bool))) (couplingSupport S)) = fun _ => (1 : ENNReal) from funext hPsK, limsup_const]
  have hle : (1 : ENNReal) ≤ (↑P₀ : Measure ((S → Bool) × (S → Bool))) (couplingSupport S) := by
    have hmain := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hK
    rwa [hlimsup] at hmain
  refine le_antisymm ?_ hle
  calc (↑P₀ : Measure ((S → Bool) × (S → Bool))) (couplingSupport S)
      = ((P₀ (couplingSupport S) : NNReal) : ENNReal) := (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure P₀ _).symm
    _ ≤ ((1 : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr (ProbabilityMeasure.apply_le_one P₀ _)
    _ = 1 := by norm_num

private theorem aux_strassen_52 {S : Type} [Countable S] (μ ν : Measure (S → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)))
    (hsupp : ∀ N, (Ps N : Measure ((S → Bool) × (S → Bool))) (couplingSupport S)ᶜ = 0)
    (hfst : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (C ×ˢ Set.univ)) atTop (𝓝 (μ C).toNNReal))
    (hsnd : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (Set.univ ×ˢ C)) atTop (𝓝 (ν C).toNNReal)) :
    ∃ π : Measure ((S → Bool) × (S → Bool)), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      ∀ᵐ p ∂π, ∀ s, p.2 s = true → p.1 s = true := by
  classical
  obtain ⟨U, P₀, hU, hlim⟩ := aux_strassen_45 Ps
  have hK : IsClosed (couplingSupport S) := aux_strassen_43 S
  refine ⟨(↑P₀ : Measure ((S → Bool) × (S → Bool))), inferInstance, ?_, ?_, ?_⟩
  · refine aux_strassen_48 _ μ ?_
    intro C hC
    obtain ⟨G, T, hT, rfl⟩ := (mem_measurableCylinders C).mp hC
    exact aux_cyl_fst μ Ps U hU P₀ hlim hfst G T hT
  · refine aux_strassen_49 _ ν ?_
    intro C hC
    obtain ⟨G, T, hT, rfl⟩ := (mem_measurableCylinders C).mp hC
    exact aux_cyl_snd ν Ps U hU P₀ hlim hsnd G T hT
  · rw [ae_iff]
    exact (prob_compl_eq_zero_iff (μ := (↑P₀ : Measure ((S → Bool) × (S → Bool)))) hK.measurableSet).mpr
      (aux_strassen_52e Ps hK hsupp U P₀ hlim)


/-- **Strassen's theorem** for `{0,1}`-valued fields on a countable set, in the domination form of
the Exploding externals: if every measurable increasing event is at least as likely under `μ` as
under `ν`, then there is a coupling whose first coordinate (law `μ`) dominates its second (law `ν`)
pointwise almost surely.
Assembly: F from aux 42; D_N := (N+1)·|P_{F N}|; π_N from aux 41 (`choose`); aux 50 + 51 give
cylinder convergence (for C = cylinder G T take N ≥ N0(G) from aux 42); aux 52. -/
theorem exists_coupling_of_domination {S : Type} [Countable S] (μ ν : Measure (S → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A) :
    ∃ π : Measure ((S → Bool) × (S → Bool)), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      ∀ᵐ p ∂π, ∀ s, p.2 s = true → p.1 s = true := by
  obtain ⟨F, hF⟩ := aux_strassen_42 (S := S)
  choose π hπprob hπsupp hπcyl using fun N : ℕ =>
    aux_strassen_41 (μ := μ) (ν := ν) hdom (F N) ((N + 1) * Fintype.card (F N → Bool))
      (Nat.pos_iff_ne_zero.mp (by positivity))
  let Ps : ℕ → ProbabilityMeasure ((S → Bool) × (S → Bool)) := fun N => ⟨π N, hπprob N⟩
  have hfst : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (C ×ˢ Set.univ)) atTop (𝓝 (μ C).toNNReal) := by
    intro C hC
    obtain ⟨G, T, hT, rfl⟩ := (mem_measurableCylinders C).mp hC
    obtain ⟨N0, hN0⟩ := hF G
    refine aux_strassen_50 _ _ _
      (aux_strassen_51 (fun N => Fintype.card (F N → Bool)) fun N => Fintype.card_pos) ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    have hb := (hπcyl N G (hN0 N hN) T hT).1
    have h1 : ((Ps N) (cylinder G T ×ˢ Set.univ) : ℝ)
        = ((π N) (cylinder G T ×ˢ Set.univ)).toReal := rfl
    have h2 : ((μ (cylinder G T)).toNNReal : ℝ) = (μ (cylinder G T)).toReal := rfl
    rw [h1, h2]
    exact hb
  have hsnd : ∀ C ∈ measurableCylinders (fun _ : S => Bool),
      Tendsto (fun N => Ps N (Set.univ ×ˢ C)) atTop (𝓝 (ν C).toNNReal) := by
    intro C hC
    obtain ⟨G, T, hT, rfl⟩ := (mem_measurableCylinders C).mp hC
    obtain ⟨N0, hN0⟩ := hF G
    refine aux_strassen_50 _ _ _
      (aux_strassen_51 (fun N => Fintype.card (F N → Bool)) fun N => Fintype.card_pos) ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    have hb := (hπcyl N G (hN0 N hN) T hT).2
    have h1 : ((Ps N) (Set.univ ×ˢ cylinder G T) : ℝ)
        = ((π N) (Set.univ ×ˢ cylinder G T)).toReal := rfl
    have h2 : ((ν (cylinder G T)).toNNReal : ℝ) = (ν (cylinder G T)).toReal := rfl
    rw [h1, h2]
    exact hb
  exact aux_strassen_52 μ ν Ps (fun N => hπsupp N) hfst hsnd

theorem exists_monotone_coupling {S : Type} [Countable S] (μ ν : Measure (S → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A) :
    ∃ π : Measure ((S → Bool) × (S → Bool)), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      ∀ᵐ p ∂π, ∀ s, p.2 s = true → p.1 s = true := by
  exact exists_coupling_of_domination μ ν hdom


/-! ### Converse (easy): a monotone coupling gives domination -/

-- ν A = π (snd ⁻¹' A) (`Measure.map_apply measurable_snd hA`) ≤ π (fst ⁻¹' A): on the full-mass
-- event, p.2 ∈ A ⇒ p.1 ∈ A (hA'); `measure_mono_ae` (`Filter.Eventually.mono`).
theorem domination_of_monotone_coupling {S : Type} (μ ν : Measure (S → Bool))
    (π : Measure ((S → Bool) × (S → Bool)))
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (hmono : ∀ᵐ p ∂π, ∀ s, p.2 s = true → p.1 s = true) :
    ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A := by
  intro A hA hA'
  rw [← hsnd, Measure.map_apply measurable_snd hA, ← hfst, Measure.map_apply measurable_fst hA]
  apply measure_mono_ae
  filter_upwards [hmono] with p hp hpA
  exact hA' p.2 p.1 hpA hp


end StrassenAux

end LatticeProb
