import Mathlib

/-!
# A. Integer Strassen on a finite poset (Hall)

Integer Strassen's theorem on a finite poset `P`: given equal totals `∑ m = ∑ n` and the
upper-set condition `∀ U, ∑_U n ≤ ∑_U m`, there is a transport plan `k : P → P → ℕ` with row sums
`n`, column sums `m`, and support in `{(y, x) | y ≤ x}` (`exists_transport_of_hall_condition`).
The route views `n`- and `m`-valued weights as "copies" `Σ y, Fin (n y)` and `Σ x, Fin (m x)`, so
that up-set domination is exactly Hall's marriage condition for an injection of copies
(`Fintype.all_card_le_filter_rel_iff_exists_injective`) that never decreases the underlying
point; bijectivity from equal totals turns the injection into a transport plan via
`transportCount`, the number of copies of `y` sent to copies of `x`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- A finset of pairs `⟨y, i⟩` has at most `∑_y n y` elements, summing `n` over the image of the
first projection. -/
private theorem card_le_sum_image_fst {P : Type*} [Fintype P] (n : P → ℕ)
    (A : Finset (Σ y : P, Fin (n y))) :
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


/-- The set of pairs with first projection in `U` has cardinality `∑_{x ∈ U} m x`. -/
private theorem card_filter_fst_mem_eq_sum {P : Type*} [Fintype P] (m : P → ℕ) (U : Finset P) :
    (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 ∈ U)).card = ∑ x ∈ U, m x := by
  rw [show (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 ∈ U))
      = U.sigma (fun _ => Finset.univ) from ?_]
  · rw [Finset.card_sigma]
    simp [Finset.card_univ, Fintype.card_fin]
  · ext b
    simp [Finset.mem_sigma]


/-- The up-closure of a finset (as a coerced set) is an upper set. -/
private theorem isUpperSet_filter_exists_mem_le {P : Type*} [Fintype P] [PartialOrder P]
    (Y : Finset P) :
    IsUpperSet ((Finset.univ.filter (fun x : P => ∃ y ∈ Y, y ≤ x) : Finset P) : Set P) := by
  intro a b hab ha
  rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
  obtain ⟨-, y, hyY, hya⟩ := ha
  exact ⟨Finset.mem_univ b, y, hyY, le_trans hya hab⟩


/-- Hall's condition on copies: if every upper set `U` has `∑_U n ≤ ∑_U m`, then every finset `A` of
`n`-copies has at most as many `m`-copies lying above its image. -/
private theorem card_le_card_filter_of_hall_condition {P : Type*} [Fintype P] [PartialOrder P]
    (m n : P → ℕ)
    (hup : ∀ U : Finset P, IsUpperSet (U : Set P) → ∑ y ∈ U, n y ≤ ∑ x ∈ U, m x)
    (A : Finset (Σ y : P, Fin (n y))) :
    A.card ≤ (Finset.univ.filter
      (fun b : Σ x : P, Fin (m x) => ∃ a ∈ A, a.1 ≤ b.1)).card := by
  classical
  set Y : Finset P := A.image Sigma.fst with hY
  set U : Finset P := Finset.univ.filter (fun x : P => ∃ y ∈ Y, y ≤ x) with hU
  have h1 : A.card ≤ ∑ y ∈ Y, n y := card_le_sum_image_fst n A
  have hYU : Y ⊆ U := fun y hy => by
    rw [hU]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨y, hy, le_rfl⟩⟩
  have h2 : ∑ y ∈ Y, n y ≤ ∑ y ∈ U, n y :=
    Finset.sum_le_sum_of_subset_of_nonneg hYU (fun i _ _ => Nat.zero_le _)
  have h3 : ∑ y ∈ U, n y ≤ ∑ x ∈ U, m x := hup U (isUpperSet_filter_exists_mem_le Y)
  have h4 : ∑ x ∈ U, m x =
      (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 ∈ U)).card :=
    (card_filter_fst_mem_eq_sum m U).symm
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


/-- Hall's marriage theorem applied to copies: the upper-set condition on `m, n` gives an injection
of `n`-copies into `m`-copies that never decreases the underlying point. -/
private theorem exists_injective_apply_fst_le_of_hall_condition {P : Type*} [Fintype P]
    [PartialOrder P] (m n : P → ℕ)
    (hup : ∀ U : Finset P, IsUpperSet (U : Set P) → ∑ y ∈ U, n y ≤ ∑ x ∈ U, m x) :
    ∃ f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x)),
      Function.Injective f ∧ ∀ a, a.1 ≤ (f a).1 := by
  have h := (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun a : Σ y : P, Fin (n y) => fun b : Σ x : P, Fin (m x) => a.1 ≤ b.1)).mp
  exact h (fun A => card_le_card_filter_of_hall_condition m n hup A)


/-- An injective map between copy types with equal total cardinalities is bijective. -/
private theorem bijective_of_injective_of_card_eq {P : Type*} [Fintype P] (m n : P → ℕ)
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

/-- The row sums of `transportCount f` recover `n y`, the number of copies of `y`. -/
private theorem sum_transportCount_eq {P : Type*} [Fintype P] {m n : P → ℕ}
    (f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x))) (y : P) :
    ∑ x, transportCount f y x = n y := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin (n y))))
    (t := (Finset.univ : Finset P))
    (f := fun i : Fin (n y) => (f ⟨y, i⟩).1) (fun i _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  simp only [transportCount]
  rw [← h]


/-- The column sums of `transportCount f` recover the number of copies of `f`'s image at `x`. -/
private theorem sum_transportCount_eq_card_filter_fst_eq {P : Type*} [Fintype P] {m n : P → ℕ}
    (f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x))) (x : P) :
    ∑ y, transportCount f y x = (Finset.univ.filter (fun a => (f a).1 = x)).card := by
  have h : (Finset.univ.filter (fun a : Σ y : P, Fin (n y) => (f a).1 = x)) = Finset.univ.sigma
      (fun y : P => Finset.univ.filter (fun i : Fin (n y) => (f ⟨y, i⟩).1 = x)) := Finset.ext
          (fun a => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma])
  rw [h, Finset.card_sigma]
  simp [transportCount]


/-- For bijective `f`, the fibre of copies with `(f a).1 = x` has the same cardinality as the fibre
`{b | b.1 = x}` of the codomain. -/
private theorem card_filter_fst_eq_eq_of_bijective {P : Type*} [Fintype P] {m n : P → ℕ}
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


/-- The fibre `{b | b.1 = x}` of copies over `x` has cardinality `m x`. -/
private theorem card_filter_fst_eq_eq_apply {P : Type*} [Fintype P] (m : P → ℕ) (x : P) :
    (Finset.univ.filter (fun b : Σ x : P, Fin (m x) => b.1 = x)).card = m x := by
  suffices h : (Finset.univ.filter (fun b : Sigma (fun y : P => Fin (m y)) => b.1 = x))
      = ({x} : Finset P).sigma (fun y => (Finset.univ : Finset (Fin (m y)))) by
    rw [h, Finset.card_sigma, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin]
  ext b
  simp [Finset.mem_sigma]


/-- A nonzero transport count `transportCount f y x` forces `y ≤ x`, given that `f` never decreases
the underlying point. -/
private theorem le_of_transportCount_ne_zero {P : Type*} [Fintype P] [PartialOrder P] {m n : P → ℕ}
    (f : (Σ y : P, Fin (n y)) → (Σ x : P, Fin (m x))) (hmono : ∀ a, a.1 ≤ (f a).1)
    (y x : P) (h : transportCount f y x ≠ 0) : y ≤ x := by
  rw [transportCount] at h
  obtain ⟨i, hi⟩ := Finset.card_ne_zero.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  calc y ≤ (f ⟨y, i⟩).1 := hmono ⟨y, i⟩
    _ = x := hi


/-- **Integer Strassen on a finite poset.** Given equal totals `∑ m = ∑ n` and the upper-set
condition `∀ U, ∑_U n ≤ ∑_U m`, there is a transport plan `k : P → P → ℕ` with row sums `n`, column
sums `m`, and support in `{(y, x) | y ≤ x}`. -/
theorem exists_transport_of_hall_condition {P : Type*} [Fintype P] [PartialOrder P]
    (m n : P → ℕ)
    (hsum : ∑ x, m x = ∑ y, n y)
    (hup : ∀ U : Finset P, IsUpperSet (U : Set P) → ∑ y ∈ U, n y ≤ ∑ x ∈ U, m x) :
    ∃ k : P → P → ℕ, (∀ y, ∑ x, k y x = n y) ∧ (∀ x, ∑ y, k y x = m x) ∧
      ∀ y x, k y x ≠ 0 → y ≤ x := by
  obtain ⟨f, hf_inj, hf_mono⟩ := exists_injective_apply_fst_le_of_hall_condition m n hup
  have hf_bij : Function.Bijective f := bijective_of_injective_of_card_eq m n hsum f hf_inj
  refine ⟨transportCount f, ?_, ?_, ?_⟩
  · intro y
    exact sum_transportCount_eq f y
  · intro x
    rw [sum_transportCount_eq_card_filter_fst_eq f x,
      card_filter_fst_eq_eq_of_bijective f hf_bij x, card_filter_fst_eq_eq_apply m x]
  · intro y x h
    exact le_of_transportCount_ne_zero f hf_mono y x h

end StrassenAux

end LatticeProb
