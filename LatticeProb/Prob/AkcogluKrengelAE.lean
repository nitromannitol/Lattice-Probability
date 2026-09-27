/-
The multiparameter subadditive ergodic theorem of Akcoglu and Krengel, along cubes: the almost
sure half.

A set function `f` on boxes of `ℤ^d`, stationary under a measure-preserving action `τ` of the
lattice, bounded by a multiple of the volume, and subadditive when a box splits into two boxes,
has a volume-normalised limit along the cubes `[0, n)^d` almost surely: `akcoglu_krengel` proves
`f (latticeCube d n) ω / n^d → L ω` for a.e. `ω`.  The mean half is
`LatticeProb.akcoglu_krengel_mean` (`LatticeProb/Prob/AkcogluKrengel.lean`), proved there by a
multiparameter Fekete argument; the one-parameter theorem is `LatticeProb.Prob.Kingman`.

Route.  The maximal inequality `aux_ak_ae_45_33` bounds the probability that some cube `Q_k`
(`k ≥ 1`) is `α k^d`-heavy by `akMaxConst d * ρ / α`, where `ρ` bounds the normalised means; it is
proved by a dyadic covering argument: a heavy cube of side `k` is covered by a dyadic cell of side
`2^j` with `2^j < 4 d k` (`aux_ak_ae_45_25`), the cells are grouped into a pairwise disjoint
maximal subfamily (`aux_ak_ae_45_22`), and each heavy cell is covered by at least half of the
offsets of a grid of side `2^J` (`aux_ak_ae_45_24`), so the count of bad sites is controlled by
the mean of the box sums (`aux_ak_ae_45_28`).  The maximal inequality gives the a.e. upper bound
`limsup ≤ G_m` for every `m` (`aux_ak_ae_45_41`), and the lower bound in integral form
(`aux_ak_ae_45_45`) gives `∫ limsup ≤ ∫ liminf`; the two together give a.e. convergence
(`aux_ak_ae_45_46`).

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
import LatticeProb.Prob.Kingman
import LatticeProb.Prob.AkcogluKrengel
import LatticeProb.Site

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

-- This is `LatticeProb.akcoglu_krengel_mean` from LatticeProb/Prob/AkcogluKrengel.lean (line 659),
-- already fully proved there (multiparameter Fekete argument via a private `AKMeanAux` namespace
-- of ~20 lemmas). This scratch file cannot import that library module without a name clash (it
-- locally redefines `latticeBox`/`latticeCube`/`IsBoxSplit`, byte-identical to the library
-- versions); when this design is wired into the library, delete the local duplicates here and
-- import `LatticeProb.Prob.AkcogluKrengel` instead of reproving this.
-- This is `LatticeProb.akcoglu_krengel_mean` from `LatticeProb/Prob/AkcogluKrengel.lean`,
-- already fully proved there; the local duplicate is deleted and the library theorem is used.
private theorem aux_akcoglu_krengel_mean_1 (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (f : Finset (Site d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A))
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (hbd : ∃ C, ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (∫ ω, f (latticeCube d n) ω ∂μ) / (n : ℝ) ^ d) atTop (𝓝 L) :=
  akcoglu_krengel_mean μ d hd τ hτ f hmeas hstat hbd hsub

/-! ## Decomposition of the almost sure half

Route.
* Box combinatorics (§1): splitting a box along one coordinate is an `IsBoxSplit`; hence
  `f` of a box is at most `f` of a nested box plus `C` times the volume difference, and `f` of the
  cube `[0, k m)^d` is at most the sum of `f` over the `k^d` grid cubes of side `m`.
* A multiparameter pointwise ergodic theorem for BOUNDED functions along cubes (§2), for any
  measure-preserving additive action `σ` of `ℤ^d`, by iterating the one-parameter Birkhoff theorem
  of the library one coordinate at a time.  Boundedness makes the iteration elementary: if
  `g n → G` a.e. with `|g n| ≤ M`, then the Birkhoff averages of `g n` (at the same time `n`)
  converge to the Birkhoff limit of `G` (`aux_ak_ae_28`).
* Upper bound (§3): applying §2 to the sublattice action `z ↦ τ (m • z)` and the grid bound,
  `limsup_n f(Q_n)/n^d ≤ G_m` a.e. with `∫ G_m = ∫ f(Q_m)/m^d`.
* Lower bound (§4, DEEP): `∫ liminf_n f(Q_n)/n^d ≥ inf_m ∫ f(Q_m)/m^d`.
  Then `∫ (limsup - liminf) ≤ 0`, so `limsup = liminf` a.e.

Junk values: `latticeCube d 0 = ∅`, `(0 : ℝ)^d = 0` for `d ≥ 1`, `x / 0 = 0`; `bAvg T g 0 = 0`.
-/

/-- Coordinates in `s` range over `[0, n)`, the others are `0`. -/
def gridSet (d : ℕ) (s : Finset (Fin d)) (n : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => if i ∈ s then Finset.range n else {0}

/-- The site with coordinates `w i`. -/
def natToSite {d : ℕ} (w : Fin d → ℕ) : Site d := fun i => (w i : ℤ)

/-- Average of `h ∘ σ z` over the partial grid `gridSet d s n`. -/
noncomputable def gridAvg {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) (s : Finset (Fin d))
    (n : ℕ) (ω : Ω) : ℝ :=
  (∑ w ∈ gridSet d s n, h (σ (natToSite w) ω)) / (n : ℝ) ^ s.card

/-- The box with lower corner `m • w`, of side `m` in the coordinates of `s` and `k m` in
the others. -/
noncomputable def gridBox {d : ℕ} (m k : ℕ) (s : Finset (Fin d)) (w : Fin d → ℕ) :
    Finset (Site d) :=
  latticeBox (fun i => (m : ℤ) * (w i : ℤ))
    (fun i => (m : ℤ) * (w i : ℤ) + (if i ∈ s then (m : ℤ) else (k : ℤ) * m) - 1)

/-- The normalised value on the cube `[0, n)^d`. -/
noncomputable def cubeRatio {d : ℕ} (f : Finset (Site d) → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  f (latticeCube d n) ω / (n : ℝ) ^ d

/-- The tail supremum of the deviation `|g (N + k) - G|`. -/
noncomputable def supDev (g : ℕ → Ω → ℝ) (G : Ω → ℝ) (N : ℕ) (x : Ω) : ℝ :=
  ⨆ k : ℕ, |g (N + k) x - G x|

/-! ### §1. Box combinatorics -/

-- `hC ∅ ω` gives `0 ≤ f ∅ ω ≤ C * 0`; `simp` + `le_antisymm`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_1 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (ω : Ω) : f ∅ ω = 0 := by
  have h0 := hC ∅ ω
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at h0
  linarith [h0.1, h0.2]


-- `hC {0} ω`: `0 ≤ f {0} ω ≤ C * 1`; `Finset.card_singleton`, `linarith`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_2 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (ω : Ω) : 0 ≤ C := by
  have h := hC ({0} : Finset (Site d)) ω
  simp at h
  linarith [h.1, h.2]


-- Unfold `IsBoxSplit`; swap the two witnesses, `Disjoint.symm`, `Finset.union_comm`.
private theorem aux_ak_ae_3 {d : ℕ} {B B₁ B₂ : Finset (Site d)} (h : IsBoxSplit B B₁ B₂) :
    IsBoxSplit B B₂ B₁ := by
  obtain ⟨hB, hB₁, hB₂, hdisj, hunion⟩ := h
  exact ⟨hB, hB₂, hB₁, hdisj.symm, by rw [Finset.union_comm]; exact hunion⟩


-- `hsub` then `hC B₂`; `B₂.card = B.card - B₁.card` from `Finset.card_union_of_disjoint`
-- (`h.2.2.2.2 ▸ ...`), cast with `Nat.cast_add`, `linarith`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_4 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {B B₁ B₂ : Finset (Site d)} (h : IsBoxSplit B B₁ B₂) (ω : Ω) :
    f B ω ≤ f B₁ ω + C * ((B.card : ℝ) - B₁.card) := by
  have h1 : f B ω ≤ f B₁ ω + f B₂ ω := hsub B B₁ B₂ ω h
  have h2 : f B₂ ω ≤ C * (B₂.card : ℝ) := (hC B₂ ω).2
  have hcardnat : B.card = B₁.card + B₂.card := h.2.2.2.2 ▸ Finset.card_union_of_disjoint h.2.2.2.1
  have hcard : (B.card : ℝ) = (B₁.card : ℝ) + (B₂.card : ℝ) := (by exact_mod_cast hcardnat)
  have hcast : C * ((B.card : ℝ) - B₁.card) = C * (B₂.card : ℝ) := (by rw [hcard]; ring)
  linarith


-- Box membership coordinatewise: `latticeBox`, `Finset.mem_Icc`, `Pi.le_def`, `forall_and`.
private theorem aux_ak_ae_5_1 {d : ℕ} (a b x : Site d) :
    x ∈ latticeBox a b ↔ ∀ j, a j ≤ x j ∧ x j ≤ b j := by
  simp only [latticeBox, Finset.mem_Icc, Pi.le_def, forall_and]

-- A point of both pieces has `x i ≤ t - 1` and `t ≤ x i`: `Finset.disjoint_left`,
-- `aux_ak_ae_5_1` at coordinate `i`, `Function.update_self`, `omega`.
private theorem aux_ak_ae_5_2 {d : ℕ} (a b : Site d) (i : Fin d) (t : ℤ) :
    Disjoint (latticeBox a (Function.update b i (t - 1))) (latticeBox (Function.update a i t) b) := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  have e1 := ((aux_ak_ae_5_1 _ _ x).1 h1 i).2
  have e2 := ((aux_ak_ae_5_1 _ _ x).1 h2 i).1
  rw [Function.update_self] at e1 e2
  omega

-- `⊆`: coordinate `j ≠ i` unchanged (`Function.update_of_ne`); coordinate `i` uses
-- `t - 1 ≤ b i` resp. `a i ≤ t`.  `aux_ak_ae_5_1`, `Function.update_apply`, `split_ifs`, `omega`.
private theorem aux_ak_ae_5_3 {d : ℕ} (a b : Site d) (i : Fin d) (t : ℤ) (h1 : a i ≤ t)
    (h2 : t ≤ b i + 1) :
    latticeBox a (Function.update b i (t - 1)) ∪ latticeBox (Function.update a i t) b ⊆
      latticeBox a b := by
  intro x hx
  rw [aux_ak_ae_5_1]
  intro j
  rcases Finset.mem_union.1 hx with h | h
  · have hj := (aux_ak_ae_5_1 _ _ x).1 h j
    have hi := ((aux_ak_ae_5_1 _ _ x).1 h i).2
    rw [Function.update_self] at hi
    by_cases hji : j = i
    · subst hji; rw [Function.update_self] at hj; exact ⟨hj.1, by omega⟩
    · rw [Function.update_of_ne hji] at hj; exact hj
  · have hj := (aux_ak_ae_5_1 _ _ x).1 h j
    have hi := ((aux_ak_ae_5_1 _ _ x).1 h i).1
    rw [Function.update_self] at hi
    by_cases hji : j = i
    · subst hji; rw [Function.update_self] at hj; exact ⟨by omega, hj.2⟩
    · rw [Function.update_of_ne hji] at hj; exact hj

-- `⊇`: for `x` in the box, `x i ≤ t - 1` or `t ≤ x i` (`le_or_lt`); the matching piece by
-- `aux_ak_ae_5_1`, `Function.update_apply`, `split_ifs`, `omega`.
private theorem aux_ak_ae_5_4 {d : ℕ} (a b : Site d) (i : Fin d) (t : ℤ) :
    latticeBox a b ⊆
      latticeBox a (Function.update b i (t - 1)) ∪ latticeBox (Function.update a i t) b := by
  intro x hx
  have hb := (aux_ak_ae_5_1 _ _ x).1 hx
  rw [Finset.mem_union, aux_ak_ae_5_1, aux_ak_ae_5_1]
  rcases le_or_gt t (x i) with h | h
  · right; intro j; by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact ⟨h, (hb j).2⟩
    · simp only [Function.update_of_ne hj]; exact hb j
  · left; intro j; by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact ⟨(hb j).1, by omega⟩
    · simp only [Function.update_of_ne hj]; exact hb j

-- Cutting coordinate `i` at `t`: the three boxes are witnessed by `⟨_, _, rfl⟩`; disjointness
-- and union by `Finset.disjoint_left` / `Finset.ext` with `Finset.mem_Icc`, `Pi.le_def`,
-- `Function.update_apply`, splitting `j = i`; `omega` on the `i`-th coordinate.
-- SPLIT? (disjoint part and union part can be separate lemmas)
private theorem aux_ak_ae_5 {d : ℕ} (a b : Site d) (i : Fin d) (t : ℤ) (h1 : a i ≤ t)
    (h2 : t ≤ b i + 1) :
    IsBoxSplit (latticeBox a b) (latticeBox a (Function.update b i (t - 1)))
      (latticeBox (Function.update a i t) b) := by
  exact ⟨⟨a, b, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, aux_ak_ae_5_2 a b i t,
    Finset.Subset.antisymm (aux_ak_ae_5_3 a b i t h1 h2) (aux_ak_ae_5_4 a b i t)⟩

-- Trim coordinate `i` to `[s, e]`: cut at `t = s` (`aux_ak_ae_5`, keep the upper part via
-- `aux_ak_ae_3` + `aux_ak_ae_4`), then cut the upper part at `t = e + 1` (keep the lower part,
-- `aux_ak_ae_4`); `Function.update_idem`, `Function.update_self`, `add_sub_cancel_right`; linarith.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_6 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (a b : Site d) (i : Fin d) (s e : ℤ) (h1 : a i ≤ s) (h2 : s ≤ e) (h3 : e ≤ b i) (ω : Ω) :
    f (latticeBox a b) ω ≤
      f (latticeBox (Function.update a i s) (Function.update b i e)) ω +
        C * (((latticeBox a b).card : ℝ) -
          (latticeBox (Function.update a i s) (Function.update b i e)).card) := by
  have hsplit1 := aux_ak_ae_5 a b i s h1 (by omega)
  have hL := aux_ak_ae_4 hC hsub (aux_ak_ae_3 hsplit1) ω
  have hsplit2 := aux_ak_ae_5 (Function.update a i s) b i (e + 1)
      (by rw [Function.update_self]; omega) (by omega)
  have hU := aux_ak_ae_4 hC hsub hsplit2 ω
  rw [show (e + 1 : ℤ) - 1 = e from by omega] at hU
  linarith [hL, hU]


-- `funext j`; `by_cases hj : j = i` with `Function.update_apply`, `Finset.mem_insert`; `simp_all`.
private theorem aux_ak_ae_7 {d : ℕ} (S : Finset (Fin d)) (i : Fin d) (a a' : Site d) :
    Function.update (fun j => if j ∈ S then a' j else a j) i (a' i) =
      fun j => if j ∈ insert i S then a' j else a j := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [ hj, Finset.mem_insert]


-- `Finset.induction_on S`; base: `simp` (`if_neg (Finset.notMem_empty _)`), `sub_self`;
-- step `insert i S`: `aux_ak_ae_6` at coordinate `i` on the `S`-box (its `i`-th corners are
-- `a i`, `b i` since `i ∉ S`), rewrite with `aux_ak_ae_7` (twice), then `linarith`.
omit [MeasurableSpace Ω] in
private theorem aux_probe2 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (a b a' b' : Site d) (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) (ω : Ω) (S : Finset (Fin d)) :
    f (latticeBox a b) ω ≤
      f (latticeBox (fun j => if j ∈ S then a' j else a j) (fun j => if j ∈ S then b' j else b j)) ω
        + C * (((latticeBox a b).card : ℝ) -
          (latticeBox (fun j => if j ∈ S then a' j else a j)
            (fun j => if j ∈ S then b' j else b j)).card) := by
  induction S using Finset.induction with
  | empty => simp
  | insert i S h ih =>
    have h1 : (if i ∈ S then a' i else a i) ≤ a' i := by rw [if_neg h]; exact ha i
    have h2 : a' i ≤ b' i := hab i
    have h3 : b' i ≤ (if i ∈ S then b' i else b i) := by rw [if_neg h]; exact hb i
    have h6 := aux_ak_ae_6 hC hsub (fun j => if j ∈ S then a' j else a j)
      (fun j => if j ∈ S then b' j else b j) i (a' i) (b' i) h1 h2 h3 ω
    have e1 := aux_ak_ae_7 S i a a'
    have e2 := aux_ak_ae_7 S i b b'
    rw [e1, e2] at h6
    linarith [ih, h6]

omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_8 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (a b a' b' : Site d) (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) (ω : Ω) (S : Finset (Fin d)) :
    f (latticeBox a b) ω ≤
      f (latticeBox (fun j => if j ∈ S then a' j else a j) (fun j => if j ∈ S then b' j else b j)) ω
        + C * (((latticeBox a b).card : ℝ) -
          (latticeBox (fun j => if j ∈ S then a' j else a j)
            (fun j => if j ∈ S then b' j else b j)).card) := by
  exact aux_probe2 hC hsub a b a' b' ha hab hb ω S


-- Nested boxes.  `by_cases hab : a' ≤ b'`: yes → `aux_ak_ae_8 … Finset.univ`, `simp` the `if`s;
-- no → `latticeBox a' b' = ∅` by `Finset.Icc_eq_empty hab`, `aux_ak_ae_1`, `hC (latticeBox a b)`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_9 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (a b a' b' : Site d) (ha : a ≤ a') (hb : b' ≤ b) (ω : Ω) :
    f (latticeBox a b) ω ≤
      f (latticeBox a' b') ω + C * (((latticeBox a b).card : ℝ) - (latticeBox a' b').card) := by
  by_cases hab : a' ≤ b'
  · have h8 := aux_ak_ae_8 (f := f) (C := C) hC hsub a b a' b' ha hab hb ω Finset.univ
    simpa using h8
  · rw [show latticeBox a' b' = (∅ : Finset (Site d)) from Finset.Icc_eq_empty hab]
    rw [aux_ak_ae_1 hC ω, Finset.card_empty]
    simpa using (hC (latticeBox a b) ω).2


-- `latticeCube`, `Pi.card_Icc`, `Int.card_Icc` (`(n - 1 + 1 - 0).toNat = n`), `Finset.prod_const`,
-- `Finset.card_univ`, `Fintype.card_fin`.
private theorem aux_ak_ae_10 (d n : ℕ) : (latticeCube d n).card = n ^ d := by
  rw [latticeCube, Pi.card_Icc]
  simp only [Pi.zero_apply, Int.card_Icc, sub_zero,
    show ((n : ℤ) - 1 + 1) = (n : ℤ) from by ring, Int.toNat_natCast,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]


-- `aux_ak_ae_9` with `a = a' = 0`, `b' = m - 1`, `b = n - 1` (`Pi.le_def`, `Int.ofNat_le`,
-- `omega`), then `aux_ak_ae_10` and `push_cast`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_11 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    f (latticeCube d n) ω ≤ f (latticeCube d m) ω + C * ((n : ℝ) ^ d - (m : ℝ) ^ d) := by
  have hb : (fun _ : Fin d => (m : ℤ) - 1) ≤ (fun _ : Fin d => (n : ℤ) - 1) :=
    fun i => sub_le_sub_right (Int.ofNat_le.mpr hmn) 1
  have h := aux_ak_ae_9 hC hsub (0 : Site d) (fun _ => (n : ℤ) - 1) (0 : Site d)
    (fun _ => (m : ℤ) - 1) le_rfl hb ω
  have h1 : (latticeBox (0 : Site d) (fun _ => (n : ℤ) - 1)).card = n ^ d := aux_ak_ae_10 d n
  have h2 : (latticeBox (0 : Site d) (fun _ => (m : ℤ) - 1)).card = m ^ d := aux_ak_ae_10 d m
  rw [h1, h2, Nat.cast_pow, Nat.cast_pow] at h
  exact h


-- `show (Equiv.addRight z).toEmbedding = addRightEmbedding z from rfl`,
-- `Finset.map_add_right_Icc`, then `congr 1`, `funext i`, `simp`, `ring`.
private theorem aux_ak_ae_12 (d m : ℕ) (z : Site d) :
    (latticeCube d m).map (Equiv.addRight z).toEmbedding =
      latticeBox z (fun i => z i + (m : ℤ) - 1) := by
  simp only [latticeCube, latticeBox]
  have h : (Equiv.addRight z).toEmbedding = addRightEmbedding z := rfl
  rw [h, Finset.map_add_right_Icc]
  congr 1 <;> funext i <;> simp only [Pi.add_apply, Pi.zero_apply] <;> ring


-- An inverted coordinate makes the box empty: `latticeBox`, `Finset.Icc_eq_empty` (the order
-- fails at coordinate `i`, `not_le.2`), then `aux_ak_ae_1`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_13_1 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) {a b : Site d} {i : Fin d} (hlt : b i < a i)
    (ω : Ω) : f (latticeBox a b) ω = 0 := by
  have he : latticeBox a b = ∅ := Finset.Icc_eq_empty (fun h => absurd (h i) (not_le.2 hlt))
  rw [he]
  exact aux_ak_ae_1 hC ω

-- Induction step `k → k + 1`: cut at `t = a i + m * k` (`aux_ak_ae_5`, hypotheses by
-- `positivity`/`push_cast`/`nlinarith`) and use `hsub`; the lower piece is the IH at
-- `Function.update b i (a i + m * k - 1)` (`Function.update_self`, `Function.update_idem`);
-- the upper piece is the `j = k` summand since `Function.update b i (b i) = b`
-- (`Function.update_eq_self`); `Finset.sum_range_succ`, `linarith`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_13_2 {d : ℕ} {f : Finset (Site d) → Ω → ℝ}
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (m : ℕ) (i : Fin d) (a : Site d) (ω : Ω) (k : ℕ)
    (ih : ∀ b : Site d, b i = a i + (k : ℤ) * m - 1 →
      f (latticeBox a b) ω ≤ ∑ j ∈ Finset.range k,
        f (latticeBox (Function.update a i (a i + (m : ℤ) * j))
          (Function.update b i (a i + (m : ℤ) * j + m - 1))) ω)
    (b : Site d) (hb : b i = a i + ((k + 1 : ℕ) : ℤ) * m - 1) :
    f (latticeBox a b) ω ≤ ∑ j ∈ Finset.range (k + 1),
        f (latticeBox (Function.update a i (a i + (m : ℤ) * j))
          (Function.update b i (a i + (m : ℤ) * j + m - 1))) ω := by
  have hs := aux_ak_ae_5 a b i (a i + (m : ℤ) * k) (le_add_of_nonneg_right (by positivity))
    (by rw [hb]; push_cast; nlinarith)
  have h1 := hsub _ _ _ ω hs
  have h2 := ih (Function.update b i (a i + (m : ℤ) * k - 1)) (by rw [Function.update_self]; ring)
  simp only [Function.update_idem] at h2
  have e : a i + (m : ℤ) * k + m - 1 = b i := by rw [hb]; push_cast; ring
  rw [Finset.sum_range_succ, e, Function.update_eq_self]
  linarith

-- One-coordinate split into `k` slabs of width `m`.  Induction on `k` generalizing `b`.
-- `k = 0`: `¬ a ≤ b` (coordinate `i`), `Finset.Icc_eq_empty`, `aux_ak_ae_1`, `Finset.sum_range_zero`.
-- `k + 1`: `hsub` with `aux_ak_ae_5` at `t = a i + k * m`; lower part by IH applied to
-- `Function.update b i (a i + k * m - 1)` (`Function.update_self`, `Function.update_idem`);
-- upper part is the `j = k` summand (`Function.update_eq_self_iff`); `Finset.sum_range_succ`.
-- SPLIT?
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_13 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (m : ℕ) (i : Fin d) (a : Site d) (ω : Ω) :
    ∀ (k : ℕ) (b : Site d), b i = a i + (k : ℤ) * m - 1 →
      f (latticeBox a b) ω ≤ ∑ j ∈ Finset.range k,
        f (latticeBox (Function.update a i (a i + (m : ℤ) * j))
          (Function.update b i (a i + (m : ℤ) * j + m - 1))) ω := by
  intro k
  induction k with
  | zero =>
    intro b hb
    rw [Finset.sum_range_zero, aux_ak_ae_13_1 hC (i := i) (by simp at hb; omega) ω]
  | succ k ih =>
    intro b hb
    exact aux_ak_ae_13_2 hsub m i a ω k ih b hb

-- `gridSet`, `if_neg (Finset.notMem_empty _)`, `Fintype.piFinset_singleton`.
private theorem aux_ak_ae_14 (d n : ℕ) : gridSet d ∅ n = {0} := by
  rw [gridSet]
  simp only [Finset.notMem_empty, if_false]
  exact Fintype.piFinset_singleton 0


-- `Fintype.mem_piFinset`, `if_neg hi`, `Finset.mem_singleton`.
private theorem aux_ak_ae_15 {d : ℕ} {s : Finset (Fin d)} {n : ℕ} {w : Fin d → ℕ} {i : Fin d}
    (hw : w ∈ gridSet d s n) (hi : i ∉ s) : w i = 0 := by
  simp only [gridSet, Fintype.mem_piFinset] at hw
  have h := hw i
  rw [if_neg hi, Finset.mem_singleton] at h
  exact h


-- Reindex the grid one coordinate at a time: `Finset.sum_product'` (right to left) and
-- `Finset.sum_nbij'` with `(w, j) ↦ Function.update w i j` and `w' ↦ (Function.update w' i 0, w' i)`;
-- membership by `Fintype.mem_piFinset`, `Function.update_apply`, `aux_ak_ae_15`;
-- inverses by `Function.update_idem`, `Function.update_eq_self`, `funext`.  SPLIT?
private theorem aux_ak_ae_16_grid {d : ℕ} {s : Finset (Fin d)} {i : Fin d} (_unused_hi : i ∉ s) (n : ℕ)
    (w : Fin d → ℕ) (j : ℕ) (hw : w ∈ gridSet d s n) :
    Function.update w i j ∈ gridSet d (insert i s) n ↔ j ∈ Finset.range n := by
  unfold gridSet at hw ⊢
  rw [Fintype.mem_piFinset] at hw ⊢
  constructor
  · intro h
    have := h i
    rw [Function.update_self, if_pos (Finset.mem_insert_self i s)] at this
    exact this
  · intro hj a
    by_cases ha : a = i
    · rw [ha, Function.update_self, if_pos (Finset.mem_insert_self i s)]
      exact hj
    · rw [Function.update_apply, if_neg ha]
      have hwa := hw a
      by_cases has : a ∈ s
      · rw [if_pos has] at hwa
        rw [if_pos (Finset.mem_insert_of_mem has)]
        exact hwa
      · rw [if_neg has] at hwa
        rw [if_neg (fun hmem => by
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact ha h'
          · exact has h')]
        exact hwa

private theorem aux_ak_ae_16_inv {d : ℕ} {s : Finset (Fin d)} {i : Fin d} (hi : i ∉ s) (n : ℕ)
    (w : Fin d → ℕ) (hw : w ∈ gridSet d (insert i s) n) :
    Function.update w i 0 ∈ gridSet d s n ∧ w i ∈ Finset.range n := by
  unfold gridSet at hw ⊢
  rw [Fintype.mem_piFinset] at hw ⊢
  refine ⟨?_, ?_⟩
  · intro a
    by_cases ha : a = i
    · rw [ha, Function.update_self, if_neg hi]
      exact Finset.mem_singleton.mpr rfl
    · rw [Function.update_apply, if_neg ha]
      have hwa := hw a
      by_cases has : a ∈ s
      · rw [if_pos has]
        rw [if_pos (Finset.mem_insert_of_mem has)] at hwa
        exact hwa
      · rw [if_neg has]
        have hni : ¬ a ∈ insert i s := fun hmem => by
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact ha h'
          · exact has h'
        rw [if_neg hni] at hwa
        rw [Finset.mem_singleton] at hwa ⊢
        exact hwa
  · have := hw i
    rw [if_pos (Finset.mem_insert_self i s)] at this
    exact this

private theorem aux_ak_ae_16 {d : ℕ} {M : Type*} [AddCommMonoid M] (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s) (n : ℕ) (g : (Fin d → ℕ) → M) :
    ∑ w ∈ gridSet d (insert i s) n, g w =
      ∑ w ∈ gridSet d s n, ∑ j ∈ Finset.range n, g (Function.update w i j) := by
  rw [← Finset.sum_product (gridSet d s n) (Finset.range n)
        (fun p : (Fin d → ℕ) × ℕ => g (Function.update p.1 i p.2))]
  refine Finset.sum_nbij' (s := gridSet d (insert i s) n)
    (t := gridSet d s n ×ˢ Finset.range n) (f := g)
    (g := fun p : (Fin d → ℕ) × ℕ => g (Function.update p.1 i p.2))
    (i := fun w : Fin d → ℕ => (Function.update w i 0, w i))
    (j := fun p : (Fin d → ℕ) × ℕ => Function.update p.1 i p.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_product]
    exact aux_ak_ae_16_inv hi n w hw
  · intro p hp
    rw [Finset.mem_product] at hp
    exact (aux_ak_ae_16_grid hi n p.1 p.2 hp.1).mpr hp.2
  · intro w hw
    rw [Function.update_idem, Function.update_eq_self]
  · intro p hp
    rw [Finset.mem_product] at hp
    have h0 : p.1 i = 0 := aux_ak_ae_15 hp.1 hi
    apply Prod.ext
    · rw [Function.update_idem, ← h0, Function.update_eq_self]
    · rw [Function.update_self]
  · intro w hw
    rw [Function.update_idem, Function.update_eq_self]


-- `aux_ak_ae_13` with `a = fun l => m * w l` (so `a i = 0` by `aux_ak_ae_15`) and the upper corner
-- of `gridBox m k s w` (its `i`-th entry is `k * m - 1` since `i ∉ s`); identify the pieces:
-- `gridBox`, `latticeBox`, `congr 1`, `funext l`, `by_cases l = i`, `Function.update_apply`,
-- `Finset.mem_insert`, `push_cast`, `ring`.
private theorem aux_ak_ae_boxid {d : ℕ} (m k : ℕ) (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s)
    (w : Fin d → ℕ) (hwi : w i = 0) (j : ℕ) :
    latticeBox (Function.update (fun l => (m : ℤ) * (w l : ℤ)) i
        ((fun l => (m : ℤ) * (w l : ℤ)) i + (m : ℤ) * (j : ℤ)))
      (Function.update (fun l => (m : ℤ) * (w l : ℤ) +
        (if l ∈ s then (m : ℤ) else (k : ℤ) * m) - 1) i
        ((fun l => (m : ℤ) * (w l : ℤ)) i + (m : ℤ) * (j : ℤ) + m - 1))
      = gridBox m k (insert i s) (Function.update w i j) := by
  simp only [gridBox, latticeBox]
  congr 1
  · funext l
    simp only [Function.update_apply]
    by_cases hl : l = i
    · subst hl
      simp [hwi]
    · simp [hl]
  · funext l
    simp only [Function.update_apply]
    by_cases hl : l = i
    · subst hl
      simp [hwi, Finset.mem_insert, hi]
    · simp [hl, Finset.mem_insert]

omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_17 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (m k : ℕ) (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ)
    (hw : w ∈ gridSet d s k) (ω : Ω) :
    f (gridBox m k s w) ω ≤
      ∑ j ∈ Finset.range k, f (gridBox m k (insert i s) (Function.update w i j)) ω := by
  have hwi : w i = 0 := aux_ak_ae_15 hw hi
  have h13 := aux_ak_ae_13 hC hsub m i (fun l => (m : ℤ) * (w l : ℤ)) ω k
    (fun l => (m : ℤ) * (w l : ℤ) + (if l ∈ s then (m : ℤ) else (k : ℤ) * m) - 1)
    (by simp [hi])
  refine h13.trans ?_
  apply Finset.sum_le_sum
  intro j hj
  rw [aux_ak_ae_boxid m k s i hi w hwi j]


-- `Finset.induction_on s`.  Base: `aux_ak_ae_14`, `Finset.sum_singleton`, and
-- `gridBox m k ∅ 0 = latticeCube d (k * m)` (`funext`, `simp`, `push_cast`).
-- Step: `Finset.sum_le_sum` with `aux_ak_ae_17`, then `(aux_ak_ae_16 …).symm`.
private theorem aux_ak_ae_18b {d : ℕ} (m k : ℕ) : gridBox m k (∅ : Finset (Fin d)) (0 : Fin d → ℕ) = latticeCube d (k * m) := by
  unfold gridBox latticeCube latticeBox
  have h1 : (fun i : Fin d => (m : ℤ) * ((0 : Fin d → ℕ) i)) = (0 : Site d) := by
    funext i; simp
  have h2 : (fun i : Fin d => (m : ℤ) * ((0 : Fin d → ℕ) i) + (if i ∈ (∅ : Finset (Fin d)) then (m : ℤ) else (k : ℤ) * m) - 1)
      = (fun _ : Fin d => ((k * m : ℕ) : ℤ) - 1) := by
    funext i; simp [Nat.cast_mul]
  rw [h1, h2]

omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_18 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (m k : ℕ) (ω : Ω) (s : Finset (Fin d)) :
    f (latticeCube d (k * m)) ω ≤ ∑ w ∈ gridSet d s k, f (gridBox m k s w) ω := by
  refine Finset.induction_on s (motive := fun t => f (latticeCube d (k * m)) ω ≤ ∑ w ∈ gridSet d t k, f (gridBox m k t w) ω) ?base ?step
  · rw [aux_ak_ae_14, Finset.sum_singleton]
    exact le_of_eq (congrArg (fun A => f A ω) (aux_ak_ae_18b m k)).symm
  · intro i t hi ih
    rw [aux_ak_ae_16 t i hi k (fun w => f (gridBox m k (insert i t) w) ω)]
    exact le_trans ih (Finset.sum_le_sum (fun w hw => aux_ak_ae_17 hC hsub m k t i hi w hw ω))


-- `aux_ak_ae_18` with `s = univ`; `gridBox m k univ w = (latticeCube d m).map (addRight (m • w))`
-- by `aux_ak_ae_12` (`if_pos (Finset.mem_univ _)`, `natToSite`, `smul_eq_mul`, `funext`);
-- then `hstat`.
private theorem aux_ak_ae_19a {d : ℕ} (m k : ℕ) (w : Fin d → ℕ) :
    gridBox m k Finset.univ w =
      (latticeCube d m).map (Equiv.addRight ((m : ℤ) • natToSite w)).toEmbedding := by
  rw [aux_ak_ae_12]
  unfold gridBox latticeBox
  congr 1
  funext i
  simp [natToSite, Pi.smul_apply]

omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_19 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ} (τ : Site d → Ω → Ω)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (m k : ℕ) (ω : Ω) :
    f (latticeCube d (k * m)) ω ≤
      ∑ w ∈ gridSet d Finset.univ k, f (latticeCube d m) (τ ((m : ℤ) • natToSite w) ω) := by
  exact le_trans (aux_ak_ae_18 hC hsub m k ω Finset.univ)
    (Finset.sum_le_sum (fun w _ => by rw [aux_ak_ae_19a m k w, hstat]))


-- `cubeRatio`; `hC (latticeCube d n) ω`, `aux_ak_ae_10`; `n = 0`: `latticeCube d 0 = ∅`
-- is not needed, `(0:ℝ)^d = 0` (`zero_pow`, `d ≠ 0`) and `div_zero`; else `div_le_iff₀`.
private theorem aux_t0 (d n : ℕ) : (latticeCube d n).card = n ^ d := by
  rw [latticeCube, Pi.Icc_eq, Fintype.card_piFinset]
  simp

omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_20 {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (n : ℕ) (ω : Ω) :
    0 ≤ cubeRatio f n ω ∧ cubeRatio f n ω ≤ C := by
  have hcard : (latticeCube d n).card = n ^ d := aux_t0 d n
  have hC0 : 0 ≤ C :=
    le_trans (hC ({0} : Finset (Site d)) ω).1 (by simpa using (hC ({0} : Finset (Site d)) ω).2)
  constructor
  · simp only [cubeRatio]
    exact div_nonneg (hC (latticeCube d n) ω).1 (by positivity)
  · simp only [cubeRatio]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]
      simp only [Nat.cast_zero, zero_pow (by omega : d ≠ 0), div_zero]
      exact hC0
    · rw [div_le_iff₀ (pow_pos (Nat.cast_pos.mpr hn) d)]
      have h := (hC (latticeCube d n) ω).2
      rw [hcard] at h
      push_cast at h
      exact h


-- `cubeRatio`; `(hmeas _).div_const _`.
private theorem aux_ak_ae_21 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} (hmeas : ∀ A, Measurable (f A))
    (n : ℕ) : Measurable (cubeRatio f n) := by
  exact (hmeas (latticeCube d n)).div_const _


/-! ### §2. Pointwise ergodic theorem along cubes for bounded functions -/

-- Induction on `j`: `Nat.cast_succ`, `add_smul`, `one_smul`,
-- `z + (j + 1) • u = u + (z + j • u)` by `abel`, `hσadd`, `Function.iterate_succ_apply'`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_22 {d : ℕ} {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (z : Site d) (i : Fin d) (ω : Ω) (j : ℕ) :
    σ (z + (j : ℤ) • unit i) ω = (σ (unit i))^[j] (σ z ω) := by
  revert ω
  induction j with
  | zero => intro ω; simp
  | succ j ih =>
    intro ω
    have hcomm : σ z (σ (unit i) ω) = σ (unit i) (σ z ω) :=
      (hσadd z (unit i) ω).symm.trans
        ((congrArg (fun w => σ w ω) (add_comm z (unit i))).trans (hσadd (unit i) z ω))
    rw [Nat.cast_succ, add_smul, one_smul]
    rw [show z + ((j : ℤ) • unit i + unit i) = z + (j : ℤ) • unit i + unit i by abel]
    rw [hσadd (z + (j : ℤ) • unit i) (unit i) ω]
    rw [ih (σ (unit i) ω), hcomm, Function.iterate_succ_apply]


-- `Function.Commute.iterate_right` of `fun x => by rw [← hσadd, ← hσadd, add_comm]`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_23 {d : ℕ} {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (z u : Site d) (j : ℕ) (ω : Ω) :
    σ z ((σ u)^[j] ω) = (σ u)^[j] (σ z ω) := by
  exact (Function.Commute.iterate_right (f := σ z) (g := σ u) (by intro ω'; rw [← hσadd z u ω', ← hσadd u z ω', add_comm]) j) ω


-- `funext l`; `natToSite`, `unit`, `Function.update_apply`, `Pi.single_apply`; `by_cases l = i`.
private theorem aux_ak_ae_24 {d : ℕ} (w : Fin d → ℕ) (i : Fin d) (hw : w i = 0) (j : ℕ) :
    natToSite (Function.update w i j) = natToSite w + (j : ℤ) • unit i := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp [natToSite, unit,   hw]
  · simp [natToSite, unit,   hl]


-- `gridAvg`, `bAvg`, `birkhoffSum` (definitional: `∑ k ∈ range n, g (T^[k] x)`),
-- `aux_ak_ae_16`, `aux_ak_ae_15`, `aux_ak_ae_24`, `aux_ak_ae_22`, `aux_ak_ae_23`,
-- `Finset.sum_comm`, `Finset.sum_div`, `Finset.card_insert_of_notMem`, `pow_succ`, `div_div`.
-- SPLIT? (first prove the numerator identity, then the division)
private theorem aux_ak_ae_25_num {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s) (n : ℕ) (ω : Ω) :
    ∑ w ∈ gridSet d (insert i s) n, h (σ (natToSite w) ω) =
      ∑ k ∈ Finset.range n, ∑ w ∈ gridSet d s n,
        h (σ (natToSite w) ((σ (unit i))^[k] ω)) := by
  rw [aux_ak_ae_16 s i hi n (fun w => h (σ (natToSite w) ω)), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro w hw
  rw [aux_ak_ae_24 w i (aux_ak_ae_15 hw hi) j, aux_ak_ae_22 hσadd (natToSite w) i ω j,
      ← aux_ak_ae_23 hσadd (natToSite w) (unit i) j ω]

private theorem aux_ak_ae_25 {d : ℕ} {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s) (n : ℕ) (ω : Ω) :
    gridAvg σ h (insert i s) n ω = bAvg (σ (unit i)) (gridAvg σ h s n) n ω := by
  simp only [gridAvg, bAvg, birkhoffSum]
  rw [Finset.card_insert_of_notMem hi, pow_succ, aux_ak_ae_25_num hσadd h s i hi n ω]
  rw [← Finset.sum_div, div_div]


-- `gridAvg`, `abs_div`, `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_card_nsmul`;
-- `(gridSet d s n).card = n ^ s.card` via `Fintype.card_piFinset`, `Finset.prod_ite_mem`,
-- `Finset.univ_inter`, `Finset.prod_const`; case `n = 0` with `s ≠ ∅` gives `0`.  SPLIT?
private theorem aux_ak_ae_26_card {d : ℕ} (s : Finset (Fin d)) (n : ℕ) :
    (gridSet d s n).card = n ^ s.card := by
  unfold gridSet
  rw [Fintype.card_piFinset]
  have hcoe : ∀ i : Fin d, (if i ∈ s then Finset.range n else ({0} : Finset ℕ)).card
      = (if i ∈ s then n else 1) := by
    intro i
    by_cases hi : i ∈ s <;> simp [hi]
  simp only [hcoe]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_26_sum {d : ℕ} {σ : Site d → Ω → Ω} {h : Ω → ℝ} {M : ℝ}
    (hh : ∀ x, |h x| ≤ M) (s : Finset (Fin d)) (n : ℕ) (ω : Ω) :
    |∑ w ∈ gridSet d s n, h (σ (natToSite w) ω)| ≤ (n : ℝ) ^ s.card * M := by
  have hconst : (∑ _w ∈ gridSet d s n, M) = (n : ℝ) ^ s.card * M := by
    rw [Finset.sum_const, aux_ak_ae_26_card, nsmul_eq_mul, Nat.cast_pow]
  calc |∑ w ∈ gridSet d s n, h (σ (natToSite w) ω)|
      ≤ ∑ w ∈ gridSet d s n, |h (σ (natToSite w) ω)| :=
        Finset.abs_sum_le_sum_abs (fun w => h (σ (natToSite w) ω)) (gridSet d s n)
    _ ≤ ∑ _w ∈ gridSet d s n, M := Finset.sum_le_sum fun w _ => hh (σ (natToSite w) ω)
    _ = (n : ℝ) ^ s.card * M := hconst

omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_26 {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hh : ∀ x, |h x| ≤ M) (s : Finset (Fin d)) (n : ℕ) (ω : Ω) :
    |gridAvg σ h s n ω| ≤ M := by
  rw [gridAvg]
  have hDn : 0 ≤ (n : ℝ) ^ s.card := pow_nonneg (Nat.cast_nonneg n) _
  rw [abs_div, abs_of_nonneg hDn]
  by_cases hD : (n : ℝ) ^ s.card = 0
  · rw [hD, div_zero]
    exact hM
  · have hDp : 0 < (n : ℝ) ^ s.card := lt_of_le_of_ne hDn (Ne.symm hD)
    rw [div_le_iff₀ hDp]
    refine le_trans (aux_ak_ae_26_sum hh s n ω) ?_
    rw [mul_comm]


-- `gridAvg`; `Finset.measurable_sum` of `hh.comp (hσ _).measurable`, then `.div_const`.
private theorem aux_ak_ae_27 {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) {h : Ω → ℝ} (hh : Measurable h)
    (s : Finset (Fin d)) (n : ℕ) : Measurable (gridAvg σ h s n) := by
  unfold gridAvg
  exact (Finset.measurable_sum _ (fun w _ => hh.comp (hσ (natToSite w)).measurable)).div_const _


-- Bounded Birkhoff limit keeps the integral.  `∫ bAvg T h n = ∫ h` for `n ≥ 1`
-- (`bAvg`, `integral_div`, `birkhoffSum`, `integral_finsetSum`, `integral_comp_iterate`);
-- `tendsto_integral_of_dominated_convergence` with bound `M` (`abs_bAvg_le`),
-- limit from `ae_tendsto_bLimsup`; `tendsto_nhds_unique` against the eventually constant sequence.
-- SPLIT?
private theorem aux_bavg_integral {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {h : Ω → ℝ} (hInt : Integrable h μ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, bAvg T h n x ∂μ = ∫ x, h x ∂μ := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm : ∀ k ∈ Finset.range n, Integrable (fun x => h (T^[k] x)) μ := fun k _ =>
    ((hT.iterate k).integrable_comp hInt.aestronglyMeasurable).mpr hInt
  have hid : (fun x => bAvg T h n x) = fun x => (∑ k ∈ Finset.range n, h (T^[k] x)) / (n : ℝ) := by
    funext x
    simp only [bAvg, birkhoffSum]
  rw [hid, integral_div, integral_finsetSum _ hterm]
  rw [Finset.sum_congr rfl (fun k _ => integral_comp_iterate hT hInt k)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hn0]

private theorem aux_ak_ae_28 {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |h x| ≤ M) :
    ∫ x, bLimsup T h x ∂μ = ∫ x, h x ∂μ := by
  have hInt : Integrable h μ :=
    Integrable.of_bound hh.aestronglyMeasurable M (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)
  have hbdd : ∀ n x, |bAvg T h n x| ≤ M := fun n x => abs_bAvg_le hM hb n x
  have hae : ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T h n x) atTop (𝓝 (bLimsup T h x)) := ae_tendsto_bLimsup hT hh hInt
  have hlim : Tendsto (fun n => ∫ x, bAvg T h n x ∂μ) atTop (𝓝 (∫ x, bLimsup T h x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun n => (measurable_bAvg hT.measurable hh n).aestronglyMeasurable)
      (integrable_const M)
      (fun n => Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hbdd n x)
      hae
  refine tendsto_nhds_unique hlim ?_
  exact Tendsto.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => (aux_bavg_integral hT hInt hn).symm⟩) tendsto_const_nhds


-- Monotonicity and bounds of `bLimsup`: `bLimsup`, `Filter.limsup_le_limsup` of the pointwise
-- `bAvg` comparison (`bAvg`, `birkhoffSum`, `Finset.sum_le_sum`, `div_le_div_of_nonneg_right`),
-- boundedness from `abs_bAvg_le`, `isBoundedUnder_le_of`, `isBoundedUnder_ge_of`;
-- the bounds `0 ≤ · ≤ M` from `Filter.le_limsup_of_frequently_le` / `Filter.limsup_le_of_le`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_29 {T : Ω → Ω} {g g' : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ M) (hg' : ∀ x, 0 ≤ g' x ∧ g' x ≤ M) (hle : ∀ x, g x ≤ g' x)
    (ω : Ω) :
    0 ≤ bLimsup T g ω ∧ bLimsup T g ω ≤ bLimsup T g' ω ∧ bLimsup T g' ω ≤ M := by
  have hgabs : ∀ x, |g x| ≤ M :=
    fun x => abs_le.mpr ⟨(neg_nonpos.mpr hM).trans (hg x).1, (hg x).2⟩
  have hg'abs : ∀ x, |g' x| ≤ M :=
    fun x => abs_le.mpr ⟨(neg_nonpos.mpr hM).trans (hg' x).1, (hg' x).2⟩
  have hg_le : ∀ n, bAvg T g n ω ≤ M := fun n => (abs_le.mp (abs_bAvg_le hM hgabs n ω)).2
  have hg'_le : ∀ n, bAvg T g' n ω ≤ M := fun n => (abs_le.mp (abs_bAvg_le hM hg'abs n ω)).2
  have hg'_ge : ∀ n, -M ≤ bAvg T g' n ω := fun n => (abs_le.mp (abs_bAvg_le hM hg'abs n ω)).1
  have hg_nonneg : ∀ n, 0 ≤ bAvg T g n ω := fun n =>
    div_nonneg (Finset.sum_nonneg fun k _ => (hg _).1) (Nat.cast_nonneg n)
  have hmono : ∀ n, bAvg T g n ω ≤ bAvg T g' n ω := fun n =>
    div_le_div_of_nonneg_right (Finset.sum_le_sum fun k _ => hle _) (Nat.cast_nonneg n)
  refine ⟨?_, ?_, ?_⟩
  · simp only [bLimsup]
    exact le_limsup_of_frequently_le (Frequently.of_forall hg_nonneg) (isBoundedUnder_le_of hg_le)
  · simp only [bLimsup]
    exact limsup_le_limsup (Eventually.of_forall hmono)
      (isBoundedUnder_ge_of hg_nonneg).isCoboundedUnder_le (isBoundedUnder_le_of hg'_le)
  · simp only [bLimsup]
    exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop hg'_ge) (Eventually.of_forall hg'_le)


-- `|bLimsup T h ω| ≤ M` for `|h| ≤ M`: `bLimsup`, `abs_le`, `Filter.limsup_le_of_le`,
-- `Filter.le_limsup_of_frequently_le`, `abs_bAvg_le`, `isBoundedUnder_le_of`, `isBoundedUnder_ge_of`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_30 {T : Ω → Ω} {h : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    (ω : Ω) : |bLimsup T h ω| ≤ M := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · rw [bLimsup]
    refine le_limsup_of_frequently_le ?_ ?_
    · exact (Eventually.of_forall fun n => (abs_le.mp (abs_bAvg_le hM hb n ω)).1).frequently
    · exact isBoundedUnder_le_of fun n => (abs_le.mp (abs_bAvg_le hM hb n ω)).2
  · rw [bLimsup]
    refine limsup_le_of_le ?_ ?_
    · exact (isBoundedUnder_ge_of fun n => (abs_le.mp (abs_bAvg_le hM hb n ω)).1).isCoboundedUnder_le
    · exact Eventually.of_forall fun n => (abs_le.mp (abs_bAvg_le hM hb n ω)).2


-- Pointwise limit of an antitone sequence bounded below by `0`: `tendsto_atTop_ciInf` with
-- `antitone_nat_of_succ_le` and `BddBelow` witnessed by `0` (`Set.mem_range`).
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_31_1 {E : ℕ → Ω → ℝ} (hb : ∀ N x, 0 ≤ E N x)
    (hanti : ∀ N x, E (N + 1) x ≤ E N x) (x : Ω) :
    Tendsto (fun N => E N x) atTop (𝓝 (⨅ N, E N x)) := by
  exact tendsto_atTop_ciInf (antitone_nat_of_succ_le fun N => hanti N x)
    ⟨0, fun _ ⟨N, hN⟩ => hN ▸ hb N x⟩

-- The pointwise infimum has integral `0`: it is measurable (`Measurable.iInf`), in `[0, M]`
-- (`le_ciInf`, `ciInf_le` with `BddBelow` by `0`), so integrable (`Integrable.of_bound`);
-- `∫ ⨅ ≤ ∫ E N` (`integral_mono`) and `le_of_tendsto'` against `hint` give `≤ 0`;
-- `integral_nonneg` gives `≥ 0`; `le_antisymm`.
private theorem aux_ak_ae_31_2 {μ : Measure Ω} [IsProbabilityMeasure μ] {E : ℕ → Ω → ℝ} {M : ℝ}
    (hE : ∀ N, Measurable (E N)) (hb : ∀ N x, 0 ≤ E N x ∧ E N x ≤ M)
    (hint : Tendsto (fun N => ∫ x, E N x ∂μ) atTop (𝓝 0)) :
    ∫ x, (⨅ N, E N x) ∂μ = 0 ∧ Integrable (fun x => ⨅ N, E N x) μ ∧ ∀ x, 0 ≤ ⨅ N, E N x := by
  have hbdd : ∀ x, BddBelow (Set.range fun N => E N x) :=
    fun x => ⟨0, fun _ ⟨N, hN⟩ => hN ▸ (hb N x).1⟩
  have hnn : ∀ x, 0 ≤ ⨅ N, E N x := fun x => le_ciInf fun N => (hb N x).1
  have hint' : Integrable (fun x => ⨅ N, E N x) μ :=
    Integrable.of_bound (Measurable.iInf hE).aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]; exact (ciInf_le (hbdd x) 0).trans (hb 0 x).2)
  have hEi : ∀ N, Integrable (E N) μ := fun N =>
    Integrable.of_bound (hE N).aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb N x).1]; exact (hb N x).2)
  refine ⟨le_antisymm (ge_of_tendsto' hint fun N => integral_mono hint' (hEi N)
    fun x => ciInf_le (hbdd x) N) (integral_nonneg hnn), hint', hnn⟩

-- `integral_eq_zero_iff_of_nonneg` (nonneg as `Pi.le_def`) applied to `aux_ak_ae_31_2`;
-- the resulting `=ᵐ 0` unfolds (`Filter.EventuallyEq`, `Pi.zero_apply`).
private theorem aux_ak_ae_31_3 {μ : Measure Ω} [IsProbabilityMeasure μ] {E : ℕ → Ω → ℝ} {M : ℝ}
    (hE : ∀ N, Measurable (E N)) (hb : ∀ N x, 0 ≤ E N x ∧ E N x ≤ M)
    (hint : Tendsto (fun N => ∫ x, E N x ∂μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, (⨅ N, E N x) = 0 := by
  obtain ⟨h0, hi, hnn⟩ := aux_ak_ae_31_2 hE hb hint
  exact (integral_eq_zero_iff_of_nonneg (fun x => hnn x) hi).1 h0

-- A bounded, pointwise antitone family of measurable functions whose integrals tend to `0`
-- tends to `0` a.e.: the limit `E∞ = ⨅ N, E N ·` exists (`tendsto_atTop_ciInf`), is measurable
-- (`Measurable.iInf`), `0 ≤ E∞ ≤ E N` so `∫ E∞ ≤ ∫ E N → 0` (`integral_mono`,
-- `ge_of_tendsto'`), hence `E∞ =ᵐ 0` by `integral_eq_zero_iff_of_nonneg`.  SPLIT?
private theorem aux_ak_ae_31 {μ : Measure Ω} [IsProbabilityMeasure μ] {E : ℕ → Ω → ℝ} {M : ℝ}
    (hE : ∀ N, Measurable (E N)) (hb : ∀ N x, 0 ≤ E N x ∧ E N x ≤ M)
    (hanti : ∀ N x, E (N + 1) x ≤ E N x)
    (hint : Tendsto (fun N => ∫ x, E N x ∂μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto (fun N => E N x) atTop (𝓝 0) := by
  filter_upwards [aux_ak_ae_31_3 hE hb hint] with x hx
  have h := aux_ak_ae_31_1 (fun N x => (hb N x).1) hanti x
  rwa [hx] at h

-- Pointwise facts on `supDev` (`⨆` over `ℕ` of values in `[0, 2M]`): `Real.iSup_nonneg`
-- (or `le_ciSup_of_le`), `ciSup_le`, `le_ciSup` with `BddAbove` from `abs_sub` + `abs_le`;
-- antitone via `ciSup_le` and `le_ciSup` at index `k + 1`; domination at `k = n - N`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_32 {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (_unused_hM : 0 ≤ M)
    (hg : ∀ n x, |g n x| ≤ M) (hG : ∀ x, |G x| ≤ M) (N : ℕ) (x : Ω) :
    0 ≤ supDev g G N x ∧ supDev g G N x ≤ 2 * M ∧ supDev g G (N + 1) x ≤ supDev g G N x ∧
      ∀ n, N ≤ n → |g n x - G x| ≤ supDev g G N x := by
  have hbound : ∀ k : ℕ, |g (N + k) x - G x| ≤ 2 * M := fun k => by
    linarith [hg (N + k) x, hG x, abs_sub (g (N + k) x) (G x)]
  have hbdd : BddAbove (Set.range fun k : ℕ => |g (N + k) x - G x|) :=
    ⟨2 * M, fun y hy => hy.elim fun k hk => hk ▸ hbound k⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold supDev
    exact Real.iSup_nonneg fun k => abs_nonneg _
  · unfold supDev
    exact ciSup_le hbound
  · unfold supDev
    apply ciSup_le
    intro k
    have hidx : N + 1 + k = N + (k + 1) :=
      (Nat.add_assoc N 1 k).trans (congrArg (Nat.add N) (Nat.add_comm 1 k))
    rw [hidx]
    exact le_ciSup hbdd (k + 1)
  · intro n hn
    unfold supDev
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact le_ciSup hbdd k


-- Where `g n x → G x`, the tail suprema tend to `0`: `Metric.tendsto_atTop`, for `ε` pick `N₀`
-- with `|g n x - G x| < ε/2` for `n ≥ N₀`, then `ciSup_le` for `N ≥ N₀`; nonneg from
-- `aux_ak_ae_32`.  Measurability: `Measurable.iSup` of `((hg n).sub hG).abs`.
private theorem aux_ak_ae_33 {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (_unused_hM : 0 ≤ M)
    (hgm : ∀ n, Measurable (g n)) (hGm : Measurable G)
    (_unused_hg : ∀ n x, |g n x| ≤ M) (_unused_hG : ∀ x, |G x| ≤ M) :
    (∀ N, Measurable (supDev g G N)) ∧
      ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (G x)) →
        Tendsto (fun N => supDev g G N x) atTop (𝓝 0) := by
  constructor
  · intro N
    exact Measurable.iSup fun k => ((hgm (N + k)).sub hGm).abs
  · intro x hx
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases Metric.tendsto_atTop.mp hx (ε / 2) (by linarith) with ⟨N₀, hN₀⟩
    refine ⟨N₀, fun N hN => ?_⟩
    have hnn : 0 ≤ (⨆ k : ℕ, |g (N + k) x - G x|) := Real.iSup_nonneg fun k => abs_nonneg _
    have hle : (⨆ k : ℕ, |g (N + k) x - G x|) ≤ ε / 2 := ciSup_le fun k => by
      have hk : N₀ ≤ N + k := le_trans hN (Nat.le_add_right N k)
      have hh := hN₀ (N + k) hk
      rw [Real.dist_eq] at hh
      linarith
    show dist (⨆ k : ℕ, |g (N + k) x - G x|) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith


-- Birkhoff averages of a difference are dominated: `bAvg`, `birkhoffSum`, `← Finset.sum_sub_distrib`,
-- `← sub_div`, `abs_div`, `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_sum`, `div_le_div_of_nonneg_right`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_34 {T : Ω → Ω} {g G D : Ω → ℝ} (hD : ∀ x, |g x - G x| ≤ D x) (n : ℕ)
    (ω : Ω) : |bAvg T g n ω - bAvg T G n ω| ≤ bAvg T D n ω := by
  rw [bAvg, bAvg, bAvg, ← sub_div]
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  apply div_le_div_of_nonneg_right
  · show |(∑ k ∈ Finset.range n, g (T^[k] ω)) - ∑ k ∈ Finset.range n, G (T^[k] ω)|
      ≤ ∑ k ∈ Finset.range n, D (T^[k] ω)
    rw [← Finset.sum_sub_distrib]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => hD _)
  · exact Nat.cast_nonneg n


-- KEY: moving-target Birkhoff for bounded functions.  With `D N := supDev g G N`:
-- `aux_ak_ae_31` applied to `E N := bLimsup T (D N)` (bounds/antitone by `aux_ak_ae_29`,
-- `∫ E N = ∫ D N` by `aux_ak_ae_28`, `∫ D N → 0` by dominated convergence and
-- `aux_ak_ae_33`), plus `ae_tendsto_bLimsup` for `G` and every `D N` (`ae_all_iff`).
-- At a good `ω`: `|bAvg (g n) n ω - bAvg G n ω| ≤ bAvg (D N) n ω` for `n ≥ N` (`aux_ak_ae_34`,
-- `aux_ak_ae_32`), whose limit `E N ω` is small; conclude with `Metric.tendsto_atTop`.
-- SPLIT? (the integral step `∫ D N → 0` and the final ε-argument can be separate lemmas)
private theorem aux_ak_35_E {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hgm : ∀ n, Measurable (g n)) (hGm : Measurable G)
    (hg : ∀ n x, |g n x| ≤ M) (hG : ∀ x, |G x| ≤ M)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (G x))) :
    ∀ᵐ x ∂μ, Tendsto (fun N => bLimsup T (supDev g G N) x) atTop (𝓝 0) := by
  have hTm : Measurable T := hT.measurable
  have hDmeas : ∀ N, Measurable (supDev g G N) :=
    (aux_ak_ae_33 hM hgm hGm hg hG).1
  have hDbound : ∀ N x, |supDev g G N x| ≤ 2 * M := fun N x => by
    have h := aux_ak_ae_32 hM hg hG N x
    rw [abs_of_nonneg h.1]; exact h.2.1
  have hEmeas : ∀ N, Measurable (fun x => bLimsup T (supDev g G N) x) :=
    fun N => measurable_bLimsup hTm (hDmeas N)
  have hEbound : ∀ N x, 0 ≤ bLimsup T (supDev g G N) x ∧
      bLimsup T (supDev g G N) x ≤ 2 * M := fun N x => by
    have h2M : (0 : ℝ) ≤ 2 * M := by linarith
    have h := aux_ak_ae_29 (T := T) h2M
      (fun y => ⟨(aux_ak_ae_32 hM hg hG N y).1, (aux_ak_ae_32 hM hg hG N y).2.1⟩)
      (fun y => ⟨(aux_ak_ae_32 hM hg hG N y).1, (aux_ak_ae_32 hM hg hG N y).2.1⟩)
      (fun y => le_rfl) x
    exact ⟨h.1, h.2.2⟩
  have hEanti : ∀ N x, bLimsup T (supDev g G (N + 1)) x ≤ bLimsup T (supDev g G N) x :=
    fun N x => by
      have h2M : (0 : ℝ) ≤ 2 * M := by linarith
      have h := aux_ak_ae_29 (T := T) h2M
        (fun y => ⟨(aux_ak_ae_32 hM hg hG (N + 1) y).1,
          (aux_ak_ae_32 hM hg hG (N + 1) y).2.1⟩)
        (fun y => ⟨(aux_ak_ae_32 hM hg hG N y).1,
          (aux_ak_ae_32 hM hg hG N y).2.1⟩)
        (fun y => (aux_ak_ae_32 hM hg hG N y).2.2.1) x
      exact h.2.1
  have hIntD : Tendsto (fun N => ∫ x, supDev g G N x ∂μ) atTop (𝓝 0) := by
    have hbdd : Integrable (fun _ : Ω => 2 * M) μ := integrable_const (2 * M)
    have hle : ∀ N, ∀ᵐ x ∂μ, ‖supDev g G N x‖ ≤ (fun _ : Ω => 2 * M) x := fun N => by
      filter_upwards with x; rw [Real.norm_eq_abs]; exact hDbound N x
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun N => supDev g G N x) atTop (𝓝 (0 : ℝ)) := by
      filter_upwards [hconv] with x hx
      exact (aux_ak_ae_33 hM hgm hGm hg hG).2 x hx
    have hmain := tendsto_integral_of_dominated_convergence (fun _ : Ω => 2 * M)
      (fun N => (hDmeas N).aestronglyMeasurable) hbdd hle hlim
    simpa using hmain
  have hEintT : Tendsto (fun N => ∫ x, bLimsup T (supDev g G N) x ∂μ) atTop (𝓝 0) := by
    have hEq : (fun N => ∫ x, bLimsup T (supDev g G N) x ∂μ) =
        (fun N => ∫ x, supDev g G N x ∂μ) := by
      funext N
      exact aux_ak_ae_28 hT (hDmeas N) (by linarith : (0:ℝ) ≤ 2 * M) (fun x => hDbound N x)
    rw [hEq]; exact hIntD
  exact aux_ak_ae_31 hEmeas hEbound hEanti hEintT

omit [MeasurableSpace Ω] in
private theorem aux_ak_35_eps {T : Ω → Ω} {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ n x, |g n x| ≤ M) (hG : ∀ x, |G x| ≤ M) {x : Ω}
    (hx0 : Tendsto (fun N => bLimsup T (supDev g G N) x) atTop (𝓝 0))
    (hxG : Tendsto (fun n => bAvg T G n x) atTop (𝓝 (bLimsup T G x)))
    (hxD : ∀ N, Tendsto (fun n => bAvg T (supDev g G N) n x) atTop
      (𝓝 (bLimsup T (supDev g G N) x))) :
    Tendsto (fun n => bAvg T (g n) n x) atTop (𝓝 (bLimsup T G x)) := by
  rw [Metric.tendsto_atTop] at hx0 hxG ⊢
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨N0, hN0⟩ := hx0 (ε / 4) hε4
  obtain ⟨N1, hN1⟩ := hxG (ε / 2) hε2
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp (hxD N0)) (ε / 4) hε4
  refine ⟨max N0 (max N1 N2), fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hN0lt : bLimsup T (supDev g G N0) x < ε / 4 := by
    have h := hN0 N0 le_rfl
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hBlt : bAvg T (supDev g G N0) n x < ε / 2 := by
    have hB : bAvg T (supDev g G N0) n x ≤ bLimsup T (supDev g G N0) x +
        |bAvg T (supDev g G N0) n x - bLimsup T (supDev g G N0) x| := by
      have hb := le_abs_self (bAvg T (supDev g G N0) n x - bLimsup T (supDev g G N0) x)
      linarith
    have h2 := hN2 n hn2
    rw [Real.dist_eq] at h2
    linarith
  have hX : |bAvg T (g n) n x - bAvg T G n x| < ε / 2 := by
    have h1 := aux_ak_ae_34 (T := T)
      (fun y => (aux_ak_ae_32 hM hg hG N0 y).2.2.2 n hn0) n x
    linarith
  have hY : dist (bAvg T G n x) (bLimsup T G x) < ε / 2 := hN1 n hn1
  calc dist (bAvg T (g n) n x) (bLimsup T G x)
      ≤ dist (bAvg T (g n) n x) (bAvg T G n x) + dist (bAvg T G n x) (bLimsup T G x) :=
        dist_triangle _ _ _
    _ < ε := by rw [Real.dist_eq]; linarith

private theorem aux_ak_ae_35 {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ} {G : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hgm : ∀ n, Measurable (g n)) (hGm : Measurable G)
    (hg : ∀ n x, |g n x| ≤ M) (hG : ∀ x, |G x| ≤ M)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (G x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T (g n) n x) atTop (𝓝 (bLimsup T G x)) := by
  have hTm : Measurable T := hT.measurable
  have hGint : Integrable G μ :=
    Integrable.of_bound hGm.aestronglyMeasurable M (by
      filter_upwards with x; rw [Real.norm_eq_abs]; exact hG x)
  have hDmeas : ∀ N, Measurable (supDev g G N) :=
    (aux_ak_ae_33 hM hgm hGm hg hG).1
  have hDbound : ∀ N x, |supDev g G N x| ≤ 2 * M := fun N x => by
    have h := aux_ak_ae_32 hM hg hG N x
    rw [abs_of_nonneg h.1]; exact h.2.1
  have hDint : ∀ N, Integrable (supDev g G N) μ := fun N =>
    Integrable.of_bound (hDmeas N).aestronglyMeasurable (2 * M) (by
      filter_upwards with x; rw [Real.norm_eq_abs]; exact hDbound N x)
  have hae0 : ∀ᵐ x ∂μ, Tendsto (fun N => bLimsup T (supDev g G N) x) atTop (𝓝 0) :=
    aux_ak_35_E hT hM hgm hGm hg hG hconv
  have haeG : ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T G n x) atTop (𝓝 (bLimsup T G x)) :=
    ae_tendsto_bLimsup hT hGm hGint
  have haeD : ∀ᵐ x ∂μ, ∀ N, Tendsto (fun n => bAvg T (supDev g G N) n x) atTop
      (𝓝 (bLimsup T (supDev g G N) x)) :=
    ae_all_iff.mpr (fun N => ae_tendsto_bLimsup hT (hDmeas N) (hDint N))
  filter_upwards [hae0, haeG, haeD] with x hx0 hxG hxD
  exact aux_ak_35_eps hM hg hG hx0 hxG hxD


-- Base of the induction: `gridAvg`, `aux_ak_ae_14`, `Finset.sum_singleton`, `Finset.card_empty`,
-- `pow_zero`, `div_one`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_36_1 {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) (n : ℕ) (ω : Ω) :
    gridAvg σ h ∅ n ω = h (σ (natToSite 0) ω) := by
  simp [gridAvg, aux_ak_ae_14]

-- Induction step: `aux_ak_ae_35` with `T := σ (unit i)`, `g n := gridAvg σ h s n`
-- (bounds `aux_ak_ae_26`, measurability `aux_ak_ae_27`), then rewrite the averages with
-- `aux_ak_ae_25` inside `filter_upwards`.
private theorem aux_ak_ae_36_2 {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) {G : Ω → ℝ} (hGm : Measurable G)
    (hGb : ∀ x, |G x| ≤ M)
    (hG : ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h s n ω) atTop (𝓝 (G ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h (insert i s) n ω) atTop
      (𝓝 (bLimsup (σ (unit i)) G ω)) := by
  have h35 := aux_ak_ae_35 (hσ (unit i)) hM (fun n => aux_ak_ae_27 hσ hh s n) hGm
    (fun n x => aux_ak_ae_26 σ h hM hb s n x) hGb hG
  filter_upwards [h35] with ω hω
  simpa only [aux_ak_ae_25 hσadd h s i hi] using hω

-- `Finset.induction_on s`.  Base: `gridAvg σ h ∅ n ω = h (σ 0 ω)` (`aux_ak_ae_14`,
-- `Finset.sum_singleton`, `natToSite`, `Finset.card_empty`, `pow_zero`, `div_one`), take
-- `G := fun ω => h (σ 0 ω)`, `tendsto_const_nhds`.  Step: rewrite with `aux_ak_ae_25`, apply
-- `aux_ak_ae_35` with `T := σ (unit i)`, `g n := gridAvg σ h s n` (`aux_ak_ae_26`, `aux_ak_ae_27`);
-- new limit `bLimsup (σ (unit i)) G` (`measurable_bLimsup`, `aux_ak_ae_30`).
private theorem aux_ak_ae_36 {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    (s : Finset (Fin d)) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h s n ω) atTop (𝓝 (G ω)) := by
  induction s using Finset.induction with
  | empty =>
    refine ⟨fun ω => h (σ (natToSite 0) ω), hh.comp (hσ _).measurable, fun x => hb _, ?_⟩
    exact ae_of_all _ fun ω => by simp only [aux_ak_ae_36_1]; exact tendsto_const_nhds
  | insert i s hi ih =>
    obtain ⟨G, hGm, hGb, hG⟩ := ih
    exact ⟨bLimsup (σ (unit i)) G, measurable_bLimsup (hσ _).measurable hGm,
      fun x => aux_ak_ae_30 hM hGb x, aux_ak_ae_36_2 hσ hσadd hh hM hb s i hi hGm hGb hG⟩

-- `gridAvg`, `integral_div`, `integral_finsetSum` (integrable: `Integrable.of_bound`),
-- each `∫ h (σ z ω) = ∫ h` by `integral_map (hσ z).measurable.aemeasurable` + `(hσ z).map_eq`;
-- `Finset.sum_const`, card `n ^ d` (`Fintype.card_piFinset`, `Finset.card_range`), `field_simp`.
private theorem aux_ak_ae_37 {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) {h : Ω → ℝ} (hh : Measurable h) {M : ℝ}
    (hb : ∀ x, |h x| ≤ M) {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, gridAvg σ h Finset.univ n ω ∂μ = ∫ ω, h ω ∂μ := by
  have hInt : ∀ w : Fin d → ℕ, Integrable (fun ω => h (σ (natToSite w) ω)) μ
  · intro w
    refine Integrable.of_bound (hh.comp (hσ (natToSite w)).measurable).aestronglyMeasurable M ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hb (σ (natToSite w) y)
  have hz : ∀ w : Fin d → ℕ, ∫ ω, h (σ (natToSite w) ω) ∂μ = ∫ ω, h ω ∂μ
  · intro w
    have hmap : ∫ y, h y ∂(Measure.map (σ (natToSite w)) μ) = ∫ ω, h (σ (natToSite w) ω) ∂μ
    · exact integral_map (hσ (natToSite w)).aemeasurable hh.aestronglyMeasurable
    rw [(hσ (natToSite w)).map_eq] at hmap
    exact hmap.symm
  have hfun : (fun ω => gridAvg σ h Finset.univ n ω) = fun ω => (∑ w ∈ gridSet d Finset.univ n, h (σ (natToSite w) ω)) / (n : ℝ) ^ d
  · funext ω
    simp only [gridAvg]
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hfun, integral_div, integral_finsetSum (gridSet d Finset.univ n) (fun w _ => hInt w)]
  rw [Finset.sum_congr rfl (fun w _ => hz w)]
  rw [Finset.sum_const, aux_ak_ae_26_card, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow]
  have hn0 : (n : ℝ) ≠ 0
  · exact_mod_cast (by omega : n ≠ 0)
  exact mul_div_cancel_left₀ _ (pow_ne_zero d hn0)


-- Multiparameter pointwise ergodic theorem along cubes, bounded case, with the mean identified:
-- `aux_ak_ae_36` at `s = univ`; `∫ G = ∫ h` by `tendsto_integral_of_dominated_convergence`
-- (bound `M`, `aux_ak_ae_26`, `aux_ak_ae_27`) and `aux_ak_ae_37` eventually
-- (`tendsto_nhds_unique`, `EventuallyEq`/`Tendsto.congr'`).
private theorem aux_ak_ae_38 {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧ ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => gridAvg σ h Finset.univ n ω) atTop (𝓝 (G ω)) := by
  obtain ⟨G, hGm, hGb, hGconv⟩ := aux_ak_ae_36 hσ hσadd hh hM hb Finset.univ
  have h1 : Tendsto (fun n : ℕ => ∫ ω, gridAvg σ h Finset.univ n ω ∂μ) atTop (𝓝 (∫ ω, G ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ : Ω => M)
      (fun n => (aux_ak_ae_27 hσ hh Finset.univ n).aestronglyMeasurable)
      (integrable_const M)
      (fun n => by
        filter_upwards with ω
        rw [Real.norm_eq_abs]
        exact aux_ak_ae_26 σ h hM hb Finset.univ n ω)
      hGconv
  have hEq : (fun n : ℕ => ∫ ω, gridAvg σ h Finset.univ n ω ∂μ) =ᶠ[atTop] (fun _ : ℕ => ∫ ω, h ω ∂μ) :=
    eventually_atTop.mpr ⟨1, fun n hn => aux_ak_ae_37 hσ hh hb hn⟩
  have htest : Tendsto (fun _ : ℕ => ∫ ω, h ω ∂μ) atTop (𝓝 (∫ ω, h ω ∂μ)) := tendsto_const_nhds
  have h2 : Tendsto (fun _ : ℕ => ∫ ω, h ω ∂μ) atTop (𝓝 (∫ ω, G ω ∂μ)) := Tendsto.congr' hEq h1
  exact ⟨G, hGm, hGb, (tendsto_nhds_unique htest h2).symm, hGconv⟩


/-! ### §3. The upper bound -/

-- The sublattice action `z ↦ τ (m • z)`: `smul_add` and `hτadd`; `hτ`.
private theorem aux_ak_ae_39 {d : ℕ} {μ : Measure Ω} (τ : Site d → Ω → Ω)
    (hτ : ∀ z, MeasurePreserving (τ z) μ μ) (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    (m : ℕ) :
    (∀ z, MeasurePreserving (fun ω => τ ((m : ℤ) • z) ω) μ μ) ∧
      ∀ z w ω, τ ((m : ℤ) • (z + w)) ω = τ ((m : ℤ) • z) (τ ((m : ℤ) • w) ω) := by
  refine ⟨fun z => hτ ((m : ℤ) • z), ?_⟩
  intro z w ω
  rw [smul_add, hτadd]


-- `k = 0`: `latticeCube d 0 = ∅` for `d ≥ 1` (`Finset.Icc_eq_empty`, coordinate `⟨0, hd⟩`,
-- `0 ≤ -1` false by `simp`), so the left side is `0` (`aux_ak_ae_1`) and the right side is
-- `0 ^ d * X = 0` (`zero_pow`, `d ≠ 0`).
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_40_1 {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (m : ℕ) (X : ℝ) (ω : Ω) :
    f (latticeCube d (0 * m)) ω ≤ ((0 * m : ℕ) : ℝ) ^ d * X := by
  have he : latticeCube d (0 * m) = ∅ :=
    Finset.Icc_eq_empty (fun h => by have := h ⟨0, hd⟩; simp at this)
  rw [he, aux_ak_ae_1 hC ω, zero_mul, Nat.cast_zero, zero_pow (by omega), zero_mul]

-- Unfold: `gridAvg`, `cubeRatio`, `Finset.card_univ`, `Fintype.card_fin`, `Finset.sum_div`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_40_2 {d : ℕ} (τ : Site d → Ω → Ω) (f : Finset (Site d) → Ω → ℝ) (m k : ℕ)
    (ω : Ω) :
    gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m) Finset.univ k ω =
      (∑ w ∈ gridSet d Finset.univ k, f (latticeCube d m) (τ ((m : ℤ) • natToSite w) ω)) /
        (m : ℝ) ^ d / (k : ℝ) ^ d := by
  simp only [gridAvg, cubeRatio, Finset.card_univ, Fintype.card_fin, Finset.sum_div]

-- Algebra: `Nat.cast_mul`, `mul_pow`, `field_simp` (`m, k ≠ 0` by `positivity`/`Nat.cast_pos`).
private theorem aux_ak_ae_40_3 (d : ℕ) {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (S : ℝ) :
    ((k * m : ℕ) : ℝ) ^ d * (S / (m : ℝ) ^ d / (k : ℝ) ^ d) = S := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_mul, mul_pow]
  field_simp

-- Grid bound in normalised form: `aux_ak_ae_19`, `f (latticeCube d m) _ = m ^ d * cubeRatio f m _`
-- (`cubeRatio`, `mul_div_cancel₀`, `m ≠ 0`), `← Finset.mul_sum`; `gridAvg`, card
-- `(gridSet d univ k).card = k ^ d`; case `k = 0`: `gridSet d univ 0 = ∅` since `d ≥ 1`
-- (`Fintype.piFinset_eq_empty`/`Finset.univ_nonempty`), both sides `0`.  `push_cast`, `mul_pow`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_40 {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (ω : Ω) :
    f (latticeCube d (k * m)) ω ≤
      ((k * m : ℕ) : ℝ) ^ d *
        gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m) Finset.univ k ω := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact aux_ak_ae_40_1 hd hC m _ ω
  · rw [aux_ak_ae_40_2, aux_ak_ae_40_3 d hm hk]
    exact aux_ak_ae_19 τ hC hsub hstat m k ω

-- Real algebra: `div_le_iff₀`, `(A + C (1 - K/N)) N = A N + C (N - K)` by `field_simp`/`ring`,
-- and `K A ≤ N A` (`mul_le_mul_of_nonneg_right`); `nlinarith`.
private theorem aux_ak_ae_41_1 {F K N A C : ℝ} (hA : 0 ≤ A) (hK : K ≤ N) (hN : 0 < N)
    (h : F ≤ K * A + C * (N - K)) : F / N ≤ A + C * (1 - K / N) := by
  rw [div_le_iff₀ hN]
  have e : (A + C * (1 - K / N)) * N = A * N + C * (N - K) := by field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hK hA]

-- `gridAvg`: `div_nonneg` of `Finset.sum_nonneg` (terms `≥ 0` by `aux_ak_ae_20`) and `positivity`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_41_2 {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (m k : ℕ) (ω : Ω) :
    0 ≤ gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m) Finset.univ k ω := by
  exact div_nonneg (Finset.sum_nonneg fun w _ => (aux_ak_ae_20 hd hC m _).1) (by positivity)

-- `pow_le_pow_left₀ (Nat.cast_nonneg _)` with `Nat.div_mul_le_self` (`exact_mod_cast`).
private theorem aux_ak_ae_41_3 (d n m : ℕ) : ((n / m * m : ℕ) : ℝ) ^ d ≤ (n : ℝ) ^ d := by
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_mul_le_self n m) d

-- Pointwise upper bound.  With `k = n / m` (`Nat.div_mul_le_self`): `aux_ak_ae_11` for
-- `k * m ≤ n`, then `aux_ak_ae_40`; divide by `n ^ d > 0`; the average is `≥ 0`
-- (`gridAvg`, `Finset.sum_nonneg`, `aux_ak_ae_20`) and `(k m)^d / n^d ≤ 1`
-- (`div_le_one`, `pow_le_pow_left₀`), so `(k m)^d/n^d * A ≤ A`.  SPLIT?
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_41 {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (ω : Ω) :
    cubeRatio f n ω ≤
      gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m) Finset.univ (n / m) ω +
        C * (1 - ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) := by
  have h11 := aux_ak_ae_11 (d := d) hC hsub (Nat.div_mul_le_self n m) ω
  have h40 := aux_ak_ae_40 hd τ hC hsub hstat hm (n / m) ω
  have hN : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (by exact_mod_cast hn) d
  show f (latticeCube d n) ω / (n : ℝ) ^ d ≤ _
  exact aux_ak_ae_41_1 (aux_ak_ae_41_2 hd τ hC m (n / m) ω) (aux_ak_ae_41_3 d n m) hN
    (by linarith)

-- `n - m < n / m * m ≤ n` (`Nat.lt_div_mul_add`/`Nat.div_mul_le_self`), so the ratio is squeezed
-- between `((n - m) / n) ^ d` and `1`; `tendsto_of_tendsto_of_tendsto_of_le_of_le'`,
-- `(1 - m / n) → 1` by `tendsto_const_div_atTop_nhds_zero_nat`, `Tendsto.pow`.  SPLIT?
private theorem aux_ak_ae_42_aux (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) atTop (𝓝 1) := by
  have hglow : Tendsto (fun n : ℕ => (1 - (m : ℝ) / (n : ℝ)) ^ d) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 - (m : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
    simpa using h1.pow d
  have hhigh : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hev1 : ∀ᶠ n : ℕ in atTop,
      (1 - (m : ℝ) / (n : ℝ)) ^ d ≤ ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d := by
    filter_upwards [eventually_ge_atTop m, eventually_ge_atTop 1] with n hmn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hmnc : ((n - m : ℕ) : ℝ) ≤ ((n / m * m : ℕ) : ℝ) := by
      have hlt : n - m ≤ n / m * m := by
        have hh := Nat.lt_div_mul_add (a := n) (b := m) hm
        omega
      exact_mod_cast hlt
    have hbase : 1 - (m : ℝ) / (n : ℝ) ≤ ((n / m * m : ℕ) : ℝ) / (n : ℝ) := by
      have hsub : (1 : ℝ) - (m : ℝ) / (n : ℝ) = ((n - m : ℕ) : ℝ) / (n : ℝ) := by
        rw [Nat.cast_sub hmn, sub_div, div_self hnne]
      rw [hsub]
      exact div_le_div_of_nonneg_right hmnc hnpos.le
    have hnn : (0 : ℝ) ≤ 1 - (m : ℝ) / (n : ℝ) := by
      have hmle : (m : ℝ) / (n : ℝ) ≤ 1 := by
        rw [div_le_one hnpos]
        exact_mod_cast hmn
      linarith
    calc (1 - (m : ℝ) / (n : ℝ)) ^ d
        ≤ (((n / m * m : ℕ) : ℝ) / (n : ℝ)) ^ d := pow_le_pow_left₀ hnn hbase d
      _ = ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d := div_pow _ _ d
  have hev2 : ∀ᶠ n : ℕ in atTop, ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d ≤ (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_le_one (pow_pos hnpos d)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg (n / m * m))
      (by exact_mod_cast Nat.div_mul_le_self n m) d
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hglow hhigh hev1 hev2

private theorem aux_ak_ae_42 (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) atTop (𝓝 1) := by
  exact aux_ak_ae_42_aux d hm


-- a.e. `limsup ≤ G`: at a good `ω`, the right side of `aux_ak_ae_41` tends to `G ω + C * 0`
-- (`Tendsto.comp` with `Nat.tendsto_div_const_atTop`, `aux_ak_ae_42`); `Filter.limsup_le_limsup`
-- (eventually for `n ≥ 1`, coboundedness from `aux_ak_ae_20`) and `Tendsto.limsup_eq`.
private theorem aux_ak_ae_43 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω)
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m : ℕ} (hm : 1 ≤ m) {G : Ω → ℝ}
    (hG : ∀ᵐ ω ∂μ, Tendsto (fun k => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
      Finset.univ k ω) atTop (𝓝 (G ω))) :
    ∀ᵐ ω ∂μ, limsup (fun n => cubeRatio f n ω) atTop ≤ G ω := by
  refine Filter.Eventually.mono hG fun ω hω => ?_
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  have hcomp : Tendsto (fun n : ℕ => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
      Finset.univ (n / m) ω) atTop (𝓝 (G ω)) :=
    hω.comp (Nat.tendsto_div_const_atTop hm0)
  have hratio : Tendsto (fun n : ℕ => ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) atTop (𝓝 1) :=
    aux_ak_ae_42 d hm
  have hlim : Tendsto (fun n : ℕ => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
      Finset.univ (n / m) ω + C * (1 - ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d))
      atTop (𝓝 (G ω + C * (1 - 1))) :=
    hcomp.add ((hratio.const_sub 1).const_mul C)
  have hz : C * (1 - (1 : ℝ)) = 0 :=
    Eq.trans (congrArg (fun t : ℝ => C * t) (sub_self (1 : ℝ))) (mul_zero C)
  have hlim' : Tendsto (fun n : ℕ => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
      Finset.univ (n / m) ω + C * (1 - ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d))
      atTop (𝓝 (G ω)) := add_zero (G ω) ▸ (hz ▸ hlim)
  have hle : (fun n : ℕ => cubeRatio f n ω) ≤ᶠ[atTop]
      (fun n : ℕ => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
        Finset.univ (n / m) ω + C * (1 - ((n / m * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d)) :=
    eventually_atTop.mpr ⟨1, fun n hn => aux_ak_ae_41 hd τ hC hsub hstat hm hn ω⟩
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => cubeRatio f n ω) :=
    (isBoundedUnder_ge_of fun n => (aux_ak_ae_20 hd hC n ω).1).isCoboundedUnder_le
  exact hlim'.limsup_eq ▸ limsup_le_limsup hle hcob hlim'.isBoundedUnder_le


-- The limsup of the cube ratios lies in `[0, C]` and is integrable: bounds exactly as in
-- `aux_ak_ae_46` (`Filter.le_limsup_of_le`, `Filter.limsup_le_of_le`, `aux_ak_ae_20`,
-- `isBoundedUnder_le_of`, `isCoboundedUnder_le_of_le`), measurability `Measurable.limsup` of
-- `aux_ak_ae_21`, then `Integrable.of_bound` (`Real.norm_eq_abs`, `abs_of_nonneg`).
private theorem aux_ak_ae_44_1 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ} (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) :
    Integrable (fun ω => limsup (fun n => cubeRatio f n ω) atTop) μ := by
  have hcu : ∀ n ω, 0 ≤ cubeRatio f n ω ∧ cubeRatio f n ω ≤ C :=
    fun n ω => aux_ak_ae_20 hd hC n ω
  have hnn : ∀ ω, 0 ≤ limsup (fun n => cubeRatio f n ω) atTop := fun ω =>
    Filter.le_limsup_of_le (isBoundedUnder_le_of (fun n => (hcu n ω).2))
      (fun b hb => by
        rcases Filter.eventually_atTop.mp hb with ⟨N, hN⟩
        exact le_trans (hcu (max N 1) ω).1 (hN _ (le_max_left _ _)))
  have hle : ∀ ω, limsup (fun n => cubeRatio f n ω) atTop ≤ C := fun ω =>
    Filter.limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n => (hcu n ω).1))
      (Filter.Eventually.of_forall (fun n => (hcu n ω).2))
  exact Integrable.of_bound (Measurable.limsup (fun i => aux_ak_ae_21 hmeas i)).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]; exact hle ω))

-- The limit object of the upper bound: `aux_ak_ae_38` for the sublattice action
-- (`aux_ak_ae_39`) and `h := cubeRatio f m`, with `M := C` (`0 ≤ C` from `aux_ak_ae_2` at a
-- point given by `nonempty_of_isProbabilityMeasure μ`; `|cubeRatio| ≤ C` from `aux_ak_ae_20`,
-- `abs_le`), measurability `aux_ak_ae_21`.
private theorem aux_ak_ae_44_2 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (m : ℕ) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ C) ∧
      ∫ ω, G ω ∂μ = ∫ ω, cubeRatio f m ω ∂μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => gridAvg (fun z => τ ((m : ℤ) • z)) (cubeRatio f m)
        Finset.univ k ω) atTop (𝓝 (G ω)) := by
  obtain ⟨hσ, hσadd⟩ := aux_ak_ae_39 τ hτ hτadd m
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hb : ∀ x, |cubeRatio f m x| ≤ C := fun x => abs_le.2
    ⟨by linarith [(aux_ak_ae_20 hd hC m x).1, aux_ak_ae_2 hC x], (aux_ak_ae_20 hd hC m x).2⟩
  exact aux_ak_ae_38 hσ (fun z w ω => hσadd z w ω) (aux_ak_ae_21 hmeas m) (aux_ak_ae_2 hC ω0) hb

-- `aux_ak_ae_38` for the action of `aux_ak_ae_39` and `h := cubeRatio f m` (bounds
-- `aux_ak_ae_20` with `M = C`, `aux_ak_ae_2`; measurable `aux_ak_ae_21`); `aux_ak_ae_43`;
-- `integral_mono_ae` (integrability by `Integrable.of_bound`, measurability `Measurable.limsup`).
private theorem aux_ak_ae_44 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m : ℕ} (hm : 1 ≤ m) :
    ∫ ω, limsup (fun n => cubeRatio f n ω) atTop ∂μ ≤ ∫ ω, cubeRatio f m ω ∂μ := by
  obtain ⟨G, hGm, hGb, hGint, hG⟩ := aux_ak_ae_44_2 hd τ hτ hτadd hmeas hC m
  have hle := aux_ak_ae_43 hd τ hC hsub hstat hm hG
  rw [← hGint]
  exact integral_mono_ae (aux_ak_ae_44_1 hd hmeas hC)
    (Integrable.of_bound hGm.aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hGb x)) hle

/-! ### §4. The lower bound and the conclusion -/

/-! ### §4a. The lower bound (`aux_ak_ae_45`): route and decomposition

Mathematical route (all subadditivity used is along two-box splits; no Vitali/pinwheel coverings).
Write `r_n := cubeRatio f n`, `γ := inf_{n ≥ 1} ∫ r_n`.

(E) Coarse-graining.  For `m ≥ 1` the blown-up process `coarse f m B := f (blowup m B) / m^d`
  (every site `z` becomes the cube `m z + [0, m)^d`) satisfies all hypotheses of the file for the
  sublattice action `z ↦ τ (m • z)` with the same `C`, and `cubeRatio (coarse f m) k = r_{k m}`.
(A) Additive part and defect.  For a process `F` with the file's hypotheses put
  `addPart F B := ∑_{z ∈ B} F {z}` and `boxDefect F B := addPart F B - F B`.  Guillotine splitting
  down to unit cells gives `F ≤ addPart F` on boxes, so `R := boxDefect F` is `≥ 0` on boxes,
  superadditive along two-box splits, monotone under inclusion of boxes (by `aux_ak_ae_9`
  applied to `min F (addPart F) - addPart F + C·card`), stationary, `≤ C·card`; and
  `addPart F (Q_k) = k^d · gridAvg τ (F Q_1) univ k`, so `r^F_k = gridAvg - R(Q_k)/k^d`.
(B) Maximal inequality (the covering step, the DEEP core).  For `R` as in (A) with
  `∫ R(Q_N) ≤ ρ N^d` for all `N ≥ 1`:
      `μ {∃ k ≥ 1, R(Q_k) > α k^d} ≤ K_d ρ / α`,   `K_d = akMaxConst d = 2 (4d)^d`.
  Proof: truncate to `k ≤ K`, fix `2^J ≥ 2dK`, count bad sites of `Q_N` (`= N^d μ(E_K)` in mean
  by stationarity).  For each offset `u ∈ [0, 2^J)^d` use the NESTED dyadic grid of offset `u`.
  A bad site `x` with witness `k` has, for at least half of the offsets `u`, its cube `x + Q_k`
  inside ONE dyadic cell `D` of side `2^j ∈ [2dk, 4dk)`; by monotonicity `D` is heavy:
  `R(D) > α (4d)^{-d} |D|`.  The maximal heavy cells of one grid are pairwise disjoint dyadic
  cells, and ANY disjoint family of cells of one nested grid extends to a guillotine partition
  of the big box `dyBig u J N` (split each cell into its `2^d` children), so superadditivity and
  `R ≥ 0` give `α (4d)^{-d} · #covered ≤ R(dyBig u J N)`.  Averaging over `u` and integrating:
  `N^d μ(E_K) ≤ 2 (4d)^d/α · ρ ((N/2^J + 4) 2^J)^d`; let `N → ∞`, then `K → ∞`.
  This is where the pinwheel trap is avoided: only cells of one nested grid are ever combined.
(C) From (B): `X := limsup R(Q_k)/k^d ∈ [0, C]`, `{X > α} ⊆ {∃ k, R(Q_k) > α k^d}`, hence
  `∫ X ≤ α + C K_d ρ / α` for every `α > 0`.
(D) Unit-scale lower bound: if `∫ r^F_N ≥ ∫ r^F_1 - η` for all `N ≥ 1` then `ρ := η` works in
  (B) (`∫ R(Q_N) = N^d (∫ r^F_1 - ∫ r^F_N)`, using `aux_ak_ae_37`), and with the bounded
  multiparameter ergodic theorem `aux_ak_ae_38` for `h := F Q_1`:
      `∫ r^F_1 ≤ ∫ liminf_k r^F_k + α + C K_d η / α`.
(F) Assembly.  Given `ε`, put `δ := ε² / (4 (C + 1) K_d)`; choose `m ≥ 1` with
  `∫ r_m - δ ≤ ∫ r_{N m}` for all `N ≥ 1` (`γ` is an infimum); apply (D) to `coarse f m`
  (`η := δ`, `α := ε/2`), and `liminf_k r_{k m} ≤ liminf_n r_n` (nested cubes, `aux_ak_ae_11`).
-/

/-- The constant of the maximal inequality. -/
noncomputable def akMaxConst (d : ℕ) : ℝ := 2 * (4 * (d : ℝ)) ^ d

/-- Sum of `F` over the unit cells of `B`. -/
noncomputable def addPart {d : ℕ} (F : Finset (Site d) → Ω → ℝ) (B : Finset (Site d)) (ω : Ω) :
    ℝ :=
  ∑ z ∈ B, F {z} ω

/-- The defect of subadditivity with respect to unit cells. -/
noncomputable def boxDefect {d : ℕ} (F : Finset (Site d) → Ω → ℝ) (B : Finset (Site d))
    (ω : Ω) : ℝ :=
  addPart F B ω - F B ω

/-- The dyadic cell of level `j`, offset `u` and index `c`: `u + 2^j c + [0, 2^j)^d`. -/
noncomputable def dyCell {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) : Finset (Site d) :=
  latticeBox (u + (2 ^ j : ℤ) • c) (u + (2 ^ j : ℤ) • c + fun _ => (2 ^ j : ℤ) - 1)

/-- The union of the level-`J` cells of offset `u` meeting `[-2^J, N + 2^J)^d`, a cube of side
`(N / 2^J + 4) 2^J` with lower corner `u - 2 · 2^J`. -/
noncomputable def dyBig {d : ℕ} (u : Site d) (J N : ℕ) : Finset (Site d) :=
  (latticeCube d ((N / 2 ^ J + 4) * 2 ^ J)).map
    (Equiv.addRight (u - fun _ => 2 * (2 ^ J : ℤ))).toEmbedding

/-- Blow-up by the factor `m`: the site `z` becomes the cube `m z + [0, m)^d`. -/
noncomputable def blowup {d : ℕ} (m : ℕ) (B : Finset (Site d)) : Finset (Site d) :=
  B.biUnion fun z => (latticeCube d m).map (Equiv.addRight ((m : ℤ) • z)).toEmbedding

/-- The coarse-grained process at scale `m`, normalised per fine site. -/
noncomputable def coarse {d : ℕ} (f : Finset (Site d) → Ω → ℝ) (m : ℕ) (B : Finset (Site d))
    (ω : Ω) : ℝ :=
  f (blowup m B) ω / (m : ℝ) ^ d

-- `akMaxConst`, `positivity` (`d ≥ 1` so `4 d > 0`).
private theorem aux_ak_ae_45_0 {d : ℕ} (hd : 1 ≤ d) : 0 < akMaxConst d := by
  unfold akMaxConst
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-! #### (A) Additive part and defect -/

-- If every coordinate had `b i ≤ a i`, the box would be `⊆ {a}` (`aux_ak_ae_5_1`, `le_antisymm`,
-- `funext`), so `card ≤ 1` (`Finset.card_le_one`).  `by_contra`, `push_neg`.
private theorem aux_ak_ae_45_1 {d : ℕ} (a b : Site d) (h : 2 ≤ (latticeBox a b).card) :
    ∃ i, a i < b i := by
  by_contra hne
  push Not at hne
  have hsub : latticeBox a b ⊆ {a} := by
    intro x hx
    have hx' := (aux_ak_ae_5_1 a b x).1 hx
    rw [Finset.mem_singleton]
    funext i
    exact le_antisymm ((hx' i).2.trans (hne i)) (hx' i).1
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  omega

-- The split of `aux_ak_ae_5` at `t = b i`: card is additive (`Finset.card_union_of_disjoint`
-- with `(aux_ak_ae_5 …).2.2.2`), and both pieces are nonempty (`a` lies in the first, `b` in the
-- second: `aux_ak_ae_5_1`, `Function.update_apply`, `omega`), so each is strictly smaller.
private theorem aux_ak_ae_45_2 {d : ℕ} (a b : Site d) (hab : a ≤ b) (i : Fin d) (hi : a i < b i) :
    (latticeBox a (Function.update b i (b i - 1))).card < (latticeBox a b).card ∧
      (latticeBox (Function.update a i (b i)) b).card < (latticeBox a b).card := by
  have hs := aux_ak_ae_5 a b i (b i) hi.le (by omega)
  have hcard := hs.2.2.2.2 ▸ Finset.card_union_of_disjoint hs.2.2.2.1
  have ha : a ∈ latticeBox a (Function.update b i (b i - 1)) := by
    rw [aux_ak_ae_5_1]; intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact ⟨le_rfl, by omega⟩
    · rw [Function.update_of_ne hj]; exact ⟨le_rfl, hab j⟩
  have hb : b ∈ latticeBox (Function.update a i (b i)) b := by
    rw [aux_ak_ae_5_1]; intro j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact ⟨le_rfl, le_rfl⟩
    · rw [Function.update_of_ne hj]; exact ⟨hab j, le_rfl⟩
  have h1 := Finset.card_pos.2 ⟨a, ha⟩
  have h2 := Finset.card_pos.2 ⟨b, hb⟩
  omega

-- `card ≤ 1`: either `= ∅` (`Finset.card_eq_zero`; `aux_ak_ae_1`, `addPart`,
-- `Finset.sum_empty`) or `= {z}` (`Finset.card_eq_one`; `addPart`, `Finset.sum_singleton`).
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_3 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card) (a b : Site d)
    (hcard : (latticeBox a b).card ≤ 1) (ω : Ω) :
    F (latticeBox a b) ω ≤ addPart F (latticeBox a b) ω := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1
  · rw [Finset.card_eq_zero.1 h0, aux_ak_ae_1 hC ω]
    simp [addPart]
  · obtain ⟨z, hz⟩ := Finset.card_eq_one.1 h1
    rw [hz]
    simp [addPart]

-- `addPart`, `h.2.2.2.2 ▸ Finset.sum_union h.2.2.2.1`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_5 {d : ℕ} (F : Finset (Site d) → Ω → ℝ) {B B₁ B₂ : Finset (Site d)}
    (h : IsBoxSplit B B₁ B₂) (ω : Ω) :
    addPart F B ω = addPart F B₁ ω + addPart F B₂ ω := by
  unfold addPart
  rw [← h.2.2.2.2, Finset.sum_union h.2.2.2.1]

-- Guillotine splitting down to unit cells.  Strong induction on `n = card`
-- (`Nat.strong_induction_on`, generalizing `a b`): `n ≤ 1` is `aux_ak_ae_45_3`; otherwise
-- `aux_ak_ae_45_1` gives `i`, `a ≤ b` from `Finset.nonempty_Icc` (card ≥ 2 > 0), split at
-- `t = b i` (`aux_ak_ae_5`), `hsub`, the IH on both pieces (`aux_ak_ae_45_2`), and
-- `addPart` of a split is the sum (`aux_ak_ae_45_5`).
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_4 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω) (a b : Site d) (ω : Ω) :
    F (latticeBox a b) ω ≤ addPart F (latticeBox a b) ω := by
  induction hn : (latticeBox a b).card using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    rcases le_or_gt n 1 with h1 | h2
    · exact aux_ak_ae_45_3 hC a b (hn ▸ h1) ω
    · obtain ⟨i, hi⟩ := aux_ak_ae_45_1 a b (by omega)
      have hab : a ≤ b := Finset.nonempty_Icc.1 (Finset.card_pos.1 (by unfold latticeBox at hn; omega))
      have hs := aux_ak_ae_5 a b i (b i) hi.le (by omega)
      obtain ⟨c1, c2⟩ := aux_ak_ae_45_2 a b hab i hi
      have e1 := ih _ (hn ▸ c1) _ _ rfl
      have e2 := ih _ (hn ▸ c2) _ _ rfl
      rw [aux_ak_ae_45_5 F hs ω]
      linarith [hsub _ _ _ ω hs]

-- `addPart`, `Finset.sum_nonneg`, `Finset.sum_le_card_nsmul` with `hC {z}`
-- (`Finset.card_singleton`), `nsmul_eq_mul`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_6 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card) (B : Finset (Site d)) (ω : Ω) :
    0 ≤ addPart F B ω ∧ addPart F B ω ≤ C * B.card := by
  unfold addPart
  refine ⟨Finset.sum_nonneg fun z _ => (hC {z} ω).1, ?_⟩
  calc ∑ z ∈ B, F {z} ω ≤ ∑ _z ∈ B, C :=
        Finset.sum_le_sum fun z _ => by simpa using (hC {z} ω).2
    _ = C * B.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

-- `boxDefect`; `aux_ak_ae_45_4` (nonneg) and `aux_ak_ae_45_6`, `hC` (upper bound); `linarith`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_7 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω) :
    (∀ a b ω, 0 ≤ boxDefect F (latticeBox a b) ω) ∧
      ∀ B ω, boxDefect F B ω ≤ C * B.card := by
  refine ⟨fun a b ω => ?_, fun B ω => ?_⟩
  · have := aux_ak_ae_45_4 hC hsub a b ω
    unfold boxDefect; linarith
  · have := (aux_ak_ae_45_6 hC B ω).2
    have := (hC B ω).1
    unfold boxDefect; linarith

-- `boxDefect`, `aux_ak_ae_45_5`, `hsub`; `linarith`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_8 {d : ℕ} {F : Finset (Site d) → Ω → ℝ}
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω)
    {B B₁ B₂ : Finset (Site d)} (h : IsBoxSplit B B₁ B₂) (ω : Ω) :
    boxDefect F B₁ ω + boxDefect F B₂ ω ≤ boxDefect F B ω := by
  have h1 := aux_ak_ae_45_5 F h ω
  have h2 := hsub B B₁ B₂ ω h
  unfold boxDefect; linarith

-- The auxiliary process `G A := min (F A) (addPart F A) - addPart F A + C |A|` has the file's
-- bounds (`min_le_right`, `le_min`, `aux_ak_ae_45_6`, `hC`) and is two-box subadditive: on boxes
-- `min = F` (`min_eq_left` with `aux_ak_ae_45_4`), so use `hsub` and `aux_ak_ae_45_5`, card
-- additivity (`Finset.card_union_of_disjoint`).
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_9 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω) :
    (∀ A ω, 0 ≤ min (F A ω) (addPart F A ω) - addPart F A ω + C * A.card ∧
        min (F A ω) (addPart F A ω) - addPart F A ω + C * A.card ≤ C * A.card) ∧
      ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ →
        min (F B ω) (addPart F B ω) - addPart F B ω + C * B.card ≤
          (min (F B₁ ω) (addPart F B₁ ω) - addPart F B₁ ω + C * B₁.card) +
            (min (F B₂ ω) (addPart F B₂ ω) - addPart F B₂ ω + C * B₂.card) := by
  refine ⟨?_, ?_⟩
  · intro A ω
    have had := aux_ak_ae_45_6 hC A ω
    have hF := hC A ω
    constructor
    · rcases le_total (F A ω) (addPart F A ω) with hmin | hmin
      · rw [min_eq_left hmin]; linarith [had.1, had.2, hF.1, hF.2]
      · rw [min_eq_right hmin]; linarith [had.1, had.2, hF.1, hF.2]
    · linarith [min_le_right (F A ω) (addPart F A ω)]
  · intro B B1 B2 ω h
    obtain ⟨hB, hB1, hB2, hdisj, hunion⟩ := h
    obtain ⟨a, b, hab⟩ := hB
    obtain ⟨c, d, hcd⟩ := hB1
    obtain ⟨e, g, heg⟩ := hB2
    subst hab
    subst hcd
    subst heg
    have h4 := aux_ak_ae_45_4 hC hsub
    have h8 := aux_ak_ae_45_8 hsub ⟨⟨a, b, rfl⟩, ⟨c, d, rfl⟩, ⟨e, g, rfl⟩, hdisj, hunion⟩ ω
    simp only [boxDefect] at h8
    have hcardnat : (latticeBox a b).card = (latticeBox c d).card + (latticeBox e g).card :=
      (congrArg Finset.card hunion).symm.trans (Finset.card_union_of_disjoint hdisj)
    have hcard : ((latticeBox a b).card : ℝ) =
        ((latticeBox c d).card : ℝ) + ((latticeBox e g).card : ℝ) :=
      (congrArg (fun t : ℕ => (t : ℝ)) hcardnat).trans (Nat.cast_add _ _)
    have hCcard : C * ((latticeBox a b).card : ℝ) =
        C * ((latticeBox c d).card : ℝ) + C * ((latticeBox e g).card : ℝ) :=
      (congrArg (fun t : ℝ => C * t) hcard).trans (mul_add C _ _)
    have e1 : min (F (latticeBox c d) ω) (addPart F (latticeBox c d) ω) =
        F (latticeBox c d) ω := min_eq_left (h4 c d ω)
    have e2 : min (F (latticeBox e g) ω) (addPart F (latticeBox e g) ω) =
        F (latticeBox e g) ω := min_eq_left (h4 e g ω)
    have emin : min (F (latticeBox a b) ω) (addPart F (latticeBox a b) ω) ≤
        F (latticeBox a b) ω := min_le_left _ _
    linarith [h8, hCcard, e1, e2, emin]


-- Monotonicity of the defect: `aux_ak_ae_9` for the process of `aux_ak_ae_45_9` gives
-- `G B ≤ G B' + C (|B| - |B'|)`; on boxes `min = F` (`aux_ak_ae_45_4`, `min_eq_left`); `boxDefect`,
-- `linarith`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_10 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω)
    (a b a' b' : Site d) (ha : a ≤ a') (hb : b' ≤ b) (ω : Ω) :
    boxDefect F (latticeBox a' b') ω ≤ boxDefect F (latticeBox a b) ω := by
  obtain ⟨hG, hGsub⟩ := aux_ak_ae_45_9 hC hsub
  have h9 := aux_ak_ae_9 (f := fun A ω => min (F A ω) (addPart F A ω) - addPart F A ω + C * A.card)
    hG hGsub a b a' b' ha hb ω
  rw [min_eq_left (aux_ak_ae_45_4 hC hsub a b ω), min_eq_left (aux_ak_ae_45_4 hC hsub a' b' ω)] at h9
  unfold boxDefect
  linarith

-- Stationarity: `boxDefect`, `addPart`, `Finset.sum_map`, `Equiv.coe_toEmbedding`,
-- `Equiv.coe_addRight`, and `{y + z} = ({y} : Finset _).map (addRight z)` (`Finset.map_singleton`)
-- with `hstat`; the `F B` term by `hstat`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_11 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (τ : Site d → Ω → Ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω))
    (B : Finset (Site d)) (z : Site d) (ω : Ω) :
    boxDefect F (B.map (Equiv.addRight z).toEmbedding) ω = boxDefect F B (τ z ω) := by
  unfold boxDefect addPart
  rw [hstat B z ω]
  congr 1
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.map_singleton (Equiv.addRight z).toEmbedding x, hstat {x} z ω]


-- `boxDefect`, `addPart`: `(Finset.measurable_sum _ fun z _ => hmeas {z}).sub (hmeas B)`.
private theorem aux_ak_ae_45_12 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (hmeas : ∀ A, Measurable (F A))
    (B : Finset (Site d)) : Measurable (boxDefect F B) := by
  exact (Finset.measurable_sum _ fun z _ => hmeas {z}).sub (hmeas B)

-- `latticeCube d 1 = {0}` (`latticeCube`, `Finset.Icc_self`, `sub_self`), its translate by `z`
-- is `{z}` (`Finset.map_singleton`, `zero_add`), then `hstat`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_13 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (τ : Site d → Ω → Ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω)) (z : Site d) (ω : Ω) :
    F {z} ω = F (latticeCube d 1) (τ z ω) := by
  have h1 : latticeCube d 1 = {0} := by
    simp [latticeCube]
    rfl
  have h2 : ({z} : Finset (Site d)) = (latticeCube d 1).map (Equiv.addRight z).toEmbedding := by
    rw [h1, Finset.map_singleton]; simp
  rw [h2, hstat]

-- Reindex the cube by `natToSite`: `Finset.sum_nbij'` with `natToSite` and
-- `fun z i => (z i).toNat`; membership via `latticeCube`, `Finset.mem_Icc`, `gridSet`,
-- `Fintype.mem_piFinset`, `Finset.mem_range`, `Int.toNat_of_nonneg`, `omega`.
private theorem aux_ak_ae_45_14 {d : ℕ} {M : Type*} [AddCommMonoid M] (k : ℕ) (g : Site d → M) :
    ∑ z ∈ latticeCube d k, g z = ∑ w ∈ gridSet d Finset.univ k, g (natToSite w) := by
  refine Finset.sum_nbij' (fun (z : Site d) (i : Fin d) => (z i).toNat)
    (fun w : Fin d → ℕ => natToSite w) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [gridSet, Fintype.mem_piFinset]
    simp only [Finset.mem_univ, if_true, Finset.mem_range]
    intro i
    rw [latticeCube, Finset.mem_Icc] at hz
    simp only [Pi.le_def, Pi.zero_apply] at hz
    have h1 := hz.1 i
    have h2 := hz.2 i
    exact (Int.toNat_lt h1).2 (by omega)
  · intro w hw
    rw [gridSet, Fintype.mem_piFinset] at hw
    simp only [Finset.mem_univ, if_true, Finset.mem_range] at hw
    rw [latticeCube, Finset.mem_Icc]
    simp only [Pi.le_def, Pi.zero_apply, natToSite]
    refine ⟨fun i => Int.natCast_nonneg (w i), ?_⟩
    intro i
    have h := hw i
    omega
  · intro z hz
    funext i
    rw [latticeCube, Finset.mem_Icc] at hz
    simp only [Pi.le_def, Pi.zero_apply] at hz
    simp only [natToSite]
    exact Int.toNat_of_nonneg (hz.1 i)
  · intro w hw
    funext i
    simp only [natToSite]
    exact Int.toNat_natCast (w i)
  · intro z hz
    rw [latticeCube, Finset.mem_Icc] at hz
    simp only [Pi.le_def, Pi.zero_apply] at hz
    congr 1
    funext i
    simp only [natToSite]
    exact (Int.toNat_of_nonneg (hz.1 i)).symm


-- `addPart`, `aux_ak_ae_45_13`, `aux_ak_ae_45_14`; `gridAvg` with `Finset.card_univ`,
-- `Fintype.card_fin`, `mul_div_cancel₀` (`(k : ℝ) ^ d ≠ 0` for `k ≥ 1`).
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_15 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (τ : Site d → Ω → Ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω)) {k : ℕ} (hk : 1 ≤ k) (ω : Ω) :
    addPart F (latticeCube d k) ω =
      (k : ℝ) ^ d * gridAvg τ (F (latticeCube d 1)) Finset.univ k ω := by
  unfold addPart
  rw [aux_ak_ae_45_14]
  rw [gridAvg]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [mul_div_cancel₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega : k ≠ 0)))]
  exact Finset.sum_congr rfl fun w _ => (aux_ak_ae_45_13 τ hstat (natToSite w) ω)


/-! #### (B) The maximal inequality -/

-- Continuity from below: `tendsto_measure_iUnion_atTop hS`, then `ENNReal.toReal` of the limit
-- (`Measure.real`, `measureReal_def`, `ENNReal.tendsto_toReal` with `measure_ne_top`) and
-- `le_of_tendsto'`.
private theorem aux_ak_ae_45_16 {μ : Measure Ω} [IsFiniteMeasure μ] {S : ℕ → Set Ω} (hS : Monotone S)
    {c : ℝ} (h : ∀ K, μ.real (S K) ≤ c) : μ.real (⋃ K, S K) ≤ c := by
  have hlim : Tendsto (fun K => μ (S K)) atTop (𝓝 (μ (⋃ K, S K))) := tendsto_measure_iUnion_atTop hS
  have hne : μ (⋃ K, S K) ≠ ⊤ := measure_ne_top μ _
  have h2 : Tendsto (fun K => (μ (S K)).toReal) atTop (𝓝 ((μ (⋃ K, S K)).toReal)) :=
    (ENNReal.tendsto_toReal hne).comp hlim
  have h' : ∀ K, (μ (S K)).toReal ≤ c := fun K => by
    rw [← measureReal_def]; exact h K
  exact le_of_tendsto' h2 h'


-- Each summand is a bounded measurable function: `Integrable.of_bound` with bound `1`,
-- measurability `(measurable_const.indicator hE).comp (hτ x).measurable` (`Measurable.indicator`),
-- `Set.indicator_apply`, `split_ifs`, `norm_num`.
private theorem aux_aux_ak_ae_45_17_1 {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ) {E : Set Ω}
    (hE : MeasurableSet E) (x : Site d) :
    Integrable (fun ω => E.indicator (fun _ => (1 : ℝ)) (τ x ω)) μ := by
  classical
  refine Integrable.of_bound ?_ 1 ?_
  · exact ((measurable_const.indicator hE).comp (hτ x).measurable).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, Set.indicator_apply]
    split_ifs <;> norm_num

-- `← Set.indicator_comp_right` turns the integrand into `(τ x ⁻¹' E).indicator 1`;
-- `integral_indicator_one` (preimage measurable: `(hτ x).measurable hE`), `measureReal_def`,
-- `MeasurePreserving.measure_preimage` (`hE.nullMeasurableSet`).
private theorem aux_aux_ak_ae_45_17_2 {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ) {E : Set Ω}
    (hE : MeasurableSet E) (x : Site d) :
    ∫ ω, E.indicator (fun _ => (1 : ℝ)) (τ x ω) ∂μ = μ.real E := by
  classical
  have h1 : (fun ω => E.indicator (fun _ => (1 : ℝ)) (τ x ω))
      = (τ x ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    exact Set.indicator_comp_right (τ x) (g := fun _ => (1 : ℝ)) (x := ω)
  rw [h1]
  have h2 : ∫ ω, (τ x ⁻¹' E).indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real (τ x ⁻¹' E) :=
    integral_indicator_one ((hτ x).measurable hE)
  rw [h2, measureReal_def, (hτ x).measure_preimage hE.nullMeasurableSet]
  rfl

-- Counting by stationarity: `integral_finsetSum` (each term integrable: bounded indicator),
-- `∫ 1_E ∘ τ x = μ.real (τ x ⁻¹' E) = μ.real E` (`integral_indicator_one`,
-- `Set.indicator_comp_right`, `MeasurePreserving.measure_preimage`), `Finset.sum_const`,
-- `aux_t0`, `nsmul_eq_mul`.
private theorem aux_ak_ae_45_17 {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] (τ : Site d → Ω → Ω)
    (hτ : ∀ z, MeasurePreserving (τ z) μ μ) {E : Set Ω} (hE : MeasurableSet E) (N : ℕ) :
    ∫ ω, (∑ x ∈ latticeCube d N, E.indicator (fun _ => (1 : ℝ)) (τ x ω)) ∂μ =
      (N : ℝ) ^ d * μ.real E := by
  rw [integral_finsetSum _ (fun x _ => aux_aux_ak_ae_45_17_1 τ hτ hE x)]
  rw [Finset.sum_congr rfl (fun x _ => aux_aux_ak_ae_45_17_2 τ hτ hE x), Finset.sum_const, aux_t0,
    nsmul_eq_mul, Nat.cast_pow]

-- One coordinate, nested case.  With `q = c / 2^(j'-j)`, `ρ = c % 2^(j'-j)`:
-- `c = 2^(j'-j) q + ρ`, `0 ≤ ρ < 2^(j'-j)` (`Int.mul_ediv_add_emod`, `Int.emod_nonneg`,
-- `Int.emod_lt_of_pos`); `2^j' = 2^j 2^(j'-j)` (`← pow_add`, `Nat.add_sub_cancel' hjj`); `nlinarith`.
private theorem aux_aux_ak_ae_45_18_1 {j j' : ℕ} (hjj : j ≤ j') (c c' : ℤ) (h : c / 2 ^ (j' - j) = c') :
    (2 : ℤ) ^ j' * c' ≤ 2 ^ j * c ∧ 2 ^ j * c + 2 ^ j ≤ 2 ^ j' * c' + 2 ^ j' := by
  have hq : c = 2 ^ (j' - j) * c' + c % 2 ^ (j' - j) := by
    rw [← h]; exact (Int.mul_ediv_add_emod c (2 ^ (j' - j))).symm
  have h0 : 0 ≤ c % 2 ^ (j' - j) := Int.emod_nonneg c (by positivity)
  have h1 : c % 2 ^ (j' - j) < 2 ^ (j' - j) := Int.emod_lt_of_pos c (by positivity)
  have hpow : (2 : ℤ) ^ j' = 2 ^ j * 2 ^ (j' - j) := by rw [← pow_add, Nat.add_sub_cancel' hjj]
  have hpj : (0 : ℤ) < 2 ^ j := by positivity
  constructor
  · rw [hpow]; nlinarith [hq, h0, hpj]
  · rw [hpow]; nlinarith [hq, h1, hpj]

-- One coordinate, disjoint case.  Write `c = 2^(j'-j) q + ρ` as in `aux_aux_ak_ae_45_18_1`;
-- `q ≠ c'` gives `q + 1 ≤ c'` or `c' + 1 ≤ q` (`lt_or_gt_of_ne`, `Int.add_one_le_iff`); then
-- `2^j c + 2^j ≤ 2^j' q + 2^j' ≤ 2^j' c'`, resp. `2^j' c' + 2^j' ≤ 2^j' q ≤ 2^j c`; `nlinarith`.
private theorem aux_aux_ak_ae_45_18_2 {j j' : ℕ} (hjj : j ≤ j') (c c' : ℤ) (h : c / 2 ^ (j' - j) ≠ c') :
    2 ^ j * c + 2 ^ j ≤ (2 : ℤ) ^ j' * c' ∨ (2 : ℤ) ^ j' * c' + 2 ^ j' ≤ 2 ^ j * c := by
  have hq : c = 2 ^ (j' - j) * (c / 2 ^ (j' - j)) + c % 2 ^ (j' - j) :=
    (Int.mul_ediv_add_emod c (2 ^ (j' - j))).symm
  have h0 : 0 ≤ c % 2 ^ (j' - j) := Int.emod_nonneg c (by positivity)
  have h1 : c % 2 ^ (j' - j) < 2 ^ (j' - j) := Int.emod_lt_of_pos c (by positivity)
  have hpow : (2 : ℤ) ^ j' = 2 ^ j * 2 ^ (j' - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hjj]
  have hA : (0 : ℤ) ≤ 2 ^ j := by positivity
  have hB : (0 : ℤ) ≤ 2 ^ (j' - j) := by positivity
  rcases lt_or_gt_of_ne h with hlt | hgt
  · left
    have hQ : c / 2 ^ (j' - j) + 1 ≤ c' := by omega
    have hR : c % 2 ^ (j' - j) + 1 ≤ 2 ^ (j' - j) := by omega
    have hc1 : c + 1 ≤ 2 ^ (j' - j) * (c / 2 ^ (j' - j) + 1) := by
      nlinarith [hq, hR]
    have hc2 : 2 ^ (j' - j) * (c / 2 ^ (j' - j) + 1) ≤ 2 ^ (j' - j) * c' :=
      mul_le_mul_of_nonneg_left hQ hB
    have hc : c + 1 ≤ 2 ^ (j' - j) * c' := le_trans hc1 hc2
    calc 2 ^ j * c + 2 ^ j = 2 ^ j * (c + 1) := by ring
      _ ≤ 2 ^ j * (2 ^ (j' - j) * c') := mul_le_mul_of_nonneg_left hc hA
      _ = 2 ^ j' * c' := by rw [hpow]; ring
  · right
    have hQ : c' + 1 ≤ c / 2 ^ (j' - j) := by omega
    have hc1 : 2 ^ (j' - j) * (c' + 1) ≤ 2 ^ (j' - j) * (c / 2 ^ (j' - j)) :=
      mul_le_mul_of_nonneg_left hQ hB
    have hc2 : 2 ^ (j' - j) * (c / 2 ^ (j' - j)) ≤ c := by
      nlinarith [hq, h0]
    have hc : 2 ^ (j' - j) * (c' + 1) ≤ c := le_trans hc1 hc2
    calc 2 ^ j' * c' + 2 ^ j' = 2 ^ j' * (c' + 1) := by ring
      _ = 2 ^ j * (2 ^ (j' - j) * (c' + 1)) := by rw [hpow]; ring
      _ ≤ 2 ^ j * c := mul_le_mul_of_nonneg_left hc hA

-- Coordinatewise nested intervals give nested cells: `dyCell`, `latticeBox`,
-- `Finset.Icc_subset_Icc` with `Pi.le_def`; `Pi.add_apply`, `Pi.smul_apply`, `smul_eq_mul`;
-- `linarith` from `h i`.
private theorem aux_aux_ak_ae_45_18_3 {d : ℕ} (u : Site d) {j j' : ℕ} (c c' : Site d)
    (h : ∀ i, (2 : ℤ) ^ j' * c' i ≤ 2 ^ j * c i ∧ 2 ^ j * c i + 2 ^ j ≤ 2 ^ j' * c' i + 2 ^ j') :
    dyCell u j c ⊆ dyCell u j' c' := by
  intro y hy
  rw [dyCell, aux_ak_ae_5_1] at hy ⊢
  intro i
  have h1 := hy i
  have h2 := h i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  constructor <;> linarith

-- One separated coordinate gives disjoint cells: `Finset.disjoint_left`; a common point `y`
-- satisfies both coordinate-`i` bounds (`dyCell`, `aux_ak_ae_5_1`, `Pi.add_apply`, `Pi.smul_apply`,
-- `smul_eq_mul`), contradicting `h` (`rcases h`, `linarith`).
private theorem aux_aux_ak_ae_45_18_4 {d : ℕ} (u : Site d) {j j' : ℕ} (c c' : Site d) (i : Fin d)
    (h : 2 ^ j * c i + 2 ^ j ≤ (2 : ℤ) ^ j' * c' i ∨ (2 : ℤ) ^ j' * c' i + 2 ^ j' ≤ 2 ^ j * c i) :
    Disjoint (dyCell u j c) (dyCell u j' c') := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  rw [dyCell, aux_ak_ae_5_1] at hy hy'
  have h1 := hy i
  have h2 := hy' i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rcases h with h | h <;> linarith [h1.1, h1.2, h2.1, h2.2]

-- Cells of one grid are nested or disjoint: coordinatewise, the intervals
-- `[u_i + 2^j c_i, u_i + 2^j c_i + 2^j)` and `[u_i + 2^{j'} c'_i, …)` with `j ≤ j'` are nested or
-- disjoint (compare `⌊c_i / 2^{j'-j}⌋` with `c'_i`: `Int.ediv_emod_unique`, `pow_add`); a box is
-- inside iff every coordinate is, disjoint if one coordinate is (`aux_ak_ae_5_1`).  SPLIT?
private theorem aux_ak_ae_45_18 {d : ℕ} (u : Site d) {j j' : ℕ} (hjj : j ≤ j') (c c' : Site d) :
    dyCell u j c ⊆ dyCell u j' c' ∨ Disjoint (dyCell u j c) (dyCell u j' c') := by
  by_cases h : ∀ i, c i / 2 ^ (j' - j) = c' i
  · exact Or.inl (aux_aux_ak_ae_45_18_3 u c c' fun i => aux_aux_ak_ae_45_18_1 hjj (c i) (c' i) (h i))
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr (aux_aux_ak_ae_45_18_4 u c c' i (aux_aux_ak_ae_45_18_2 hjj (c i) (c' i) hi))

-- Base: the half-box with no coordinate cut is the parent cell.  `dyCell`, `latticeBox`;
-- `congr 1`, `funext l`, `Pi.add_apply`, `Pi.smul_apply`, `smul_eq_mul`, `Pi.zero_apply`,
-- `Finset.notMem_empty`, `if_false`, `Nat.cast_zero`, `mul_zero`, `add_zero`; `ring`.
private theorem aux_aux_ak_ae_45_19_1 {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) :
    latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * (((0 : Fin d → ℕ) l : ℕ) : ℤ))
      (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * (((0 : Fin d → ℕ) l : ℕ) : ℤ) +
        (if l ∈ (∅ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) =
      dyCell u (j + 1) c := by
  rw [dyCell]
  congr 1 <;> funext l <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.notMem_empty,
      if_false, Nat.cast_zero, mul_zero, add_zero] <;>
    ring

-- Lower piece of the cut of coordinate `i ∉ s` at `t = a i + 2^j`: it is the half-box of
-- `insert i s` at `Function.update w i 0`.  `latticeBox`; `congr 1`, `funext l`,
-- `Function.update_apply`, `by_cases l = i` (`subst`, `hw`, `Finset.mem_insert_self`) /
-- (`Finset.mem_insert`, `if_neg`); `push_cast`, `ring`.
private theorem aux_aux_ak_ae_45_19_2 {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) (s : Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ) (hw : w i = 0) :
    latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
        (Function.update (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) i
          ((u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) + 2 ^ j) - 1)) =
      latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 0 l : ℕ) : ℤ))
      (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 0 l : ℕ) : ℤ) +
        (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) := by
  congr 1 <;> funext l <;>
    simp only [Function.update_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mem_insert] <;>
    by_cases hl : l = i <;>
      simp only [hl, ↓reduceIte, hw, hi, not_false_eq_true, true_or, false_or] <;>
      ring

-- Upper piece of the same cut: the half-box of `insert i s` at `Function.update w i 1`.
-- `latticeBox`; `congr 1`, `funext l`, `Function.update_apply`, `by_cases l = i`, `hw`, `hi`
-- (`if_neg`), `Finset.mem_insert`, `pow_succ`; `push_cast`, `ring`.
private theorem aux_aux_ak_ae_45_19_3 {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) (s : Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ) (hw : w i = 0) :
    latticeBox (Function.update (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ)) i
        (u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) + 2 ^ j))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) =
      latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 1 l : ℕ) : ℤ))
      (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 1 l : ℕ) : ℤ) +
        (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) := by
  congr 1 <;> funext l <;>
    simp only [Function.update_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mem_insert] <;>
    by_cases hl : l = i <;>
      simp only [hl, ↓reduceIte, hw, hi, not_false_eq_true, true_or, false_or] <;>
      ring

private theorem aux_aux_ak_ae_45_19_4 {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) (s : Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ) (hw : w i = 0) :
    IsBoxSplit (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1))
      (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 0 l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 0 l : ℕ) : ℤ) +
          (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1))
      (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 1 l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 1 l : ℕ) : ℤ) +
          (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)) := by
  rw [← aux_aux_ak_ae_45_19_2 u j c s i hi w hw, ← aux_aux_ak_ae_45_19_3 u j c s i hi w hw]
  have hp : (0 : ℤ) < 2 ^ j := by positivity
  apply aux_ak_ae_5
  · show u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) ≤
      u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) + 2 ^ j
    linarith
  · show u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) + 2 ^ j ≤
      u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) +
        (if i ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1 + 1
    rw [if_neg hi, pow_succ]
    linarith

private theorem aux_aux_ak_ae_45_19_5 {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (j : ℕ)
    (c : Site d) (s : Finset (Fin d)) :
    ∑ w ∈ gridSet d s 2, r (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)) ≤
      r (dyCell u (j + 1) c) := by
  induction s using Finset.induction with
  | empty =>
    rw [aux_ak_ae_14, Finset.sum_singleton]
    exact le_of_eq (congrArg r (aux_aux_ak_ae_45_19_1 u j c))
  | insert i s hi ih =>
    rw [aux_ak_ae_16 s i hi 2 (fun w => r (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)))]
    refine le_trans (Finset.sum_le_sum fun w hw => ?_) ih
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    exact hrsup _ _ _ (aux_aux_ak_ae_45_19_4 u j c s i hi w (aux_ak_ae_15 hw hi))

-- A child cell is the full half-box at `w = e`.  `dyCell`, `latticeBox`; `congr 1`, `funext l`,
-- `Pi.add_apply`, `Pi.smul_apply`, `smul_eq_mul`, `Finset.mem_univ`, `if_true`, `pow_succ`; `ring`.
private theorem aux_aux_ak_ae_45_19_6 {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) (e : Fin d → Fin 2) :
    dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)) =
      latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((e l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((e l : ℕ) : ℤ) +
          (if l ∈ (Finset.univ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) := by
  rw [dyCell]
  congr 1 <;> funext l <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mem_univ, if_true] <;>
    ring

-- Reindex `{0,1}^d` as `gridSet d univ 2`: `Finset.sum_nbij'` with `fun e l => (e l : ℕ)` and
-- `fun w l => (⟨w l % 2, Nat.mod_lt _ two_pos⟩ : Fin 2)`; membership `gridSet`,
-- `Fintype.mem_piFinset`, `Finset.mem_range`, `Fin.is_lt`; inverses `funext`, `Fin.ext`,
-- `Nat.mod_eq_of_lt`.
private theorem aux_aux_ak_ae_45_19_7 {d : ℕ} {M : Type*} [AddCommMonoid M] (g : (Fin d → ℕ) → M) :
    ∑ e : Fin d → Fin 2, g (fun i => (e i : ℕ)) = ∑ w ∈ gridSet d Finset.univ 2, g w := by
  refine Finset.sum_nbij' (fun (e : Fin d → Fin 2) => fun i => (e i : ℕ))
    (fun (w : Fin d → ℕ) => fun i => (⟨w i % 2, Nat.mod_lt _ two_pos⟩ : Fin 2)) ?_ ?_ ?_ ?_ ?_
  · intro e _
    rw [gridSet, Fintype.mem_piFinset]
    intro i
    simp only [Finset.mem_univ, if_true, Finset.mem_range]
    exact (e i).isLt
  · intro w _
    exact Finset.mem_univ _
  · intro e _
    funext i
    simp only [Fin.ext_iff]
    exact Nat.mod_eq_of_lt (e i).isLt
  · intro w hw
    funext i
    simp only []
    have h2 : w i < 2 := by
      have h3 : w ∈ Fintype.piFinset (fun i : Fin d => if i ∈ Finset.univ then Finset.range 2 else {0}) := by
        simpa only [gridSet] using hw
      have h4 := (Fintype.mem_piFinset.mp h3) i
      simpa using h4
    exact Nat.mod_eq_of_lt h2
  · intro e _
    rfl

-- A cell is the guillotine union of its `2^d` children `dyCell u j (2 c + e)`, `e ∈ {0,1}^d`:
-- cut the coordinates one at a time (`aux_ak_ae_5` at `t = u_i + 2^j (2 c_i + 1)`,
-- `Finset.induction` over the cut coordinates as in `aux_ak_ae_18`), superadditivity at each cut.
-- SPLIT? (mirror `aux_ak_ae_16`–`aux_ak_ae_18` with `≥`).
private theorem aux_ak_ae_45_19 {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (j : ℕ)
    (c : Site d) :
    ∑ e : Fin d → Fin 2, r (dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ))) ≤
      r (dyCell u (j + 1) c) := by
  calc ∑ e : Fin d → Fin 2, r (dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)))
      = ∑ e : Fin d → Fin 2, (fun w : Fin d → ℕ => r (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
            (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
              (if l ∈ (Finset.univ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1))) (fun i => (e i : ℕ)) :=
        Finset.sum_congr rfl fun e _ => by rw [aux_aux_ak_ae_45_19_6 u j c e]
    _ = ∑ w ∈ gridSet d Finset.univ 2, r (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
            (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
              (if l ∈ (Finset.univ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)) :=
        aux_aux_ak_ae_45_19_7 (fun w : Fin d → ℕ => r (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
            (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
              (if l ∈ (Finset.univ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)))
    _ ≤ r (dyCell u (j + 1) c) := aux_aux_ak_ae_45_19_5 r hrsup u j c Finset.univ

-- Cells are nonempty: the lower corner lies in the cell.  `dyCell`, `latticeBox`,
-- `Finset.nonempty_Icc`, `Pi.le_def`, `Pi.add_apply`; `2^j - 1 ≥ 0` (`one_le_two_pow`/`positivity`), `linarith`.
private theorem aux_aux_ak_ae_45_20_1 {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) :
    (dyCell u j c).Nonempty := by
  refine ⟨fun l => u l + 2 ^ j * c l, ?_⟩
  rw [dyCell, latticeBox, Finset.mem_Icc]
  refine ⟨le_refl _, ?_⟩
  rw [Pi.le_def]
  intro l
  have h : (1 : ℤ) ≤ (2 : ℤ) ^ j := one_le_pow₀ (show (1 : ℤ) ≤ 2 by norm_num)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

-- `dyCell`, `latticeBox`, `Pi.card_Icc`, `Int.card_Icc` (each factor
-- `(a + (2^j - 1) + 1 - a).toNat = 2^j`: `ring_nf`, `← Nat.cast_pow`/`push_cast`, `Int.toNat_natCast`),
-- `Finset.prod_const`, `Finset.card_univ`, `Fintype.card_fin`.
private theorem aux_aux_ak_ae_45_20_2 {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) :
    (dyCell u j c).card = (2 ^ j) ^ d := by
  have h : dyCell u j c = (latticeCube d (2 ^ j)).map
      (Equiv.addRight (u + (2 ^ j : ℤ) • c)).toEmbedding := by
    rw [dyCell, aux_ak_ae_12]
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h, Finset.card_map, aux_t0]

-- A cell of level `j'` inside a cell of level `j` has `j' ≤ j`: cardinality
-- (`aux_aux_ak_ae_45_20_2`, `Finset.card_le_card`, `Nat.pow_le_pow_iff_left`,
-- `Nat.pow_le_pow_iff_right`).
private theorem aux_aux_ak_ae_45_20_3 {d : ℕ} (hd : 1 ≤ d) (u : Site d) {j j' : ℕ} {c c' : Site d}
    (h : dyCell u j' c' ⊆ dyCell u j c) : j' ≤ j := by
  have hcard := Finset.card_le_card h
  rw [aux_aux_ak_ae_45_20_2 u j' c', aux_aux_ak_ae_45_20_2 u j c] at hcard
  have h1 : 2 ^ j' ≤ 2 ^ j :=
    (Nat.pow_le_pow_iff_left (by omega : d ≠ 0)).mp hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1

-- Two cells of the same level, one inside the other, are equal: the corner of the smaller one
-- lies in the bigger one (`aux_aux_ak_ae_45_20_1`), so `aux_ak_ae_45_18` gives containment or
-- disjointness, and disjointness is impossible.
private theorem aux_aux_ak_ae_45_20_4 {d : ℕ} (u : Site d) {j : ℕ} {c c' : Site d}
    (h : dyCell u j c' ⊆ dyCell u j c) : c' = c := by
  have hcell : ∀ (c : Site d), dyCell u j c = latticeBox (fun l => u l + 2 ^ j * c l)
      (fun l => u l + 2 ^ j * c l + 2 ^ j - 1) := by
    intro c
    rw [dyCell]
    congr 1 <;> funext l <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  have h1 : ∀ l, u l + 2 ^ j * c l ≤ u l + 2 ^ j * c' l := by
    have hmem : (fun l => u l + 2 ^ j * c' l) ∈ dyCell u j c' := by
      rw [hcell]
      rw [aux_ak_ae_5_1]
      intro l
      constructor
      · exact le_refl _
      · have h5 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (show (1 : ℤ) ≤ 2 by norm_num)
        linarith
    have h2 := h hmem
    rw [hcell, aux_ak_ae_5_1] at h2
    intro l
    exact (h2 l).1
  have h3 : ∀ l, u l + 2 ^ j * c' l ≤ u l + 2 ^ j * c l := by
    have hmem : (fun l => u l + 2 ^ j * c' l + 2 ^ j - 1) ∈ dyCell u j c' := by
      rw [hcell]
      rw [aux_ak_ae_5_1]
      intro l
      constructor
      · have h5 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (show (1 : ℤ) ≤ 2 by norm_num)
        linarith
      · exact le_refl _
    have h2 := h hmem
    rw [hcell, aux_ak_ae_5_1] at h2
    intro l
    have h4 := (h2 l).2
    have h5 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (show (1 : ℤ) ≤ 2 by norm_num)
    linarith
  funext l
  have h6 := h1 l
  have h7 := h3 l
  have h8 : (0 : ℤ) < 2 ^ j := by positivity
  nlinarith [h6, h7]

-- A cell of level `j' ≥ j` inside a cell of level `j` is that cell: cardinality
-- (`aux_aux_ak_ae_45_20_2`, `Finset.card_le_card`, `Nat.pow_le_pow_iff_right`) gives `j' ≤ j`,
-- hence `j' = j`, and then `aux_aux_ak_ae_45_20_4` gives `c' = c`.
private theorem aux_aux_ak_ae_45_20_5 {d : ℕ} (hd : 1 ≤ d) (u : Site d) {j j' : ℕ} {c c' : Site d}
    (hsub : dyCell u j' c' ⊆ dyCell u j c) (hle : j ≤ j') : (j', c') = (j, c) := by
  have hcard := Finset.card_le_card hsub
  rw [aux_aux_ak_ae_45_20_2 u j' c', aux_aux_ak_ae_45_20_2 u j c] at hcard
  have h1 : 2 ^ j' ≤ 2 ^ j := (Nat.pow_le_pow_iff_left (by omega : d ≠ 0)).mp hcard
  have h2 : j' ≤ j := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have h3 : j' = j := le_antisymm h2 hle
  subst h3
  have h4 : c' = c := aux_aux_ak_ae_45_20_4 u hsub
  rw [h4]

-- `aux_aux_ak_ae_45_20_1` (`Finset.Nonempty.ne_empty`); `(j, c)` is in the filter
-- (`Finset.mem_filter`, `subset_refl`).
private theorem aux_aux_ak_ae_45_20_6 {d : ℕ} (r : Finset (Site d) → ℝ) (u : Site d)
    (fam : Finset (ℕ × Site d))
    (hdisj : ∀ p ∈ fam, ∀ q ∈ fam, p ≠ q → Disjoint (dyCell u p.1 p.2) (dyCell u q.1 q.2))
    (j : ℕ) (c : Site d) (hmem : (j, c) ∈ fam) :
    ∑ p ∈ fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u j c), r (dyCell u p.1 p.2) =
      r (dyCell u j c) := by
  have h1 : fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u j c) = {(j, c)} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hmem, subset_refl _⟩, ?_⟩
    intro p hp
    obtain ⟨hpf, hpsub⟩ := Finset.mem_filter.mp hp
    by_contra hne
    have hdis := hdisj p hpf (j, c) hmem hne
    obtain ⟨y, hy⟩ := aux_aux_ak_ae_45_20_1 u p.1 p.2
    exact Finset.disjoint_left.1 hdis hy (hpsub hy)
  rw [h1, Finset.sum_singleton]

-- A point of a cell lies in one of its `2^d` children: `e i := if y i < u i + 2^(j+1) c i + 2^j
-- then 0 else 1`; membership coordinatewise (`dyCell`, `aux_ak_ae_5_1`, `Pi.add_apply`,
-- `Pi.smul_apply`, `smul_eq_mul`, `pow_succ`), `split_ifs`, `simp`, `linarith`.
private theorem aux_aux_ak_ae_45_20_7 {d : ℕ} (u : Site d) (j : ℕ) (c y : Site d)
    (hy : y ∈ dyCell u (j + 1) c) :
    ∃ e : Fin d → Fin 2, y ∈ dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)) := by
  have hy' : ∀ i, u i + 2 ^ (j + 1) * c i ≤ y i ∧
      y i ≤ u i + 2 ^ (j + 1) * c i + 2 ^ (j + 1) - 1 := by
    have h := hy
    rw [dyCell, aux_ak_ae_5_1] at h
    intro i
    have h1 := (h i).1
    have h2 := (h i).2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    refine ⟨h1, ?_⟩
    linarith
  refine ⟨fun i => if y i < u i + 2 ^ (j + 1) * c i + 2 ^ j then 0 else 1, ?_⟩
  rw [dyCell, aux_ak_ae_5_1]
  intro i
  have h1 := hy' i
  have h2 : (2 : ℤ) ^ (j + 1) = 2 ^ j * 2 := by rw [pow_succ]
  by_cases hc : y i < u i + 2 ^ (j + 1) * c i + 2 ^ j
  · simp only [hc, ↓reduceIte, Fin.val_zero, Nat.cast_zero, add_zero, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have h4 : 2 ^ j * (2 * c i) = 2 ^ (j + 1) * c i := by rw [h2]; ring
    constructor
    · rw [h4]; exact h1.1
    · rw [h4]; linarith [h1.2]
  · simp only [hc, ↓reduceIte, Fin.val_one, Nat.cast_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    push Not at hc
    have h4 : 2 ^ j * (2 * c i + 1) = 2 ^ (j + 1) * c i + 2 ^ j := by rw [h2]; ring
    constructor
    · rw [h4]; linarith [hc]
    · rw [h4]; linarith [h1.2]

private theorem aux_aux_ak_ae_45_20_8 {d : ℕ} (u : Site d) {j j' : ℕ} (c c' : Site d) (hle : j' ≤ j)
    (h : dyCell u j' c' ⊆ dyCell u (j + 1) c) :
    ∃ e : Fin d → Fin 2, dyCell u j' c' ⊆ dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)) := by
  obtain ⟨y, hy⟩ := aux_aux_ak_ae_45_20_1 u j' c'
  obtain ⟨e, he⟩ := aux_aux_ak_ae_45_20_7 u j c y (h hy)
  refine ⟨e, ?_⟩
  rcases aux_ak_ae_45_18 u hle c' ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)) with h1 | h1
  · exact h1
  · exact absurd he (Finset.disjoint_left.1 h1 hy)

-- Generic fibre bound: `Finset.sum_fiberwise_of_maps_to` (maps-to from `(hφ p hp).1`) rewrites
-- the left side as `∑ b ∈ I, ∑ p ∈ T with φ p = b, g p`; then `Finset.sum_le_sum` and
-- `Finset.sum_le_sum_of_subset_of_nonneg` (fibre `⊆ A b` by `(hφ p hp).2`, `Finset.mem_filter`; `hg`).
private theorem aux_aux_ak_ae_45_20_9 {α β : Type*} [DecidableEq β] (T : Finset α) (I : Finset β)
    (A : β → Finset α) (g : α → ℝ) (hg : ∀ p, 0 ≤ g p) (φ : α → β)
    (hφ : ∀ p ∈ T, φ p ∈ I ∧ p ∈ A (φ p)) :
    ∑ p ∈ T, g p ≤ ∑ b ∈ I, ∑ p ∈ A b, g p := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun p hp => (hφ p hp).1) g]
  refine Finset.sum_le_sum fun b hb => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    obtain ⟨hpT, hpb⟩ := Finset.mem_filter.mp hp
    subst hpb
    exact (hφ p hpT).2
  · intro p _ _
    exact hg p

private theorem aux_aux_ak_ae_45_20_10 {d : ℕ} (hd : 1 ≤ d) (u : Site d) (fam : Finset (ℕ × Site d))
    {j : ℕ} {c : Site d} (hmem : (j, c) ∉ fam) (p : ℕ × Site d) (hp : p ∈ fam)
    (hsub : dyCell u p.1 p.2 ⊆ dyCell u j c) : p.1 < j := by
  by_contra hlt
  push Not at hlt
  have h := aux_aux_ak_ae_45_20_5 hd u hsub hlt
  exact hmem (by rw [← h]; exact hp)

-- A pairwise disjoint family of cells inside one cell: induction on the level `j` of the big cell.
-- `j = 0` or the cell itself belongs to the family: then it is the only member inside
-- (cells are nonempty; disjointness).  Otherwise every member inside lies in exactly one child
-- (`aux_ak_ae_45_18`, sizes: a member of level `≥ j + 1` inside would equal the cell), so
-- `Finset.sum_fiberwise`, the IH for each child, `aux_ak_ae_45_19`; members of `r ≥ 0`.
private theorem aux_ak_ae_45_20 {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d)
    (fam : Finset (ℕ × Site d))
    (hdisj : ∀ p ∈ fam, ∀ q ∈ fam, p ≠ q → Disjoint (dyCell u p.1 p.2) (dyCell u q.1 q.2))
    (j : ℕ) (c : Site d) :
    ∑ p ∈ fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u j c), r (dyCell u p.1 p.2) ≤
      r (dyCell u j c) := by
  induction j generalizing c with
  | zero =>
    by_cases hmem : ((0 : ℕ), c) ∈ fam
    · exact le_of_eq (aux_aux_ak_ae_45_20_6 r u fam hdisj 0 c hmem)
    · rw [Finset.sum_eq_zero fun p hp => absurd (aux_aux_ak_ae_45_20_10 hd u fam hmem p
        (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2) (Nat.not_lt_zero _)]
      exact hrnn _ _
  | succ j ih =>
    by_cases hmem : (j + 1, c) ∈ fam
    · exact le_of_eq (aux_aux_ak_ae_45_20_6 r u fam hdisj (j + 1) c hmem)
    · have hch : ∀ p : ℕ × Site d, ∃ e : Fin d → Fin 2,
          p ∈ fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u (j + 1) c) →
            (e ∈ (Finset.univ : Finset (Fin d → Fin 2)) ∧
              p ∈ fam.filter (fun q => dyCell u q.1 q.2 ⊆
                dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)))) := by
        intro p
        by_cases hp : p ∈ fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u (j + 1) c)
        · obtain ⟨hpf, hps⟩ := Finset.mem_filter.1 hp
          obtain ⟨e, he⟩ := aux_aux_ak_ae_45_20_8 u c p.2
            (Nat.lt_succ_iff.1 (aux_aux_ak_ae_45_20_10 hd u fam hmem p hpf hps)) hps
          exact ⟨e, fun _ => ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨hpf, he⟩⟩⟩
        · exact ⟨0, fun h => absurd h hp⟩
      choose φ hφ using hch
      calc _ ≤ ∑ e : Fin d → Fin 2, ∑ p ∈ fam.filter (fun q => dyCell u q.1 q.2 ⊆
              dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ))), r (dyCell u p.1 p.2) :=
            aux_aux_ak_ae_45_20_9 (fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u (j + 1) c))
              (Finset.univ : Finset (Fin d → Fin 2))
              (fun e : Fin d → Fin 2 => fam.filter (fun q => dyCell u q.1 q.2 ⊆
                dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ))))
              (fun p => r (dyCell u p.1 p.2)) (fun p => hrnn _ _) φ hφ
        _ ≤ ∑ e : Fin d → Fin 2, r (dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ))) :=
            Finset.sum_le_sum fun e _ => ih _
        _ ≤ r (dyCell u (j + 1) c) := aux_ak_ae_45_19 r hrsup u j c

-- A translated box is a box: `latticeBox`, `show (Equiv.addRight z).toEmbedding = addRightEmbedding z
-- from rfl`, `Finset.map_add_right_Icc` (as in `aux_ak_ae_12`).
private theorem aux_aux_ak_ae_45_21_1 {d : ℕ} (a b z : Site d) :
    (latticeBox a b).map (Equiv.addRight z).toEmbedding = latticeBox (a + z) (b + z) := by
  simp only [latticeBox]
  have h : (Equiv.addRight z).toEmbedding = addRightEmbedding z := rfl
  rw [h, Finset.map_add_right_Icc]

-- Translation preserves two-box splits: unfold `IsBoxSplit`; the three boxes by
-- `aux_aux_ak_ae_45_21_1`; `Finset.disjoint_map`; `← Finset.map_union`.
private theorem aux_aux_ak_ae_45_21_2 {d : ℕ} {B B₁ B₂ : Finset (Site d)} (z : Site d)
    (h : IsBoxSplit B B₁ B₂) :
    IsBoxSplit (B.map (Equiv.addRight z).toEmbedding) (B₁.map (Equiv.addRight z).toEmbedding)
      (B₂.map (Equiv.addRight z).toEmbedding) := by
  obtain ⟨⟨a, b, rfl⟩, ⟨a₁, b₁, rfl⟩, ⟨a₂, b₂, rfl⟩, hdisj, hunion⟩ := h
  refine ⟨⟨a + z, b + z, aux_aux_ak_ae_45_21_1 a b z⟩,
    ⟨a₁ + z, b₁ + z, aux_aux_ak_ae_45_21_1 a₁ b₁ z⟩,
    ⟨a₂ + z, b₂ + z, aux_aux_ak_ae_45_21_1 a₂ b₂ z⟩, ?_, ?_⟩
  · rw [Finset.disjoint_map]
    exact hdisj
  · rw [← Finset.map_union, hunion, aux_aux_ak_ae_45_21_1 a b z]

private theorem aux_aux_ak_ae_45_21_3 {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (m : ℕ) (i : Fin d) (a : Site d) :
    ∀ (k : ℕ) (b : Site d), b i = a i + (k : ℤ) * m - 1 →
      ∑ j ∈ Finset.range k, r (latticeBox (Function.update a i (a i + (m : ℤ) * j))
          (Function.update b i (a i + (m : ℤ) * j + m - 1))) ≤ r (latticeBox a b) := by
  intro k
  induction k with
  | zero => intro b _; rw [Finset.sum_range_zero]; exact hrnn a b
  | succ k ih =>
    intro b hb
    have hs := aux_ak_ae_5 a b i (a i + (m : ℤ) * k) (le_add_of_nonneg_right (by positivity))
      (by rw [hb]; push_cast; nlinarith)
    have h1 := hrsup _ _ _ hs
    have h2 := ih (Function.update b i (a i + (m : ℤ) * k - 1)) (by rw [Function.update_self]; ring)
    simp only [Function.update_idem] at h2
    have e : a i + (m : ℤ) * k + m - 1 = b i := by rw [hb]; push_cast; ring
    rw [Finset.sum_range_succ, e, Function.update_eq_self]
    linarith

private theorem aux_aux_ak_ae_45_21_4 {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B)
    (m k : ℕ) (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ)
    (hw : w ∈ gridSet d s k) :
    ∑ j ∈ Finset.range k, r (gridBox m k (insert i s) (Function.update w i j)) ≤
      r (gridBox m k s w) := by
  have hwi : w i = 0 := aux_ak_ae_15 hw hi
  have h13 := aux_aux_ak_ae_45_21_3 r hrnn hrsup m i (fun l => (m : ℤ) * (w l : ℤ)) k
    (fun l => (m : ℤ) * (w l : ℤ) + (if l ∈ s then (m : ℤ) else (k : ℤ) * m) - 1)
    (by simp [hi])
  refine le_trans (le_of_eq ?_) h13
  apply Finset.sum_congr rfl
  intro j _
  rw [aux_ak_ae_boxid m k s i hi w hwi j]

private theorem aux_aux_ak_ae_45_21_5 {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (m k : ℕ) (s : Finset (Fin d)) :
    ∑ w ∈ gridSet d s k, r (gridBox m k s w) ≤ r (latticeCube d (k * m)) := by
  induction s using Finset.induction with
  | empty =>
    rw [aux_ak_ae_14, Finset.sum_singleton]
    exact le_of_eq (congrArg r (aux_ak_ae_18b m k))
  | insert i t hi ih =>
    rw [aux_ak_ae_16 t i hi k (fun w => r (gridBox m k (insert i t) w))]
    exact le_trans (Finset.sum_le_sum (fun w hw => aux_aux_ak_ae_45_21_4 r hrnn hrsup m k t i hi w hw)) ih

-- A grid cube of side `2^J` translated by `u - 2 · 2^J` is the level-`J` cell of index `w - 2`:
-- `aux_ak_ae_19a`-style: `gridBox`, `latticeBox`, `aux_aux_ak_ae_45_21_1`, `dyCell`, `congr 1`,
-- `funext i`, `natToSite`, `Pi.add_apply`, `Pi.sub_apply`, `Pi.smul_apply`, `smul_eq_mul`,
-- `Finset.mem_univ`, `if_true`, `push_cast`, `ring`.
private theorem aux_aux_ak_ae_45_21_6 {d : ℕ} (u : Site d) (J k : ℕ) (w : Fin d → ℕ) :
    (gridBox (2 ^ J) k Finset.univ w).map (Equiv.addRight (u - fun _ => 2 * (2 ^ J : ℤ))).toEmbedding =
      dyCell u J (natToSite w - fun _ => 2) := by
  rw [gridBox, aux_aux_ak_ae_45_21_1, dyCell]
  congr 1 <;> funext i <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, natToSite,
      Finset.mem_univ, if_true] <;>
    (push_cast; ring)

private theorem aux_aux_ak_ae_45_21_7 {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (J N : ℕ) :
    ∑ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4), r (dyCell u J (natToSite w - fun _ => 2)) ≤
      r (dyBig u J N) := by
  have h := aux_aux_ak_ae_45_21_5
    (fun B => r (B.map (Equiv.addRight (u - fun _ => 2 * (2 ^ J : ℤ))).toEmbedding))
    (fun a b => by
      show 0 ≤ r ((latticeBox a b).map (Equiv.addRight (u - fun _ => 2 * (2 ^ J : ℤ))).toEmbedding)
      rw [aux_aux_ak_ae_45_21_1]; exact hrnn _ _)
    (fun B B₁ B₂ hs => hrsup _ _ _ (aux_aux_ak_ae_45_21_2 _ hs)) (2 ^ J) (N / 2 ^ J + 4) Finset.univ
  simp only [aux_aux_ak_ae_45_21_6] at h
  exact h

-- One coordinate: `Int.ediv_nonneg`, `Int.ediv_lt_iff_lt_mul` (from `t < M L`),
-- `Int.mul_ediv_add_emod`, `Int.emod_nonneg`, `Int.emod_lt_of_pos`; `linarith`.
private theorem aux_aux_ak_ae_45_21_8 (t M L : ℤ) (hL : 0 < L) (h0 : 0 ≤ t) (h1 : t ≤ M * L - 1) :
    0 ≤ t / L ∧ t / L < M ∧ L * (t / L) ≤ t ∧ t ≤ L * (t / L) + L - 1 := by
  refine ⟨Int.ediv_nonneg h0 hL.le, ?_, ?_, ?_⟩
  · rw [Int.ediv_lt_iff_lt_mul hL]
    omega
  · have h := Int.mul_ediv_add_emod t L
    have h2 := Int.emod_nonneg t hL.ne'
    omega
  · have h := Int.mul_ediv_add_emod t L
    have h2 := Int.emod_lt_of_pos t hL
    omega

-- A site of `dyBig u J N` lies in a level-`J` cell of index `w - 2`, `w ∈ [0, N/2^J + 4)^d`:
-- `dyBig`, `aux_ak_ae_12`, `aux_ak_ae_5_1` give `0 ≤ y i - z i ≤ M 2^J - 1` for
-- `z = u - 2 · 2^J`, `M = N/2^J + 4` (`push_cast`); `w i := ((y i - z i) / 2^J).toNat`;
-- `aux_aux_ak_ae_45_21_8`, `Int.toNat_of_nonneg`, `Int.toNat_lt`; membership `gridSet`,
-- `Fintype.mem_piFinset`, `Finset.mem_range`; the cell by `dyCell`, `aux_ak_ae_5_1`, `natToSite`,
-- `Pi.add_apply`, `Pi.sub_apply`, `Pi.smul_apply`, `smul_eq_mul`; `linarith`.
private theorem aux_aux_ak_ae_45_21_9 {d : ℕ} (u : Site d) (J N : ℕ) (y : Site d)
    (hy : y ∈ dyBig u J N) :
    ∃ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4), y ∈ dyCell u J (natToSite w - fun _ => 2) := by
  have hz : dyBig u J N = latticeBox (u - fun _ => 2 * (2 ^ J : ℤ))
      (fun i => (u i - 2 * (2 ^ J : ℤ)) + (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℤ) - 1) := by
    rw [dyBig, aux_ak_ae_12]
    congr 1
  rw [hz, aux_ak_ae_5_1] at hy
  have hL : (0 : ℤ) < 2 ^ J := by positivity
  have hM : (0 : ℤ) ≤ ((N / 2 ^ J + 4 : ℕ) : ℤ) := by positivity
  have hbound : ∀ i, 0 ≤ y i - (u i - 2 * (2 ^ J : ℤ)) ∧
      y i - (u i - 2 * (2 ^ J : ℤ)) ≤ ((N / 2 ^ J + 4 : ℕ) : ℤ) * 2 ^ J - 1 := by
    intro i
    have h1 := (hy i).1
    have h2 := (hy i).2
    simp only [Pi.sub_apply] at h1 h2
    have h3 : ((N / 2 ^ J + 4 : ℕ) : ℤ) * 2 ^ J
        = (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℤ) := by push_cast; ring
    constructor <;> linarith [h1, h2, h3]
  refine ⟨fun i => ((y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J).toNat, ?_, ?_⟩
  · rw [gridSet, Fintype.mem_piFinset]
    intro i
    simp only [Finset.mem_univ, if_true]
    have h1 := (hbound i).1
    have h2 := (hbound i).2
    have h3 := aux_aux_ak_ae_45_21_8 (y i - (u i - 2 * (2 ^ J : ℤ)))
      ((N / 2 ^ J + 4 : ℕ) : ℤ) (2 ^ J) hL h1 h2
    rw [Finset.mem_range]
    have h4 : ((y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J).toNat < N / 2 ^ J + 4 := by
      have h5 : (0 : ℤ) ≤ (y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J := h3.1
      have h6 : ((y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J).toNat
          < ((N / 2 ^ J + 4 : ℕ) : ℤ).toNat := by
        have h7 : (0 : ℤ) < ((N / 2 ^ J + 4 : ℕ) : ℤ) := by positivity
        rw [Int.toNat_lt_toNat h7]
        exact h3.2.1
      have h8 : ((N / 2 ^ J + 4 : ℕ) : ℤ).toNat = N / 2 ^ J + 4 := Int.toNat_natCast _
      omega
    exact h4
  · rw [dyCell, aux_ak_ae_5_1]
    intro i
    have h1 := (hbound i).1
    have h3 := aux_aux_ak_ae_45_21_8 (y i - (u i - 2 * (2 ^ J : ℤ)))
      ((N / 2 ^ J + 4 : ℕ) : ℤ) (2 ^ J) hL h1 (hbound i).2
    have h4 : (((y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J).toNat : ℤ)
        = (y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J := Int.toNat_of_nonneg h3.1
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, natToSite]
    rw [h4]
    constructor <;> linarith [h3.2.2.1, h3.2.2.2]

private theorem aux_aux_ak_ae_45_21_10 {d : ℕ} (u : Site d) {J N : ℕ} (p : ℕ × Site d) (hJ : p.1 ≤ J)
    (hin : dyCell u p.1 p.2 ⊆ dyBig u J N) :
    ∃ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4),
      dyCell u p.1 p.2 ⊆ dyCell u J (natToSite w - fun _ => 2) := by
  obtain ⟨y, hy⟩ := aux_aux_ak_ae_45_20_1 u p.1 p.2
  obtain ⟨w, hw, hyw⟩ := aux_aux_ak_ae_45_21_9 u J N y (hin hy)
  refine ⟨w, hw, ?_⟩
  rcases aux_ak_ae_45_18 u hJ p.2 (natToSite w - fun _ => 2) with h | h
  · exact h
  · exact absurd hyw (Finset.disjoint_left.1 h hy)

-- `dyBig u J N` is the grid of level-`J` cells with indices in `[-2, N/2^J + 1]^d`: guillotine
-- grid bound (superadditive analogue of `aux_ak_ae_18`), every member lies in exactly one top cell
-- (`aux_ak_ae_45_18` at level `J`, `hin`), `Finset.sum_fiberwise`, then `aux_ak_ae_45_20` per top
-- cell.  SPLIT? (grid identity for `dyBig`; the fibre decomposition).
private theorem aux_ak_ae_45_21 {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (J N : ℕ)
    (fam : Finset (ℕ × Site d)) (hJ : ∀ p ∈ fam, p.1 ≤ J)
    (hin : ∀ p ∈ fam, dyCell u p.1 p.2 ⊆ dyBig u J N)
    (hdisj : ∀ p ∈ fam, ∀ q ∈ fam, p ≠ q → Disjoint (dyCell u p.1 p.2) (dyCell u q.1 q.2)) :
    ∑ p ∈ fam, r (dyCell u p.1 p.2) ≤ r (dyBig u J N) := by
  have hch : ∀ p : ℕ × Site d, ∃ w : Fin d → ℕ, p ∈ fam →
      (w ∈ gridSet d Finset.univ (N / 2 ^ J + 4) ∧
        p ∈ fam.filter (fun q => dyCell u q.1 q.2 ⊆ dyCell u J (natToSite w - fun _ => 2))) := by
    intro p
    by_cases hp : p ∈ fam
    · obtain ⟨w, hw, hsub⟩ := aux_aux_ak_ae_45_21_10 u p (hJ p hp) (hin p hp)
      exact ⟨w, fun _ => ⟨hw, Finset.mem_filter.2 ⟨hp, hsub⟩⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose φ hφ using hch
  calc ∑ p ∈ fam, r (dyCell u p.1 p.2)
      ≤ ∑ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4), ∑ p ∈ fam.filter (fun q =>
          dyCell u q.1 q.2 ⊆ dyCell u J (natToSite w - fun _ => 2)), r (dyCell u p.1 p.2) :=
        aux_aux_ak_ae_45_20_9 fam _
          (fun w => fam.filter (fun q => dyCell u q.1 q.2 ⊆ dyCell u J (natToSite w - fun _ => 2)))
          (fun p => r (dyCell u p.1 p.2)) (fun p => hrnn _ _) φ hφ
    _ ≤ ∑ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4), r (dyCell u J (natToSite w - fun _ => 2)) :=
        Finset.sum_le_sum fun w _ => aux_ak_ae_45_20 hd r hrnn hrsup u fam hdisj J _
    _ ≤ r (dyBig u J N) := aux_aux_ak_ae_45_21_7 r hrnn hrsup u J N

-- Every member lies in a maximal one.  For `p ∈ hvy` take `q` maximising `q.1` over
-- `hvy.filter (fun q => dyCell p ⊆ dyCell q)` (nonempty: `p`; `Finset.exists_max_image`); if
-- `dyCell q ⊆ dyCell q'` with `q' ∈ hvy` then `q'` is in that filter, so `q'.1 ≤ q.1`; hence
-- `(q.1, q.2) = (q'.1, q'.2)` by `aux_aux_ak_ae_45_20_5`, i.e. `q' = q` (`Prod.ext`).
private theorem aux_aux_ak_ae_45_22_1 {d : ℕ} (hd : 1 ≤ d) (u : Site d) (hvy : Finset (ℕ × Site d))
    (p : ℕ × Site d) (hp : p ∈ hvy) :
    ∃ q ∈ hvy, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 ∧
      ∀ q' ∈ hvy, dyCell u q.1 q.2 ⊆ dyCell u q'.1 q'.2 → q' = q := by
  classical
  let S : Finset (ℕ × Site d) := hvy.filter (fun q => dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2)
  have hne : S.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp, subset_refl _⟩⟩
  obtain ⟨q, hq, hqmax⟩ := Finset.exists_max_image S (fun q : ℕ × Site d => q.1) hne
  refine ⟨q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2, ?_⟩
  intro q' hq' hsub
  have hmem : q' ∈ S := Finset.mem_filter.mpr ⟨hq', (Finset.mem_filter.mp hq).2.trans hsub⟩
  have hle : q'.1 ≤ q.1 := hqmax q' hmem
  have hle' : q.1 ≤ q'.1 := by
    by_contra hlt
    push Not at hlt
    have h := aux_aux_ak_ae_45_20_3 hd u hsub
    omega
  have hjeq : q'.1 = q.1 := le_antisymm hle hle'
  have hsub'' : dyCell u q.1 q.2 ⊆ dyCell u q.1 q'.2 := by
    rw [hjeq] at hsub
    exact hsub
  have h2 : q.2 = q'.2 := aux_aux_ak_ae_45_20_4 u hsub''
  exact Prod.ext hjeq h2.symm

-- Maximal members are pairwise disjoint: `le_total p.1 q.1`, `aux_ak_ae_45_18` (nested or
-- disjoint); nested `dyCell p ⊆ dyCell q` gives `q = p` by maximality of `p` (`(hmax p hp).2 q
-- (hmax q hq).1`), contradicting `p ≠ q`; the other order symmetrically, `Disjoint.symm`.
private theorem aux_aux_ak_ae_45_22_2 {d : ℕ} (u : Site d) (hvy maxl : Finset (ℕ × Site d))
    (hmax : ∀ p ∈ maxl, p ∈ hvy ∧ ∀ q ∈ hvy, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 → q = p) :
    ∀ p ∈ maxl, ∀ q ∈ maxl, p ≠ q → Disjoint (dyCell u p.1 p.2) (dyCell u q.1 q.2) := by
  intro p hp q hq hne
  rcases le_total p.1 q.1 with hle | hle
  · rcases aux_ak_ae_45_18 u hle p.2 q.2 with hsub | hdisj
    · exfalso
      have h1 : q = p := (hmax p hp).2 q (hmax q hq).1 hsub
      exact hne h1.symm
    · exact hdisj
  · rcases aux_ak_ae_45_18 u hle q.2 p.2 with hsub | hdisj
    · exfalso
      have h1 : p = q := (hmax q hq).2 p (hmax p hp).1 hsub
      exact hne h1
    · exact hdisj.symm

-- The union is covered by the maximal cells: `Finset.biUnion_subset` + `hcov` +
-- `Finset.subset_biUnion_of_mem` give `⋃ hvy ⊆ ⋃ maxl` (`Finset.card_le_card`), then
-- `Finset.card_biUnion_le`; cast by `Nat.cast_le`, `Nat.cast_sum`.
private theorem aux_aux_ak_ae_45_22_3 {d : ℕ} (u : Site d) (hvy maxl : Finset (ℕ × Site d))
    (hcov : ∀ p ∈ hvy, ∃ q ∈ maxl, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2) :
    ((hvy.biUnion fun p => dyCell u p.1 p.2).card : ℝ) ≤
      ∑ q ∈ maxl, ((dyCell u q.1 q.2).card : ℝ) := by
  have hsub : hvy.biUnion (fun p => dyCell u p.1 p.2) ⊆
      maxl.biUnion (fun q => dyCell u q.1 q.2) := by
    intro y hy
    rw [Finset.mem_biUnion] at hy ⊢
    obtain ⟨p, hp, hyp⟩ := hy
    obtain ⟨q, hq, hpq⟩ := hcov p hp
    exact ⟨q, hq, hpq hyp⟩
  have h1 : (hvy.biUnion fun p => dyCell u p.1 p.2).card ≤
      (maxl.biUnion fun q => dyCell u q.1 q.2).card := Finset.card_le_card hsub
  have h2 : ((maxl.biUnion fun q => dyCell u q.1 q.2).card : ℝ) ≤
      ∑ q ∈ maxl, ((dyCell u q.1 q.2).card : ℝ) := by
    have h3 : (maxl.biUnion fun q => dyCell u q.1 q.2).card ≤
        ∑ q ∈ maxl, (dyCell u q.1 q.2).card := Finset.card_biUnion_le
    exact_mod_cast h3
  exact le_trans (by exact_mod_cast h1) h2

-- Heavy cells: pass to the maximal members `maxl` of `hvy` for inclusion of cells (distinct pairs give
-- distinct cells: side `2^j` and corner determine `(j, c)`); they are pairwise disjoint
-- (`aux_ak_ae_45_18`), have the same union, and `card (⋃) ≤ ∑ card` (`Finset.card_biUnion_le`);
-- then `hheavy`, `Finset.mul_sum`, `aux_ak_ae_45_21`.  SPLIT? (the maximal-subfamily facts).
private theorem aux_ak_ae_45_22 {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (J N : ℕ)
    {β : ℝ} (hβ : 0 ≤ β) (hvy : Finset (ℕ × Site d)) (hJ : ∀ p ∈ hvy, p.1 ≤ J)
    (hin : ∀ p ∈ hvy, dyCell u p.1 p.2 ⊆ dyBig u J N)
    (hheavy : ∀ p ∈ hvy, β * ((dyCell u p.1 p.2).card : ℝ) ≤ r (dyCell u p.1 p.2)) :
    β * ((hvy.biUnion fun p => dyCell u p.1 p.2).card : ℝ) ≤ r (dyBig u J N) := by
  classical
  obtain ⟨maxl, hmaxl⟩ : ∃ maxl : Finset (ℕ × Site d), maxl =
      hvy.filter (fun p => ∀ q ∈ hvy, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 → q = p) := ⟨_, rfl⟩
  have hmax : ∀ p ∈ maxl, p ∈ hvy ∧ ∀ q ∈ hvy, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 → q = p :=
    fun p hp => Finset.mem_filter.1 (hmaxl ▸ hp)
  have hsub : ∀ q ∈ maxl, q ∈ hvy := fun q hq => (hmax q hq).1
  have hcov : ∀ p ∈ hvy, ∃ q ∈ maxl, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 := by
    intro p hp
    obtain ⟨q, hq, hpq, hqmax⟩ := aux_aux_ak_ae_45_22_1 hd u hvy p hp
    exact ⟨q, hmaxl ▸ Finset.mem_filter.2 ⟨hq, hqmax⟩, hpq⟩
  calc β * ((hvy.biUnion fun p => dyCell u p.1 p.2).card : ℝ)
      ≤ β * ∑ q ∈ maxl, ((dyCell u q.1 q.2).card : ℝ) :=
        mul_le_mul_of_nonneg_left (aux_aux_ak_ae_45_22_3 u hvy maxl hcov) hβ
    _ = ∑ q ∈ maxl, β * ((dyCell u q.1 q.2).card : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ maxl, r (dyCell u q.1 q.2) := Finset.sum_le_sum fun q hq => hheavy q (hsub q hq)
    _ ≤ r (dyBig u J N) := aux_ak_ae_45_21 hd r hrnn hrsup u J N maxl
        (fun q hq => hJ q (hsub q hq)) (fun q hq => hin q (hsub q hq))
        (aux_aux_ak_ae_45_22_2 u hvy maxl hmax)

-- The right dyadic scale: `j := Nat.clog 2 n`; `Nat.le_pow_clog`, and for `n ≥ 2`
-- `Nat.pow_pred_clog_lt_self` gives `2^(j-1) < n`, so `2^j < 2 n`; `n = 1`: `j = 0`.
private theorem aux_ak_ae_45_23 (n : ℕ) (hn : 1 ≤ n) : ∃ j, n ≤ 2 ^ j ∧ 2 ^ j < 2 * n := by
  refine ⟨Nat.clog 2 n, @Nat.le_pow_clog 2 (by norm_num) n, ?_⟩
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    have hc : Nat.clog 2 1 = 0 := Nat.clog_of_right_le_one le_rfl 2
    rw [hc]
    norm_num
  · have hpred : 2 ^ (Nat.clog 2 n).pred < n := @Nat.pow_pred_clog_lt_self 2 (by norm_num) n h
    have hpos : 0 < Nat.clog 2 n := @Nat.clog_pos 2 n (by norm_num) h
    have hkey : 2 ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n).pred * 2 := (Nat.pow_pred_mul hpos).symm
    rw [hkey]
    have hm := Nat.mul_lt_mul_of_pos_right hpred (by norm_num : (0:ℕ) < 2)
    rw [Nat.mul_comm n 2] at hm
    exact hm


-- One coordinate, existence of the cell index: `c := (x - u) / L`; `Int.mul_ediv_add_emod`
-- (`L * ((x - u) / L) + (x - u) % L = x - u`), `Int.emod_nonneg` (`L ≠ 0`); `linarith`.
private theorem aux_aux_ak_ae_45_24_1 (x u L k : ℤ) (hL : 0 < L) (h : (x - u) % L ≤ L - k) :
    ∃ c : ℤ, u + L * c ≤ x ∧ x + (k - 1) ≤ u + L * c + (L - 1) := by
  refine ⟨(x - u) / L, ?_, ?_⟩
  · have h1 := Int.mul_ediv_add_emod (x - u) L
    have h2 := Int.emod_nonneg (x - u) hL.ne'
    linarith
  · have h1 := Int.mul_ediv_add_emod (x - u) L
    linarith

-- Coordinatewise containment gives box containment: `aux_ak_ae_12` (the cube is
-- `latticeBox x (x + k - 1)`), `dyCell`, `latticeBox`, `Finset.Icc_subset_Icc`, `Pi.le_def`,
-- `Pi.add_apply`, `Pi.smul_apply`, `smul_eq_mul`; `h i`.
private theorem aux_aux_ak_ae_45_24_2 {d : ℕ} (x u c : Site d) (j k : ℕ)
    (h : ∀ i, u i + 2 ^ j * c i ≤ x i ∧ x i + (k : ℤ) - 1 ≤ u i + 2 ^ j * c i + (2 ^ j - 1)) :
    (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c := by
  intro y hy
  rw [aux_ak_ae_12, aux_ak_ae_5_1] at hy
  rw [dyCell, aux_ak_ae_5_1]
  intro i
  have h1 := hy i
  have h2 := h i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  constructor <;> linarith

private theorem aux_aux_ak_ae_45_24_3 {d : ℕ} (x u : Site d) {j k : ℕ}
    (h : ∀ i, (x i - u i) % 2 ^ j ≤ 2 ^ j - (k : ℤ)) :
    ∃ c, (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c := by
  choose c hc using fun i => aux_aux_ak_ae_45_24_1 (x i) (u i) (2 ^ j) k (by positivity) (h i)
  exact ⟨c, aux_aux_ak_ae_45_24_2 x u c j k fun i => ⟨(hc i).1, by linarith [(hc i).2]⟩⟩

-- The coordinatewise condition cuts out a product set: `Finset.ext`, `Finset.mem_filter`,
-- `Fintype.mem_piFinset`, `latticeCube`, `Finset.mem_Icc`, `Pi.le_def`, `Pi.zero_apply`,
-- `forall_and`; `aesop`/`tauto`.
private theorem aux_aux_ak_ae_45_24_4 {d : ℕ} (x : Site d) (j k n : ℕ) :
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

-- `y - (v + L q) = (y - v) + L * (-q)` (`ring`), `Int.add_mul_emod_self_left`.
private theorem aux_aux_ak_ae_45_24_5 (y v L q : ℤ) : (y - (v + L * q)) % L = (y - v) % L := by
  have h : y - (v + L * q) = (y - v) + L * (-q) := by ring
  rw [h, Int.add_mul_emod_self_left]

-- Shift by `L q`: `Finset.card_nbij'` with `fun v => v - L * q` and `fun v => v + L * q`;
-- membership `Finset.mem_filter`, `Finset.mem_Ico` and `aux_aux_ak_ae_45_24_5` (after
-- `v = (v - L q) + L q`, `sub_add_cancel`); `linarith`; inverses `sub_add_cancel`, `add_sub_cancel_right`.
private theorem aux_aux_ak_ae_45_24_6 (y L t q : ℤ) (_unused_hL : 0 < L) :
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

-- Induction on `m`: `Finset.Ico_union_Ico_eq_Ico` at `L m`, `Finset.filter_union`,
-- `Finset.card_union_of_disjoint` (`Finset.disjoint_filter_filter`,
-- `Finset.Ico_disjoint_Ico_consecutive`), `aux_aux_ak_ae_45_24_6` at `q = m`; `push_cast`, `ring`.
private theorem aux_aux_ak_ae_45_24_7 (y L t : ℤ) (hL : 0 < L) (m : ℕ) :
    ((Finset.Ico 0 (L * m)).filter (fun v => (y - v) % L ≤ t)).card =
      m * ((Finset.Ico 0 L).filter (fun v => (y - v) % L ≤ t)).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hLm : (0:ℤ) ≤ L * ↑m := by positivity
    have hsplit : Finset.Ico 0 (L * ↑(m+1)) = Finset.Ico 0 (L * ↑m) ∪ Finset.Ico (L * ↑m) (L * ↑m + L) := by
      have h : L * ↑(m+1) = L * ↑m + L := by push_cast; ring
      rw [h]
      exact (Finset.Ico_union_Ico_eq_Ico hLm (by linarith)).symm
    have hdisj' : Disjoint ((Finset.Ico 0 (L * ↑m)).filter (fun v => (y - v) % L ≤ t))
                           ((Finset.Ico (L * ↑m) (L * ↑m + L)).filter (fun v => (y - v) % L ≤ t)) := by
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

-- `v ↦ (y - v) % L` is an involution of `[0, L)`: `Int.emod_def` gives
-- `y - (y - v) % L = v + L * ((y - v) / L)`; `Int.add_mul_emod_self_left`, `Int.emod_eq_of_lt`.
private theorem aux_aux_ak_ae_45_24_8 (y v L : ℤ) (_unused_hL : 0 < L) (hv0 : 0 ≤ v) (hvL : v < L) :
    (y - (y - v) % L) % L = v := by
  have h : y - (y - v) % L = (y - v) - (y - v) % L + v := by ring
  rw [h]
  have h1 : ((y - v) - (y - v) % L) % L = 0 := by
    rw [Int.sub_emod, Int.emod_emod]
    simp
  rw [Int.add_emod, h1]
  simp [Int.emod_eq_of_lt (a := v) (b := L) hv0 hvL]

-- `Finset.card_nbij'` with `fun v => (y - v) % L` both ways; membership `Finset.mem_filter`,
-- `Finset.mem_Ico`, `Int.emod_nonneg`, `Int.emod_lt_of_pos`; inverses and the condition by
-- `aux_aux_ak_ae_45_24_8`.
private theorem aux_aux_ak_ae_45_24_9 (y L t : ℤ) (hL : 0 < L) :
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

-- The filter is `Finset.Icc 0 t` (`Finset.ext`, `Finset.mem_filter`, `Finset.mem_Ico`,
-- `Finset.mem_Icc`, `omega`), then `Int.card_Icc`, `sub_zero`.
private theorem aux_aux_ak_ae_45_24_10 (L t : ℤ) (_unused_h0 : 0 ≤ t) (ht : t < L) :
    ((Finset.Ico 0 L).filter (fun r => r ≤ t)).card = (t + 1).toNat := by
  have h : (Finset.Ico 0 L).filter (fun r => r ≤ t) = Finset.Ico 0 (t + 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [h, Int.card_Ico]
  simp

-- `Finset.ext`, `Finset.mem_Icc`, `Finset.mem_Ico`, `omega`.
private theorem aux_aux_ak_ae_45_24_11 (n : ℤ) : Finset.Icc (0 : ℤ) (n - 1) = Finset.Ico 0 n := by
  ext v
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

private theorem aux_aux_ak_ae_45_24_12 (y : ℤ) {k j J : ℕ} (hk : 1 ≤ k) (hkj : k ≤ 2 ^ j) (hjJ : j ≤ J) :
    ((Finset.Icc (0 : ℤ) (((2 ^ J : ℕ) : ℤ) - 1)).filter
      (fun v => (y - v) % 2 ^ j ≤ 2 ^ j - (k : ℤ))).card = 2 ^ (J - j) * (2 ^ j - k + 1) := by
  have hL : (0 : ℤ) < 2 ^ j := by positivity
  have hkj' : (k : ℤ) ≤ 2 ^ j := by exact_mod_cast hkj
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hJ : ((2 ^ J : ℕ) : ℤ) = 2 ^ j * ((2 ^ (J - j) : ℕ) : ℤ) := by
    push_cast; rw [← pow_add, Nat.add_sub_cancel' hjJ]
  rw [aux_aux_ak_ae_45_24_11, hJ, aux_aux_ak_ae_45_24_7 y _ _ hL, aux_aux_ak_ae_45_24_9 y _ _ hL,
    aux_aux_ak_ae_45_24_10 _ _ (by linarith) (by linarith)]
  congr 1
  have e : (2 : ℤ) ^ j - k + 1 = ((2 ^ j - k + 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub hkj]; ring
  rw [e, Int.toNat_natCast]

-- Bernoulli: `one_add_mul_le_pow` (`-2 ≤ a` from `ha`); `linarith`.
private theorem aux_aux_ak_ae_45_24_13 (d : ℕ) {a : ℝ} (ha : -1 ≤ a) (h : -1 / 2 ≤ (d : ℝ) * a) :
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

-- With `a := B / A - 1` (`1 + a = B / A`): `-1 ≤ a` (`div_nonneg`), `-1/2 ≤ d a` (from `h`,
-- `div_le_iff₀`, `sub_div`, `div_self`); `aux_aux_ak_ae_45_24_13`, `div_pow`, `le_div_iff₀`; `linarith`.
private theorem aux_aux_ak_ae_45_24_14 (d : ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
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
    have h13 := aux_aux_ak_ae_45_24_13 d ha hda
    have hBA : (1 : ℝ) + (B / A - 1) = B / A := by ring
    rw [hBA] at h13
    rw [div_pow] at h13
    rw [le_div_iff₀ (pow_pos hA d)] at h13
    linarith

-- `d = 0`: both sides `1 ≤ 2` (`pow_zero`).  `d ≥ 1`: `k ≤ 2^j` (from `hkj`, `nlinarith`),
-- `2^J = 2^(J-j) 2^j` (`← pow_add`, `Nat.sub_add_cancel`); `aux_aux_ak_ae_45_24_14` with
-- `A = 2^J`, `B = 2^(J-j) (2^j - k + 1)`: `A - B = 2^(J-j) (k - 1)` and `2 d (k - 1) ≤ 2^j`
-- (`push_cast [Nat.cast_sub]`, `nlinarith`).
private theorem aux_aux_ak_ae_45_24_15 {d k j J : ℕ} (hk : 1 ≤ k) (hjJ : j ≤ J) (hkj : 2 * d * k ≤ 2 ^ j) :
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
    have := aux_aux_ak_ae_45_24_14 d hA hBnn hmain
    linarith [this]

-- Random offsets: per coordinate `x_i + [0, k)` lies in one cell of side `2^j` iff
-- `(x_i - u_i) mod 2^j ≤ 2^j - k`, true for `2^{J-j} (2^j - k + 1)` of the `2^J` values of `u_i`;
-- the good set is a product (`Fintype.card_piFinset`-type count), so it has at least
-- `2^{Jd} (1 - k/2^j)^d ≥ 2^{Jd} (1 - d k/2^j) ≥ 2^{Jd}/2` elements (`one_add_mul_le_pow`).
-- SPLIT? (one-coordinate count; product; Bernoulli).
open Classical in
private theorem aux_ak_ae_45_24 {d : ℕ} (x : Site d) {k j J : ℕ} (hk : 1 ≤ k) (hjJ : j ≤ J)
    (hkj : 2 * d * k ≤ 2 ^ j) :
    ((2 ^ J : ℕ) : ℝ) ^ d ≤
      2 * (((latticeCube d (2 ^ J)).filter fun u =>
        ∃ c, (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c).card : ℝ) := by
  have hsubset : (latticeCube d (2 ^ J)).filter
        (fun u => ∀ i, (x i - u i) % 2 ^ j ≤ 2 ^ j - (k : ℤ)) ⊆
      (latticeCube d (2 ^ J)).filter (fun u => ∃ c, (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
    exact Finset.mem_filter.2 ⟨hu1, aux_aux_ak_ae_45_24_3 x u hu2⟩
  have hmono := Finset.card_le_card hsubset
  rw [aux_aux_ak_ae_45_24_4 x j k (2 ^ J), Fintype.card_piFinset] at hmono
  have hcount : ∀ i : Fin d, ((Finset.Icc (0 : ℤ) (((2 ^ J : ℕ) : ℤ) - 1)).filter
      (fun v => (x i - v) % 2 ^ j ≤ 2 ^ j - (k : ℤ))).card = 2 ^ (J - j) * (2 ^ j - k + 1) :=
    fun i => aux_aux_ak_ae_45_24_12 (x i) hk (le_trans (by have := i.pos; nlinarith) hkj) hjJ
  simp only [hcount, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hmono
  have hX : (((2 ^ (J - j) * (2 ^ j - k + 1) : ℕ) : ℝ)) ^ d ≤
      (((latticeCube d (2 ^ J)).filter fun u => ∃ c, (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c).card : ℝ) := by
    exact_mod_cast hmono
  linarith [aux_aux_ak_ae_45_24_15 (d := d) hk hjJ hkj]

-- The bad cube sits inside the cell, so `hrmono` applies: the cube is
-- `latticeBox x (fun i => x i + k - 1)` (`aux_ak_ae_12`), nonempty as `k ≥ 1` (`Pi.le_def`),
-- so `Finset.Icc_subset_Icc_iff` on `hsub` (after `dyCell`, `latticeBox`) gives both corner bounds.
private theorem aux_aux_ak_ae_45_25_1 {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrmono : ∀ a b a' b', a ≤ a' → b' ≤ b → r (latticeBox a' b') ≤ r (latticeBox a b))
    (x : Site d) {k j : ℕ} (hk : 1 ≤ k) (u c : Site d)
    (hsub : (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c) :
    r ((latticeCube d k).map (Equiv.addRight x).toEmbedding) ≤ r (dyCell u j c) := by
  have hcube : (latticeCube d k).map (Equiv.addRight x).toEmbedding =
      latticeBox x (fun i => x i + (k : ℤ) - 1) := aux_ak_ae_12 d k x
  have hcell : dyCell u j c = latticeBox (fun l => u l + 2 ^ j * c l)
      (fun l => u l + 2 ^ j * c l + 2 ^ j - 1) := by
    rw [dyCell]
    congr 1 <;> funext l <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [hcube, hcell]
  refine hrmono _ _ _ _ ?_ ?_
  · rw [hcell] at hsub
    rw [hcube] at hsub
    have hmem : x ∈ latticeBox x (fun i => x i + (k : ℤ) - 1) := by
      rw [aux_ak_ae_5_1]
      intro i
      constructor <;> omega
    have h1 := hsub hmem
    rw [aux_ak_ae_5_1] at h1
    intro i
    exact (h1 i).1
  · rw [hcell] at hsub
    rw [hcube] at hsub
    have hmem : (fun i => x i + (k : ℤ) - 1) ∈ latticeBox x (fun i => x i + (k : ℤ) - 1) := by
      rw [aux_ak_ae_5_1]
      intro i
      constructor <;> omega
    have h1 := hsub hmem
    rw [aux_ak_ae_5_1] at h1
    intro i
    exact (h1 i).2

-- `P^d ≤ (D k)^d` (`pow_le_pow_left₀`), `α / D^d * (D k)^d = α k^d` (`mul_pow`, `field_simp`,
-- `D ≠ 0`); `mul_le_mul_of_nonneg_left` (`div_nonneg`, `pow_nonneg`), `hbad`, `hRR`; `linarith`.
private theorem aux_aux_ak_ae_45_25_2 (d : ℕ) {α D k P R R' : ℝ} (hα : 0 ≤ α) (hD : 0 < D) (hP0 : 0 ≤ P)
    (hP : P ≤ D * k) (hbad : α * k ^ d < R) (hRR : R ≤ R') : α / D ^ d * P ^ d ≤ R' := by
  have h1 : P ^ d ≤ (D * k) ^ d := pow_le_pow_left₀ hP0 hP d
  have h2 : α / D ^ d * (D * k) ^ d = α * k ^ d := by
    rw [mul_pow]
    field_simp
  have h3 : α / D ^ d * P ^ d ≤ α / D ^ d * (D * k) ^ d :=
    mul_le_mul_of_nonneg_left h1 (div_nonneg hα (pow_nonneg hD.le d))
  linarith [h3, h2.le, h2.ge, hbad, hRR]

-- A bad cube inside a cell of side `2^j < 4 d k` makes the cell heavy: `card (dyCell u j c) =
-- (2^j)^d` (`dyCell`, `Pi.card_Icc`, `Int.card_Icc`), `< (4 d k)^d` (`pow_lt_pow_left₀`); the cube is
-- `latticeBox x (x + k - 1)` (`aux_ak_ae_12`), nonempty, so `Finset.Icc_subset_Icc_iff` gives the
-- corner inequalities for `hrmono`; `div_mul_eq_mul_div`, `mul_pow`, `lt_of_lt_of_le`.
private theorem aux_ak_ae_45_25 {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrmono : ∀ a b a' b', a ≤ a' → b' ≤ b → r (latticeBox a' b') ≤ r (latticeBox a b))
    (x : Site d) {k j : ℕ} (hk : 1 ≤ k) (hj : 2 ^ j < 4 * d * k) (u c : Site d)
    (hsub : (latticeCube d k).map (Equiv.addRight x).toEmbedding ⊆ dyCell u j c)
    {α : ℝ} (hα : 0 < α)
    (hbad : α * (k : ℝ) ^ d < r ((latticeCube d k).map (Equiv.addRight x).toEmbedding)) :
    α / (4 * (d : ℝ)) ^ d * ((dyCell u j c).card : ℝ) ≤ r (dyCell u j c) := by
  rw [aux_aux_ak_ae_45_20_2 u j c]
  have hD : (0 : ℝ) < 4 * (d : ℝ) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hP : (2 : ℝ) ^ j ≤ 4 * (d : ℝ) * (k : ℝ) := by exact_mod_cast hj.le
  have h := aux_aux_ak_ae_45_25_2 d hα.le hD (by positivity) hP hbad
    (aux_aux_ak_ae_45_25_1 r hrmono x hk u c hsub)
  push_cast
  exact h

-- Per-offset covering: `hvy := S.image sel` covers `S` (`Finset.subset_biUnion_of_mem`-type
-- argument: `x ∈ dyCell (sel x)`), so `#S ≤ #⋃`; then `aux_ak_ae_45_22` (`Finset.card_le_card`,
-- `mul_le_mul_of_nonneg_left`).
private theorem aux_ak_ae_45_26 {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
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
  exact aux_ak_ae_45_22 hd r hrnn hrsup u J N hβ (S.image sel)
    (fun p hp => (Finset.mem_image.1 hp).elim fun x hx => hx.2 ▸ (hsel x hx.1).2.1)
    (fun p hp => (Finset.mem_image.1 hp).elim fun x hx => hx.2 ▸ (hsel x hx.1).2.2.1)
    (fun p hp => (Finset.mem_image.1 hp).elim fun x hx => hx.2 ▸ (hsel x hx.1).2.2.2)


-- A cell of level `j ≤ J` (offset `u ∈ [0, 2^J)^d`) containing a site of `Q_N` lies in
-- `dyBig u J N`: coordinatewise the cell lies in `[x_i - 2^j + 1, x_i + 2^j - 1]`
-- `⊆ [u_i - 2^{J+1}, u_i - 2^{J+1} + (N/2^J + 4) 2^J - 1]` (`dyCell`, `dyBig`, `aux_ak_ae_12`,
-- `aux_ak_ae_5_1`, `pow_le_pow_right₀`, `Nat.lt_div_mul_add`, `push_cast`, `omega`/`nlinarith`).
private theorem aux_ak_ae_45_27 {d : ℕ} {u x c : Site d} {j J N : ℕ} (hu : u ∈ latticeCube d (2 ^ J))
    (hjJ : j ≤ J) (hx : x ∈ latticeCube d N) (hxc : x ∈ dyCell u j c) :
    dyCell u j c ⊆ dyBig u J N := by
  have hc2 : ∀ n : ℕ, ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := fun n => (by
    rw [Nat.cast_pow]
    norm_num)
  have hL : (2 : ℤ) ^ j ≤ (2 : ℤ) ^ J :=
    pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hjJ
  have hu' : ∀ i, 0 ≤ u i ∧ u i ≤ (2 : ℤ) ^ J - 1 := (by
    intro i
    have h := (aux_ak_ae_5_1 (0 : Site d) (fun _ => ((2 ^ J : ℕ) : ℤ) - 1) u).1 hu i
    rw [hc2 J] at h
    simpa only [Pi.zero_apply] using h)
  have hx' : ∀ i, 0 ≤ x i ∧ x i ≤ (N : ℤ) - 1 := (by
    intro i
    simpa only [Pi.zero_apply] using
      (aux_ak_ae_5_1 (0 : Site d) (fun _ => (N : ℤ) - 1) x).1 hx i)
  have hxc' : ∀ i, u i + (2 : ℤ) ^ j • c i ≤ x i ∧
      x i ≤ u i + (2 : ℤ) ^ j • c i + ((2 : ℤ) ^ j - 1) := (by
    intro i
    simpa only [Pi.add_apply, Pi.smul_apply] using
      (aux_ak_ae_5_1 (u + (2 ^ j : ℤ) • c)
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
  rw [dyBig, aux_ak_ae_12]
  intro y hy
  have hy' : ∀ i, u i + (2 : ℤ) ^ j • c i ≤ y i ∧
      y i ≤ u i + (2 : ℤ) ^ j • c i + ((2 : ℤ) ^ j - 1) := (by
    intro i
    simpa only [Pi.add_apply, Pi.smul_apply] using
      (aux_ak_ae_5_1 (u + (2 ^ j : ℤ) • c)
        (u + (2 ^ j : ℤ) • c + fun _ => (2 ^ j : ℤ) - 1) y).1 hy i)
  rw [aux_ak_ae_5_1]
  intro i
  simp only [Pi.sub_apply]
  constructor
  · linarith [hy' i, hxc' i, hu' i, hx' i, hL]
  · linarith [hy' i, hxc' i, hx' i, hu' i, hL, h3k]


-- The dyadic scale of a witness `k ≤ K`: `aux_ak_ae_45_23` at `n = 2 d k` (`1 ≤ 2 d k`,
-- `Nat.mul_pos`/`nlinarith`); `2^j < 4 d k ≤ 2 · 2^J = 2^(J+1)` (`hK`, `hKJ`, `pow_succ`), so `j ≤ J`
-- by `Nat.pow_lt_pow_iff_right`, `Nat.lt_succ_iff`; `ring_nf`/`linarith` for `2 (2 d k) = 4 d k`.
private theorem aux_aux_ak_ae_45_28_1 {d : ℕ} (hd : 1 ≤ d) {k K J : ℕ} (hk : 1 ≤ k) (hK : k ≤ K)
    (hKJ : 2 * d * K ≤ 2 ^ J) : ∃ j, j ≤ J ∧ 2 * d * k ≤ 2 ^ j ∧ 2 ^ j < 4 * d * k := by
  have h1 : 1 ≤ 2 * d * k := by
    have h2 : 1 ≤ 2 * d := by omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp h2) (Nat.one_le_iff_ne_zero.mp hk))
  obtain ⟨j, hj⟩ := aux_ak_ae_45_23 (2 * d * k) h1
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

-- Choice of witnesses: for `x` in the filter take `k` from `Finset.mem_filter` and `j` from
-- `aux_aux_ak_ae_45_28_1`; package as `∀ x, ∃ p : ℕ × ℕ, x ∈ S → …` (default `(0, 0)` off `S`,
-- `by_cases`), then `choose g hg` and `kf := fun x => (g x).1`, `jf := fun x => (g x).2`.
open Classical in
private theorem aux_aux_ak_ae_45_28_2 {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ) {α : ℝ} {K J : ℕ}
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
      obtain ⟨j, hjJ, hjk, hjk2⟩ := aux_aux_ak_ae_45_28_1 hd hk1 hkK hKJ
      exact ⟨(k, j), fun _ => ⟨hk1, hjJ, hjk, hjk2, hkr⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hx⟩
  choose g hg using hchoice
  exact ⟨fun x => (g x).1, fun x => (g x).2, fun x hx => hg x hx⟩

-- `aux_ak_ae_12`, `aux_ak_ae_5_1`: coordinatewise `x i ≤ x i ≤ x i + k - 1` (`k ≥ 1`; `omega`).
private theorem aux_aux_ak_ae_45_28_3 {d : ℕ} (x : Site d) {k : ℕ} (hk : 1 ≤ k) :
    x ∈ (latticeCube d k).map (Equiv.addRight x).toEmbedding := by
  rw [aux_ak_ae_12, aux_ak_ae_5_1]
  intro i
  constructor <;> omega

open Classical in
private theorem aux_aux_ak_ae_45_28_4 {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B)
    (hrmono : ∀ a b a' b', a ≤ a' → b' ≤ b → r (latticeBox a' b') ≤ r (latticeBox a b))
    {α : ℝ} (hα : 0 < α) {J N : ℕ} (u : Site d) (hu : u ∈ latticeCube d (2 ^ J))
    (S : Finset (Site d)) (hS : S ⊆ latticeCube d N) (kf jf : Site d → ℕ)
    (hw : ∀ x ∈ S, 1 ≤ kf x ∧ jf x ≤ J ∧ 2 ^ jf x < 4 * d * kf x ∧
      α * (kf x : ℝ) ^ d < r ((latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding)) :
    α / (4 * (d : ℝ)) ^ d *
        ((S.filter fun x => ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c).card : ℝ) ≤
      r (dyBig u J N) := by
  refine aux_ak_ae_45_26 hd r hrnn hrsup u J N (div_nonneg hα.le (by positivity)) _
    (fun x => (jf x, if h : ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c
      then h.choose else 0)) ?_
  intro x hx
  obtain ⟨hxS, hex⟩ := Finset.mem_filter.1 hx
  obtain ⟨hk, hjJ, hj, hbad⟩ := hw x hxS
  simp only [dif_pos hex]
  have hc := hex.choose_spec
  have hxc := hc (aux_aux_ak_ae_45_28_3 x hk)
  exact ⟨hxc, hjJ, aux_ak_ae_45_27 hu hjJ (hS hxS) hxc,
    aux_ak_ae_45_25 hd r hrmono x hk hj u _ hc hα hbad⟩

-- Double counting: `Finset.card_filter` on both sides (`∑ … if … then 1 else 0`), `Finset.sum_comm`.
private theorem aux_aux_ak_ae_45_28_5 {α β : Type*} (S : Finset α) (U : Finset β) (P : β → α → Prop)
    [∀ u x, Decidable (P u x)] :
    ∑ u ∈ U, (S.filter fun x => P u x).card = ∑ x ∈ S, (U.filter fun u => P u x).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

-- `Finset.sum_le_sum` with `h`, `Finset.sum_const`, `nsmul_eq_mul`, `Finset.mul_sum`; `linarith`.
private theorem aux_aux_ak_ae_45_28_6 {α : Type*} (S : Finset α) (b : α → ℝ) {P : ℝ}
    (h : ∀ x ∈ S, P ≤ 2 * b x) : (S.card : ℝ) * P ≤ 2 * ∑ x ∈ S, b x := by
  have h1 : (S.card : ℝ) * P = ∑ _x ∈ S, P := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1, Finset.mul_sum]
  exact Finset.sum_le_sum h

-- `Finset.mul_sum`, `Finset.sum_le_sum` with `h`.
private theorem aux_aux_ak_ae_45_28_7 {β : Type*} (U : Finset β) (a R : β → ℝ) {γ : ℝ}
    (h : ∀ u ∈ U, γ * a u ≤ R u) : γ * ∑ u ∈ U, a u ≤ ∑ u ∈ U, R u := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum h

-- `h2` gives `A ≤ D R' / α` (`div_mul_eq_mul_div`, `div_le_iff₀`); with `h1`,
-- `s P ≤ 2 D R' / α`; `le_div_iff₀`-type rearrangement (`field_simp`, `nlinarith`).
private theorem aux_aux_ak_ae_45_28_8 {s P A R' α D : ℝ} (hα : 0 < α) (hD : 0 < D) (hP : 0 < P)
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

-- DEEP (combinatorial core, deterministic).  Double counting over offsets `u ∈ Q_{2^J}`: for each
-- `u` let `heavy_u` be the cells `(j(k), c)` (`j(k)` from `aux_ak_ae_45_23` at `n = 2 d k`, so
-- `j(k) ≤ J` by `hKJ`) that contain `x + Q_k` for some bad `x ∈ Q_N` with witness `k`; they are
-- heavy with `β = α/(4d)^d` (`aux_ak_ae_45_25`) and lie in `dyBig u J N`, so
-- `β · #{bad x covered at u} ≤ r (dyBig u J N)` (`aux_ak_ae_45_22`).  Each bad `x` is covered for
-- at least half of the offsets (`aux_ak_ae_45_24`): `Finset.sum_comm` on
-- `∑_u ∑_x 1[covered]`, `Finset.card_eq_sum_ones`, `Finset.sum_le_sum`; `akMaxConst`.
open Classical in
private theorem aux_ak_ae_45_28 {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B)
    (hrmono : ∀ a b a' b', a ≤ a' → b' ≤ b → r (latticeBox a' b') ≤ r (latticeBox a b))
    {α : ℝ} (hα : 0 < α) {K J : ℕ} (hKJ : 2 * d * K ≤ 2 ^ J) (N : ℕ) :
    (((latticeCube d N).filter fun x => ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < r ((latticeCube d k).map (Equiv.addRight x).toEmbedding)).card : ℝ) ≤
      akMaxConst d / α *
        ((∑ u ∈ latticeCube d (2 ^ J), r (dyBig u J N)) / ((2 ^ J : ℕ) : ℝ) ^ d) := by
  obtain ⟨kf, jf, hw⟩ := aux_aux_ak_ae_45_28_2 hd r (α := α) hKJ N
  set S := (latticeCube d N).filter (fun x => ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < r ((latticeCube d k).map (Equiv.addRight x).toEmbedding)) with hSdef
  have hSN : S ⊆ latticeCube d N := Finset.filter_subset _ _
  have hA : ∀ u ∈ latticeCube d (2 ^ J), α / (4 * (d : ℝ)) ^ d *
      ((S.filter fun x => ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c).card : ℝ) ≤
        r (dyBig u J N) :=
    fun u hu => aux_aux_ak_ae_45_28_4 hd r hrnn hrsup hrmono hα u hu S hSN kf jf
      (fun x hx => ⟨(hw x hx).1, (hw x hx).2.1, (hw x hx).2.2.2.1, (hw x hx).2.2.2.2⟩)
  have hB : ∀ x ∈ S, ((2 ^ J : ℕ) : ℝ) ^ d ≤ 2 * ((((latticeCube d (2 ^ J)).filter fun u =>
      ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c).card : ℕ) : ℝ) :=
    fun x hx => aux_ak_ae_45_24 x (hw x hx).1 (hw x hx).2.1 (hw x hx).2.2.1
  have hswap := aux_aux_ak_ae_45_28_5 S (latticeCube d (2 ^ J))
    (fun u x => ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c)
  have hswapR : ∑ u ∈ latticeCube d (2 ^ J),
      ((S.filter fun x => ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c).card : ℝ) =
      ∑ x ∈ S, ((((latticeCube d (2 ^ J)).filter fun u =>
        ∃ c, (latticeCube d (kf x)).map (Equiv.addRight x).toEmbedding ⊆ dyCell u (jf x) c).card : ℕ) : ℝ) := by
    exact_mod_cast hswap
  have h7 := aux_aux_ak_ae_45_28_7 (latticeCube d (2 ^ J)) _ _ hA
  rw [hswapR] at h7
  have h6 := aux_aux_ak_ae_45_28_6 S _ hB
  have hP : (0 : ℝ) < ((2 ^ J : ℕ) : ℝ) ^ d := by positivity
  have hD : (0 : ℝ) < (4 * (d : ℝ)) ^ d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact pow_pos (by linarith) d
  unfold akMaxConst
  exact aux_aux_ak_ae_45_28_8 hα hD hP h6 h7

-- `dyBig` is a translate of `Q_{N'}`, `N' = (N/2^J + 4) 2^J ≥ 1`: `hRstat`, then
-- `MeasurePreserving.integral_comp'`-type change of variables (`integral_map`,
-- `(hτ z).map_eq`, `(hRm _).aestronglyMeasurable`), and `hρ`.
private theorem aux_ak_ae_45_29 {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] (τ : Site d → Ω → Ω)
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


-- Pointwise count: `Finset.card_filter`, `Finset.sum_congr`, `Set.indicator_apply`,
-- `Set.mem_setOf_eq`, and `R (x + Q_k) ω = R Q_k (τ x ω)` (`hRstat`).
open Classical in
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_30 {d : ℕ} (τ : Site d → Ω → Ω) (R : Finset (Site d) → Ω → ℝ)
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


-- `E_K` is measurable: it is `⋃ k ∈ Finset.Icc 1 K, {ω | α k^d < R (Q_k) ω}` (`Set.ext`,
-- `Set.mem_iUnion₂`, `Finset.mem_Icc`); `Finset.measurableSet_biUnion` with
-- `measurableSet_lt measurable_const (hRm _)`.
private theorem aux_aux_ak_ae_45_31_1 {d : ℕ} (R : Finset (Site d) → Ω → ℝ) (hRm : ∀ B, Measurable (R B))
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

-- `dyBig u J N` is a box (`dyBig`, `aux_ak_ae_12`), so `0 ≤ R ≤ M · card` there (`hRnn`, `hRbd`):
-- `Integrable.of_bound` with `(hRm _).aestronglyMeasurable`, `Real.norm_eq_abs`, `abs_of_nonneg`.
private theorem aux_aux_ak_ae_45_31_2 {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R : Finset (Site d) → Ω → ℝ) (hRm : ∀ B, Measurable (R B))
    (hRnn : ∀ a b ω, 0 ≤ R (latticeBox a b) ω) {M : ℝ} (hRbd : ∀ B ω, R B ω ≤ M * B.card)
    (u : Site d) (J N : ℕ) : Integrable (R (dyBig u J N)) μ := by
  have hab : dyBig u J N = latticeBox (u - fun _ => 2 * (2 ^ J : ℤ))
      (fun i => (u i - 2 * (2 ^ J : ℤ)) + (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℤ) - 1) := by
    rw [dyBig, aux_ak_ae_12]
    congr 1
  refine Integrable.of_bound (hRm _).aestronglyMeasurable (M * (dyBig u J N).card) ?_
  filter_upwards with ω
  have h1 : 0 ≤ R (dyBig u J N) ω := by
    rw [hab]
    exact hRnn _ _ ω
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact hRbd _ ω

-- `integral_finsetSum` (terms integrable by `aux_aux_ak_ae_45_31_2`), `Finset.sum_le_sum` with
-- `aux_ak_ae_45_29`, `Finset.sum_const`, `aux_t0`, `nsmul_eq_mul`, `Nat.cast_pow`.
private theorem aux_aux_ak_ae_45_31_3 {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (R : Finset (Site d) → Ω → ℝ) (hRm : ∀ B, Measurable (R B))
    (hRstat : ∀ (B : Finset (Site d)) (z : Site d) (ω : Ω),
      R (B.map (Equiv.addRight z).toEmbedding) ω = R B (τ z ω))
    (hRnn : ∀ a b ω, 0 ≤ R (latticeBox a b) ω) {M : ℝ} (hRbd : ∀ B ω, R B ω ≤ M * B.card)
    {ρ : ℝ} (hρ : ∀ N : ℕ, 1 ≤ N → ∫ ω, R (latticeCube d N) ω ∂μ ≤ ρ * (N : ℝ) ^ d)
    (J N : ℕ) :
    ∫ ω, (∑ u ∈ latticeCube d (2 ^ J), R (dyBig u J N) ω) ∂μ ≤
      ((2 ^ J : ℕ) : ℝ) ^ d * (ρ * (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d) := by
  rw [integral_finsetSum _ (fun u _ => aux_aux_ak_ae_45_31_2 R hRm hRnn hRbd u J N)]
  have h1 : ∑ u ∈ latticeCube d (2 ^ J), ∫ ω, R (dyBig u J N) ω ∂μ ≤
      ∑ _u ∈ latticeCube d (2 ^ J), ρ * (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d :=
    Finset.sum_le_sum (fun u _ => aux_ak_ae_45_29 τ hτ R hRm hRstat hρ u J N)
  rw [Finset.sum_const, aux_t0, nsmul_eq_mul] at h1
  simpa only [Nat.cast_pow] using h1

-- `h2` gives `S / P ≤ ρ Nd'` (`div_le_iff₀`, `mul_comm`), so `Nd X ≤ c ρ Nd'`
-- (`mul_le_mul_of_nonneg_left`); then `le_div_iff₀ hN`, `mul_div_assoc`; `linarith`.
private theorem aux_aux_ak_ae_45_31_4 {X c S P Nd Nd' ρ : ℝ} (hc : 0 ≤ c) (hP : 0 < P) (hN : 0 < Nd)
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

-- Finite-`N` form: the number of bad sites of `Q_N` is `∑_x 1_{E_K} (τ x ω)` (`aux_ak_ae_45_30`); integrate `aux_ak_ae_45_28` at `r := (R · ω)`
-- (`integral_mono`; integrability from `0 ≤ R ≤ M card` on boxes), `aux_ak_ae_45_17`
-- (`E_K` measurable: `MeasurableSet` of a finite union, `measurableSet_lt`), `integral_finsetSum`,
-- `aux_ak_ae_45_29`, `Finset.sum_const`, `aux_t0`; divide by `N^d` (`le_div_iff₀`).  SPLIT?
private theorem aux_ak_ae_45_31 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
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
  have hEm := aux_aux_ak_ae_45_31_1 (d := d) R hRm α K
  have h17 := aux_ak_ae_45_17 τ hτ hEm N
  have hc : 0 ≤ akMaxConst d / α := div_nonneg (aux_ak_ae_45_0 hd).le hα.le
  have hpt : ∀ ω, (∑ x ∈ latticeCube d N,
      {ω' | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω'}.indicator
        (fun _ => (1 : ℝ)) (τ x ω)) ≤
      akMaxConst d / α * ((∑ u ∈ latticeCube d (2 ^ J), R (dyBig u J N) ω) /
        ((2 ^ J : ℕ) : ℝ) ^ d) := by
    intro ω
    rw [← aux_ak_ae_45_30 τ R hRstat α K N ω]
    exact aux_ak_ae_45_28 hd (fun B => R B ω) (fun a b => hRnn a b ω)
      (fun B B₁ B₂ h => hRsup B B₁ B₂ ω h) (fun a b a' b' ha hb => hRmono a b a' b' ω ha hb) hα hKJ N
  have hint1 : Integrable (fun ω => ∑ x ∈ latticeCube d N,
      {ω' | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω'}.indicator
        (fun _ => (1 : ℝ)) (τ x ω)) μ :=
    integrable_finsetSum _ (fun x _ => aux_aux_ak_ae_45_17_1 τ hτ hEm x)
  have hint2 : Integrable (fun ω => akMaxConst d / α *
      ((∑ u ∈ latticeCube d (2 ^ J), R (dyBig u J N) ω) / ((2 ^ J : ℕ) : ℝ) ^ d)) μ :=
    ((integrable_finsetSum _ (fun u _ =>
      aux_aux_ak_ae_45_31_2 R hRm hRnn hRbd u J N)).div_const _).const_mul _
  have hmono := integral_mono hint1 hint2 hpt
  rw [h17, integral_const_mul, integral_div] at hmono
  have hNpos : (0 : ℝ) < (N : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr (by omega)) d
  exact aux_aux_ak_ae_45_31_4 hc (by positivity) hNpos hmono
    (aux_aux_ak_ae_45_31_3 τ hτ R hRm hRstat hRnn hRbd hρ J N)

-- `N ≤ N' ≤ N + 4 · 2^J` (`Nat.lt_div_mul_add`, `Nat.div_mul_le_self`); squeeze as in
-- `aux_ak_ae_42_aux` between `1` and `(1 + 4 · 2^J / N)^d` (`tendsto_const_div_atTop_nhds_zero_nat`,
-- `Tendsto.pow`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`).
private theorem aux_32_h1 {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < N)

private theorem aux_32_nat1 {J N : ℕ} : N ≤ (N / 2 ^ J + 4) * 2 ^ J := by rw [Nat.add_mul]; exact le_trans (le_of_lt (Nat.lt_div_mul_add (b := 2 ^ J) (pow_pos (by norm_num) J))) (Nat.add_le_add_left (Nat.le_mul_of_pos_left (n := 4) (2 ^ J) (by norm_num)) _)

private theorem aux_32_h4 {J N : ℕ} : (N / 2 ^ J + 4) * 2 ^ J ≤ N + 4 * 2 ^ J := by rw [Nat.add_mul]; exact Nat.add_le_add_right (Nat.div_mul_le_self N (2 ^ J)) (4 * 2 ^ J)

private theorem aux_32_cast {J N : ℕ} : ((N + 4 * 2 ^ J : ℕ) : ℝ) = (N : ℝ) + 4 * ((2 ^ J : ℕ) : ℝ) := by push_cast; ring

private theorem aux_32_h3 {d J N : ℕ} (hN : 1 ≤ N) : (1 : ℝ) ≤ (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d := (le_div_iff₀ (pow_pos (aux_32_h1 hN) d)).mpr (by rw [one_mul]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast aux_32_nat1 (J := J) (N := N)) d)

private theorem aux_32_div_eq {J N : ℕ} (hN : 1 ≤ N) : ((N + 4 * 2 ^ J : ℕ) : ℝ) / (N : ℝ) = 1 + 4 * ((2 ^ J : ℕ) : ℝ) / (N : ℝ) := by rw [aux_32_cast (J := J) (N := N), add_div, div_self (ne_of_gt (aux_32_h1 hN))]

private theorem aux_32_h5a {d J N : ℕ} (hN : 1 ≤ N) : (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d ≤ (((N + 4 * 2 ^ J : ℕ) : ℝ) / (N : ℝ)) ^ d := by rw [div_pow]; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast aux_32_h4 (J := J) (N := N)) d) (pow_nonneg (aux_32_h1 hN).le d)

private theorem aux_32_h5 {d J N : ℕ} (hN : 1 ≤ N) : (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d ≤ (1 + 4 * ((2 ^ J : ℕ) : ℝ) / (N : ℝ)) ^ d := by have h := aux_32_h5a (d := d) (J := J) (N := N) hN; rwa [aux_32_div_eq hN] at h

private theorem aux_32_h6 {d J : ℕ} : Tendsto (fun N : ℕ => (1 + 4 * ((2 ^ J : ℕ) : ℝ) / (N : ℝ)) ^ d) atTop (𝓝 1) := by simpa using ((tendsto_const_div_atTop_nhds_zero_nat (4 * ((2 ^ J : ℕ) : ℝ))).const_add 1).pow d

private theorem aux_32_h7 {d J : ℕ} : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d := eventually_atTop.mpr ⟨1, fun N hN => aux_32_h3 (d := d) (J := J) (N := N) hN⟩

private theorem aux_32_h8 {d J : ℕ} : ∀ᶠ N : ℕ in atTop, (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d ≤ (1 + 4 * ((2 ^ J : ℕ) : ℝ) / (N : ℝ)) ^ d := eventually_atTop.mpr ⟨1, fun N hN => aux_32_h5 (d := d) (J := J) (N := N) hN⟩

private theorem aux_ak_ae_45_32 (d J : ℕ) :
    Tendsto (fun N : ℕ => ((((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℝ) ^ d / (N : ℝ) ^ d)) atTop (𝓝 1) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (aux_32_h6 (d := d) (J := J)) (aux_32_h7 (d := d) (J := J)) (aux_32_h8 (d := d) (J := J))


-- The maximal inequality.  `{∃ k ≥ 1, …} = ⋃ K, E_K` (`Set.ext`, `Set.mem_iUnion`), `E_K`
-- monotone; `aux_ak_ae_45_16`; for each `K` take `J := 2 d K` (`Nat.lt_two_pow_self`), then
-- `ge_of_tendsto` of `aux_ak_ae_45_32` (times the constant, `Tendsto.const_mul`) against
-- `aux_ak_ae_45_31` for `N ≥ 1` (`eventually_ge_atTop`); `mul_one`, `div_mul_eq_mul_div`.
private theorem aux_ak_ae_45_33 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
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
  refine aux_ak_ae_45_16 (S := fun K => {ω : Ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
      α * (k : ℝ) ^ d < R (latticeCube d k) ω}) (monotone_nat_of_le_succ fun K => ?_) ?_
  · intro ω hω
    obtain ⟨k, hk1, hkK, hk⟩ := hω
    exact ⟨k, hk1, Nat.le_succ_of_le hkK, hk⟩
  · intro K
    have h' : μ.real {ω : Ω | ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
        α * (k : ℝ) ^ d < R (latticeCube d k) ω} ≤ (akMaxConst d / α * ρ) * 1 :=
      ge_of_tendsto ((aux_ak_ae_45_32 d (2 * d * K)).const_mul (akMaxConst d / α * ρ))
        (Filter.eventually_atTop.2 ⟨1, fun N hN => aux_ak_ae_45_31 hd τ hτ R hRm hRstat hRnn
          hRbd hRsup hRmono hρ hα (le_of_lt Nat.lt_two_pow_self) hN⟩)
    rwa [mul_one, div_mul_eq_mul_div] at h'


/-! #### (C) From the maximal inequality to the integral -/

-- `X ≤ α + M · 1_{α < X}` pointwise (`Set.indicator_apply`, `split_ifs`); `integral_mono`
-- (`Integrable.of_bound`, `integrable_const`, `(integrable_const M).indicator`),
-- `integral_add`, `integral_const`, `integral_indicator_const` (`measurableSet_lt`),
-- `probReal_univ`/`measureReal_univ_eq_one`; `M ≥ 0` from `hXb` at a point
-- (`nonempty_of_isProbabilityMeasure`); `mul_le_mul_of_nonneg_left`.
private theorem aux_ak_ae_34_help {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) {M c : ℝ} (hXb : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M)
    (htail : ∀ α, 0 < α → μ.real {ω | α < X ω} ≤ c / α) {α : ℝ} (hα : 0 < α) :
    ∫ ω, X ω ∂μ ≤ α + M * (c / α) := by
  have hTm : MeasurableSet {ω | α < X ω} := measurableSet_lt measurable_const hX
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hM0 : (0 : ℝ) ≤ M := le_trans (hXb ω0).1 (hXb ω0).2
  have hXint : Integrable X μ := Integrable.of_bound hX.aestronglyMeasurable M (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hXb ω).1]
    exact (hXb ω).2)
  have hind : Integrable (Set.indicator {ω | α < X ω} (fun _ => M)) μ :=
    (integrable_const M).indicator hTm
  have hgint : Integrable (fun ω => α + Set.indicator {ω | α < X ω} (fun _ => M) ω) μ :=
    (integrable_const α).add hind
  have hpoint : ∀ ω, X ω ≤ α + Set.indicator {ω | α < X ω} (fun _ => M) ω := fun ω => by
    rw [Set.indicator_apply]
    split_ifs with h
    · linarith [(hXb ω).2]
    · have hle : X ω ≤ α := not_lt.1 h
      linarith
  have hInt2 : ∫ ω, (α + Set.indicator {ω | α < X ω} (fun _ => M) ω) ∂μ
      = α + M * μ.real {ω | α < X ω} := by
    rw [integral_add (integrable_const α) hind, integral_const,
      integral_indicator_const M hTm, probReal_univ]
    simp only [smul_eq_mul]
    ring
  have hkey : ∫ ω, X ω ∂μ ≤ α + M * μ.real {ω | α < X ω} := by
    rw [← hInt2]
    exact integral_mono hXint hgint hpoint
  exact le_trans hkey (by linarith [mul_le_mul_of_nonneg_left (htail α hα) hM0])

private theorem aux_ak_ae_45_34 {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {M c : ℝ} (hXb : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M)
    (htail : ∀ α, 0 < α → μ.real {ω | α < X ω} ≤ c / α) {α : ℝ} (hα : 0 < α) :
    ∫ ω, X ω ∂μ ≤ α + M * (c / α) := by
  exact aux_ak_ae_34_help hX hXb htail hα


-- `Filter.frequently_lt_of_lt_limsup` (coboundedness from the lower bound `0`,
-- `isCoboundedUnder_le_of_le`) combined with `eventually_ge_atTop 1`
-- (`Filter.Frequently.and_eventually`), then `Frequently.exists`; `lt_div_iff₀` (`k ≥ 1`).
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_35 {d : ℕ} {R : Finset (Site d) → Ω → ℝ} {M : ℝ}
    (hR : ∀ (k : ℕ) ω, 0 ≤ R (latticeCube d k) ω / (k : ℝ) ^ d ∧
      R (latticeCube d k) ω / (k : ℝ) ^ d ≤ M) {α : ℝ} (_unused_hα : 0 < α) :
    {ω | α < limsup (fun k : ℕ => R (latticeCube d k) ω / (k : ℝ) ^ d) atTop} ⊆
      {ω | ∃ k : ℕ, 1 ≤ k ∧ α * (k : ℝ) ^ d < R (latticeCube d k) ω} := by
  intro ω hω
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun k : ℕ => R (latticeCube d k) ω / (k : ℝ) ^ d) :=
    isCoboundedUnder_le_of_le atTop (fun k => (hR k ω).1)
  have hfreq : ∃ᶠ k in atTop, α < R (latticeCube d k) ω / (k : ℝ) ^ d :=
    frequently_lt_of_lt_limsup hcob hω
  have hall : ∃ᶠ k : ℕ in atTop,
      1 ≤ k ∧ α < R (latticeCube d k) ω / (k : ℝ) ^ d :=
    (hfreq.and_eventually (eventually_ge_atTop 1)).mono fun k h => ⟨h.2, h.1⟩
  obtain ⟨k, hk1, hklt⟩ := hall.exists
  refine ⟨k, hk1, ?_⟩
  have hpos : (0 : ℝ) < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk1) d
  exact (lt_div_iff₀ hpos).mp hklt


/-! #### (D) The unit-scale lower bound -/

-- `∫ R(Q_N) = ∫ addPart - ∫ F(Q_N)` (`boxDefect`, `integral_sub`, integrability by bounds);
-- `∫ addPart F (Q_N) = N^d ∫ F Q_1` (`aux_ak_ae_45_15`, `integral_const_mul`, `aux_ak_ae_37`
-- with `σ := τ`, `h := F Q_1`); `∫ F (Q_N) = N^d ∫ cubeRatio F N` (`cubeRatio`, `integral_div`,
-- `aux_t0`); `cubeRatio F 1 = F Q_1` (`one_pow`, `div_one`, `Nat.cast_one`); then `hFη`, `nlinarith`.
private theorem aux_ak_ae_45_36 {d : ℕ} (_unused_hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hmeas : ∀ A, Measurable (F A))
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω))
    {η : ℝ} (hFη : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio F 1 ω ∂μ - η ≤ ∫ ω, cubeRatio F N ω ∂μ)
    {N : ℕ} (hN : 1 ≤ N) :
    ∫ ω, boxDefect F (latticeCube d N) ω ∂μ ≤ η * (N : ℝ) ^ d := by
  have hb1 : ∀ x, |F (latticeCube d 1) x| ≤ C := by
    intro x
    have h := hC (latticeCube d 1) x
    have hc : ((latticeCube d 1).card : ℝ) = 1 := by
      rw [aux_t0 d 1, one_pow, Nat.cast_one]
    rw [hc, mul_one] at h
    exact abs_le.2 ⟨by linarith [h.1], h.2⟩
  have hAPm : Measurable (fun ω => addPart F (latticeCube d N) ω) := by
    unfold addPart
    exact Finset.measurable_sum _ fun z _ => hmeas {z}
  have hAPint : Integrable (fun ω => addPart F (latticeCube d N) ω) μ := by
    refine Integrable.of_bound hAPm.aestronglyMeasurable (C * ((latticeCube d N).card : ℝ)) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_ak_ae_45_6 hC _ ω).1]
    exact (aux_ak_ae_45_6 hC _ ω).2
  have hFint : Integrable (fun ω => F (latticeCube d N) ω) μ := by
    refine Integrable.of_bound (hmeas _).aestronglyMeasurable (C * ((latticeCube d N).card : ℝ)) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hC _ ω).1]
    exact (hC _ ω).2
  have hEq : ∫ ω, boxDefect F (latticeCube d N) ω ∂μ =
      ∫ ω, addPart F (latticeCube d N) ω ∂μ - ∫ ω, F (latticeCube d N) ω ∂μ := by
    simp only [boxDefect]
    exact integral_sub hAPint hFint
  have hAP : ∫ ω, addPart F (latticeCube d N) ω ∂μ =
      (N : ℝ) ^ d * ∫ ω, cubeRatio F 1 ω ∂μ := by
    have hfun : (fun ω => addPart F (latticeCube d N) ω) =
        fun ω => (N : ℝ) ^ d * gridAvg τ (F (latticeCube d 1)) Finset.univ N ω :=
      funext fun ω => aux_ak_ae_45_15 τ hstat hN ω
    rw [hfun, integral_const_mul, aux_ak_ae_37 hτ (hmeas (latticeCube d 1)) hb1 hN]
    congr 1
    simp [cubeRatio]
  have hF' : ∫ ω, cubeRatio F N ω ∂μ =
      (∫ ω, F (latticeCube d N) ω ∂μ) / (N : ℝ) ^ d := by
    have hfun : (fun ω => cubeRatio F N ω) =
        fun ω => F (latticeCube d N) ω / (N : ℝ) ^ d := rfl
    rw [hfun, integral_div]
  have hNd : (N : ℝ) ^ d ≠ 0 := pow_ne_zero d (by positivity)
  have hF : ∫ ω, F (latticeCube d N) ω ∂μ =
      (N : ℝ) ^ d * ∫ ω, cubeRatio F N ω ∂μ := by
    rw [hF']
    exact (mul_div_cancel₀ _ hNd).symm
  have hexp : (N : ℝ) ^ d * (∫ ω, cubeRatio F 1 ω ∂μ) -
        (N : ℝ) ^ d * (∫ ω, cubeRatio F N ω ∂μ) ≤ η * (N : ℝ) ^ d := by
    have h1 := mul_le_mul_of_nonneg_left (hFη N hN) (pow_nonneg (Nat.cast_nonneg N) d)
    have e : (N : ℝ) ^ d * (∫ ω, cubeRatio F 1 ω ∂μ - η) =
        (N : ℝ) ^ d * (∫ ω, cubeRatio F 1 ω ∂μ) - (N : ℝ) ^ d * η := by ring
    rw [e] at h1
    rw [mul_comm η]
    linarith
  rw [hEq, hAP, hF]
  exact hexp


-- `cubeRatio`, `boxDefect`, `aux_ak_ae_45_15`, `sub_div`, `mul_div_cancel_left₀`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_37 {d : ℕ} {F : Finset (Site d) → Ω → ℝ} (τ : Site d → Ω → Ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω)) {k : ℕ} (hk : 1 ≤ k) (ω : Ω) :
    cubeRatio F k ω =
      gridAvg τ (F (latticeCube d 1)) Finset.univ k ω -
        boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d := by
  have hk0 : (k : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : k ≠ 0))
  unfold cubeRatio boxDefect
  rw [aux_ak_ae_45_15 τ hstat hk ω, sub_div, mul_div_cancel_left₀ _ hk0]
  ring

-- Real analysis: eventually `u = v - w`; `liminf (v - w) ≥ lim v - limsup w`
-- (`Filter.liminf_congr`, `Tendsto.liminf_eq`, `Filter.le_liminf_of_le` with
-- `Filter.eventually_lt_of_limsup_lt`-type ε-argument, or `liminf_add_le`-style lemmas for
-- `v + (-w)`); boundedness from `hw` and convergence of `v`.  SPLIT?
private theorem aux_ak_38_main {u v w : ℕ → ℝ} {H M : ℝ} (huvw : ∀ k, 1 ≤ k → u k = v k - w k)
    (hv : Tendsto v atTop (𝓝 H)) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ M) :
    H - limsup w atTop ≤ liminf u atTop := by
  have huub : ∀ᶠ k in atTop, u k ≤ H + 1 := by
    obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hv 1 one_pos
    filter_upwards [eventually_ge_atTop N1, eventually_ge_atTop 1] with k hk1 hk2
    have h := hN1 k hk1
    rw [Real.dist_eq] at h
    have hb := (abs_lt.mp h).2
    rw [huvw k hk2]
    linarith [(hw k).1]
  have hcob : IsCoboundedUnder (· ≥ ·) atTop u :=
    isCoboundedUnder_ge_of_eventually_le atTop huub
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hv (ε / 2) hε2
  have h1 : ∀ᶠ k in atTop, H - ε / 2 < v k := by
    filter_upwards [eventually_ge_atTop N] with k hk
    have h := hN k hk
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).1]
  have h2 : ∀ᶠ k in atTop, w k < limsup w atTop + ε / 2 :=
    eventually_lt_of_limsup_lt (by linarith) (isBoundedUnder_le_of fun k => (hw k).2)
  have h3 : ∀ᶠ k in atTop, H - limsup w atTop - ε ≤ u k := by
    filter_upwards [h1, h2, eventually_ge_atTop 1] with k hk1 hk2 hk3
    rw [huvw k hk3]
    linarith
  have h4 : H - limsup w atTop - ε ≤ liminf u atTop :=
    @le_liminf_of_le ℝ ℕ _ atTop u _ hcob h3
  linarith

private theorem aux_ak_ae_45_38 {u v w : ℕ → ℝ} {H M : ℝ} (huvw : ∀ k, 1 ≤ k → u k = v k - w k)
    (hv : Tendsto v atTop (𝓝 H)) (hw : ∀ k, 0 ≤ w k ∧ w k ≤ M) :
    H - limsup w atTop ≤ liminf u atTop := by
  exact aux_ak_38_main huvw hv hw


-- `X := limsup R(Q_k)/k^d` with `R := boxDefect F`: measurable (`Measurable.limsup`,
-- `aux_ak_ae_45_12`), in `[0, C]` (`aux_ak_ae_45_7`, `k = 0` gives `0` by `div_zero`/`zero_pow`);
-- `aux_ak_ae_45_34` with `c := akMaxConst d * η`, tail bound from `aux_ak_ae_45_35` and
-- `aux_ak_ae_45_33` (`measureReal_mono`), hypotheses of the latter from `aux_ak_ae_45_7`,
-- `aux_ak_ae_45_8`, `aux_ak_ae_45_10`, `aux_ak_ae_45_11`, `aux_ak_ae_45_12`, `aux_ak_ae_45_36`.
private theorem aux_ak_ae_45_39 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hmeas : ∀ A, Measurable (F A))
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω))
    {η : ℝ} (hFη : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio F 1 ω ∂μ - η ≤ ∫ ω, cubeRatio F N ω ∂μ)
    {α : ℝ} (hα : 0 < α) :
    ∫ ω, limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop ∂μ ≤
      α + C * (akMaxConst d * η / α) := by
  exact (
    let hC0 : (0 : ℝ) ≤ C := aux_ak_ae_2 hC (Classical.choice (nonempty_of_isProbabilityMeasure μ));
    let h7a : ∀ a b ω, 0 ≤ boxDefect F (latticeBox a b) ω := (aux_ak_ae_45_7 hC hsub).1;
    let h7b : ∀ B ω, boxDefect F B ω ≤ C * (B.card : ℝ) := (aux_ak_ae_45_7 hC hsub).2;
    let hgb : ∀ k ω, 0 ≤ boxDefect F (latticeCube d k) ω ∧ boxDefect F (latticeCube d k) ω ≤ C * (k : ℝ) ^ d :=
      fun k ω => ⟨h7a 0 (fun _ : Fin d => (k : ℤ) - 1) ω,
        by simpa [aux_t0, Nat.cast_pow] using h7b (latticeCube d k) ω⟩;
    let hg : ∀ k ω, 0 ≤ boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d ∧
        boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d ≤ C :=
      fun k ω => ⟨div_nonneg (hgb k ω).1 (pow_nonneg (Nat.cast_nonneg k) d),
        if hk : k = 0
          then by subst hk; simp only [Nat.cast_zero, zero_pow (by omega : d ≠ 0), div_zero]; exact hC0
          else by
            rw [div_le_iff₀ (pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)) d)]
            exact (hgb k ω).2⟩;
    aux_ak_ae_45_34
      (Measurable.limsup fun k => (aux_ak_ae_45_12 hmeas (latticeCube d k)).div_const _)
      (fun ω => ⟨
        le_limsup_of_frequently_le (Frequently.of_forall fun k => (hg k ω).1)
          (isBoundedUnder_le_of fun k => (hg k ω).2),
        limsup_le_of_le (isCoboundedUnder_le_of_le atTop fun k => (hg k ω).1)
          (Eventually.of_forall fun k => (hg k ω).2)⟩)
      (fun β hβ => le_trans
        (measureReal_mono (aux_ak_ae_45_35 (R := boxDefect F) (M := C) hg hβ))
        (aux_ak_ae_45_33 hd τ hτ (boxDefect F) (aux_ak_ae_45_12 hmeas) (aux_ak_ae_45_11 τ hstat)
          h7a h7b (fun B B₁ B₂ ω h => aux_ak_ae_45_8 hsub h ω)
          (fun a b a' b' ω ha hb => aux_ak_ae_45_10 hC hsub a b a' b' ha hb ω)
          (fun N hN => aux_ak_ae_45_36 hd τ hτ hmeas hC hstat hFη hN) hβ))
      hα)


-- Unit-scale lower bound: `aux_ak_ae_38` (`σ := τ`, `h := F Q_1`, `M := C`) gives `H` with
-- `∫ H = ∫ F Q_1 = ∫ cubeRatio F 1`; pointwise `H - X ≤ liminf cubeRatio F k` a.e.
-- (`aux_ak_ae_45_37`, `aux_ak_ae_45_38` with `w k := R(Q_k)/k^d`); `integral_mono_ae`
-- (integrability of `liminf` as in `aux_ak_ae_46`), `integral_sub`, `aux_ak_ae_45_39`; `linarith`.
private theorem aux_a40_limsup_bounds {u : ℕ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hu : ∀ k, 0 ≤ u k ∧ u k ≤ C) : |limsup u atTop| ≤ C := by
  refine abs_le.2 ⟨?_, ?_⟩
  · refine le_trans (neg_nonpos.mpr hC0) ?_
    exact le_limsup_of_le (isBoundedUnder_le_of fun n => (hu n).2) fun b hb => by
      rcases eventually_atTop.mp hb with ⟨N, hN⟩
      exact le_trans (hu (max N 1)).1 (hN _ (le_max_left N 1))
  · exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop fun n => (hu n).1)
      (Eventually.of_forall fun n => (hu n).2)

private theorem aux_a40_liminf_bounds {u : ℕ → ℝ} {C : ℝ} (_unused_hC0 : 0 ≤ C)
    (hu : ∀ k, 0 ≤ u k ∧ u k ≤ C) : 0 ≤ liminf u atTop ∧ liminf u atTop ≤ C := by
  refine ⟨?_, ?_⟩
  · exact le_liminf_of_le ((isBoundedUnder_le_of fun n => (hu n).2).isCoboundedUnder_ge)
      (Eventually.of_forall fun n => (hu n).1)
  · exact liminf_le_of_le (isBoundedUnder_ge_of fun n => (hu n).1) fun b hb => by
      rcases eventually_atTop.mp hb with ⟨N, hN⟩
      exact le_trans (hN _ (le_max_left N 1)) (hu (max N 1)).2

omit [MeasurableSpace Ω] in
private theorem aux_a40_seq {d : ℕ} (hd : 1 ≤ d) {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω) (hC0 : 0 ≤ C)
    (k : ℕ) (ω : Ω) :
    0 ≤ boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d ∧
      boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d ≤ C := by
  obtain ⟨h7nn, h7bd⟩ := aux_ak_ae_45_7 hC hsub
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Nat.cast_zero, zero_pow (by omega : d ≠ 0), div_zero]
    exact ⟨le_rfl, hC0⟩
  · have hnn : 0 ≤ boxDefect F (latticeCube d k) ω :=
      h7nn (0 : Site d) (fun _ => (k : ℤ) - 1) ω
    have hup : boxDefect F (latticeCube d k) ω ≤ C * (k : ℝ) ^ d := by
      have h := h7bd (latticeCube d k) ω
      rw [aux_t0 d k, Nat.cast_pow] at h
      exact h
    refine ⟨div_nonneg hnn (by positivity), ?_⟩
    rw [div_le_iff₀ (pow_pos (by exact_mod_cast hk) d)]
    exact hup

private theorem aux_ak_ae_45_40 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (F A))
    (hC : ∀ A ω, 0 ≤ F A ω ∧ F A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → F B ω ≤ F B₁ ω + F B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      F (A.map (Equiv.addRight z).toEmbedding) ω = F A (τ z ω))
    {η : ℝ} (hFη : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio F 1 ω ∂μ - η ≤ ∫ ω, cubeRatio F N ω ∂μ)
    {α : ℝ} (hα : 0 < α) :
    ∫ ω, cubeRatio F 1 ω ∂μ ≤
      ∫ ω, liminf (fun k => cubeRatio F k ω) atTop ∂μ + α + C * (akMaxConst d * η / α) := by
  have hC0 : 0 ≤ C := (by
    obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
    exact aux_ak_ae_2 hC ω0)
  obtain ⟨G, hGm, hGb, hGint, hGconv⟩ :=
    aux_ak_ae_38 hτ hτadd (hmeas (latticeCube d 1)) hC0
      (fun x => by
        have h0 := (aux_ak_ae_20 hd hC 1 x).1
        have h1 := (aux_ak_ae_20 hd hC 1 x).2
        simp only [cubeRatio, Nat.cast_one, one_pow, div_one] at h0 h1
        exact abs_le.2 ⟨(by linarith), h1⟩)
  have hXm : Measurable (fun ω : Ω =>
      limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop) :=
    Measurable.limsup fun k =>
      (aux_ak_ae_45_12 hmeas (latticeCube d k)).div_const ((k : ℝ) ^ d)
  have hXb : ∀ ω : Ω,
      |limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop| ≤ C :=
    fun ω => aux_a40_limsup_bounds hC0 (fun k => aux_a40_seq hd hC hsub hC0 k ω)
  have hXint : Integrable (fun ω : Ω =>
      limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop) μ :=
    Integrable.of_bound hXm.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact hXb x)
  have hLb : ∀ ω : Ω, 0 ≤ liminf (fun k : ℕ => cubeRatio F k ω) atTop ∧
      liminf (fun k : ℕ => cubeRatio F k ω) atTop ≤ C :=
    fun ω => aux_a40_liminf_bounds hC0 (fun k => aux_ak_ae_20 hd hC k ω)
  have hLm : Measurable (fun ω : Ω => liminf (fun k : ℕ => cubeRatio F k ω) atTop) :=
    Measurable.liminf fun k => aux_ak_ae_21 hmeas k
  have hLint : Integrable (fun ω : Ω => liminf (fun k : ℕ => cubeRatio F k ω) atTop) μ :=
    Integrable.of_bound hLm.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hLb x).1]
      exact (hLb x).2)
  have hGint' : Integrable G μ :=
    Integrable.of_bound hGm.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact hGb x)
  have hcr1 : (∫ ω, cubeRatio F 1 ω ∂μ) = ∫ ω, F (latticeCube d 1) ω ∂μ := (by
    refine integral_congr_ae ?_
    filter_upwards with ω
    simp [cubeRatio])
  have hpt : ∀ᵐ ω ∂μ, G ω -
      limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop ≤
      liminf (fun k : ℕ => cubeRatio F k ω) atTop := (by
    filter_upwards [hGconv] with ω hω
    exact aux_ak_ae_45_38 (u := fun k => cubeRatio F k ω)
      (v := fun k => gridAvg τ (F (latticeCube d 1)) Finset.univ k ω)
      (w := fun k => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d)
      (fun k hk => aux_ak_ae_45_37 τ hstat hk ω) hω
      (fun k => aux_a40_seq hd hC hsub hC0 k ω))
  have hmono : (∫ ω, G ω ∂μ) -
      (∫ ω, limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop ∂μ) ≤
      ∫ ω, liminf (fun k : ℕ => cubeRatio F k ω) atTop ∂μ := (by
    have h := integral_mono_ae (hGint'.sub hXint) hLint hpt
    have hsub' := integral_sub hGint' hXint
    simp only [Pi.sub_apply] at h
    rwa [hsub'] at h)
  have h39 : ∫ ω, limsup (fun k : ℕ => boxDefect F (latticeCube d k) ω / (k : ℝ) ^ d) atTop ∂μ ≤
      α + C * (akMaxConst d * η / α) :=
    aux_ak_ae_45_39 hd τ hτ hmeas hC hsub hstat hFη hα
  rw [hGint] at hmono
  rw [hcr1]
  exact (by linarith)


/-! #### (E) Coarse-graining -/

-- `blowup`, `Finset.ext`, `Finset.mem_biUnion`, `Finset.mem_map`, `aux_ak_ae_5_1`, `latticeCube`:
-- `y ∈ m a + … ↔ ∃ z ∈ [a, b], y - m z ∈ [0, m)^d`; take `z i := (y i - …) / m` (`Int.ediv`,
-- `Int.emod_emod_of_dvd`, `Int.ediv_add_emod`); both sides empty when some `a i > b i`.  SPLIT?
private theorem aux_ak_ae_45_41 {d m : ℕ} (hm : 1 ≤ m) (a b : Site d) :
    blowup m (latticeBox a b) =
      latticeBox ((m : ℤ) • a) ((m : ℤ) • b + fun _ => (m : ℤ) - 1) := by
  have hm0 : (0 : ℤ) < (m : ℤ) := (by exact_mod_cast hm)
  have hmne : (m : ℤ) ≠ 0 := ne_of_gt hm0
  have hsm : ∀ (v : Site d) (i : Fin d), ((m : ℤ) • v) i = (m : ℤ) * v i :=
    fun v i => by simp []
  have hadd : ∀ (v : Site d) (i : Fin d),
      ((m : ℤ) • v + fun _ : Fin d => (m : ℤ) - 1) i = (m : ℤ) * v i + ((m : ℤ) - 1) :=
    fun v i => by simp [zsmul_eq_mul]
  ext y
  rw [aux_ak_ae_5_1]
  constructor
  · intro hy
    rw [blowup, Finset.mem_biUnion] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    rw [aux_ak_ae_12 d m ((m : ℤ) • z), aux_ak_ae_5_1] at hyz
    intro i
    have h1 := (aux_ak_ae_5_1 a b z).1 hz i
    have h2 := hyz i
    rw [hsm z i] at h2
    rw [hsm a i, hadd b i]
    exact ⟨le_trans (mul_le_mul_of_nonneg_left h1.1 hm0.le) h2.1,
      by linarith [mul_le_mul_of_nonneg_left h1.2 hm0.le, h2.2]⟩
  · intro hy
    rw [blowup, Finset.mem_biUnion]
    refine ⟨fun i => y i / (m : ℤ), ?_, ?_⟩
    · rw [aux_ak_ae_5_1]
      intro i
      have h := hy i
      rw [hsm a i, hadd b i] at h
      exact ⟨(Int.le_ediv_iff_mul_le hm0).2 (by linarith [h.1]),
        (Int.ediv_le_iff_le_mul hm0).2 (by linarith [h.2])⟩
    · rw [aux_ak_ae_12 d m ((m : ℤ) • fun i => y i / (m : ℤ)), aux_ak_ae_5_1]
      intro i
      have h := hy i
      rw [hsm a i, hadd b i] at h
      rw [hsm (fun i => y i / (m : ℤ)) i]
      have hdiv := Int.emod_add_mul_ediv (y i) (m : ℤ)
      have hmod_nn := Int.emod_nonneg (y i) hmne
      have hmod_lt := Int.emod_lt_of_pos (y i) hm0
      refine ⟨?_, ?_⟩ <;> linarith


-- Union: `blowup`, `Finset.union_biUnion`.  Disjointness: blocks of distinct sites are disjoint
-- (`y - m z ∈ [0, m)^d` determines `z`: `Int.ediv_emod_unique`); `Finset.disjoint_biUnion_left`,
-- `Finset.disjoint_biUnion_right`.
private theorem aux_blocks_disjoint {d m : ℕ} (_unused_hm : 1 ≤ m) {z w : Site d} (hzw : z ≠ w) :
    Disjoint ((latticeCube d m).map (Equiv.addRight ((m : ℤ) • z)).toEmbedding)
      ((latticeCube d m).map (Equiv.addRight ((m : ℤ) • w)).toEmbedding) := by
  rw [aux_ak_ae_12, aux_ak_ae_12]
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  have h1 := (aux_ak_ae_5_1 _ _ y).1 hy1
  have h2 := (aux_ak_ae_5_1 _ _ y).1 hy2
  obtain ⟨i, hi⟩ : ∃ i : Fin d, z i ≠ w i := by
    by_contra h
    push Not at h
    exact hzw (funext fun i => h i)
  have e1 := h1 i
  have e2 := h2 i
  simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
  have hbound : |(m : ℤ) * (z i - w i)| ≤ (m : ℤ) - 1 := by
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hge : (m : ℤ) ≤ |(m : ℤ) * (z i - w i)| := by
    rw [abs_mul]
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast Nat.zero_le m
    have ht : (1 : ℤ) ≤ |z i - w i| := by
      have hpos : (0 : ℤ) < |z i - w i| := abs_pos.mpr (sub_ne_zero.mpr hi)
      omega
    rw [abs_of_nonneg hm0]
    calc (m : ℤ) = (m : ℤ) * 1 := by ring
      _ ≤ (m : ℤ) * |z i - w i| := mul_le_mul_of_nonneg_left ht hm0
  omega

private theorem aux_ak_ae_45_42 {d m : ℕ} (hm : 1 ≤ m) (B₁ B₂ : Finset (Site d)) :
    blowup m (B₁ ∪ B₂) = blowup m B₁ ∪ blowup m B₂ ∧
      (Disjoint B₁ B₂ → Disjoint (blowup m B₁) (blowup m B₂)) := by
  constructor
  · unfold blowup
    exact Finset.union_biUnion
  · intro h
    unfold blowup
    rw [Finset.disjoint_biUnion_left]
    intro z hz
    rw [Finset.disjoint_biUnion_right]
    intro w hw
    exact aux_blocks_disjoint hm (fun hzw => (Finset.disjoint_left.mp h hz) (hzw.symm ▸ hw))


-- `IsBoxSplit`: boxes by `aux_ak_ae_45_41`, union and disjointness by `aux_ak_ae_45_42`.
private theorem aux_ak_ae_45_43 {d m : ℕ} (hm : 1 ≤ m) {B B₁ B₂ : Finset (Site d)}
    (h : IsBoxSplit B B₁ B₂) : IsBoxSplit (blowup m B) (blowup m B₁) (blowup m B₂) := by
  obtain ⟨⟨a, b, rfl⟩, ⟨a₁, b₁, rfl⟩, ⟨a₂, b₂, rfl⟩, hdisj, hun⟩ := h
  refine ⟨⟨_, _, aux_ak_ae_45_41 hm a b⟩, ⟨_, _, aux_ak_ae_45_41 hm a₁ b₁⟩,
    ⟨_, _, aux_ak_ae_45_41 hm a₂ b₂⟩, (aux_ak_ae_45_42 hm _ _).2 hdisj, ?_⟩
  rw [← (aux_ak_ae_45_42 hm _ _).1, hun]

-- `blowup`, `Finset.map_biUnion`/`Finset.biUnion_map`, `Finset.map_map`, `smul_add`, `add_comm`.
private theorem aux_ak_ae_45_44 {d : ℕ} (m : ℕ) (B : Finset (Site d)) (z : Site d) :
    blowup m (B.map (Equiv.addRight z).toEmbedding) =
      (blowup m B).map (Equiv.addRight ((m : ℤ) • z)).toEmbedding := by
  ext y
  simp only [blowup, Finset.mem_biUnion, Finset.mem_map, Equiv.coe_toEmbedding,
    Equiv.coe_addRight]
  constructor
  · rintro ⟨w, ⟨b, hb, rfl⟩, v, hv, rfl⟩
    refine ⟨v + (m : ℤ) • b, ⟨b, hb, v, hv, rfl⟩, ?_⟩
    rw [add_assoc, ← smul_add]
  · rintro ⟨t, ⟨b, hb, v, hv, rfl⟩, ht⟩
    refine ⟨b + z, ⟨b, hb, rfl⟩, v, hv, ?_⟩
    rw [← ht, smul_add, add_assoc]


-- `Finset.card_biUnion` (pairwise disjoint blocks as in `aux_ak_ae_45_42`), `Finset.card_map`,
-- `aux_ak_ae_10`, `Finset.sum_const`, `smul_eq_mul`, `mul_comm`.
private theorem aux_blowup_disj {d m : ℕ} (hm : 1 ≤ m) {z w : Site d} (hne : z ≠ w) :
    Disjoint ((latticeCube d m).map (Equiv.addRight ((m : ℤ) • z)).toEmbedding)
      ((latticeCube d m).map (Equiv.addRight ((m : ℤ) • w)).toEmbedding) := by
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  obtain ⟨v1, hv1, h1⟩ := Finset.mem_map.1 hy1
  obtain ⟨v2, hv2, h2⟩ := Finset.mem_map.1 hy2
  refine hne (funext fun i => ?_)
  have hmz : (0 : ℤ) < (m : ℤ) := by omega
  have b1 := ((aux_ak_ae_5_1 (0 : Site d) (fun _ => (m : ℤ) - 1) v1).1 hv1 i)
  have b2 := ((aux_ak_ae_5_1 (0 : Site d) (fun _ => (m : ℤ) - 1) v2).1 hv2 i)
  simp only [Pi.zero_apply] at b1 b2
  have e1 : v1 i + (m : ℤ) * z i = y i := by
    have hh := congrFun h1 i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
  have e2 : v2 i + (m : ℤ) * w i = y i := by
    have hh := congrFun h2 i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
  have hmul : (m : ℤ) * (z i - w i) = v2 i - v1 i := by linarith
  have key : (m : ℤ) * |z i - w i| < (m : ℤ) * 1 := by
    calc (m : ℤ) * |z i - w i| = |(m : ℤ) * (z i - w i)| := by rw [abs_mul, abs_of_pos hmz]
      _ = |v2 i - v1 i| := by rw [hmul]
      _ ≤ (m : ℤ) - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      _ < (m : ℤ) * 1 := by omega
  have hlt : |z i - w i| < 1 := lt_of_mul_lt_mul_left key (le_of_lt hmz)
  have ha := (abs_lt.mp hlt).1
  have hb := (abs_lt.mp hlt).2
  omega

private theorem aux_ak_ae_45_45 {d m : ℕ} (hm : 1 ≤ m) (B : Finset (Site d)) :
    (blowup m B).card = m ^ d * B.card := by
  rw [blowup, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun z _ => by rw [Finset.card_map, aux_ak_ae_10]),
      Finset.sum_const, nsmul_eq_mul]
    exact Nat.mul_comm _ _
  · intro z _ w _ hne
    exact aux_blowup_disj hm hne


-- `latticeCube` is `latticeBox 0 (k - 1)`; `aux_ak_ae_45_41`, `smul_zero`, and
-- `m (k - 1) + m - 1 = k m - 1` (`funext`, `push_cast`, `ring`).
private theorem aux_ak_ae_45_46 {d m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    blowup m (latticeCube d k) = latticeCube d (k * m) := by
  have h := aux_ak_ae_45_41 (d := d) hm (0 : Site d) (fun _ : Fin d => (k : ℤ) - 1)
  rw [show latticeCube d k = latticeBox (0 : Site d) (fun _ : Fin d => (k : ℤ) - 1) from rfl, h]
  unfold latticeBox latticeCube
  congr 1
  all_goals (funext i; simp only [Pi.add_apply, Pi.smul_apply]; push_cast; ring)


-- `coarse`: measurability `(hmeas _).div_const _`; bounds by `hC`, `aux_ak_ae_45_45`
-- (`div_le_iff₀`, `Nat.cast_mul`, `Nat.cast_pow`); splits by `aux_ak_ae_45_43`, `hsub`,
-- `add_div`, `div_le_div_of_nonneg_right`; stationarity by `aux_ak_ae_45_44`, `hstat`.
private theorem aux_ak_ae_45_47 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ} (τ : Site d → Ω → Ω)
    (hmeas : ∀ A, Measurable (f A)) (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω)) {m : ℕ} (hm : 1 ≤ m) :
    (∀ A, Measurable (coarse f m A)) ∧
      (∀ A ω, 0 ≤ coarse f m A ω ∧ coarse f m A ω ≤ C * A.card) ∧
      (∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → coarse f m B ω ≤ coarse f m B₁ ω + coarse f m B₂ ω) ∧
      ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
        coarse f m (A.map (Equiv.addRight z).toEmbedding) ω = coarse f m A (τ ((m : ℤ) • z) ω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A
    rw [show coarse f m A = fun ω => f (blowup m A) ω / (m : ℝ) ^ d from rfl]
    exact (hmeas (blowup m A)).div_const _
  · intro A ω
    rw [show coarse f m A ω = f (blowup m A) ω / (m : ℝ) ^ d from rfl]
    refine ⟨div_nonneg (hC (blowup m A) ω).1 (by positivity), ?_⟩
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ d)]
    have h := (hC (blowup m A) ω).2
    rw [aux_ak_ae_45_45 hm A] at h
    push_cast at h
    nlinarith [h]
  · intro B B₁ B₂ ω hs
    rw [show coarse f m B ω = f (blowup m B) ω / (m : ℝ) ^ d from rfl,
      show coarse f m B₁ ω = f (blowup m B₁) ω / (m : ℝ) ^ d from rfl,
      show coarse f m B₂ ω = f (blowup m B₂) ω / (m : ℝ) ^ d from rfl]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (hsub _ _ _ ω (aux_ak_ae_45_43 hm hs)) (by positivity)
  · intro A z ω
    rw [show coarse f m (A.map (Equiv.addRight z).toEmbedding) ω =
        f (blowup m (A.map (Equiv.addRight z).toEmbedding)) ω / (m : ℝ) ^ d from rfl,
      show coarse f m A (τ ((m : ℤ) • z) ω) =
        f (blowup m A) (τ ((m : ℤ) • z) ω) / (m : ℝ) ^ d from rfl]
    rw [aux_ak_ae_45_44 m A z, hstat]


-- `cubeRatio`, `coarse`, `aux_ak_ae_45_46`, `div_div`, `Nat.cast_mul`, `mul_pow`, `mul_comm`.
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_48 {d : ℕ} (f : Finset (Site d) → Ω → ℝ) {m : ℕ} (hm : 1 ≤ m) (k : ℕ)
    (ω : Ω) : cubeRatio (coarse f m) k ω = cubeRatio f (k * m) ω := by
  unfold cubeRatio coarse
  rw [aux_ak_ae_45_46 hm, Nat.cast_mul, mul_pow, div_div, mul_comm ((m : ℝ) ^ d)]

/-! #### (F) Back to all cube sizes, and the assembly -/

-- `n ≤ (n / m + 1) m`: `Nat.lt_div_mul_add` (`0 < m`), `Nat.add_mul`, `one_mul`, `omega`.
private theorem aux_aux_ak_ae_45_49_1 {m n : ℕ} (hm : 1 ≤ m) : n ≤ (n / m + 1) * m := by
  have h : n < n / m * m + m := Nat.lt_div_mul_add (by omega : 0 < m)
  rw [Nat.add_mul, one_mul]
  omega

-- Real algebra: `F / a * (a / b) = F / b` (`field_simp`), `C (a / b - 1) = C (a - b) / b`;
-- then `← sub_div`, `div_le_div_of_nonneg_right` with `h`; `linarith`.
private theorem aux_aux_ak_ae_45_49_2 {F G C a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : F ≤ G + C * (a - b)) : F / a * (a / b) - C * (a / b - 1) ≤ G / b := by
  have h1 : F / a * (a / b) = F / b := by
    field_simp
  have h2 : C * (a / b - 1) = C * (a - b) / b := by
    field_simp
  rw [h1, h2, ← sub_div]
  exact div_le_div_of_nonneg_right (by linarith) hb.le

-- `n ≤ (n/m + 1) m` (`Nat.lt_div_mul_add`), so `aux_ak_ae_11` gives
-- `f(Q_{(n/m+1)m}) ≤ f(Q_n) + C (((n/m+1)m)^d - n^d)`; divide by `n^d > 0` (`cubeRatio`,
-- `div_le_iff₀`, `mul_div_assoc`, `field_simp`).
omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_49 {d : ℕ} {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (ω : Ω) :
    cubeRatio f ((n / m + 1) * m) ω * ((((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) -
        C * ((((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d - 1) ≤ cubeRatio f n ω := by
  have hle := aux_aux_ak_ae_45_49_1 (n := n) hm
  have h11 := aux_ak_ae_11 (d := d) hC hsub hle ω
  have hn0 : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr (by omega)) d
  have ha0 : (0 : ℝ) < (((n / m + 1) * m : ℕ) : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr (by omega)) d
  unfold cubeRatio
  exact aux_aux_ak_ae_45_49_2 ha0 hn0 h11

-- `n ≤ (n/m + 1) m ≤ n + m`: squeeze between `1` and `(1 + m/n)^d` exactly as in
-- `aux_ak_ae_42_aux`.
private theorem aux_ak_45_50_lim (d : ℕ) {m : ℕ} (_unused_hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => (1 + (m : ℝ) / (n : ℝ)) ^ d) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + (m : ℝ) / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
  simpa using h1.pow d

private theorem aux_ak_45_50_low (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d := by
  rw [eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : n ≤ (n / m + 1) * m := by
    have h := Nat.lt_div_mul_add (a := n) (b := m) hm
    rw [Nat.add_mul, one_mul]
    omega
  have hcast : (n : ℝ) ≤ (((n / m + 1) * m : ℕ) : ℝ) := by exact_mod_cast hle
  have hpow : (n : ℝ) ^ d ≤ (((n / m + 1) * m : ℕ) : ℝ) ^ d :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) hcast d
  rw [le_div_iff₀ (pow_pos hnpos d)]
  linarith

private theorem aux_ak_45_50_high (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∀ᶠ n : ℕ in atTop,
      (((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d ≤ (1 + (m : ℝ) / (n : ℝ)) ^ d := by
  rw [eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n / m + 1) * m ≤ n + m := by
    have h := Nat.div_mul_le_self n m
    rw [Nat.add_mul, one_mul]
    omega
  have hcast : (((n / m + 1) * m : ℕ) : ℝ) ≤ (n : ℝ) + (m : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hle
    rwa [Nat.cast_add] at h
  have hAn : (((n / m + 1) * m : ℕ) : ℝ) / (n : ℝ) ≤ 1 + (m : ℝ) / (n : ℝ) := by
    rw [div_le_iff₀ hnpos]
    have e : (1 + (m : ℝ) / (n : ℝ)) * (n : ℝ) = (n : ℝ) + (m : ℝ) := by
      field_simp
    rw [e]
    exact hcast
  rw [← div_pow]
  exact pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hnpos.le) hAn d

private theorem aux_ak_ae_45_50 (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => (((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d) atTop (𝓝 1) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => (1 : ℝ))
    tendsto_const_nhds (aux_ak_45_50_lim d hm) (aux_ak_45_50_low d hm) (aux_ak_45_50_high d hm)


-- `liminf_n r_n ≥ liminf_n r_{(n/m+1)m}` by `Filter.liminf_le_liminf` of `aux_ak_ae_45_49`
-- (the error terms tend to `0` by `aux_ak_ae_45_50`, bounds `aux_ak_ae_20`; an ε-argument or
-- `Filter.liminf_add_le`-type lemma), and `liminf_k r_{km} ≤ liminf_n r_{(n/m+1)m}` by
-- `Filter.Tendsto.liminf_le_liminf_comp` with `n ↦ n/m + 1` (`Nat.tendsto_div_const_atTop`,
-- `tendsto_add_atTop_nat`).  SPLIT?
private theorem aux_ak_45_51_delta (d : ℕ) {m : ℕ} (hm : 1 ≤ m) (C : ℝ) :
    Tendsto (fun n : ℕ => C * ((((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d - 1)) atTop (𝓝 0) := by
  have h := ((aux_ak_ae_45_50 d hm).sub_const 1).const_mul C
  simpa only [sub_self, mul_zero] using h

omit [MeasurableSpace Ω] in
private theorem aux_ak_45_51_stepA {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) {m : ℕ} (hm : 1 ≤ m) (ω : Ω) :
    liminf (fun k : ℕ => cubeRatio f (k * m) ω) atTop ≤
      liminf (fun n : ℕ => cubeRatio f ((n / m + 1) * m) ω) atTop := by
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  have hv : Tendsto (fun n : ℕ => n / m + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (Nat.tendsto_div_const_atTop hm0)
  refine liminf_le_of_le (u := fun k : ℕ => cubeRatio f (k * m) ω)
    (isBoundedUnder_ge_of (fun k => (aux_ak_ae_20 hd hC (k * m) ω).1)) ?_
  intro A hA
  refine le_liminf_of_le (u := fun n : ℕ => cubeRatio f ((n / m + 1) * m) ω)
    ((isBoundedUnder_le_of (fun n => (aux_ak_ae_20 hd hC ((n / m + 1) * m) ω).2)).isCoboundedUnder_ge) ?_
  obtain ⟨K, hK⟩ := eventually_atTop.mp hA
  filter_upwards [hv.eventually (eventually_ge_atTop K)] with n hn
  exact hK _ hn

omit [MeasurableSpace Ω] in
private theorem aux_ak_45_51_ev {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {m : ℕ} (hm : 1 ≤ m) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, cubeRatio f ((n / m + 1) * m) ω ≤
      cubeRatio f n ω + C * ((((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d - 1) := by
  have hm0 : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h49 := aux_ak_ae_45_49 hC hsub hm hn ω
  have hnm : n ≤ (n / m + 1) * m := by
    have hlt : n < n / m * m + m := Nat.lt_div_mul_add (Nat.pos_of_ne_zero hm0)
    rw [Nat.add_mul, one_mul]
    omega
  have hq1 : 1 ≤ (((n / m + 1) * m : ℕ) : ℝ) ^ d / (n : ℝ) ^ d := by
    rw [one_le_div (pow_pos (by exact_mod_cast hn : (0 : ℝ) < n) d)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast hnm) d
  have hB0 : 0 ≤ cubeRatio f ((n / m + 1) * m) ω := (aux_ak_ae_20 hd hC ((n / m + 1) * m) ω).1
  linarith [le_mul_of_one_le_right hB0 hq1]

omit [MeasurableSpace Ω] in
private theorem aux_ak_ae_45_51 {d : ℕ} (hd : 1 ≤ d) {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    {m : ℕ} (hm : 1 ≤ m) (ω : Ω) :
    liminf (fun k => cubeRatio f (k * m) ω) atTop ≤ liminf (fun n => cubeRatio f n ω) atTop := by
  have h1 := aux_ak_45_51_stepA hd hC hm ω
  have h2 := liminf_le_liminf_of_le_add (u := fun n : ℕ => cubeRatio f n ω)
    (v := fun n : ℕ => cubeRatio f ((n / m + 1) * m) ω)
    (isBoundedUnder_le_of (fun n => (aux_ak_ae_20 hd hC n ω).2))
    (isBoundedUnder_ge_of (fun n => (aux_ak_ae_20 hd hC ((n / m + 1) * m) ω).1))
    (aux_ak_45_51_delta d hm C) (aux_ak_45_51_ev hd hC hsub hm ω)
  exact h1.trans h2


-- As `aux_ak_ae_44_1` with `liminf` (`Measurable.liminf`, `Filter.le_liminf_of_le`,
-- `Filter.liminf_le_of_le`, `aux_ak_ae_20`).
private theorem aux_ak_ae_45_52 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ} (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) (φ : ℕ → ℕ) :
    Integrable (fun ω => liminf (fun k => cubeRatio f (φ k) ω) atTop) μ := by
  have hcu : ∀ n ω, 0 ≤ cubeRatio f n ω ∧ cubeRatio f n ω ≤ C :=
    fun n ω => aux_ak_ae_20 hd hC n ω
  have hnn : ∀ ω, 0 ≤ liminf (fun k => cubeRatio f (φ k) ω) atTop := fun ω =>
    Filter.le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n => (hcu (φ n) ω).2))
      (Filter.Eventually.of_forall (fun n => (hcu (φ n) ω).1))
  have hle : ∀ ω, liminf (fun k => cubeRatio f (φ k) ω) atTop ≤ C := fun ω =>
    Filter.liminf_le_of_le (isBoundedUnder_ge_of (fun n => (hcu (φ n) ω).1))
      (fun b hb => by
        rcases Filter.eventually_atTop.mp hb with ⟨N, hN⟩
        exact le_trans (hN _ le_rfl) (hcu (φ N) ω).2)
  exact Integrable.of_bound
    (Measurable.liminf (fun i => aux_ak_ae_21 hmeas (φ i))).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]; exact hle ω))

-- Choice of the scale: `γ := ⨅ n : ℕ, ∫ cubeRatio f (n + 1)` (bounded below by `0`:
-- `integral_nonneg`, `aux_ak_ae_20`); `exists_lt_of_ciInf_lt` at `γ < γ + δ` gives `m = n + 1`;
-- for `N ≥ 1`, `N m = (N m - 1) + 1` and `ciInf_le`.
private theorem aux_ak_ae_45_53 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} {f : Finset (Site d) → Ω → ℝ}
    {C : ℝ} (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ ω, cubeRatio f m ω ∂μ - δ ≤ ∫ ω, cubeRatio f (N * m) ω ∂μ := by
  have hnn : ∀ n, 0 ≤ ∫ ω, cubeRatio f n ω ∂μ :=
    fun n => integral_nonneg fun ω => (aux_ak_ae_20 hd hC n ω).1
  have hbdd : BddBelow (Set.range fun n : ℕ => ∫ ω, cubeRatio f (n + 1) ω ∂μ) :=
    ⟨0, fun _ ⟨n, hn⟩ => hn ▸ hnn _⟩
  obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (⨅ n : ℕ, ∫ ω, cubeRatio f (n + 1) ω ∂μ) hδ)
  refine ⟨n + 1, by omega, fun N hN => ?_⟩
  have h := ciInf_le hbdd (N * (n + 1) - 1)
  rw [show N * (n + 1) - 1 + 1 = N * (n + 1) by
    have : 1 ≤ N * (n + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega] at h
  linarith

-- Scale-`m` lower bound: `aux_ak_ae_45_40` for `F := coarse f m` and the action
-- `z ↦ τ ((m : ℤ) • z)` (`aux_ak_ae_39`, `aux_ak_ae_45_47`), `η := δ`; rewrite
-- `cubeRatio (coarse f m) k = cubeRatio f (k * m)` (`aux_ak_ae_45_48`, `funext`, `one_mul`);
-- then `integral_mono` with `aux_ak_ae_45_51`, `aux_ak_ae_45_52`, `aux_ak_ae_44_1`-type
-- integrability of the liminf; `linarith`.
private theorem aux_ak_ae_45_54 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {m : ℕ} (hm : 1 ≤ m) {δ : ℝ}
    (hmδ : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio f m ω ∂μ - δ ≤ ∫ ω, cubeRatio f (N * m) ω ∂μ)
    {α : ℝ} (hα : 0 < α) :
    ∫ ω, cubeRatio f m ω ∂μ ≤
      ∫ ω, liminf (fun n => cubeRatio f n ω) atTop ∂μ + α + C * (akMaxConst d * δ / α) := by
  obtain ⟨hσ, hσadd⟩ := aux_ak_ae_39 τ hτ hτadd m
  obtain ⟨hFm, hFC, hFsub, hFstat⟩ := aux_ak_ae_45_47 τ hmeas hC hsub hstat hm
  have hr : ∀ k ω, cubeRatio (coarse f m) k ω = cubeRatio f (k * m) ω :=
    fun k ω => aux_ak_ae_45_48 f hm k ω
  have hFη : ∀ N : ℕ, 1 ≤ N → ∫ ω, cubeRatio (coarse f m) 1 ω ∂μ - δ ≤
      ∫ ω, cubeRatio (coarse f m) N ω ∂μ := fun N hN => by
    simp only [hr, one_mul]; exact hmδ N hN
  have h := aux_ak_ae_45_40 hd (fun z => τ ((m : ℤ) • z)) hσ (fun z w ω => hσadd z w ω) hFm hFC
    hFsub hFstat hFη hα
  simp only [hr, one_mul] at h
  have hmono : ∫ ω, liminf (fun k => cubeRatio f (k * m) ω) atTop ∂μ ≤
      ∫ ω, liminf (fun n => cubeRatio f n ω) atTop ∂μ :=
    integral_mono (aux_ak_ae_45_52 hd hmeas hC (fun k => k * m))
      (aux_ak_ae_45_52 hd hmeas hC id) fun ω => aux_ak_ae_45_51 hd hC hsub hm ω
  linarith

-- Algebra: the left side equals `C ε / (2 (C + 1))` (`field_simp`, `ring_nf`), and
-- `C ≤ C + 1`; `div_le_iff₀`, `nlinarith`.
private theorem aux_ak_ae_45_55 {C K ε : ℝ} (hC : 0 ≤ C) (hK : 0 < K) (hε : 0 < ε) :
    C * (K * (ε ^ 2 / (4 * (C + 1) * K)) / (ε / 2)) ≤ ε / 2 := by
  have hC1 : 0 < C + 1 := by linarith
  have e : C * (K * (ε ^ 2 / (4 * (C + 1) * K)) / (ε / 2)) = C * ε / (2 * (C + 1)) := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith

-- DEEP.  The Akcoglu–Krengel lower bound: the liminf has integral at least the time constant
-- `inf_m ∫ f(Q_m)/m^d`.  (True: it follows from the theorem by bounded convergence.)
-- Suggested route: `S B := ∑_{z ∈ B} f {z} ∘ τ z - f B` is superadditive for box splits,
-- `0 ≤ S B ≤ 2 C |B|`, and monotone under inclusion of boxes (by `aux_ak_ae_9`); the a.e. upper
-- bound for `S` comes from a maximal inequality for superadditive processes along cubes.
-- CAUTION: Vitali/"good cube" coverings by cubes of varying size need not be reachable by
-- two-box splits (pinwheel configurations), and `hsub` is only for two-box splits.  Use cubes of
-- a nested grid (dyadic cubes of `2^d` shifted grids), where every disjoint family plus unit
-- cells is a guillotine partition, and absorb the enlargement cube ⊆ grid cube by monotonicity
-- of `S`.  Steele's one-parameter argument (`LatticeProb.ae_tendsto_gLow`, `costFn`,
-- `limsup_div_le_add_cost`) is the model for the stopping argument.
private theorem aux_ak_ae_45 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧
      ∫ ω, cubeRatio f m ω ∂μ ≤ ∫ ω, liminf (fun n => cubeRatio f n ω) atTop ∂μ + ε := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hC0 : 0 ≤ C := aux_ak_ae_2 hC ω0
  have hK := aux_ak_ae_45_0 hd
  have hδ : 0 < ε ^ 2 / (4 * (C + 1) * akMaxConst d) := by positivity
  obtain ⟨m, hm, hmδ⟩ := aux_ak_ae_45_53 (μ := μ) hd hC hδ
  refine ⟨m, hm, ?_⟩
  have h := aux_ak_ae_45_54 hd τ hτ hτadd hmeas hC hsub hstat hm hmδ (half_pos hε)
  have hs := aux_ak_ae_45_55 hC0 hK hε
  linarith

-- `limsup = liminf` a.e.: `D ω := limsup - liminf ≥ 0` (`liminf_le_limsup` with bounds from
-- `aux_ak_ae_20`, `isBoundedUnder_le_of`, `isBoundedUnder_ge_of`); `∫ D ≤ ε` for all `ε > 0` by
-- `aux_ak_ae_45` and `aux_ak_ae_44` (`integral_sub`, integrability by `Integrable.of_bound`,
-- measurability `Measurable.limsup`/`Measurable.liminf` of `aux_ak_ae_21`), so `∫ D = 0`
-- (`le_of_forall_pos_le_add`), and `integral_eq_zero_iff_of_nonneg`.  SPLIT?
private theorem aux_ak_ae_46 {d : ℕ} (hd : 1 ≤ d) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Finset (Site d) → Ω → ℝ} {C : ℝ}
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω)) (hmeas : ∀ A, Measurable (f A))
    (hC : ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω)
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω)) :
    ∀ᵐ ω ∂μ, liminf (fun n => cubeRatio f n ω) atTop = limsup (fun n => cubeRatio f n ω) atTop := by
  have hcu : ∀ n ω, 0 ≤ cubeRatio f n ω ∧ cubeRatio f n ω ≤ C :=
    fun n ω => aux_ak_ae_20 hd hC n ω
  have hls_nonneg : ∀ ω, 0 ≤ limsup (fun n => cubeRatio f n ω) atTop := fun ω =>
    Filter.le_limsup_of_le (isBoundedUnder_le_of (fun n => (hcu n ω).2))
      (fun b hb => by
        rcases Filter.eventually_atTop.mp hb with ⟨N, hN⟩
        exact le_trans (hcu (max N 1) ω).1 (hN _ (le_max_left _ _)))
  have hls_le : ∀ ω, limsup (fun n => cubeRatio f n ω) atTop ≤ C := fun ω =>
    Filter.limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n => (hcu n ω).1))
      (Filter.Eventually.of_forall (fun n => (hcu n ω).2))
  have hli_nonneg : ∀ ω, 0 ≤ liminf (fun n => cubeRatio f n ω) atTop := fun ω =>
    Filter.le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n => (hcu n ω).2))
      (Filter.Eventually.of_forall (fun n => (hcu n ω).1))
  have hli_le : ∀ ω, liminf (fun n => cubeRatio f n ω) atTop ≤ C := fun ω =>
    Filter.liminf_le_of_le (isBoundedUnder_ge_of (fun n => (hcu n ω).1))
      (fun b hb => by
        rcases Filter.eventually_atTop.mp hb with ⟨N, hN⟩
        exact le_trans (hN _ (le_max_left _ _)) (hcu (max N 1) ω).2)
  have hlimsup_meas : Measurable (fun ω => limsup (fun n => cubeRatio f n ω) atTop) :=
    Measurable.limsup (fun i => aux_ak_ae_21 hmeas i)
  have hliminf_meas : Measurable (fun ω => liminf (fun n => cubeRatio f n ω) atTop) :=
    Measurable.liminf (fun i => aux_ak_ae_21 hmeas i)
  have hls_int : Integrable (fun ω => limsup (fun n => cubeRatio f n ω) atTop) μ :=
    Integrable.of_bound hlimsup_meas.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hls_nonneg ω)]
        exact hls_le ω))
  have hli_int : Integrable (fun ω => liminf (fun n => cubeRatio f n ω) atTop) μ :=
    Integrable.of_bound hliminf_meas.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hli_nonneg ω)]
        exact hli_le ω))
  set D : Ω → ℝ := fun ω => limsup (fun n => cubeRatio f n ω) atTop -
      liminf (fun n => cubeRatio f n ω) atTop with hD
  have hDnn : ∀ ω, 0 ≤ D ω := fun ω => by
    have hle := liminf_le_limsup
      (isBoundedUnder_le_of (fun n => (hcu n ω).2))
      (isBoundedUnder_ge_of (fun n => (hcu n ω).1))
    simp only [hD]
    linarith
  have hDint : Integrable D μ :=
    Integrable.of_bound (hlimsup_meas.sub hliminf_meas).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hDnn ω)]
        simp only [hD]
        linarith [hls_le ω, hli_nonneg ω]))
  have hDle : ∀ ε : ℝ, 0 < ε → ∫ ω, D ω ∂μ ≤ ε := fun ε hε => by
    obtain ⟨m, hm1, hme⟩ := aux_ak_ae_45 hd τ hτ hτadd hmeas hC hsub hstat hε
    have hup := aux_ak_ae_44 hd τ hτ hτadd hmeas hC hsub hstat hm1
    simp only [hD]
    rw [integral_sub hls_int hli_int]
    linarith [hme, hup]
  have hDz : ∫ ω, D ω ∂μ = 0 :=
    le_antisymm
      (le_of_forall_pos_le_add (fun ε hε => by
        have := hDle ε hε
        linarith))
      (integral_nonneg (fun ω => hDnn ω))
  have hDae : ∀ᵐ ω ∂μ, D ω = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => hDnn ω) hDint).1 hDz
  filter_upwards [hDae] with ω hω
  simp only [hD] at hω
  linarith


/-- The almost sure half. -/
theorem akcoglu_krengel (μ : Measure Ω) [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hτadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    (f : Finset (Site d) → Ω → ℝ) (hmeas : ∀ A, Measurable (f A))
    (hstat : ∀ (A : Finset (Site d)) (z : Site d) (ω : Ω),
      f (A.map (Equiv.addRight z).toEmbedding) ω = f A (τ z ω))
    (hbd : ∃ C, ∀ A ω, 0 ≤ f A ω ∧ f A ω ≤ C * A.card)
    (hsub : ∀ B B₁ B₂ ω, IsBoxSplit B B₁ B₂ → f B ω ≤ f B₁ ω + f B₂ ω) :
    ∃ L : Ω → ℝ, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => f (latticeCube d n) ω / (n : ℝ) ^ d) atTop (𝓝 (L ω)) := by
  obtain ⟨C, hC⟩ := hbd
  refine ⟨fun ω => limsup (fun n => cubeRatio f n ω) atTop, ?_⟩
  filter_upwards [aux_ak_ae_46 hd τ hτ hτadd hmeas hC hsub hstat] with ω hω
  have hb := fun n => aux_ak_ae_20 hd hC n ω
  exact tendsto_of_liminf_eq_limsup hω rfl (isBoundedUnder_le_of fun n => (hb n).2)
    (isBoundedUnder_ge_of fun n => (hb n).1)

end LatticeProb
