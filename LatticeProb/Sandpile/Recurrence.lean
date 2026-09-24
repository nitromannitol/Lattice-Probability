/-
The recurrence toolkit for the classical integer sandpile, moved from
`Exploding-Sandpiles`'s `Exploding/Support/Vocab.lean` (the `RecurrentOn`/
`Recurrent` predicates), `Exploding/Support/SubRec*.lean`,
`Exploding/Support/SubMax.lean`, `Exploding/Support/SubTopple.lean` (the
`recOdo` toolkit), and `Exploding/Frozen/Recurrence.lean` (Proposition 7.3:
the constant background `d` is recurrent).  That last file is one of only two
sorry-free files under `Exploding/Frozen/` (the other being the file this
theorem itself needs nothing further from), independently checked here to be
free of `sorry` in its full dependency closure with `#print axioms`.

`η` restricted to a finite domain `V` is *recurrent* if firing the outer
boundary `∂V` once each makes every site of `V` eventually topple: the
`Vᶜ`-frozen odometer started from `w₀ = 1_{∂V}` reaches `1` on all of `V` by
time `|V|`.  The proof that the constant background `η ≡ d` has this property
is the paper's: among the untoppled sites of `V`, one maximizing the
coordinate sum has every `x + eᵢ` neighbour already toppled (each such
neighbour is either toppled inside `V` or lies in `∂V`, toppled from the
start), so it has at least `d` toppled neighbours and topples next; this
finds one new toppled site of `V` at every step before `V` is full, so `|V|`
steps suffice.  This coordinate-maximizer argument is specific to the
lattice, unlike the two predicates it instantiates.

`Random-Abelian-Sandpile`'s `RandomSandpile/Support/Basic.lean:224-233` has
its own, differently-named `IsRecurrent η A`: a configuration is recurrent
there when it decomposes as `2d - 1 + s + Δu` for a legal toppling `u`, the
least-action-principle characterization of recurrence.  `RecurrentOn`/
`Recurrent` below are the burning-test characterization instead (fire `∂V`
once and check that `V` fully topples).  These are the two classically
equivalent formulations of the same notion (Dhar); no equivalence between
them is proved in either repo, so they are recorded here as two vocabularies
for one concept, not merged.
-/
import LatticeProb.Sandpile.Waves
import LatticeProb.Graph.Boundary

namespace LatticeProb.Sandpile

open LatticeProb
open scoped Classical

variable {d : ℕ}

/-! ### Recurrence -/

/-- `η` restricted to the finite domain `V` is *recurrent*: the `Vᶜ`-frozen
odometer from `w₀ = 1_{∂V}` is `1` on `V` from time `|V|` on. -/
def RecurrentOn (η : Site d → ℤ) (V : Finset (Site d)) : Prop :=
  ∀ t : ℕ, V.card ≤ t → ∀ x ∈ V,
    fodo ((↑V : Set (Site d))ᶜ) η
      (fun y => if y ∈ Graph.outerBoundary (lattice d) (↑V : Set (Site d)) then 1 else 0) t x = 1

/-- `η : ℤ^d → ℤ` is *recurrent* if its restriction to every finite domain
is. -/
def Recurrent (η : Site d → ℤ) : Prop := ∀ V : Finset (Site d), RecurrentOn η V

/-! ### The recurrence odometer for a constant background -/

/-- The `Vᶜ`-frozen odometer of the recurrence argument: background `d`,
initial odometer the indicator of `∂V`. -/
noncomputable def recOdo (d : ℕ) (V : Finset (Site d)) : ℕ → Site d → ℤ :=
  fodo ((↑V : Set (Site d))ᶜ) (fun _ => (d : ℤ))
    (fun y => if y ∈ Graph.outerBoundary (lattice d) (↑V : Set (Site d)) then 1 else 0)

@[simp] theorem recOdo_zero (d : ℕ) (V : Finset (Site d)) (x : Site d) :
    recOdo d V 0 x = if x ∈ Graph.outerBoundary (lattice d) (↑V : Set (Site d)) then 1 else 0 :=
  rfl

theorem recOdo_succ (d : ℕ) (V : Finset (Site d)) (t : ℕ) (x : Site d) :
    recOdo d V (t + 1) x =
      if x ∈ (↑V : Set (Site d))ᶜ then
        (if x ∈ Graph.outerBoundary (lattice d) (↑V : Set (Site d)) then 1 else 0)
      else recOdo d V t x +
        (if 2 * (d : ℤ) ≤ (d : ℤ) + lap (recOdo d V t) x then 1 else 0) := by
  rw [recOdo, fodo_succ]
  by_cases hx : x ∈ (↑V : Set (Site d))ᶜ
  · rw [if_pos hx, if_pos hx]
  · rw [if_neg hx, if_neg hx]
    congr 1

/-- Off `V` the recurrence odometer never moves. -/
theorem recOdo_of_notMem (d : ℕ) (V : Finset (Site d)) (t : ℕ) {x : Site d}
    (hx : x ∉ V) :
    recOdo d V t x = if x ∈ Graph.outerBoundary (lattice d) (↑V : Set (Site d)) then 1 else 0 :=
  fodo_of_mem _ _ _ _ (by simpa using hx)

/-- On `V` the recurrence odometer starts at `0`. -/
theorem recOdo_zero_of_mem (d : ℕ) (V : Finset (Site d)) {x : Site d} (hx : x ∈ V) :
    recOdo d V 0 x = 0 := by
  rw [recOdo_zero, if_neg (fun h => h.1 hx)]

/-- The recurrence odometer is nonnegative. -/
theorem recOdo_nonneg (d : ℕ) (V : Finset (Site d)) (t : ℕ) (x : Site d) :
    0 ≤ recOdo d V t x :=
  fodo_nonneg _ _ _ (fun y => by
    by_cases hy : y ∈ Graph.outerBoundary (lattice d) (↑V : Set (Site d)) <;> simp [hy]) t x

/-- The recurrence odometer is nondecreasing in time. -/
theorem recOdo_mono (d : ℕ) (V : Finset (Site d)) (t : ℕ) (x : Site d) :
    recOdo d V t x ≤ recOdo d V (t + 1) x := by
  rw [recOdo_succ]
  by_cases hx : x ∈ (↑V : Set (Site d))ᶜ
  · rw [if_pos hx, recOdo_of_notMem d V t (by simpa using hx)]
  · rw [if_neg hx]
    split_ifs <;> omega

/-- The recurrence odometer is at most `1` on `V`. -/
theorem recOdo_le_one (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ) {x : Site d}
    (hx : x ∈ V) : recOdo d V t x ≤ 1 := by
  have key : ∀ t : ℕ, ∀ x ∈ V, recOdo d V t x ≤ 1 := by
    intro t
    induction t with
    | zero => intro x hx; rw [recOdo_zero_of_mem d V hx]; omega
    | succ t ih =>
      intro x hx
      rw [recOdo_succ, if_neg (by simpa using hx)]
      have hnb : nbrSumZ (recOdo d V t) x ≤ 2 * (d : ℤ) := by
        rw [nbrSumZ]
        have h2 : ∀ i : Fin d, recOdo d V t (x + unit i) + recOdo d V t (x - unit i) ≤ 2 := by
          intro i
          have h1 : recOdo d V t (x + unit i) ≤ 1 := by
            by_cases h : x + unit i ∈ V
            · exact ih _ h
            · rw [recOdo_of_notMem d V t h]; split_ifs <;> omega
          have h3 : recOdo d V t (x - unit i) ≤ 1 := by
            by_cases h : x - unit i ∈ V
            · exact ih _ h
            · rw [recOdo_of_notMem d V t h]; split_ifs <;> omega
          linarith
        calc ∑ i : Fin d, (recOdo d V t (x + unit i) + recOdo d V t (x - unit i))
            ≤ ∑ _ : Fin d, (2 : ℤ) := Finset.sum_le_sum (fun i _ => h2 i)
          _ = 2 * (d : ℤ) := by simp; ring
      split_ifs with hc
      · have hz : recOdo d V t x = 0 := by
          by_contra hne
          have hge : 1 ≤ recOdo d V t x := by
            have := recOdo_nonneg d V t x; omega
          rw [lap] at hc
          nlinarith [hc, hnb, hge]
        omega
      · simpa using ih x hx
  exact key t x hx

/-- The set of toppled sites of `V` grows with time. -/
theorem recOdo_subset_succ (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ) :
    V.filter (fun x => recOdo d V t x = 1) ⊆ V.filter (fun x => recOdo d V (t + 1) x = 1) := by
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have h1 := recOdo_mono d V t x
  have h2 := recOdo_le_one d hd V (t + 1) hx.1
  omega

/-- Among the sites of `V` that have not yet toppled, one maximizing the
coordinate sum has all its `+eᵢ` neighbours toppled. -/
theorem exists_max_unfilled (d : ℕ) (V : Finset (Site d)) (t : ℕ)
    (hnot : ∃ x ∈ V, recOdo d V t x = 0) :
    ∃ x ∈ V, recOdo d V t x = 0 ∧ ∀ i : Fin d, 1 ≤ recOdo d V t (x + unit i) := by
  obtain ⟨x0, hx0V, hx00⟩ := hnot
  have hs : (V.filter (fun x => recOdo d V t x = 0)).Nonempty :=
    ⟨x0, Finset.mem_filter.mpr ⟨hx0V, hx00⟩⟩
  obtain ⟨x, hxs, hmax⟩ := Finset.exists_max_image (V.filter (fun x => recOdo d V t x = 0))
    (fun x => ∑ i, x i) hs
  rw [Finset.mem_filter] at hxs
  refine ⟨x, hxs.1, hxs.2, fun i => ?_⟩
  by_cases hmem : x + unit i ∈ V
  · have h1 : recOdo d V t (x + unit i) ≠ 0 := by
      intro hz
      have h2 := hmax (x + unit i) (Finset.mem_filter.mpr ⟨hmem, hz⟩)
      have h3 : (∑ l, (x + unit i) l) = (∑ l, x l) + 1 := by
        simp [Pi.add_apply, unit, Finset.sum_add_distrib]
      omega
    have hnn := recOdo_nonneg d V t (x + unit i)
    omega
  · have hb : x + unit i ∈ Graph.outerBoundary (lattice d) (↑V : Set (Site d)) :=
      ⟨hmem, x, hxs.1, adj_add_unit x i⟩
    rw [recOdo_of_notMem d V t hmem, if_pos hb]

/-- A site of `V` with no toppling yet and all `+eᵢ` neighbours toppled
topples at the next step. -/
theorem recOdo_topple (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ) {x : Site d}
    (hx : x ∈ V) (h0 : recOdo d V t x = 0)
    (hup : ∀ i : Fin d, 1 ≤ recOdo d V t (x + unit i)) :
    recOdo d V (t + 1) x = 1 := by
  rw [recOdo_succ, if_neg (by simpa using hx), h0, zero_add]
  rw [if_pos]
  rw [lap, nbrSumZ, h0, mul_zero, sub_zero]
  have hsum : (d : ℤ) ≤ ∑ i : Fin d, (recOdo d V t (x + unit i) + recOdo d V t (x - unit i)) := by
    have hle : (∑ _ : Fin d, (1 : ℤ)) ≤
        ∑ i : Fin d, (recOdo d V t (x + unit i) + recOdo d V t (x - unit i)) := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := hup i
      have h2 := recOdo_nonneg d V t (x - unit i)
      linarith
    simpa using hle
  have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  linarith [hd1]

/-- While some site of `V` has not toppled, the set of toppled sites of `V`
grows strictly. -/
theorem recOdo_filter_grows (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ)
    (h : ∃ x ∈ V, recOdo d V t x = 0) :
    (V.filter (fun x => recOdo d V t x = 1)).card <
      (V.filter (fun x => recOdo d V (t + 1) x = 1)).card := by
  obtain ⟨x, hxV, hx0, hup⟩ := exists_max_unfilled d V t h
  have hx1 : x ∈ V.filter (fun x => recOdo d V (t+1) x = 1) :=
    Finset.mem_filter.mpr ⟨hxV, recOdo_topple d hd V t hxV hx0 hup⟩
  have hxnot : x ∉ V.filter (fun x => recOdo d V t x = 1) := fun hh => by
    rw [Finset.mem_filter] at hh; omega
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨recOdo_subset_succ d hd V t, fun heq => hxnot (heq ▸ hx1)⟩

/-- After `min t |V|` steps, at least `min t |V|` sites of `V` have toppled. -/
theorem recOdo_card_le (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ) :
    min t V.card ≤ (V.filter (fun x => recOdo d V t x = 1)).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    by_cases h : ∃ x ∈ V, recOdo d V t x = 0
    · have := recOdo_filter_grows d hd V t h
      omega
    · simp only [not_exists, not_and] at h
      have hV : V.filter (fun x => recOdo d V t x = 1) = V := by
        apply Finset.ext
        intro x
        rw [Finset.mem_filter]
        constructor
        · exact fun hh => hh.1
        · intro hx
          refine ⟨hx, ?_⟩
          have h1 := recOdo_le_one d hd V t hx
          have h2 := recOdo_nonneg d V t x
          have h3 := h x hx
          omega
      have hc : (V.filter (fun x => recOdo d V t x = 1)).card = V.card := by rw [hV]
      have hmono := Finset.card_le_card (recOdo_subset_succ d hd V t)
      omega

/-- **Proposition 7.3** (`exploding.tex:1906-1908`).  For every `d ≥ 1`,
`η : ℤ^d → {d}` is recurrent. -/
theorem recurrent_const (d : ℕ) (hd : 1 ≤ d) : Recurrent (fun _ : Site d => (d : ℤ)) := by
  intro V t ht x hx
  have h1 : min t V.card ≤ (V.filter (fun x => recOdo d V t x = 1)).card := recOdo_card_le d hd V t
  have h2 : (V.filter (fun x => recOdo d V t x = 1)).card ≤ V.card := Finset.card_filter_le _ _
  have h3 : V.card ≤ t := ht
  have h4 : min t V.card = V.card := by rw [Nat.min_comm]; exact min_eq_left h3
  have h5 : (V.filter (fun x => recOdo d V t x = 1)).card = V.card := le_antisymm h2 (h4 ▸ h1)
  have h6 : V.filter (fun x => recOdo d V t x = 1) = V :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [h5])
  have h7 : x ∈ V.filter (fun x => recOdo d V t x = 1) := by rw [h6]; exact hx
  rw [Finset.mem_filter] at h7
  exact h7.2

end LatticeProb.Sandpile
