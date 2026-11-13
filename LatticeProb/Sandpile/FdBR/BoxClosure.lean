import LatticeProb.Site

/-!
# Two-neighbour closed connected sets are boxes

A finite set `T` of sites of `ℤ^d` that is connected in the nearest-neighbour graph
and closed under the rule "a site with two distinct neighbours in `T` lies in `T`"
is an integer box.  Among the boxes inside `T` that contain the base point, a box of
maximal cardinality is taken.  A site of `T` adjacent to such a box and outside it
forces a strictly larger box into `T`, so a site of `T` outside the box cannot exist.
-/

namespace LatticeProb.Sandpile

open LatticeProb

/-- A site with two distinct lattice neighbours in `T` lies in `T`. -/
def TwoNeighborClosed {d : ℕ} (T : Set (Site d)) : Prop :=
  ∀ x y z : Site d, (lattice d).Adj x y → (lattice d).Adj x z → y ≠ z → y ∈ T → z ∈ T → x ∈ T

/-- The integer box `[a, b]` of sites. -/
def boxSet {d : ℕ} (a b : Fin d → ℤ) : Set (Site d) :=
  {x | ∀ l, a l ≤ x l ∧ x l ≤ b l}

theorem mem_boxSet {d : ℕ} {a b : Fin d → ℤ} {x : Site d} :
    x ∈ boxSet a b ↔ ∀ l, a l ≤ x l ∧ x l ≤ b l :=
  Iff.rfl

theorem lattice_adj_iff {d : ℕ} {x y : Site d} :
    (lattice d).Adj x y ↔ ∃ i : Fin d, y = x + unit i ∨ x = y + unit i :=
  Iff.rfl

/-- In the layer just outside a box `[a, b]` in the coordinate `i`, one site of `T` forces
every site of the layer into `T`, as long as the box lies in `T`. -/
theorem layer_subset {d : ℕ} {T : Set (Site d)} (hclosed : TwoNeighborClosed T)
    {a b : Fin d → ℤ} (hB : boxSet a b ⊆ T) {i : Fin d} {p q : ℤ}
    (hp : a i ≤ p ∧ p ≤ b i) (hpq : q = p + 1 ∨ q = p - 1)
    {z : Site d} (hzT : z ∈ T) (hzi : z i = q)
    (hzr : ∀ l, l ≠ i → a l ≤ z l ∧ z l ≤ b l)
    (w : Site d) (hwi : w i = q) (hwr : ∀ l, l ≠ i → a l ≤ w l ∧ w l ≤ b l) :
    w ∈ T := by
  have step : ∀ v v' : Site d, v i = q → v' i = q → (lattice d).Adj v v' →
      (∀ l, l ≠ i → a l ≤ v l ∧ v l ≤ b l) → v' ∈ T → v ∈ T := by
    intro v v' hv hv' hadj hvr hv'T
    have hu : Function.update v i p ∈ boxSet a b := by
      rw [mem_boxSet]
      intro l
      by_cases hl : l = i
      · rw [hl, Function.update_self]
        exact hp
      · rw [Function.update_of_ne hl]
        exact hvr l hl
    have hadj' : (lattice d).Adj v (Function.update v i p) := by
      refine lattice_adj_iff.2 ⟨i, ?_⟩
      rcases hpq with h | h
      · right
        funext l
        by_cases hl : l = i
        · rw [hl]
          simp [unit, hv, h]
        · simp [unit, hl, Function.update_of_ne]
      · left
        funext l
        by_cases hl : l = i
        · rw [hl]
          simp [unit, hv, h]
        · simp [unit, hl, Function.update_of_ne]
    have hne : v' ≠ Function.update v i p := by
      intro h
      have h1 := congrFun h i
      rw [hv', Function.update_self] at h1
      rcases hpq with h2 | h2 <;> omega
    exact hclosed v v' (Function.update v i p) hadj hadj' hne hv'T (hB hu)
  suffices H : ∀ n : ℕ, ∀ v : Site d, v i = q → (∀ l, l ≠ i → a l ≤ v l ∧ v l ≤ b l) →
      ∑ l, (v l - z l).natAbs = n → v ∈ T by
    exact H _ w hwi hwr rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv hvr hn
    by_cases hvz : v = z
    · rw [hvz]
      exact hzT
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ z j := by
      by_contra hcon
      push Not at hcon
      exact hvz (funext hcon)
    have hji : j ≠ i := by
      rintro rfl
      exact hj (hv.trans hzi.symm)
    obtain ⟨s, hs, hdir⟩ :
        ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (s = 1 ∧ v j < z j ∨ s = -1 ∧ z j < v j) := by
      rcases lt_or_gt_of_ne hj with h | h
      · exact ⟨1, Or.inl rfl, Or.inl ⟨rfl, h⟩⟩
      · exact ⟨-1, Or.inr rfl, Or.inr ⟨rfl, h⟩⟩
    have hvj := hvr j hji
    have hzj := hzr j hji
    obtain ⟨v', hv'⟩ : ∃ v' : Site d, v' = Function.update v j (v j + s) := ⟨_, rfl⟩
    have hv'j : v' j = v j + s := by
      rw [hv', Function.update_self]
    have hv'l : ∀ l, l ≠ j → v' l = v l := fun l hl => by
      rw [hv', Function.update_of_ne hl]
    have hv'i : v' i = q := by
      rw [hv'l i (Ne.symm hji), hv]
    have hadj : (lattice d).Adj v v' := by
      refine lattice_adj_iff.2 ⟨j, ?_⟩
      rcases hs with rfl | rfl
      · left
        funext l
        by_cases hl : l = j
        · rw [hl]
          simp [unit, hv'j]
        · simp [unit, hl, hv'l l hl]
      · right
        funext l
        by_cases hl : l = j
        · rw [hl]
          simp [unit, hv'j]
        · simp [unit, hl, hv'l l hl]
    have hv'r : ∀ l, l ≠ i → a l ≤ v' l ∧ v' l ≤ b l := by
      intro l hl
      by_cases hlj : l = j
      · rw [hlj, hv'j]
        constructor <;> omega
      · rw [hv'l l hlj]
        exact hvr l hl
    have hlt : ∑ l, (v' l - z l).natAbs < ∑ l, (v l - z l).natAbs := by
      apply Finset.sum_lt_sum
      · intro l _
        show (v' l - z l).natAbs ≤ (v l - z l).natAbs
        by_cases hl : l = j
        · rw [hl, hv'j]
          omega
        · rw [hv'l l hl]
      · exact ⟨j, Finset.mem_univ _, by
          show (v' j - z j).natAbs < (v j - z j).natAbs
          rw [hv'j]
          omega⟩
    have hv'T : v' ∈ T :=
      ih (∑ l, (v' l - z l).natAbs) (by rw [hn] at hlt; exact hlt) v' hv'i hv'r rfl
    exact step v v' hv hv'i hadj hvr hv'T

/-- A box `[a, b] ⊆ T` with a site `z ∈ T` outside it that is adjacent to a site `y` of the box
is contained in a strictly larger box inside `T`. -/
theorem exists_box_ssubset_of_adj {d : ℕ} {T : Set (Site d)} (hclosed : TwoNeighborClosed T)
    {a b : Fin d → ℤ} (hB : boxSet a b ⊆ T) {y z : Site d} (hy : y ∈ boxSet a b)
    (hzT : z ∈ T) (hzB : z ∉ boxSet a b) (hadj : (lattice d).Adj y z) :
    ∃ a' b' : Fin d → ℤ, boxSet a b ⊂ boxSet a' b' ∧ boxSet a' b' ⊆ T := by
  have hyl := mem_boxSet.1 hy
  obtain ⟨i, hz | hy'⟩ := lattice_adj_iff.1 hadj
  · -- `z = y + unit i`: the layer above the top face `b i`
    have hzl : ∀ l, l ≠ i → z l = y l := by
      intro l hl
      rw [hz]
      simp [unit, hl]
    have hzi : z i = y i + 1 := by
      rw [hz]
      simp [unit]
    have hzr : ∀ l, l ≠ i → a l ≤ z l ∧ z l ≤ b l := fun l hl => by
      rw [hzl l hl]
      exact hyl l
    have hzi' : z i = b i + 1 := by
      by_contra hne
      apply hzB
      rw [mem_boxSet]
      intro l
      by_cases hl : l = i
      · rw [hl]
        have := hyl i
        constructor <;> omega
      · exact hzr l hl
    have hbu : ∀ l, b l ≤ (b + unit i) l := by
      intro l
      by_cases hl : l = i
      · rw [hl]
        simp [unit]
      · simp [unit, hl]
    have hbl : ∀ l, l ≠ i → (b + unit i) l = b l := fun l hl => by
      simp [unit, hl]
    have hbi : (b + unit i) i = b i + 1 := by
      simp [unit]
    have hzmem : z ∈ boxSet a (b + unit i) := by
      rw [mem_boxSet]
      intro l
      by_cases hl : l = i
      · rw [hl, hbi]
        have := hyl i
        constructor <;> omega
      · exact ⟨(hzr l hl).1, (hzr l hl).2.trans (hbu l)⟩
    refine ⟨a, b + unit i,
      Set.ssubset_iff_subset_ne.2 ⟨?_, fun h => hzB (by rw [h]; exact hzmem)⟩, ?_⟩
    · intro x hx
      rw [mem_boxSet] at hx ⊢
      intro l
      exact ⟨(hx l).1, (hx l).2.trans (hbu l)⟩
    · intro x hx
      rw [mem_boxSet] at hx
      by_cases hxi : x i ≤ b i
      · refine hB (mem_boxSet.2 fun l => ?_)
        by_cases hl : l = i
        · rw [hl]
          exact ⟨(hx i).1, hxi⟩
        · have h2 := (hx l).2
          rw [hbl l hl] at h2
          exact ⟨(hx l).1, h2⟩
      · have hxi' : x i = b i + 1 := by
          have h2 := (hx i).2
          rw [hbi] at h2
          omega
        refine layer_subset hclosed hB ⟨(hyl i).1.trans (hyl i).2, le_rfl⟩ (Or.inl rfl)
          hzT hzi' hzr x hxi' fun l hl => ?_
        have h2 := (hx l).2
        rw [hbl l hl] at h2
        exact ⟨(hx l).1, h2⟩
  · -- `y = z + unit i`: the layer below the bottom face `a i`
    have hzl : ∀ l, l ≠ i → z l = y l := by
      intro l hl
      rw [hy']
      simp [unit, hl]
    have hzi : y i = z i + 1 := by
      rw [hy']
      simp [unit]
    have hzr : ∀ l, l ≠ i → a l ≤ z l ∧ z l ≤ b l := fun l hl => by
      rw [hzl l hl]
      exact hyl l
    have hzi' : z i = a i - 1 := by
      by_contra hne
      apply hzB
      rw [mem_boxSet]
      intro l
      by_cases hl : l = i
      · rw [hl]
        have := hyl i
        constructor <;> omega
      · exact hzr l hl
    have hbu : ∀ l, (a - unit i) l ≤ a l := by
      intro l
      by_cases hl : l = i
      · rw [hl]
        simp [unit]
      · simp [unit, hl]
    have hbl : ∀ l, l ≠ i → (a - unit i) l = a l := fun l hl => by
      simp [unit, hl]
    have hai : (a - unit i) i = a i - 1 := by
      simp [unit]
    have hzmem : z ∈ boxSet (a - unit i) b := by
      rw [mem_boxSet]
      intro l
      by_cases hl : l = i
      · rw [hl, hai]
        have := hyl i
        constructor <;> omega
      · exact ⟨(hbu l).trans (hzr l hl).1, (hzr l hl).2⟩
    refine ⟨a - unit i, b,
      Set.ssubset_iff_subset_ne.2 ⟨?_, fun h => hzB (by rw [h]; exact hzmem)⟩, ?_⟩
    · intro x hx
      rw [mem_boxSet] at hx ⊢
      intro l
      exact ⟨(hbu l).trans (hx l).1, (hx l).2⟩
    · intro x hx
      rw [mem_boxSet] at hx
      by_cases hxi : a i ≤ x i
      · refine hB (mem_boxSet.2 fun l => ?_)
        by_cases hl : l = i
        · rw [hl]
          exact ⟨hxi, (hx i).2⟩
        · have h2 := (hx l).1
          rw [hbl l hl] at h2
          exact ⟨h2, (hx l).2⟩
      · have hxi' : x i = a i - 1 := by
          have h2 := (hx i).1
          rw [hai] at h2
          omega
        refine layer_subset hclosed hB ⟨le_rfl, (hyl i).1.trans (hyl i).2⟩ (Or.inr rfl)
          hzT hzi' hzr x hxi' fun l hl => ?_
        have h2 := (hx l).1
        rw [hbl l hl] at h2
        exact ⟨h2, (hx l).2⟩

/-- A finite set of sites that is connected in the nearest-neighbour graph and closed under
`TwoNeighborClosed` is an integer box. -/
theorem eq_box_of_twoNeighborClosed {d : ℕ} {T : Set (Site d)} (hfin : T.Finite) {x₀ : Site d}
    (hx₀ : x₀ ∈ T) (hclosed : TwoNeighborClosed T)
    (hconn : ∀ x ∈ T, Relation.ReflTransGen (fun y z => y ∈ T ∧ z ∈ T ∧ (lattice d).Adj y z) x₀ x) :
    ∃ a b : Fin d → ℤ, T = {x : Site d | ∀ i : Fin d, a i ≤ x i ∧ x i ≤ b i} := by
  have hne : {k : ℕ | ∃ a b : Fin d → ℤ, x₀ ∈ boxSet a b ∧ boxSet a b ⊆ T ∧
      (boxSet a b).ncard = k}.Nonempty := by
    refine ⟨(boxSet x₀ x₀).ncard, x₀, x₀, mem_boxSet.2 fun l => ⟨le_rfl, le_rfl⟩, ?_, rfl⟩
    intro x hx
    rw [mem_boxSet] at hx
    have hxe : x = x₀ := funext fun l => le_antisymm (hx l).2 (hx l).1
    rw [hxe]
    exact hx₀
  have hbdd : BddAbove {k : ℕ | ∃ a b : Fin d → ℤ, x₀ ∈ boxSet a b ∧ boxSet a b ⊆ T ∧
      (boxSet a b).ncard = k} := by
    refine ⟨T.ncard, ?_⟩
    rintro k ⟨a, b, -, hsub, rfl⟩
    exact Set.ncard_le_ncard hsub hfin
  obtain ⟨a, b, hx₀B, hBT, hK⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ a' b' : Fin d → ℤ, x₀ ∈ boxSet a' b' → boxSet a' b' ⊆ T →
      (boxSet a' b').ncard ≤ (boxSet a b).ncard := by
    intro a' b' h1 h2
    rw [hK]
    exact le_csSup hbdd ⟨a', b', h1, h2, rfl⟩
  have path : ∀ x, Relation.ReflTransGen (fun y z => y ∈ T ∧ z ∈ T ∧ (lattice d).Adj y z) x₀ x →
      x ∈ boxSet a b ∨
        ∃ y z, y ∈ boxSet a b ∧ z ∉ boxSet a b ∧ (y ∈ T ∧ z ∈ T ∧ (lattice d).Adj y z) := by
    intro x hx
    induction hx with
    | refl => exact Or.inl hx₀B
    | @tail y c _ hyc ih =>
      by_cases hc : c ∈ boxSet a b
      · exact Or.inl hc
      · rcases ih with hy | ⟨u, v, hu, hv, huv⟩
        · exact Or.inr ⟨y, c, hy, hc, hyc⟩
        · exact Or.inr ⟨u, v, hu, hv, huv⟩
  have hsub : T ⊆ boxSet a b := by
    intro x hx
    by_contra hxB
    rcases path x (hconn x hx) with h | ⟨y, z, hy, hz, hyz⟩
    · exact hxB h
    · obtain ⟨-, hzT, hadj⟩ := hyz
      obtain ⟨a', b', hss, hsT⟩ := exists_box_ssubset_of_adj hclosed hBT hy hzT hz hadj
      have h1 := Set.ncard_lt_ncard hss (hfin.subset hsT)
      have h2 := hmax a' b' (hss.subset hx₀B) hsT
      omega
  exact ⟨a, b, Set.Subset.antisymm hsub hBT⟩

end LatticeProb.Sandpile
