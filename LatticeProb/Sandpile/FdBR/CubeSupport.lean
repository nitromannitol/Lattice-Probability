import LatticeProb.Sandpile.FdBR.BoxClosure
import LatticeProb.Sandpile.RadiusConsequences

/-!
# The positive support of the parallel toppling odometer is an integer cube

Let `w = podo s0 T` be the parallel toppling odometer of the background `2d - 2` with `N ≥ 2`
extra chips at the origin, at a time `T` where the sandpile is stable and the positive support
`{x | 0 < w x}` is finite. Then the support is an integer cube `{x | ∀ i, |x i| ≤ r}`.

The origin lies in the support. The support is closed under two-neighbour completion, since a
site with two distinct neighbours of positive odometer has Laplacian at least `2` and cannot be
stable. The support is connected: the odometer restricted to the component of the origin is
stable and dominates `w` by the least action principle. A finite connected two-neighbour closed
set is a box (`eq_box_of_twoNeighborClosed`). Coordinate reflections and permutations commute
with the parallel dynamics, which makes the box a cube.
-/

namespace LatticeProb.Sandpile

open LatticeProb

namespace FdBRCube

variable {d : ℕ}

/-! ### Neighbours and the Laplacian -/

theorem adj_iff_exists_unit {x z : Site d} :
    (lattice d).Adj x z ↔ ∃ i : Fin d, z = x + unit i ∨ z = x - unit i := by
  rw [lattice_adj_iff]
  exact exists_congr fun i => or_congr Iff.rfl (by rw [eq_sub_iff_add_eq]; exact eq_comm)

theorem adj_add_unit (x : Site d) (i : Fin d) : (lattice d).Adj x (x + unit i) :=
  lattice_adj_iff.2 ⟨i, Or.inl rfl⟩

theorem adj_sub_unit (x : Site d) (i : Fin d) : (lattice d).Adj x (x - unit i) :=
  lattice_adj_iff.2 ⟨i, Or.inr (sub_add_cancel x (unit i)).symm⟩

theorem summand_le_nbrSumZ {w : Site d → ℤ} (hw : ∀ y, 0 ≤ w y) (x : Site d) (i : Fin d) :
    w (x + unit i) + w (x - unit i) ≤ nbrSumZ w x :=
  Finset.single_le_sum (f := fun k : Fin d => w (x + unit k) + w (x - unit k))
    (fun _ _ => add_nonneg (hw _) (hw _)) (Finset.mem_univ i)

/-- Two distinct neighbours of `x` contribute their values to the neighbour sum of a nonnegative
function. -/
theorem nbrSumZ_ge_of_adj {w : Site d → ℤ} (hw : ∀ y, 0 ≤ w y) {x y z : Site d}
    (hy : (lattice d).Adj x y) (hz : (lattice d).Adj x z) (hyz : y ≠ z) :
    w y + w z ≤ nbrSumZ w x := by
  obtain ⟨i, hi⟩ := adj_iff_exists_unit.1 hy
  obtain ⟨j, hj⟩ := adj_iff_exists_unit.1 hz
  by_cases hij : i = j
  · subst hij
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hyz rfl).elim
    · exact summand_le_nbrSumZ hw x i
    · linarith [summand_le_nbrSumZ hw x i]
    · exact (hyz rfl).elim
  · have hy' : w y ≤ w (x + unit i) + w (x - unit i) := by
      rcases hi with rfl | rfl
      · linarith [hw (x - unit i)]
      · linarith [hw (x + unit i)]
    have hz' : w z ≤ w (x + unit j) + w (x - unit j) := by
      rcases hj with rfl | rfl
      · linarith [hw (x - unit j)]
      · linarith [hw (x + unit j)]
    have hsub : ∑ k ∈ ({i, j} : Finset (Fin d)), (w (x + unit k) + w (x - unit k))
        ≤ nbrSumZ w x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => add_nonneg (hw _) (hw _))
    rw [Finset.sum_pair hij] at hsub
    linarith

/-- The Laplacian at `x` depends only on the values at `x` and at its neighbours. -/
theorem lap_congr_nbr {u v : Site d → ℤ} {x : Site d} (hx : u x = v x)
    (h : ∀ z, (lattice d).Adj x z → u z = v z) : lap u x = lap v x := by
  have hs : nbrSumZ u x = nbrSumZ v x := by
    unfold nbrSumZ
    exact Finset.sum_congr rfl fun i _ => by
      rw [h _ (adj_add_unit x i), h _ (adj_sub_unit x i)]
  unfold lap
  rw [hs, hx]

theorem lap_const_zero (x : Site d) : lap (fun _ => (0 : ℤ)) x = 0 := by
  simp [lap, nbrSumZ]

theorem dirac_nonneg (z x : Site d) : 0 ≤ dirac z x := by
  unfold dirac
  split_ifs <;> norm_num

/-! ### Coordinate reflections and permutations -/

/-- The reflection `x ↦ -x` in the coordinate `i`. -/
def flipAt (i : Fin d) (x : Site d) : Site d := fun m => if m = i then -x m else x m

/-- The coordinate permutation `x ↦ x ∘ τ`. -/
def permAt (τ : Equiv.Perm (Fin d)) (x : Site d) : Site d := fun m => x (τ m)

theorem flipAt_add_unit_of_ne {i k : Fin d} (hk : k ≠ i) (x : Site d) :
    flipAt i (x + unit k) = flipAt i x + unit k := by
  funext m
  by_cases hm : m = i
  · subst hm
    simp [flipAt, unit, Ne.symm hk]
  · simp [flipAt, unit, hm]

theorem flipAt_sub_unit_of_ne {i k : Fin d} (hk : k ≠ i) (x : Site d) :
    flipAt i (x - unit k) = flipAt i x - unit k := by
  funext m
  by_cases hm : m = i
  · subst hm
    simp [flipAt, unit, Ne.symm hk]
  · simp [flipAt, unit, hm]

theorem flipAt_add_unit_self (i : Fin d) (x : Site d) :
    flipAt i (x + unit i) = flipAt i x - unit i := by
  funext m
  by_cases hm : m = i
  · subst hm
    simp [flipAt, unit]
    ring
  · simp [flipAt, unit, hm]

theorem flipAt_sub_unit_self (i : Fin d) (x : Site d) :
    flipAt i (x - unit i) = flipAt i x + unit i := by
  funext m
  by_cases hm : m = i
  · subst hm
    simp [flipAt, unit]
    ring
  · simp [flipAt, unit, hm]

theorem flipAt_zero (i : Fin d) : flipAt i (0 : Site d) = 0 := by
  funext m
  simp [flipAt]

theorem flipAt_injective (i : Fin d) : Function.Injective (flipAt i) := by
  intro x y h
  funext m
  have hm := congrFun h m
  simp only [flipAt] at hm
  split_ifs at hm <;> omega

theorem flipAt_single (i : Fin d) (c : ℤ) :
    flipAt i (Pi.single i c : Site d) = Pi.single i (-c) := by
  funext m
  by_cases hm : m = i
  · subst hm
    simp [flipAt]
  · simp [flipAt, hm]

theorem lap_flipAt (u : Site d → ℤ) (i : Fin d) (x : Site d) :
    lap (fun y => u (flipAt i y)) x = lap u (flipAt i x) := by
  simp only [lap, nbrSumZ]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    rw [flipAt_add_unit_self, flipAt_sub_unit_self]
    exact add_comm _ _
  · rw [flipAt_add_unit_of_ne hk, flipAt_sub_unit_of_ne hk]

theorem perm_apply_eq_iff (τ : Equiv.Perm (Fin d)) (m k : Fin d) :
    τ m = k ↔ m = τ.symm k := by
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

theorem permAt_add_unit (τ : Equiv.Perm (Fin d)) (x : Site d) (k : Fin d) :
    permAt τ (x + unit k) = permAt τ x + unit (τ.symm k) := by
  funext m
  simp only [permAt, unit, Pi.add_apply, Pi.single_apply, perm_apply_eq_iff τ m k]

theorem permAt_sub_unit (τ : Equiv.Perm (Fin d)) (x : Site d) (k : Fin d) :
    permAt τ (x - unit k) = permAt τ x - unit (τ.symm k) := by
  funext m
  simp only [permAt, unit, Pi.sub_apply, Pi.single_apply, perm_apply_eq_iff τ m k]

theorem permAt_zero (τ : Equiv.Perm (Fin d)) : permAt τ (0 : Site d) = 0 := rfl

theorem permAt_single (τ : Equiv.Perm (Fin d)) (i : Fin d) (c : ℤ) :
    permAt τ (Pi.single i c : Site d) = Pi.single (τ.symm i) c := by
  funext m
  simp only [permAt, Pi.single_apply, perm_apply_eq_iff τ m i]

theorem permAt_injective (τ : Equiv.Perm (Fin d)) : Function.Injective (permAt τ) := by
  intro x y h
  funext m
  have hm := congrFun h (τ.symm m)
  simpa [permAt] using hm

theorem lap_permAt (τ : Equiv.Perm (Fin d)) (u : Site d → ℤ) (x : Site d) :
    lap (fun y => u (permAt τ y)) x = lap u (permAt τ x) := by
  simp only [lap, nbrSumZ]
  congr 1
  calc ∑ k : Fin d, (u (permAt τ (x + unit k)) + u (permAt τ (x - unit k)))
      = ∑ k : Fin d, (u (permAt τ x + unit (τ.symm k)) + u (permAt τ x - unit (τ.symm k))) :=
        Finset.sum_congr rfl fun k _ => by rw [permAt_add_unit, permAt_sub_unit]
    _ = ∑ j : Fin d, (u (permAt τ x + unit j) + u (permAt τ x - unit j)) :=
        Equiv.sum_comp τ.symm (fun j => u (permAt τ x + unit j) + u (permAt τ x - unit j))

theorem dirac_comp_eq (σ : Site d → Site d) (h0 : σ 0 = 0) (hinj : Function.Injective σ)
    (x : Site d) : dirac 0 (σ x) = dirac 0 x := by
  by_cases hx : x = 0
  · rw [hx, h0]
  · have hσ : σ x ≠ 0 := fun h => hx (hinj (h.trans h0.symm))
    rw [dirac_of_ne hx, dirac_of_ne hσ]

/-- A symmetry `σ` of the Laplacian and of the background fixes the parallel odometer. -/
theorem podo_comp (s0 : Site d → ℤ) (σ : Site d → Site d) (hs0 : ∀ x, s0 (σ x) = s0 x)
    (hlap : ∀ (u : Site d → ℤ) (x : Site d), lap (fun y => u (σ y)) x = lap u (σ x))
    (t : ℕ) : ∀ x, podo s0 t (σ x) = podo s0 t x := by
  induction t with
  | zero => intro x; rfl
  | succ t ih =>
    intro x
    have hlapx : lap (podo s0 t) (σ x) = lap (podo s0 t) x := by
      rw [← hlap, show (fun y => podo s0 t (σ y)) = podo s0 t from funext ih]
    rw [podo_succ, podo_succ, pconf, pconf, hs0, hlapx, ih x]

/-- Adjacent sites at which `w` is positive. -/
abbrev posAdj {d : ℕ} (w : Site d → ℤ) (y z : Site d) : Prop :=
  0 < w y ∧ 0 < w z ∧ (lattice d).Adj y z

end FdBRCube

open FdBRCube

/-- **The support of the parallel toppling odometer is a cube.** For the background `2d - 2`
with `N ≥ 2` extra chips at the origin, if the sandpile is stable at time `T` and its positive
support is finite, then the positive support is `{x | ∀ i, |x i| ≤ r}` for some natural `r`. -/
theorem fdbr_support_eq_cube {d : ℕ} (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) (s0 : Site d → ℤ)
    (hs0 : ∀ x, s0 x = (2 * (d : ℤ) - 2) + (N : ℤ) * dirac 0 x) (T : ℕ)
    (hstab : ∀ x : Site d, s0 x + lap (podo s0 T) x < 2 * (d : ℤ))
    (hfin : {x : Site d | 0 < podo s0 T x}.Finite) :
    ∃ r : ℕ, {x : Site d | 0 < podo s0 T x} = {x : Site d | ∀ i : Fin d, |x i| ≤ (r : ℤ)} := by
  classical
  set w : Site d → ℤ := podo s0 T
  have hw0 : ∀ x, 0 ≤ w x := (podo_isLegal s0).nonneg T
  have hN' : (2 : ℤ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℤ) ≤ N := by positivity
  have hs0_ge : ∀ x, 2 * (d : ℤ) - 2 ≤ s0 x := fun x => by
    rw [hs0 x]
    have := mul_nonneg hN0 (dirac_nonneg (0 : Site d) x)
    linarith
  -- The origin lies in the support.
  have h0S : 0 < w 0 := by
    by_contra h
    have hw00 : w 0 = 0 := le_antisymm (not_lt.1 h) (hw0 0)
    have hlap0 : lap w 0 = nbrSumZ w 0 := by
      simp only [lap, hw00, mul_zero, sub_zero]
    have hnb : 0 ≤ nbrSumZ w 0 := by
      unfold nbrSumZ
      exact Finset.sum_nonneg fun i _ => add_nonneg (hw0 _) (hw0 _)
    have h1 := hstab 0
    rw [hlap0, hs0 0, dirac_self] at h1
    linarith
  -- The support is closed under two-neighbour completion.
  have hclosed : TwoNeighborClosed {x : Site d | 0 < w x} := by
    intro x y z hxy hxz hyz hy hz
    simp only [Set.mem_ofPred_eq] at hy hz ⊢
    by_contra hx
    have hx0 : w x = 0 := le_antisymm (not_lt.1 hx) (hw0 x)
    have hsum := nbrSumZ_ge_of_adj hw0 hxy hxz hyz
    have hlapx : lap w x = nbrSumZ w x := by
      simp only [lap, hx0, mul_zero, sub_zero]
    have h1 : 1 ≤ w y := by omega
    have h2 : 1 ≤ w z := by omega
    have h3 := hstab x
    have h4 := hs0_ge x
    linarith
  -- The component of the origin: the odometer restricted to it is stable and dominates `w`.
  obtain ⟨v, hvC, hvN⟩ : ∃ v : Site d → ℤ,
      (∀ x, Relation.ReflTransGen (posAdj w) 0 x → v x = w x) ∧
      (∀ x, ¬ Relation.ReflTransGen (posAdj w) 0 x → v x = 0) :=
    ⟨fun x => if Relation.ReflTransGen (posAdj w) 0 x then w x else 0,
      fun x hx => ite_eq_left hx, fun x hx => ite_eq_right hx⟩
  have hpos : ∀ x, Relation.ReflTransGen (posAdj w) 0 x → 0 < w x := by
    intro x hx
    induction hx with
    | refl => exact h0S
    | tail _ hbc _ => exact hbc.2.1
  have hv0 : ∀ x, 0 ≤ v x := fun x => by
    by_cases h : Relation.ReflTransGen (posAdj w) 0 x
    · rw [hvC x h]; exact hw0 x
    · exact (hvN x h).ge
  have hvw : ∀ x, v x ≤ w x := fun x => by
    by_cases h : Relation.ReflTransGen (posAdj w) 0 x
    · exact (hvC x h).le
    · rw [hvN x h]; exact hw0 x
  have hvstab : ∀ y, s0 y + lap v y < 2 * (d : ℤ) := by
    intro y
    by_cases hC : Relation.ReflTransGen (posAdj w) 0 y
    · have hpy : 0 < w y := hpos y hC
      have hcong : lap v y = lap w y := by
        refine lap_congr_nbr (hvC y hC) fun z hz => ?_
        by_cases hzC : Relation.ReflTransGen (posAdj w) 0 z
        · exact hvC z hzC
        · have hwz : w z = 0 := by
            have hle : ¬ 0 < w z := fun hpz =>
              hzC (Relation.ReflTransGen.tail hC (⟨hpy, hpz, hz⟩ : posAdj w y z))
            exact le_antisymm (not_lt.1 hle) (hw0 z)
          rw [hvN z hzC, hwz]
      rw [hcong]
      exact hstab y
    · by_cases hpy : 0 < w y
      · have hy0 : y ≠ 0 := by
          rintro rfl
          exact hC Relation.ReflTransGen.refl
        have hnbr : ∀ z, (lattice d).Adj y z → v z = (fun _ => (0 : ℤ)) z := by
          intro z hz
          by_cases hzC : Relation.ReflTransGen (posAdj w) 0 z
          · exact absurd
              (Relation.ReflTransGen.tail hzC (⟨hpos z hzC, hpy, hz.symm⟩ : posAdj w z y)) hC
          · exact hvN z hzC
        have hlap0 : lap v y = 0 :=
          (lap_congr_nbr (v := fun _ => (0 : ℤ)) (hvN y hC) hnbr).trans (lap_const_zero y)
        have hs : s0 y = 2 * (d : ℤ) - 2 := by
          rw [hs0 y, dirac_of_ne hy0, mul_zero, add_zero]
        rw [hlap0, hs]
        linarith
      · have hwy : w y = 0 := le_antisymm (not_lt.1 hpy) (hw0 y)
        have hle : lap v y ≤ lap w y := lap_le_lap_of_le hvw (by rw [hvN y hC, hwy])
        linarith [hstab y]
  have hvle : ∀ x, w x ≤ v x := fun x =>
    le_of_isLegalToppling (podo_isLegal s0) hv0 hvstab T x
  have hconn : ∀ x, 0 < w x → Relation.ReflTransGen (posAdj w) 0 x := by
    intro x hx
    by_contra hn
    have h1 := hvN x hn
    have h2 := hvle x
    linarith
  -- The support is a box.
  obtain ⟨a, b, hSbox⟩ :=
    eq_box_of_twoNeighborClosed (x₀ := 0) hfin h0S hclosed (fun x hx => hconn x hx)
  have hmem : ∀ x, 0 < w x ↔ ∀ l, a l ≤ x l ∧ x l ≤ b l := fun x => Set.ext_iff.1 hSbox x
  have hab0 : ∀ l, a l ≤ 0 ∧ 0 ≤ b l := fun l => (hmem 0).1 h0S l
  have hpt : ∀ (i : Fin d) (c : ℤ),
      (∀ l, a l ≤ (Pi.single i c : Site d) l ∧ (Pi.single i c : Site d) l ≤ b l) ↔
        (a i ≤ c ∧ c ≤ b i) := by
    intro i c
    constructor
    · intro h
      simpa using h i
    · intro h l
      by_cases hl : l = i
      · subst hl
        simpa using h
      · rw [Pi.single_apply, ite_eq_right hl]
        exact hab0 l
  -- The symmetries of the dynamics.
  have hs0_inv : ∀ σ : Site d → Site d, σ 0 = 0 → Function.Injective σ →
      ∀ x, s0 (σ x) = s0 x := by
    intro σ h0 hinj x
    rw [hs0, hs0, dirac_comp_eq σ h0 hinj x]
  have hwf : ∀ (i : Fin d) (x : Site d), w (flipAt i x) = w x := fun i x =>
    podo_comp s0 (flipAt i) (hs0_inv _ (flipAt_zero i) (flipAt_injective i))
      (fun u y => lap_flipAt u i y) T x
  have hwp : ∀ (τ : Equiv.Perm (Fin d)) (x : Site d), w (permAt τ x) = w x := fun τ x =>
    podo_comp s0 (permAt τ) (hs0_inv _ (permAt_zero τ) (permAt_injective τ))
      (fun u y => lap_permAt τ u y) T x
  -- Reflections force `a i = -b i`.
  have hab : ∀ i, a i = -b i := by
    intro i
    have hai : a i ≤ b i := le_trans (hab0 i).1 (hab0 i).2
    have h1 : a i ≤ -b i := by
      have hp : 0 < w (Pi.single i (b i) : Site d) :=
        (hmem _).2 ((hpt i (b i)).2 ⟨hai, le_rfl⟩)
      have hq : 0 < w (flipAt i (Pi.single i (b i) : Site d)) := by
        rw [hwf]; exact hp
      rw [flipAt_single] at hq
      exact ((hpt i (-b i)).1 ((hmem _).1 hq)).1
    have h2 : -b i ≤ a i := by
      have hp : 0 < w (Pi.single i (a i) : Site d) :=
        (hmem _).2 ((hpt i (a i)).2 ⟨le_rfl, hai⟩)
      have hq : 0 < w (flipAt i (Pi.single i (a i) : Site d)) := by
        rw [hwf]; exact hp
      rw [flipAt_single] at hq
      have h3 := ((hpt i (-a i)).1 ((hmem _).1 hq)).2
      linarith
    exact le_antisymm h1 h2
  -- Permutations force all radii to agree.
  have hbeq : ∀ i j : Fin d, b i ≤ b j := by
    intro i j
    have hp : 0 < w (Pi.single i (b i) : Site d) :=
      (hmem _).2 ((hpt i (b i)).2 ⟨le_trans (hab0 i).1 (hab0 i).2, le_rfl⟩)
    have hq : 0 < w (permAt (Equiv.swap i j) (Pi.single i (b i) : Site d)) := by
      rw [hwp]; exact hp
    rw [permAt_single, Equiv.symm_swap, Equiv.swap_apply_left] at hq
    exact ((hpt j (b i)).1 ((hmem _).1 hq)).2
  obtain ⟨i0⟩ : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hc0 : 0 ≤ b i0 := (hab0 i0).2
  have hr : ∀ i, ((b i0).toNat : ℤ) = b i := fun i => by
    rw [Int.toNat_of_nonneg hc0]
    exact le_antisymm (hbeq i0 i) (hbeq i i0)
  refine ⟨(b i0).toNat, ?_⟩
  rw [hSbox]
  ext x
  simp only [Set.mem_ofPred_eq]
  refine forall_congr' fun l => ?_
  rw [hr l, abs_le, hab l]

end LatticeProb.Sandpile
