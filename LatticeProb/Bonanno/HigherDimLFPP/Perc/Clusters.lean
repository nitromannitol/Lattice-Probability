/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Perc.Clusters at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Perc.Peierls
import LatticeProb.Bonanno.HigherDimLFPP.Perc.Surgery
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Diameters of closed clusters and the enclosure bound (HA5 D6(iii)–(iv))

With the hypotheses of the Peierls bound (`peierlsD`):

* `diameterBound` (D6(iii)): the probability that some closed cluster meets the box `B̄_N(x)` and has
  `ℓ^∞`-diameter `> D` is at most `(2N+1)^d 2^{-⌊D/2⌋}`. If `C` meets `B̄_N(x)` at `z` and contains
  `y, y'` with `|y - y'|_∞ > D`, one of `y, y'` is at distance `> ⌊D/2⌋` from `z`, and the cluster
  contains a closed `*`-path from `z` to it; sum the Peierls bound over the `(2N+1)^d` sites `z`.
* `enclosureBound` (D6(iv), replaces DGZ Lemma 2.10; needs `d ≥ 2`): the probability that `B̄_N(x)`
  contains a closed site, or that some closed cluster `C ⊆ [-R, R]^d` encloses `x` (`x ∉ C`,
  `x ∉ Ext R C`), is at most `(2N+1)^d ε + 2^{-N}`. If `B̄_N(x)` is open and `C` encloses `x`, both
  rays `x ± j e₁` (`j ≥ 0`) meet `C`: a ray avoiding `C` reaches the complement of the box, which is
  L-connected to the base point `(R+1, …, R+1)` outside the box when `d ≥ 2`
  (`mem_ext_of_not_withinInf`), and would put `x` in `Ext R C`. The hit `x + j e₁` has `j > N`, and
  the cluster joins it to the hit `x - j' e₁` (`j' ≥ 1`), at distance `j + j' > j`; so a closed
  `*`-path from `x + j e₁` leaves `B̄_j(x + j e₁)`. Sum `2^{-j}` over `j > N`.

For `d = 1` the enclosure bound is false: a single closed site to the right of `x` encloses `x`
(the exterior of a set of integers is the half-line beyond its maximum).
-/

set_option autoImplicit false

open MeasureTheory Relation
open scoped ENNReal

namespace HigherDimLFPP

namespace Perc

variable {d : ℕ}

/-! ### Boxes -/

/-- The box `B̄_N(x) = {y : |y - x|_∞ ≤ N}` as a finset. -/
def boxF (x : Zd d) (N : ℕ) : Finset (Zd d) :=
  Fintype.piFinset fun i => Finset.Icc (x i - N) (x i + N)

lemma mem_boxF {x y : Zd d} {N : ℕ} : y ∈ boxF x N ↔ WithinInf (N : ℤ) y x := by
  simp only [boxF, Fintype.mem_piFinset, Finset.mem_Icc, WithinInf, abs_le]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

lemma card_boxF (x : Zd d) (N : ℕ) : (boxF x N).card = (2 * N + 1) ^ d := by
  rw [boxF, Fintype.card_piFinset]
  have : ∀ i : Fin d, (Finset.Icc (x i - N) (x i + N)).card = 2 * N + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

lemma card_boxF_ennreal (x : Zd d) (N : ℕ) :
    ((boxF x N).card : ℝ≥0∞) = (2 * (N : ℝ≥0∞) + 1) ^ d := by
  rw [card_boxF]
  push_cast
  rfl

/-! ### The Peierls event -/

/-- The Peierls event at `x` with radius `L`: a closed `*`-path from `x` leaves `B̄_L(x)`. -/
def peierlsEvent {Ω : Type*} (closed : Zd d → Set Ω) (x : Zd d) (L : ℕ) : Set Ω :=
  {ω | ∃ γ : List (Zd d), γ.head? = some x ∧ γ.IsChain SAdj ∧ (∀ y ∈ γ, ω ∈ closed y) ∧
    ∃ y ∈ γ, ¬ WithinInf (L : ℤ) y x}

/-- A `*`-path inside a set of closed sites that ends outside `B̄_L(z)` gives the Peierls event. -/
lemma mem_peierlsEvent_of_reflTransGen {Ω : Type*} {closed : Zd d → Set Ω} {ω : Ω}
    {C : Set (Zd d)} (hC : ∀ y ∈ C, ω ∈ closed y) {z w : Zd d} (hz : z ∈ C)
    (hzw : ReflTransGen (StepIn C SAdj) z w) {L : ℕ} (hw : ¬ WithinInf (L : ℤ) w z) :
    ω ∈ peierlsEvent closed z L := by
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hzw
  have hmem : ∀ y ∈ z :: l, y ∈ C :=
    List.IsChain.induction (fun y => y ∈ C) (z :: l) hl (fun _ _ hab _ => hab.2.1) (fun _ => hz)
  refine ⟨z :: l, rfl, hl.imp fun _ _ h => h.2.2, fun y hy => hC y (hmem y hy), w, ?_, hw⟩
  rw [← hlast]
  exact List.getLast_mem _

/-- The Peierls bound for `peierlsEvent`. -/
lemma measure_peierlsEvent_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {closed : Zd d → Set Ω} {r : ℕ} {ε θ : ℝ≥0∞} (hε : ∀ x, μ (closed x) ≤ ε)
    (hind : ProductBound μ closed r) (hθ1 : θ ≤ 1) (hεθ : ε ≤ θ ^ ((r + 1) ^ d))
    (hθ : (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹) (x : Zd d) (L : ℕ) :
    μ (peierlsEvent closed x L) ≤ 2⁻¹ ^ L :=
  peierlsD d μ closed r ε θ hε hind hθ1 hεθ hθ x L

/-! ### D6(iii): diameters -/

/-- **D6(iii): diameter bound.** -/
theorem diameterBound (d : ℕ) : DiameterBound d := by
  intro Ω _ μ closed r ε θ hε hind hθ1 hεθ hθ x N D
  classical
  have hsub : {ω | ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧ (∃ z ∈ C, WithinInf (N : ℤ) z x) ∧
      ∃ y ∈ C, ∃ y' ∈ C, ¬ WithinInf (D : ℤ) y y'} ⊆
      ⋃ z ∈ boxF x N, peierlsEvent closed z (D / 2) := by
    intro ω hω
    obtain ⟨C, hCcl, ⟨z, hzC, hzx⟩, y, hyC, y', hy'C, hyy'⟩ := hω
    have hCcl' : ∀ y ∈ C, ω ∈ closed y := fun y hy => by
      have := hCcl.2.1 hy
      simpa using this
    have hfar : ∃ w ∈ C, ¬ WithinInf ((D / 2 : ℕ) : ℤ) w z := by
      by_contra hcon
      push Not at hcon
      apply hyy'
      have h := (hcon y hyC).trans (hcon y' hy'C).symm
      exact h.mono (by omega)
    obtain ⟨w, hwC, hw⟩ := hfar
    simp only [Set.mem_iUnion]
    exact ⟨z, mem_boxF.mpr hzx,
      mem_peierlsEvent_of_reflTransGen hCcl' hzC (hCcl.2.2.1 z hzC w hwC) hw⟩
  calc μ {ω | ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧ (∃ z ∈ C, WithinInf (N : ℤ) z x) ∧
        ∃ y ∈ C, ∃ y' ∈ C, ¬ WithinInf (D : ℤ) y y'}
      ≤ μ (⋃ z ∈ boxF x N, peierlsEvent closed z (D / 2)) := measure_mono hsub
    _ ≤ ∑ z ∈ boxF x N, μ (peierlsEvent closed z (D / 2)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ boxF x N, (2⁻¹ : ℝ≥0∞) ^ (D / 2) :=
        Finset.sum_le_sum fun z _ => measure_peierlsEvent_le hε hind hθ1 hεθ hθ z _
    _ = (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (D / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, card_boxF_ennreal]

/-! ### The complement of a box is L-connected (`d ≥ 2`) -/

/-- Setting the coordinates other than `i` to `R + 1`, one at a time. -/
def raiseOthers (y : Zd d) (i : Fin d) (R : ℤ) (n : ℕ) : Zd d :=
  fun k => if k ≠ i ∧ k.val < n then R + 1 else y k

lemma raiseOthers_zero (y : Zd d) (i : Fin d) (R : ℤ) : raiseOthers y i R 0 = y := by
  funext k
  simp [raiseOthers]

lemma raiseOthers_apply_self (y : Zd d) (i : Fin d) (R : ℤ) (n : ℕ) :
    raiseOthers y i R n i = y i := by
  simp [raiseOthers]

/-- If `|y i| > R`, then `y` is joined, outside the box `[-R, R]^d`, to the site whose `i`-th
coordinate is `y i` and whose other coordinates are `R + 1`. -/
lemma reflTransGen_raiseOthers {R : ℤ} {y : Zd d} {i : Fin d} (hyi : R < |y i|) (n : ℕ) :
    ReflTransGen (StepIn {z | ¬ WithinInf R z 0} LAdj) y (raiseOthers y i R n) := by
  have hout : ∀ z : Zd d, z i = y i → z ∈ {z : Zd d | ¬ WithinInf R z 0} := by
    intro z hz hw
    have := hw i
    rw [Pi.zero_apply, sub_zero, hz] at this
    exact absurd this (not_le.mpr hyi)
  induction n with
  | zero => rw [raiseOthers_zero]
  | succ n ih =>
    by_cases hn : n < d
    · set j : Fin d := ⟨n, hn⟩ with hj
      by_cases hji : j = i
      · have : raiseOthers y i R (n + 1) = raiseOthers y i R n := by
          funext k
          simp only [raiseOthers]
          by_cases hk : k = i
          · simp [hk]
          · have hkn : k.val ≠ n := fun h' => hk (by rw [← hji]; exact Fin.ext h')
            have e : (k.val < n + 1) ↔ (k.val < n) := by omega
            simp only [ne_eq, hk, not_false_eq_true, true_and, e]
        rw [this]; exact ih
      · have hupd : raiseOthers y i R (n + 1) = Function.update (raiseOthers y i R n) j (R + 1) := by
          funext k
          by_cases hk : k = j
          · subst hk
            rw [Function.update_self]
            simp only [raiseOthers]
            have h1 : (j : ℕ) < n + 1 := by rw [hj]; exact Nat.lt_succ_self n
            simp only [ne_eq, hji, not_false_eq_true, true_and, h1, ↓reduceIte]
          · rw [Function.update_of_ne hk]
            simp only [raiseOthers]
            have hkn : k.val ≠ n := fun h' => hk (Fin.ext h')
            have e : (k.val < n + 1) ↔ (k.val < n) := by omega
            simp only [e]
        rw [hupd]
        refine ih.trans (reflTransGen_update _ j (R + 1) fun s _ _ => hout _ ?_)
        rw [Function.update_of_ne (Ne.symm hji), raiseOthers_apply_self]
    · have : raiseOthers y i R (n + 1) = raiseOthers y i R n := by
        funext k
        simp only [raiseOthers]
        have e : (k.val < n + 1) ↔ (k.val < n) := by have := k.isLt; omega
        simp only [e]
      rw [this]; exact ih

/-- For `d ≥ 2` every site outside the box `[-R, R]^d` lies in the exterior of every subset of the
box. -/
lemma mem_ext_of_not_withinInf (hd : 2 ≤ d) {R : ℤ} {C : Set (Zd d)}
    (hC : ∀ c ∈ C, WithinInf R c 0) {y : Zd d} (hy : ¬ WithinInf R y 0) : y ∈ Ext R C := by
  have hOutC : {z : Zd d | ¬ WithinInf R z 0} ⊆ Cᶜ := fun z hz hzC => hz (hC z hzC)
  obtain ⟨i, hi⟩ : ∃ i, R < |y i| := by
    by_contra hcon
    push Not at hcon
    exact hy fun i => by simpa using hcon i
  -- a second coordinate
  obtain ⟨k, hki⟩ : ∃ k : Fin d, k ≠ i := by
    by_cases h0 : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩
  set y' := raiseOthers y i R d with hy'
  have h1 := reflTransGen_raiseOthers hi d
  have hy'k : ∀ m : Fin d, m ≠ i → y' m = R + 1 := by
    intro m hm
    simp [hy', raiseOthers, hm, m.isLt]
  have h2 : ReflTransGen (StepIn {z : Zd d | ¬ WithinInf R z 0} LAdj) y'
      (Function.update y' i (R + 1)) := by
    refine reflTransGen_update y' i (R + 1) fun s _ _ hw => ?_
    have := hw k
    rw [Function.update_of_ne hki, hy'k k hki, Pi.zero_apply, sub_zero, abs_le] at this
    omega
  have hbase : Function.update y' i (R + 1) = (fun _ => R + 1 : Zd d) := by
    funext m
    by_cases hm : m = i
    · subst hm; simp
    · rw [Function.update_of_ne hm, hy'k m hm]
  rw [hbase] at h2
  exact reflTransGen_stepIn_mono hOutC (h1.trans h2)

/-- The ray `x + j e_i` (`j ≥ 0`): if it avoids `C ⊆ [-R, R]^d` then `x ∈ Ext R C` (`d ≥ 2`). -/
lemma mem_ext_of_ray_add (hd : 2 ≤ d) {R : ℤ} {C : Set (Zd d)} (hC : ∀ c ∈ C, WithinInf R c 0)
    (x : Zd d) (i : Fin d) (hray : ∀ j : ℕ, x + Pi.single i (j : ℤ) ∉ C) : x ∈ Ext R C := by
  set J : ℕ := (R + 1 - x i).toNat with hJ
  have hpath : ReflTransGen (StepIn Cᶜ LAdj) x (x + Pi.single i (J : ℤ)) :=
    reflTransGen_add_single_nat x i J fun s _ => hray s
  refine hpath.trans (mem_ext_of_not_withinInf hd hC fun hw => ?_)
  have := hw i
  rw [add_single_apply_self, Pi.zero_apply, sub_zero, abs_le] at this
  omega

/-- The ray `x - j e_i` (`j ≥ 0`): if it avoids `C ⊆ [-R, R]^d` then `x ∈ Ext R C` (`d ≥ 2`). -/
lemma mem_ext_of_ray_sub (hd : 2 ≤ d) {R : ℤ} {C : Set (Zd d)} (hC : ∀ c ∈ C, WithinInf R c 0)
    (x : Zd d) (i : Fin d) (hray : ∀ j : ℕ, x + Pi.single i (-(j : ℤ)) ∉ C) : x ∈ Ext R C := by
  set J : ℕ := (x i + R + 1).toNat with hJ
  have hpath : ReflTransGen (StepIn Cᶜ LAdj) x (x + Pi.single i (-(J : ℤ))) :=
    reflTransGen_sub_single_nat x i J fun s _ => hray s
  refine hpath.trans (mem_ext_of_not_withinInf hd hC fun hw => ?_)
  have := hw i
  rw [add_single_apply_self, Pi.zero_apply, sub_zero, abs_le] at this
  omega

/-! ### D6(iv): the enclosure bound -/

/-- **D6(iv): enclosure bound** (`d ≥ 2`; replaces DGZ Lemma 2.10). -/
theorem enclosureBound (d : ℕ) (hd : 2 ≤ d) : EnclosureBound d := by
  intro Ω _ μ closed r ε θ hε hind hθ1 hεθ hθ x N
  classical
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set ray : ℕ → Zd d := fun j => x + Pi.single i₀ ((N + 1 + j : ℕ) : ℤ) with hray
  have hsub : {ω | (∃ y, WithinInf (N : ℤ) y x ∧ ω ∈ closed y) ∨
      ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧ Encloses C x} ⊆
      (⋃ y ∈ boxF x N, closed y) ∪ ⋃ j : ℕ, peierlsEvent closed (ray j) (N + 1 + j) := by
    intro ω hω
    by_cases hbox : ∃ y, WithinInf (N : ℤ) y x ∧ ω ∈ closed y
    · obtain ⟨y, hyx, hy⟩ := hbox
      left
      simp only [Set.mem_iUnion]
      exact ⟨y, mem_boxF.mpr hyx, hy⟩
    · right
      obtain ⟨C, hCcl, R, hCbox, hxC, hxE⟩ := hω.resolve_left hbox
      have hCcl' : ∀ y ∈ C, ω ∈ closed y := fun y hy => by
        have := hCcl.2.1 hy
        simpa using this
      -- both rays meet `C`
      obtain ⟨j, hj⟩ : ∃ j : ℕ, x + Pi.single i₀ (j : ℤ) ∈ C := by
        by_contra hcon
        push Not at hcon
        exact hxE (mem_ext_of_ray_add hd hCbox x i₀ hcon)
      obtain ⟨j', hj'⟩ : ∃ j' : ℕ, x + Pi.single i₀ (-(j' : ℤ)) ∈ C := by
        by_contra hcon
        push Not at hcon
        exact hxE (mem_ext_of_ray_sub hd hCbox x i₀ hcon)
      -- the hits are outside `B̄_N(x)`
      have hNj : N < j := by
        by_contra hle
        apply hbox
        refine ⟨_, fun k => ?_, hCcl' _ hj⟩
        rw [add_single_apply]
        split_ifs
        · simp only [add_sub_cancel_left, abs_le]; constructor <;> omega
        · simp
      have hj'0 : j' ≠ 0 := by
        rintro rfl
        simp only [Nat.cast_zero, neg_zero, Pi.single_zero, add_zero] at hj'
        exact hxC hj'
      obtain ⟨j₀, rfl⟩ : ∃ j₀, j = N + 1 + j₀ := ⟨j - (N + 1), by omega⟩
      simp only [Set.mem_iUnion]
      refine ⟨j₀, mem_peierlsEvent_of_reflTransGen hCcl' hj (hCcl.2.2.1 _ hj _ hj') ?_⟩
      intro hw
      have := hw i₀
      rw [add_single_apply_self, add_single_apply_self, abs_le] at this
      omega
  have hgeom : ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (N + 1 + j) = 2⁻¹ ^ N := by
    simp_rw [pow_add]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, pow_one, mul_assoc,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  calc μ {ω | (∃ y, WithinInf (N : ℤ) y x ∧ ω ∈ closed y) ∨
        ∃ C, IsClosedCluster {y | ω ∉ closed y} C ∧ Encloses C x}
      ≤ μ ((⋃ y ∈ boxF x N, closed y) ∪ ⋃ j : ℕ, peierlsEvent closed (ray j) (N + 1 + j)) :=
        measure_mono hsub
    _ ≤ μ (⋃ y ∈ boxF x N, closed y) + μ (⋃ j : ℕ, peierlsEvent closed (ray j) (N + 1 + j)) :=
        measure_union_le _ _
    _ ≤ ∑ y ∈ boxF x N, μ (closed y) + ∑' j : ℕ, μ (peierlsEvent closed (ray j) (N + 1 + j)) :=
        add_le_add (measure_biUnion_finset_le _ _) (measure_iUnion_le _)
    _ ≤ ∑ _y ∈ boxF x N, ε + ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (N + 1 + j) :=
        add_le_add (Finset.sum_le_sum fun y _ => hε y)
          (ENNReal.tsum_le_tsum fun j => measure_peierlsEvent_le hε hind hθ1 hεθ hθ _ _)
    _ = (2 * (N : ℝ≥0∞) + 1) ^ d * ε + 2⁻¹ ^ N := by
        rw [Finset.sum_const, nsmul_eq_mul, card_boxF_ennreal, hgeom]

end Perc

end HigherDimLFPP
