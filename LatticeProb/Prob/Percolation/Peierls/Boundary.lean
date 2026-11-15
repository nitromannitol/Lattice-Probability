import LatticeProb.Site
import LatticeProb.Bonanno.HigherDimLFPP.Perc.Poincare

/-!
# Star-connected boundaries on integer lattices

The boundary between two connected sets is star-connected when one is a component
of the complement of the other. The proof is adapted from Exploding-Sandpiles,
`Exploding/Support/ExtMHBase.lean`, `ECProofStar.lean`, `ExtMHProof5.lean` and
`ExtMHProof11.lean`.
It uses the discrete Poincaré lemma in `HigherDimLFPP.Perc.Poincare`.
-/

namespace LatticeProb.Percolation.Peierls.Boundary

open LatticeProb Relation

variable {d : ℕ}

/-- King adjacency on `ℤ^d`: two distinct sites at sup-norm distance at most one. -/
def xmh_star (a b : Site d) : Prop := a ≠ b ∧ ∀ i, |a i - b i| ≤ 1

theorem xmh_star_symm {a b : Site d} (h : xmh_star a b) : xmh_star b a := by
  refine ⟨h.1.symm, fun i => ?_⟩
  rw [abs_sub_comm]
  exact h.2 i

/-- A set of sites is `*`-connected: any two of its points are joined by a chain of king moves
inside it. -/
def xmh_SConn (F : Set (Site d)) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, ReflTransGen (fun a b => a ∈ F ∧ b ∈ F ∧ xmh_star a b) x y

/-- **The boundary between two connected sets is `*`-connected.**  `A` and `B` are disjoint
connected sets of nearest-neighbour adjacency, with `B` closed under adjacency outside `A`
(`B` is a component of the complement of `A`); the sites of `B` adjacent to `A` are joined by
chains of king moves inside that boundary. -/
def xmh_BoundaryStar (d : ℕ) : Prop :=
  ∀ A B : Set (Site d),
    (∀ u ∈ A, ∀ v ∈ A, ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ (lattice d).Adj a b) u v) →
    (∀ u ∈ B, ∀ v ∈ B, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice d).Adj a b) u v) →
    (∀ z, z ∈ A → z ∈ B → False) →
    (∀ b ∈ B, ∀ z, (lattice d).Adj b z → z ∉ A → z ∈ B) →
    ∀ x y : Site d, (x ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c x) →
      (y ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c y) →
      ReflTransGen (fun a b => (a ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c a) ∧
        (b ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c b) ∧ xmh_star a b) x y


/-- The status of a vertex: in `A`; in the part `D₁` of the boundary; in the rest `D₂`
of the boundary; inside `B` but off the boundary; or elsewhere. -/
inductive ECSt
  | a | d1 | d2 | bi | o
  deriving DecidableEq

/-- Which statuses may be nearest neighbours. -/
def ECSt.okAdj : ECSt → ECSt → Bool
  | .bi, .a => false
  | .a, .bi => false
  | .o, .d1 => false
  | .d1, .o => false
  | .o, .d2 => false
  | .d2, .o => false
  | .o, .bi => false
  | .bi, .o => false
  | _, _ => true

/-- Which statuses may lie in a common unit square. -/
def ECSt.okNear : ECSt → ECSt → Bool
  | .d1, .d2 => false
  | .d2, .d1 => false
  | _, _ => true

/-- The edge indicator between `A` and `D₁`. -/
def ECSt.cross : ECSt → ECSt → ZMod 2
  | .a, .d1 => 1
  | .d1, .a => 1
  | _, _ => 0

theorem ECSt.cross_symm (s t : ECSt) : ECSt.cross s t = ECSt.cross t s := by
  cases s <;> cases t <;> rfl

theorem ec_square_parity : ∀ s0 s1 s2 s3 : ECSt,
    ECSt.okAdj s0 s1 = true → ECSt.okAdj s1 s3 = true → ECSt.okAdj s0 s2 = true →
    ECSt.okAdj s2 s3 = true → ECSt.okNear s0 s1 = true → ECSt.okNear s0 s2 = true →
    ECSt.okNear s0 s3 = true → ECSt.okNear s1 s2 = true → ECSt.okNear s1 s3 = true →
    ECSt.okNear s2 s3 = true →
    ECSt.cross s0 s1 + ECSt.cross s1 s3 = ECSt.cross s0 s2 + ECSt.cross s2 s3 := by
  intro s0 s1 s2 s3
  cases s0 <;> cases s1 <;> cases s2 <;> cases s3 <;> decide

theorem ECSt.cross_eq_zero_of_ne_a {s t : ECSt} (hs : s ≠ .a) (ht : t ≠ .a) :
    ECSt.cross s t = 0 := by
  cases s <;> cases t <;> simp_all [ECSt.cross]


private theorem ec_zmod2_add_self (a : ZMod 2) : a + a = 0 := CharTwo.add_self_eq_zero a

private theorem xmh3_poincare (d : ℕ) (H : (i : Fin d) → Site d → ZMod 2)
    (hclosed : ∀ i j, i ≠ j → ∀ p : Site d,
      H i p + H j (p + unit i) = H j p + H i (p + unit j)) :
    ∃ F : Site d → ZMod 2, ∀ i p, F (p + unit i) = F p + H i p := by
  have hc : ∀ p i j, H i p + H j (p + unit i) + H i (p + unit j) + H j p = 0 := by
    intro p i j
    by_cases hij : i = j
    · subst j
      generalize H i p = a
      generalize H i (p + unit i) = b
      revert a b
      decide
    · have h := hclosed i j hij p
      generalize H i p = a at h ⊢
      generalize H j (p + unit i) = b at h ⊢
      generalize H j p = c at h ⊢
      generalize H i (p + unit j) = e at h ⊢
      revert a b c e
      decide
  obtain ⟨F, hF⟩ := HigherDimLFPP.Perc.poincareMod2 d (fun p i => H i p) (by
    simpa only [unit] using hc)
  refine ⟨F, fun i p => ?_⟩
  have h := hF p i
  change F (p + unit i) - F p = H i p at h
  have ht : F (p + unit i) = H i p + F p := sub_eq_iff_eq_add.mp h
  simpa only [add_comm] using ht

/-- Chebyshev-adjacency: all coordinates differ by at most one.  (This is `xmh_star`
without the proviso of distinctness.) -/
def xmh3_near (a b : Site d) : Prop := ∀ i, |a i - b i| ≤ 1

theorem xmh3_unit_abs_le (i k : Fin d) : |(unit i : Site d) k| ≤ 1 := by
  by_cases h : k = i
  · subst h; simp [unit, Pi.single_eq_same]
  · simp [unit, Pi.single_eq_of_ne h]

theorem xmh3_near_refl (a : Site d) : xmh3_near a a := fun _ => by simp

theorem xmh3_near_symm {a b : Site d} (h : xmh3_near a b) : xmh3_near b a :=
  fun i => by rw [abs_sub_comm]; exact h i

theorem xmh3_near_of_adj {a b : Site d} (h : (lattice d).Adj a b) : xmh3_near a b := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [hi]; intro k
    rw [abs_sub_comm]
    simpa [Pi.add_apply, add_sub_cancel_right] using xmh3_unit_abs_le i k
  · rw [hi]; intro k
    simpa [Pi.add_apply, add_sub_cancel_left] using xmh3_unit_abs_le i k

open Classical in
/-- The status of a vertex. -/
noncomputable def xmh3_st (A B D1 : Set (Site d)) (z : Site d) : ECSt :=
  if z ∈ A then .a else if z ∈ D1 then .d1 else if z ∈ B then
    (if ∃ c ∈ A, (lattice d).Adj c z then .d2 else .bi) else .o

section
variable {A B D1 : Set (Site d)} {z : Site d}

theorem xmh3_st_cases (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z)
    (z : Site d) :
    (z ∈ A ∧ xmh3_st A B D1 z = .a) ∨
    (z ∉ A ∧ z ∈ B ∧ z ∈ D1 ∧ xmh3_st A B D1 z = .d1) ∨
    (z ∉ A ∧ z ∈ B ∧ z ∉ D1 ∧ (∃ c ∈ A, (lattice d).Adj c z) ∧
      xmh3_st A B D1 z = .d2) ∨
    (z ∉ A ∧ z ∈ B ∧ ¬ (∃ c ∈ A, (lattice d).Adj c z) ∧ xmh3_st A B D1 z = .bi) ∨
    (z ∉ A ∧ z ∉ B ∧ xmh3_st A B D1 z = .o) := by
  classical
  unfold xmh3_st
  by_cases hA : z ∈ A
  · left; simp [hA]
  · by_cases hD : z ∈ D1
    · right; left; exact ⟨hA, (hD1 z hD).1, hD, by simp [hA, hD]⟩
    · by_cases hB : z ∈ B
      · by_cases hc : ∃ c ∈ A, (lattice d).Adj c z
        · right; right; left; exact ⟨hA, hB, hD, hc, by simp [hA, hD, hB, hc]⟩
        · right; right; right; left; exact ⟨hA, hB, hc, by simp [hA, hD, hB, hc]⟩
      · right; right; right; right; exact ⟨hA, hB, by simp [hA, hD, hB]⟩

theorem xmh3_st_adj (hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → z ∉ A → z ∈ B)
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z) {z w : Site d}
    (h : (lattice d).Adj z w) :
    ECSt.okAdj (xmh3_st A B D1 z) (xmh3_st A B D1 w) = true := by
  have hs : (lattice d).Adj w z := h.symm
  have hI : w ∈ A → z ∈ B → ∃ c ∈ A, (lattice d).Adj c z := fun hw _ => ⟨w, hw, hs⟩
  have hII : z ∈ A → w ∈ B → ∃ c ∈ A, (lattice d).Adj c w := fun hz _ => ⟨z, hz, h⟩
  have hIII : w ∈ B → z ∉ A → z ∈ B := fun hw hz => hclose w hw z hs hz
  have hIV : z ∈ B → w ∉ A → w ∈ B := fun hz hw => hclose z hz w h hw
  rcases xmh3_st_cases hD1 z with ⟨hzA, hz⟩ | ⟨hzA, hzB, _, hz⟩ | ⟨hzA, hzB, _, _, hz⟩ |
      ⟨hzA, hzB, hzN, hz⟩ | ⟨hzA, hzB, hz⟩ <;>
  rcases xmh3_st_cases hD1 w with ⟨hwA, hw⟩ | ⟨hwA, hwB, _, hw⟩ | ⟨hwA, hwB, _, _, hw⟩ |
      ⟨hwA, hwB, hwN, hw⟩ | ⟨hwA, hwB, hw⟩ <;>
  rw [hz, hw] <;>
  first
  | rfl
  | simp_all

theorem xmh3_st_near (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z)
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → (∃ c ∈ A, (lattice d).Adj c y) → y ∉ D1 →
      ¬ xmh3_near x y)
    {z w : Site d} (h : xmh3_near z w) :
    ECSt.okNear (xmh3_st A B D1 z) (xmh3_st A B D1 w) = true := by
  have h' : xmh3_near w z := xmh3_near_symm h
  have hN1 : z ∈ D1 → w ∈ B → (∃ c ∈ A, (lattice d).Adj c w) → w ∉ D1 → False :=
    fun hz hwB hc hwD => hsep z hz w hwB hc hwD h
  have hN2 : w ∈ D1 → z ∈ B → (∃ c ∈ A, (lattice d).Adj c z) → z ∉ D1 → False :=
    fun hw hzB hc hzD => hsep w hw z hzB hc hzD h'
  rcases xmh3_st_cases hD1 z with ⟨hzA, hz⟩ | ⟨hzA, hzB, hzD1, hz⟩ | ⟨hzA, hzB, hzD2, hzc, hz⟩ |
      ⟨hzA, hzB, hzN, hz⟩ | ⟨hzA, hzB, hz⟩ <;>
  rcases xmh3_st_cases hD1 w with ⟨hwA, hw⟩ | ⟨hwA, hwB, hwD1, hw⟩ | ⟨hwA, hwB, hwD2, hwc, hw⟩ |
      ⟨hwA, hwB, hwN, hw⟩ | ⟨hwA, hwB, hw⟩ <;>
  rw [hz, hw] <;>
  first
  | rfl
  | simp_all

theorem xmh3_st_of_mem (hz : z ∈ A) : xmh3_st A B D1 z = .a := by
  classical
  unfold xmh3_st; simp [hz]

theorem xmh3_st_ne_a (hz : z ∉ A) : xmh3_st A B D1 z ≠ .a := by
  classical
  unfold xmh3_st; simp only [hz, ite_false]; split_ifs <;> simp

theorem xmh3_st_d1 (hzA : z ∉ A) (hzD : z ∈ D1) : xmh3_st A B D1 z = .d1 := by
  classical
  unfold xmh3_st; simp [hzA, hzD]

theorem xmh3_st_d2 (hzA : z ∉ A) (hzD : z ∉ D1) (hzB : z ∈ B)
    (hc : ∃ c ∈ A, (lattice d).Adj c z) : xmh3_st A B D1 z = .d2 := by
  classical
  unfold xmh3_st; simp [hzA, hzD, hzB, hc]

end

/-! ### Chebyshev-nearness of the elementary displacements -/

theorem xmh3_unit_eq_zero_or_one (i k : Fin d) :
    (unit i : Site d) k = 0 ∨ (unit i : Site d) k = 1 := by
  by_cases h : k = i
  · right; rw [unit, h, Pi.single_eq_same]
  · left; rw [unit, Pi.single_eq_of_ne h]

theorem xmh3_unit_eq_one {i k : Fin d} (h : (unit i : Site d) k = 1) : k = i := by
  by_contra hk
  rw [unit, Pi.single_eq_of_ne hk] at h
  exact one_ne_zero h.symm

theorem xmh3_unit_sub_abs_le (i j k : Fin d) : |(unit i : Site d) k - unit j k| ≤ 1 := by
  rcases xmh3_unit_eq_zero_or_one i k with h | h <;>
    rcases xmh3_unit_eq_zero_or_one j k with h' | h' <;>
    rw [h, h'] <;> norm_num

theorem xmh3_unit_add_abs_le {i j : Fin d} (hij : i ≠ j) (k : Fin d) :
    |(unit i : Site d) k + unit j k| ≤ 1 := by
  rcases xmh3_unit_eq_zero_or_one i k with h | h <;>
    rcases xmh3_unit_eq_zero_or_one j k with h' | h'
  · rw [h, h']; norm_num
  · rw [h, h']; norm_num
  · rw [h, h']; norm_num
  · exact (hij ((xmh3_unit_eq_one h).symm.trans (xmh3_unit_eq_one h'))).elim

theorem xmh3_near_add_unit (p : Site d) (i : Fin d) : xmh3_near p (p + unit i) := by
  intro k
  rw [abs_sub_comm]
  simpa [Pi.add_apply, add_sub_cancel_right] using xmh3_unit_abs_le i k

theorem xmh3_near_add_units {i j : Fin d} (hij : i ≠ j) (p : Site d) :
    xmh3_near p (p + unit i + unit j) := by
  intro k
  rw [abs_sub_comm]
  have h : (p + unit i + unit j) k - p k = (unit i) k + (unit j) k := by
    simp only [Pi.add_apply]; ring
  rw [h]
  exact xmh3_unit_add_abs_le hij k

theorem xmh3_near_units (i j : Fin d) (p : Site d) :
    xmh3_near (p + unit i) (p + unit j) := by
  intro k
  have h : (p + unit i) k - (p + unit j) k = (unit i) k - (unit j) k := by
    simp only [Pi.add_apply]; ring
  rw [h]
  exact xmh3_unit_sub_abs_le i j k

theorem xmh3_near_add_unit_left (p : Site d) (i j : Fin d) :
    xmh3_near (p + unit i) (p + unit i + unit j) := by
  intro k
  rw [abs_sub_comm]
  have h : (p + unit i + unit j) k - (p + unit i) k = (unit j) k := by
    simp only [Pi.add_apply]; ring
  rw [h]
  exact xmh3_unit_abs_le j k

theorem xmh3_near_add_unit_right (p : Site d) (i j : Fin d) :
    xmh3_near (p + unit j) (p + unit i + unit j) := by
  intro k
  have h : (p + unit j) k - (p + unit i + unit j) k = -((unit i) k) := by
    simp only [Pi.add_apply]; ring
  rw [h, abs_neg]
  exact xmh3_unit_abs_le i k

/-! ### The boundary cocycle is a coboundary -/

section
variable {A B D1 : Set (Site d)}

theorem xmh3_coboundary (hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → z ∉ A → z ∈ B)
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z)
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → (∃ c ∈ A, (lattice d).Adj c y) → y ∉ D1 →
      ¬ xmh3_near x y) :
    ∃ f : Site d → ZMod 2, ∀ u v, (lattice d).Adj u v →
      f u + f v = ECSt.cross (xmh3_st A B D1 u) (xmh3_st A B D1 v) := by
  have hclosed : ∀ i j, i ≠ j → ∀ p : Site d,
      ECSt.cross (xmh3_st A B D1 p) (xmh3_st A B D1 (p + unit i))
        + ECSt.cross (xmh3_st A B D1 (p + unit i)) (xmh3_st A B D1 (p + unit i + unit j))
      = ECSt.cross (xmh3_st A B D1 p) (xmh3_st A B D1 (p + unit j))
        + ECSt.cross (xmh3_st A B D1 (p + unit j)) (xmh3_st A B D1 (p + unit j + unit i)) := by
    intro i j hij p
    have h01 := xmh3_st_adj hclose hD1 (show (lattice d).Adj p (p + unit i) from ⟨i, Or.inl rfl⟩)
    have h13 := xmh3_st_adj hclose hD1
      (show (lattice d).Adj (p + unit i) (p + unit i + unit j) from ⟨j, Or.inl rfl⟩)
    have h02 := xmh3_st_adj hclose hD1 (show (lattice d).Adj p (p + unit j) from ⟨j, Or.inl rfl⟩)
    have h23 := xmh3_st_adj hclose hD1
      (show (lattice d).Adj (p + unit j) (p + unit i + unit j) from ⟨i, Or.inl (by abel)⟩)
    have n01 := xmh3_st_near hD1 hsep (xmh3_near_add_unit p i)
    have n02 := xmh3_st_near hD1 hsep (xmh3_near_add_unit p j)
    have n03 := xmh3_st_near hD1 hsep (xmh3_near_add_units hij p)
    have n12 := xmh3_st_near hD1 hsep (xmh3_near_units i j p)
    have n13 := xmh3_st_near hD1 hsep (xmh3_near_add_unit_left p i j)
    have n23 := xmh3_st_near hD1 hsep (xmh3_near_add_unit_right p i j)
    have hsq := ec_square_parity _ _ _ _ h01 h13 h02 h23 n01 n02 n03 n12 n13 n23
    rw [show (p + unit j + unit i : Site d) = p + unit i + unit j by abel]
    exact hsq
  obtain ⟨F, hF⟩ := xmh3_poincare d
    (fun i p => ECSt.cross (xmh3_st A B D1 p) (xmh3_st A B D1 (p + unit i))) hclosed
  refine ⟨F, ?_⟩
  intro u v huv
  obtain ⟨i, hi | hi⟩ := huv
  · rw [hi, hF i u, ← add_assoc, ec_zmod2_add_self, zero_add]
  · rw [hi, hF i v, add_assoc,
      add_comm (ECSt.cross (xmh3_st A B D1 v) (xmh3_st A B D1 (v + unit i))) (F v),
      ← add_assoc, ec_zmod2_add_self, zero_add, ECSt.cross_symm]

end

/-! ### The boundary is `*`-connected -/

/-- The boundary between connected sets is star-connected. -/
theorem xmh3_boundaryStar (d : ℕ) : xmh_BoundaryStar d := by
  intro A B hA hB hdisj hclose x y hx hy
  classical
  by_contra hne
  set R : Site d → Site d → Prop := fun a b => (a ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c a) ∧
      (b ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c b) ∧ xmh_star a b
  set D1 : Set (Site d) := {z | (z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z) ∧ ReflTransGen R x z}
  have hyD1 : y ∉ D1 := fun h => hne h.2
  have hxD1 : x ∈ D1 := ⟨hx, ReflTransGen.refl⟩
  have hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z := fun z hz => hz.1
  have hsep : ∀ x' ∈ D1, ∀ y', y' ∈ B → (∃ c ∈ A, (lattice d).Adj c y') → y' ∉ D1 →
      ¬ xmh3_near x' y' := by
    intro x' hx' y' hy'B hy'c hy'D hnear
    apply hy'D
    refine ⟨⟨hy'B, hy'c⟩, hx'.2.tail ?_⟩
    exact ⟨hx'.1, ⟨hy'B, hy'c⟩, (fun heq => hy'D (heq ▸ hx')), hnear⟩
  obtain ⟨f, hf⟩ := xmh3_coboundary hclose hD1 hsep
  have char2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have hfA : ∀ u ∈ A, ∀ v ∈ A, f u = f v := by
    intro u hu v hv
    have hstep : ∀ v, ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ (lattice d).Adj a b) u v →
        f u = f v := by
      intro v h
      induction h with
      | refl => rfl
      | tail _ hbc ih =>
        refine ih.trans (char2 _ _ ?_)
        rw [hf _ _ hbc.2.2, xmh3_st_of_mem hbc.1, xmh3_st_of_mem hbc.2.1]
        rfl
    exact hstep v (hA u hu v hv)
  have hfB : ∀ u ∈ B, ∀ v ∈ B, f u = f v := by
    intro u hu v hv
    have hstep : ∀ v, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice d).Adj a b) u v →
        f u = f v := by
      intro v h
      induction h with
      | refl => rfl
      | tail _ hbc ih =>
        refine ih.trans (char2 _ _ ?_)
        rw [hf _ _ hbc.2.2]
        exact ECSt.cross_eq_zero_of_ne_a (xmh3_st_ne_a fun h => hdisj _ h hbc.1)
          (xmh3_st_ne_a fun h => hdisj _ h hbc.2.1)
    exact hstep v (hB u hu v hv)
  obtain ⟨a1, ha1, hadj1⟩ := hx.2
  obtain ⟨a2, ha2, hadj2⟩ := hy.2
  have hxA : x ∉ A := fun h => hdisj _ h hx.1
  have hyA : y ∉ A := fun h => hdisj _ h hy.1
  have e1 : f a1 + f x = 1 := by
    rw [hf _ _ hadj1, xmh3_st_of_mem ha1, xmh3_st_d1 hxA hxD1]
    rfl
  have e2 : f a2 + f y = 0 := by
    rw [hf _ _ hadj2, xmh3_st_of_mem ha2, xmh3_st_d2 hyA hyD1 hy.1 ⟨a2, ha2, hadj2⟩]
    rfl
  have h3 := hfA a1 ha1 a2 ha2
  have h4 := hfB x hx.1 y hy.1
  rw [h3, h4, e2] at e1
  exact absurd e1 (by decide)

/-- Every integer between the coordinates of two sites in a star-connected set is attained. -/
theorem exists_site_coord_eq_of_star_connected {S : Set (Site d)}
    (hS : xmh_SConn S) {x y : Site d} (hx : x ∈ S) (hy : y ∈ S) (i : Fin d)
    {k : ℤ} (hxk : x i ≤ k) (hky : k ≤ y i) : ∃ z ∈ S, z i = k := by
  have hpath := hS x hx y hy
  have hstep : ∀ z, ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ xmh_star a b) x z →
      ∀ k : ℤ, x i ≤ k → k ≤ z i → ∃ w ∈ S, w i = k := by
    intro z hz
    induction hz with
    | refl =>
      intro k hk1 hk2
      exact ⟨x, hx, by omega⟩
    | @tail z w _ hzw ih =>
      intro k hk1 hk2
      by_cases hkz : k ≤ z i
      · exact ih k hk1 hkz
      · have hbound := (abs_le.mp (hzw.2.2.2 i)).1
        exact ⟨w, hzw.2.1, by omega⟩
  exact hstep y hpath k hxk hky

/-- A finite star-connected set has at least as many sites as the integer interval spanned
by any two of its coordinates. -/
theorem coord_span_add_one_le_ncard {S : Set (Site d)} (hfin : S.Finite)
    (hS : xmh_SConn S) {x y : Site d} (hx : x ∈ S) (hy : y ∈ S) (i : Fin d)
    (hxy : x i ≤ y i) : y i - x i + 1 ≤ (S.ncard : ℤ) := by
  classical
  let T := hfin.toFinset
  have hsub : Finset.Icc (x i) (y i) ⊆ T.image (fun z => z i) := by
    intro k hk
    obtain ⟨z, hz, hzk⟩ := exists_site_coord_eq_of_star_connected hS hx hy i
      (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    exact Finset.mem_image.mpr ⟨z, by simpa [T] using hz, hzk⟩
  have hc : ((Finset.Icc (x i) (y i)).card : ℤ) ≤ (T.card : ℤ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_image_le)
  have hinterval : ((Finset.Icc (x i) (y i)).card : ℤ) = y i - x i + 1 := by
    have hi := Int.card_Icc_of_le (a := x i) (b := y i) (by omega)
    omega
  rw [hinterval] at hc
  simpa [T, Set.ncard_eq_toFinset_card _ hfin] using hc

/-- A coordinate segment avoids a set if a different coordinate is fixed outside its projection. -/
theorem path_update_avoiding {A : Set (Site d)} (x : Site d) (i j : Fin d) (t : ℤ)
    (hji : j ≠ i) (hsep : ∀ a ∈ A, a j ≠ x j) :
    ReflTransGen (fun a b => a ∈ Aᶜ ∧ b ∈ Aᶜ ∧ (lattice d).Adj a b)
      x (Function.update x i t) := by
  have hp := HigherDimLFPP.Perc.reflTransGen_update (S := Aᶜ) x i t (by
    intro s _ _ hs
    apply hsep _ hs
    simp [Function.update_of_ne hji])
  apply ReflTransGen.mono (r := HigherDimLFPP.Perc.StepIn Aᶜ HigherDimLFPP.Perc.LAdj) ?_ _ _ hp
  intro a b hab
  refine ⟨hab.1, hab.2.1, ?_⟩
  obtain ⟨k, hk | hk⟩ := HigherDimLFPP.Perc.LAdj.exists_eq_add_single hab.2.2
  · exact ⟨k, Or.inl (by simpa [unit] using hk)⟩
  · exact ⟨k, Or.inr (by simpa [unit] using hk)⟩

/-- Every site outside a bounding rectangle can reach its lower-left exterior corner
without entering the bounded set. -/
theorem path_to_exterior_corner (A : Set (Site 2)) (l₀ r₀ l₁ r₁ : ℤ)
    (hbox : ∀ a ∈ A, l₀ ≤ a 0 ∧ a 0 ≤ r₀ ∧ l₁ ≤ a 1 ∧ a 1 ≤ r₁)
    (x : Site 2) (hx : x 0 < l₀ ∨ r₀ < x 0 ∨ x 1 < l₁ ∨ r₁ < x 1) :
    ReflTransGen (fun a b => a ∈ Aᶜ ∧ b ∈ Aᶜ ∧ (lattice 2).Adj a b)
      x ![l₀ - 1, l₁ - 1] := by
  have hhorizontal : x 0 < l₀ ∨ r₀ < x 0 →
      ReflTransGen (fun a b => a ∈ Aᶜ ∧ b ∈ Aᶜ ∧ (lattice 2).Adj a b)
        x ![l₀ - 1, l₁ - 1] := by
    intro hx0
    have p1 := path_update_avoiding x 1 0 (l₁ - 1) (by decide) (A := A) (by
      intro a ha
      have hb := hbox a ha
      omega)
    have p2 := path_update_avoiding (Function.update x 1 (l₁ - 1)) 0 1 (l₀ - 1)
      (by decide) (A := A) (by
        intro a ha
        have hb := hbox a ha
        simp only [Function.update_self]
        omega)
    convert p1.trans p2 using 1
    funext i
    fin_cases i <;> simp
  have hvertical : x 1 < l₁ ∨ r₁ < x 1 →
      ReflTransGen (fun a b => a ∈ Aᶜ ∧ b ∈ Aᶜ ∧ (lattice 2).Adj a b)
        x ![l₀ - 1, l₁ - 1] := by
    intro hx1
    have p1 := path_update_avoiding x 0 1 (l₀ - 1) (by decide) (A := A) (by
      intro a ha
      have hb := hbox a ha
      omega)
    have p2 := path_update_avoiding (Function.update x 0 (l₀ - 1)) 1 0 (l₁ - 1)
      (by decide) (A := A) (by
        intro a ha
        have hb := hbox a ha
        simp only [Function.update_self]
        omega)
    convert p1.trans p2 using 1
    funext i
    fin_cases i <;> simp
  rcases hx with h | h | h | h
  · exact hhorizontal (Or.inl h)
  · exact hhorizontal (Or.inr h)
  · exact hvertical (Or.inl h)
  · exact hvertical (Or.inr h)

theorem xmh_rtg_symm {α : Type*} {R : α → α → Prop} (h : ∀ a b, R a b → R b a) {a b : α}
    (hab : ReflTransGen R a b) : ReflTransGen R b a := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (h _ _ hbc) ih

/-- A component is closed under an adjacent step that remains in the underlying set. -/
theorem xmh_componentIn_step {S : Set (Site d)} {x b z : Site d}
    (hb : b ∈ componentIn S x) (hz : z ∈ S) (hbz : (lattice d).Adj b z) :
    z ∈ componentIn S x := by
  obtain ⟨hx, hbS, hreach⟩ := hb
  refine ⟨hx, hz, hreach.trans ?_⟩
  exact SimpleGraph.Adj.reachable (by simpa [SimpleGraph.induce_adj] using hbz)

/-- Membership in a component supplies a finite nearest-neighbour walk within the underlying
set, represented as a sequence of sites. -/
theorem xmh_walk_of_component {S : Set (Site d)} {x y : Site d}
    (h : y ∈ componentIn S x) :
    ∃ (m : ℕ) (c : ℕ → Site d), c 0 = x ∧ c m = y ∧ (∀ s, s ≤ m → c s ∈ S) ∧
      ∀ s, s < m → (lattice d).Adj (c s) (c (s + 1)) := by
  obtain ⟨hx, hy, hreach⟩ := h
  obtain ⟨w⟩ := hreach
  refine ⟨w.length, fun s => (w.getVert s).1, ?_, ?_, ?_, ?_⟩
  · simp
  · simp only
    rw [SimpleGraph.Walk.getVert_length]
  · intro s _
    exact (w.getVert s).2
  · intro s hs
    have := w.adj_getVert_succ hs
    simpa [SimpleGraph.induce_adj] using this

/-- The component of `x` in `S` is connected by nearest-neighbour steps inside itself. -/
theorem xmh7_componentIn_conn {S : Set (Site d)} {x u v : Site d}
    (hu : u ∈ componentIn S x) (hv : v ∈ componentIn S x) :
    ReflTransGen (fun a b => a ∈ componentIn S x ∧ b ∈ componentIn S x ∧
      (lattice d).Adj a b) u v := by
  have key : ∀ (m : ℕ) (c : ℕ → Site d), c 0 = x →
      (∀ s ≤ m, c s ∈ S) → (∀ s < m, (lattice d).Adj (c s) (c (s + 1))) →
      (∀ s ≤ m, c s ∈ componentIn S x) ∧
        ReflTransGen (fun a b => a ∈ componentIn S x ∧ b ∈ componentIn S x ∧
          (lattice d).Adj a b) x (c m) := by
    intro m
    induction m with
    | zero =>
        intro c hc0 hS _
        refine ⟨?_, ?_⟩
        · intro s hs
          have hs0 : s = 0 := Nat.le_zero.mp hs
          subst hs0
          rw [hc0]
          exact ⟨hu.1, hu.1, SimpleGraph.Reachable.refl _⟩
        · rw [hc0]
    | succ m ih =>
        intro c hc0 hS hadj
        obtain ⟨ihmem, ihtg⟩ := ih c hc0
          (fun s hs => hS s (le_trans hs (Nat.le_succ m)))
          (fun s hs => hadj s (lt_of_lt_of_le hs (Nat.le_succ m)))
        have hcmem : c (m + 1) ∈ componentIn S x :=
          xmh_componentIn_step (ihmem m le_rfl) (hS (m + 1) le_rfl)
            (hadj m (Nat.lt_succ_self m))
        refine ⟨?_, ihtg.tail ⟨ihmem m le_rfl, hcmem, hadj m (Nat.lt_succ_self m)⟩⟩
        intro s hs
        rcases Nat.lt_or_eq_of_le hs with h | h
        · exact ihmem s (Nat.lt_succ_iff.mp h)
        · rw [h]; exact hcmem
  obtain ⟨mu, cu, hcu0, hcum, hcuS, hcuadj⟩ := xmh_walk_of_component hu
  obtain ⟨mv, cv, hcv0, hcvm, hcvS, hcvadj⟩ := xmh_walk_of_component hv
  have h1 := (key mu cu hcu0 hcuS hcuadj).2
  rw [hcum] at h1
  have h2 := (key mv cv hcv0 hcvS hcvadj).2
  rw [hcvm] at h2
  exact (xmh_rtg_symm (fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩) h1).trans h2


/-- A path inside a set ends in the component of its starting site. -/
theorem mem_componentIn_of_path {S : Set (Site d)} {x y : Site d} (hx : x ∈ S)
    (h : ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ (lattice d).Adj a b) x y) :
    y ∈ componentIn S x := by
  induction h with
  | refl => exact ⟨hx, hx, SimpleGraph.Reachable.refl _⟩
  | tail _ hbc ih => exact xmh_componentIn_step ih hbc.2.1 hbc.2.2

/-- The boundary of a complement component of a finite open cluster is finite,
star-connected, and consists of closed sites. -/
theorem component_exterior_boundary {S : Set (Site d)} {x : Site d}
    (hfinite : (componentIn S x).Finite) (p : Site d) :
    let A := componentIn S x
    let B := componentIn Aᶜ p
    let D := {z | z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z}
    D.Finite ∧ D ⊆ Sᶜ ∧ xmh_SConn D := by
  dsimp only
  let A := componentIn S x
  let B := componentIn Aᶜ p
  let D : Set (Site d) := {z | z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z}
  change D.Finite ∧ D ⊆ Sᶜ ∧ xmh_SConn D
  have hA : A.Finite := hfinite
  have hDfinite : D.Finite := by
    classical
    let T := hA.toFinset.biUnion nbrFinset
    refine T.finite_toSet.subset ?_
    intro z hz
    obtain ⟨_, a, ha, haz⟩ := hz
    apply Finset.mem_coe.mpr
    refine Finset.mem_biUnion.mpr ⟨a, by simpa using ha, ?_⟩
    obtain ⟨i, hi | hi⟩ := haz
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hi]⟩
    · have hz : z = a - unit i := by rw [hi]; abel
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hz]⟩
  refine ⟨hDfinite, ?_, ?_⟩
  · intro z hz hzS
    obtain ⟨hzB, a, haA, haz⟩ := hz
    exact hzB.2.1 (xmh_componentIn_step haA hzS haz)
  · intro u hu v hv
    exact xmh3_boundaryStar d A B
      (fun _ ha _ hb => xmh7_componentIn_conn ha hb)
      (fun _ ha _ hb => xmh7_componentIn_conn ha hb)
      (fun _ ha hb => hb.2.1 ha)
      (fun _ hb _ hab hz => xmh_componentIn_step hb hz hab)
      u v hu hv

/-- A finite planar open cluster has a finite closed star-connected exterior boundary.
Its cardinality exceeds each coordinate span of the cluster by at least three. -/
theorem finite_cluster_exterior_boundary {S : Set (Site 2)} {x : Site 2} (hx : x ∈ S)
    (hfinite : (componentIn S x).Finite) :
    ∃ p : Site 2,
      let A := componentIn S x
      let B := componentIn Aᶜ p
      let D := {z | z ∈ B ∧ ∃ c ∈ A, (lattice 2).Adj c z}
      B.Infinite ∧ D.Finite ∧ D.Nonempty ∧ D ⊆ Sᶜ ∧ xmh_SConn D ∧
        ∀ i : Fin 2, ∀ u ∈ A, ∀ v ∈ A, v i - u i + 3 ≤ (D.ncard : ℤ) := by
  classical
  let A := componentIn S x
  let T := hfinite.toFinset
  have hxA : x ∈ A := ⟨hx, hx, SimpleGraph.Reachable.refl _⟩
  have hT : T.Nonempty := ⟨x, by simpa [T] using hxA⟩
  obtain ⟨a₀, ha₀, hmin₀⟩ := Finset.exists_min_image T (fun a => a 0) hT
  obtain ⟨b₀, hb₀, hmax₀⟩ := Finset.exists_max_image T (fun a => a 0) hT
  obtain ⟨a₁, ha₁, hmin₁⟩ := Finset.exists_min_image T (fun a => a 1) hT
  obtain ⟨b₁, hb₁, hmax₁⟩ := Finset.exists_max_image T (fun a => a 1) hT
  have ha₀A : a₀ ∈ A := by simpa [T] using ha₀
  have hb₀A : b₀ ∈ A := by simpa [T] using hb₀
  have ha₁A : a₁ ∈ A := by simpa [T] using ha₁
  have hb₁A : b₁ ∈ A := by simpa [T] using hb₁
  have hbox : ∀ a ∈ A, a₀ 0 ≤ a 0 ∧ a 0 ≤ b₀ 0 ∧ a₁ 1 ≤ a 1 ∧ a 1 ≤ b₁ 1 := by
    intro a ha
    have haT : a ∈ T := by simpa [T] using ha
    exact ⟨hmin₀ a haT, hmax₀ a haT, hmin₁ a haT, hmax₁ a haT⟩
  let L : Site 2 := a₀ - unit 0
  let R : Site 2 := b₀ + unit 0
  let U : Site 2 := b₁ + unit 1
  let V : Site 2 := a₁ - unit 1
  let B := componentIn Aᶜ L
  let D : Set (Site 2) := {z | z ∈ B ∧ ∃ c ∈ A, (lattice 2).Adj c z}
  have hLout : L 0 < a₀ 0 := by simp [L, unit]
  have hRout : b₀ 0 < R 0 := by simp [R, unit]
  have hUout : b₁ 1 < U 1 := by simp [U, unit]
  have hVout : V 1 < a₁ 1 := by simp [V, unit]
  have hL : L ∈ Aᶜ := by
    intro h
    have h' := hbox L h
    omega
  have hB : ∀ y : Site 2, y 0 < a₀ 0 ∨ b₀ 0 < y 0 ∨ y 1 < a₁ 1 ∨ b₁ 1 < y 1 → y ∈ B := by
    intro y hy
    have hp := path_to_exterior_corner A (a₀ 0) (b₀ 0) (a₁ 1) (b₁ 1) hbox L
      (Or.inl hLout)
    have hq := path_to_exterior_corner A (a₀ 0) (b₀ 0) (a₁ 1) (b₁ 1) hbox y hy
    have hsymm := xmh_rtg_symm (fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩) hq
    exact mem_componentIn_of_path hL (hp.trans hsymm)
  have hLD : L ∈ D := by
    refine ⟨hB L (Or.inl hLout), a₀, ha₀A, ⟨0, Or.inr ?_⟩⟩
    dsimp [L]
    abel
  have hRD : R ∈ D := ⟨hB R (Or.inr (Or.inl hRout)), b₀, hb₀A, ⟨0, Or.inl rfl⟩⟩
  have hUD : U ∈ D := ⟨hB U (Or.inr (Or.inr (Or.inr hUout))), b₁, hb₁A,
    ⟨1, Or.inl rfl⟩⟩
  have hVD : V ∈ D := by
    refine ⟨hB V (Or.inr (Or.inr (Or.inl hVout))), a₁, ha₁A, ⟨1, Or.inr ?_⟩⟩
    dsimp [V]
    abel
  obtain ⟨hDfin, hDclosed, hDconn⟩ := component_exterior_boundary hfinite L
  have hDfin' : D.Finite := hDfin
  have hDclosed' : D ⊆ Sᶜ := hDclosed
  have hDconn' : xmh_SConn D := hDconn
  have hBinf : B.Infinite := by
    let f : ℕ → Site 2 := fun n => ![a₀ 0 - ((n : ℤ) + 1), 0]
    have hinj : Function.Injective f := by
      intro n m h
      have h0 := congrFun h 0
      simp [f] at h0
      omega
    refine (Set.infinite_range_of_injective hinj).mono ?_
    rintro _ ⟨n, rfl⟩
    apply hB
    left
    simp [f]
  refine ⟨L, ?_⟩
  change B.Infinite ∧ D.Finite ∧ D.Nonempty ∧ D ⊆ Sᶜ ∧ xmh_SConn D ∧ _
  refine ⟨hBinf, hDfin', ⟨L, hLD⟩, hDclosed', hDconn', ?_⟩
  intro i u hu v hv
  have hu' := hbox u hu
  have hv' := hbox v hv
  fin_cases i
  · change v 0 - u 0 + 3 ≤ (D.ncard : ℤ)
    have hLR : L 0 ≤ R 0 := by
      have h := hbox b₀ hb₀A
      simp [L, R, unit]
      omega
    have hc := coord_span_add_one_le_ncard hDfin' hDconn' hLD hRD 0 hLR
    simp [L, R, unit] at hc
    omega
  · change v 1 - u 1 + 3 ≤ (D.ncard : ℤ)
    have hVU : V 1 ≤ U 1 := by
      have h := hbox b₁ hb₁A
      simp [V, U, unit]
      omega
    have hc := coord_span_add_one_le_ncard hDfin' hDconn' hVD hUD 1 hVU
    simp [V, U, unit] at hc
    omega

end LatticeProb.Percolation.Peierls.Boundary
