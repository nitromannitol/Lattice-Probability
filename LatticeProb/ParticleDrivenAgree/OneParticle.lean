/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.OneParticle at commit 66d817d; only the module paths and the namespace `Parking` are renamed
   (to `LatticeProb.ParticleDrivenAgree`). -/
/-
Lemma 3.3 of `parking.tex`: adding one particle to the configuration changes
the state by exactly one active particle at one site, or by exactly one
unfilled hole at one site, and never by both.

The discrepancy is carried through the rounds as `OneParticleInv`: either the
second process has one active particle the first has not and the holes agree,
or the actives agree and the first process has one unfilled hole the second has
not.  The base case splits on the sign of the count at the site: raising a
nonnegative count adds the next label there and leaves the holes alone, raising
a negative one cancels a hole and leaves the actives alone.

The step is a count.  Writing `A` for the arrivals at the site in question and
`h` for the holes there, `min(|A|, h)` of the arrivals settle, and the ones
that do not are those the round's order puts at rank `h` or above
(`settledIn`, `card_settledIn`).  Adding an arrival cannot make a survivor
settle, and neither can removing a hole (`survivors_subset_insert`,
`survivors_subset_holes`), so the survivors of the second process contain those
of the first, and the two counts decide which case holds:

- from the extra particle, at the site it reaches: if `|A| + 1 ≤ h` every
  arrival settles in both and the second process is left one hole short; if
  `h ≤ |A|` both fill all `h` holes and exactly one particle is left over;
- from the extra hole, at its site: if `|A| ≤ h - 1` every arrival settles in
  both and the extra hole survives; if `h ≤ |A|` one common particle settles
  only in the first process.

Where exactly one particle is left over, `eq_insert_of_card_succ` names it, and
nothing in the argument has to say which particle that is.
-/
import LatticeProb.ParticleDrivenAgree.Coupling

/-!
# Lemma 3.3: the one-particle coupling discrepancy

Lemma 3.3 of `parking.tex`: adding one particle to the configuration changes
the state by exactly one active particle at one site, or by exactly one
unfilled hole at one site, and never by both.

The discrepancy is carried through the rounds as `OneParticleInv`: either the
second process has one active particle the first has not and the holes agree,
or the actives agree and the first process has one unfilled hole the second has
not. The base case splits on the sign of the count at the site: raising a
nonnegative count adds the next label there and leaves the holes alone, raising
a negative one cancels a hole and leaves the actives alone.

The step is a count.  Writing `A` for the arrivals at the site in question and
`h` for the holes there, `min(|A|, h)` of the arrivals settle, and the ones
that do not are those the round's order puts at rank `h` or above
(`settledIn`, `card_settledIn`).  Adding an arrival cannot make a survivor
settle, and neither can removing a hole (`survivors_subset_insert`,
`survivors_subset_holes`), so the survivors of the second process contain those
of the first, and the two counts decide which case holds:

- from the extra particle, at the site it reaches: if `|A| + 1 ≤ h` every
  arrival settles in both and the second process is left one hole short; if
  `h ≤ |A|` both fill all `h` holes and exactly one particle is left over;
- from the extra hole, at its site: if `|A| ≤ h - 1` every arrival settles in
  both and the extra hole survives; if `h ≤ |A|` one common particle settles
  only in the first process.

Where exactly one particle is left over, `eq_insert_of_card_succ` names it, and
nothing in the argument has to say which particle that is.
-/

noncomputable section

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {d : ℕ}

/-! ### Who settles, abstractly -/

section Abstract

variable {α : Type*} [DecidableEq α] {r : α → α → Prop} [DecidableRel r]

/-- The elements of `A` that the order `r` puts below the threshold `h`. -/
def settledIn (A : Finset α) (r : α → α → Prop) [DecidableRel r] (h : ℕ) : Finset α :=
  A.filter fun p => (A.filter fun q => r q p).card < h

omit [DecidableEq α] in
/-- `settledIn A r h` is a subset of `A`. -/
theorem settledIn_subset (A : Finset α) (h : ℕ) : settledIn A r h ⊆ A :=
  Finset.filter_subset _ _

/-- When `A.card ≤ h`, every element of `A` counts as settled: `settledIn A r h = A`. -/
theorem settledIn_eq_self (hirr : ∀ a, ¬ r a a) (htr : ∀ a b c, r a b → r b c → r a c)
    (htot : ∀ a b, a ≠ b → r a b ∨ r b a) {A : Finset α} {h : ℕ} (hA : A.card ≤ h) :
    settledIn A r h = A := by
  refine Finset.eq_of_subset_of_card_le (settledIn_subset A h) ?_
  rw [settledIn, card_filter_countLT_lt hirr htr htot h]
  omega

/-- The number of settled elements of `A` is `min A.card h`. -/
theorem card_settledIn (hirr : ∀ a, ¬ r a a) (htr : ∀ a b c, r a b → r b c → r a c)
    (htot : ∀ a b, a ≠ b → r a b ∨ r b a) (A : Finset α) (h : ℕ) :
    (settledIn A r h).card = min A.card h :=
  card_filter_countLT_lt hirr htr htot h

/-- Adding an element to the pool cannot make an element that survived settle. -/
theorem survivors_subset_insert {A : Finset α} (u : α) (h : ℕ) :
    A \ settledIn A r h ⊆ insert u A \ settledIn (insert u A) r h := by
  intro p hp
  rw [Finset.mem_sdiff] at hp ⊢
  obtain ⟨hpA, hps⟩ := hp
  refine ⟨Finset.mem_insert_of_mem hpA, ?_⟩
  intro hq
  refine hps ?_
  rw [settledIn, Finset.mem_filter] at hq ⊢
  refine ⟨hpA, lt_of_le_of_lt (Finset.card_le_card ?_) hq.2⟩
  exact Finset.filter_subset_filter _ (Finset.subset_insert _ _)

/-- Removing a hole cannot make an element that survived settle. -/
theorem survivors_subset_holes {A : Finset α} {h h' : ℕ} (hh : h' ≤ h) :
    A \ settledIn A r h ⊆ A \ settledIn A r h' := by
  intro p hp
  rw [Finset.mem_sdiff] at hp ⊢
  refine ⟨hp.1, fun hq => hp.2 ?_⟩
  rw [settledIn, Finset.mem_filter] at hq ⊢
  exact ⟨hq.1, lt_of_lt_of_le hq.2 hh⟩

/-- A subset whose complement has one element is an insertion. -/
theorem eq_insert_of_card_succ {S T : Finset α} (hsub : S ⊆ T) (hcard : T.card = S.card + 1) :
    ∃ v, v ∉ S ∧ T = insert v S := by
  have hc : (T \ S).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]; omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  refine ⟨v, ?_, ?_⟩
  · intro hvS
    have : v ∈ T \ S := hv ▸ Finset.mem_singleton_self v
    exact (Finset.mem_sdiff.mp this).2 hvS
  · have hvS : v ∉ S := by
      intro hvS
      have : v ∈ T \ S := hv ▸ Finset.mem_singleton_self v
      exact (Finset.mem_sdiff.mp this).2 hvS
    refine Finset.eq_of_subset_of_card_le (fun q hq => ?_) ?_
    · by_cases hqS : q ∈ S
      · exact Finset.mem_insert_of_mem hqS
      · have : q ∈ T \ S := Finset.mem_sdiff.mpr ⟨hq, hqS⟩
        rw [hv, Finset.mem_singleton] at this
        exact this ▸ Finset.mem_insert_self _ _
    · rw [Finset.card_insert_of_notMem hvS, hcard]

end Abstract

/-! ### One round, in counts -/

/-- The particles active at `x` after round `t + 1` are exactly that round's arrivals
at `x` that did not settle. -/
theorem pActiveAt_succ_eq (D : PDriver d) (t : ℕ) (x : Site d) :
    pActiveAt D (pState D (t + 1)) (t + 1) x
      = pArrivalsAt D (pState D t) t x \ pSettledAt D t x := by
  classical
  ext p
  rw [mem_pActiveAt_iff, Finset.mem_sdiff, mem_pArrivalsAt_iff, pSettledAt,
    Finset.mem_filter, pActive_succ_iff, pPos_succ]
  constructor
  · rintro ⟨⟨hact, hset⟩, hpos⟩
    exact ⟨⟨hact, hpos⟩, fun hq => by rw [hq.2] at hset; exact Bool.noConfusion hset⟩
  · rintro ⟨⟨hact, hpos⟩, hno⟩
    refine ⟨⟨hact, ?_⟩, hpos⟩
    by_contra hs
    exact hno ⟨(mem_pArrivalsAt_iff D t x p).mpr ⟨hact, hpos⟩,
      Bool.not_eq_false _ |>.mp hs⟩

/-- Given a `LabelOrder`, the active count at `x` after round `t + 1` is that round's
arrival count at `x` minus the holes `x` had at `t`. -/
theorem pActiveCount_succ (h : LabelOrder d) (D : PDriver d) (t : ℕ) (x : Site d) :
    pActiveCount D (t + 1) x
      = (pArrivalsAt D (pState D t) t x).card - pHoleCount D t x := by
  unfold pActiveCount
  rw [pActiveAt_succ_eq, Finset.card_sdiff_of_subset (pSettledAt_subset' D t x),
    card_pSettledAt h]
  omega

/-- The hole count at `x` after round `t + 1` is the hole count at `t` minus that
round's arrival count at `x`. -/
theorem pHoleCount_succ (D : PDriver d) (t : ℕ) (x : Site d) :
    pHoleCount D (t + 1) x
      = pHoleCount D t x - (pArrivalsAt D (pState D t) t x).card := rfl

/-- The particles active at `x` after round `t + 1` are that round's arrivals at `x`
with the bottom `pHoleCount D t x` of them, in the order `prec D.rank t`, removed. -/
theorem pActiveAt_succ_eq' (D : PDriver d) (t : ℕ) (x : Site d) :
    pActiveAt D (pState D (t + 1)) (t + 1) x
      = pArrivalsAt D (pState D t) t x
        \ settledIn (pArrivalsAt D (pState D t) t x) (prec D.rank t) (pHoleCount D t x) := by
  rw [pActiveAt_succ_eq, pSettledAt_eq]
  rfl

/-! ### How the two processes' arrivals compare -/

/-- Two drivers with the same move map send an active particle with the same
position at `t` to the same next position. -/
theorem pNextPos_congr {D E : PDriver d} (hmove : E.move = D.move) {t : ℕ} {p : Label d}
    (hD : (pState D t).active p = true) (hE : (pState E t).active p = true)
    (hp : (pState D t).pos p = (pState E t).pos p) :
    pNextPos E (pState E t) t p = pNextPos D (pState D t) t p := by
  rw [pNextPos_of_active _ _ _ _ hD, pNextPos_of_active _ _ _ _ hE, hp, hmove]

/-- Two drivers with the same move map and matching active sets and positions at `t`
have the same arrivals at every site. -/
theorem pArrivalsAt_congr {D E : PDriver d} (hmove : E.move = D.move) (t : ℕ)
    (hact : ∀ p, (pState E t).active p = (pState D t).active p)
    (hpos : ∀ p, (pState D t).active p = true → (pState D t).pos p = (pState E t).pos p)
    (x : Site d) :
    pArrivalsAt E (pState E t) t x = pArrivalsAt D (pState D t) t x := by
  ext p
  rw [mem_pArrivalsAt_iff, mem_pArrivalsAt_iff, hact p]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [pNextPos_congr hmove h1 (by rw [hact p]; exact h1) (hpos p h1)] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [pNextPos_congr hmove h1 (by rw [hact p]; exact h1) (hpos p h1)]⟩

/-- A particle inactive at `t` is not among that round's arrivals at any site. -/
theorem notMem_pArrivalsAt {D : PDriver d} {t : ℕ} {u : Label d}
    (hu : (pState D t).active u = false) (x : Site d) :
    u ∉ pArrivalsAt D (pState D t) t x := by
  intro hmem
  rw [mem_pArrivalsAt_iff] at hmem
  rw [hu] at hmem
  exact Bool.noConfusion hmem.1

/-- If `u` is the sole extra active particle of `E` over `D` (same move map, positions and
other actives agreeing), `E`'s arrivals at `u`'s next position `w` are `D`'s arrivals at `w`
with `u` inserted, and agree with `D`'s elsewhere. -/
theorem pArrivalsAt_insert {D E : PDriver d} (hmove : E.move = D.move) (t : ℕ) (u : Label d)
    (hu' : (pState E t).active u = true) (hu : (pState D t).active u = false)
    (hother : ∀ p, p ≠ u → (pState E t).active p = (pState D t).active p)
    (hpos : ∀ p, (pState D t).active p = true → (pState D t).pos p = (pState E t).pos p)
    (x : Site d) :
    pArrivalsAt E (pState E t) t x
      = if pNextPos E (pState E t) t u = x then insert u (pArrivalsAt D (pState D t) t x)
        else pArrivalsAt D (pState D t) t x := by
  classical
  ext p
  rw [mem_pArrivalsAt_iff]
  by_cases hpu : p = u
  · subst hpu
    by_cases hx : pNextPos E (pState E t) t p = x
    · simp [hx, hu']
    · simp only [hx, if_false, hu', true_and]
      exact ((iff_false _).mpr (notMem_pArrivalsAt hu x)).symm
  · have hactp : (pState E t).active p = (pState D t).active p := hother p hpu
    have hiff : ((pState E t).active p = true ∧ pNextPos E (pState E t) t p = x)
        ↔ p ∈ pArrivalsAt D (pState D t) t x := by
      rw [mem_pArrivalsAt_iff, hactp]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [pNextPos_congr hmove h1 (by rw [hactp]; exact h1) (hpos p h1)] at h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [pNextPos_congr hmove h1 (by rw [hactp]; exact h1) (hpos p h1)]⟩
    by_cases hx : pNextPos E (pState E t) t u = x
    · rw [if_pos hx, Finset.mem_insert]
      simp only [hpu, false_or]
      exact hiff
    · rw [if_neg hx]
      exact hiff

/-- Two drivers with matching active sets and positions at `t` have the same active
particles at every site. -/
theorem pActiveAt_congr {D E : PDriver d} (t : ℕ)
    (hact : ∀ p, (pState E t).active p = (pState D t).active p)
    (hpos : ∀ p, (pState D t).active p = true → (pState D t).pos p = (pState E t).pos p)
    (x : Site d) : pActiveAt E (pState E t) t x = pActiveAt D (pState D t) t x := by
  ext p
  rw [mem_pActiveAt_iff, mem_pActiveAt_iff, hact p]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hpos p h1]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← hpos p h1]⟩

/-- A particle inactive at `t` is not among the particles active at any site at `t`. -/
theorem notMem_pActiveAt {D : PDriver d} {t : ℕ} {u : Label d}
    (hu : (pState D t).active u = false) (x : Site d) :
    u ∉ pActiveAt D (pState D t) t x := by
  intro hmem
  rw [mem_pActiveAt_iff, hu] at hmem
  exact Bool.noConfusion hmem.1

/-- If `u` is the sole extra active particle of `E` over `D`, `E`'s active set at `u`'s
position is `D`'s active set there with `u` inserted, and agrees with `D`'s elsewhere. -/
theorem pActiveAt_insert {D E : PDriver d} (t : ℕ) (u : Label d)
    (hu' : (pState E t).active u = true) (hu : (pState D t).active u = false)
    (hother : ∀ p, p ≠ u → (pState E t).active p = (pState D t).active p)
    (hpos : ∀ p, (pState D t).active p = true → (pState D t).pos p = (pState E t).pos p)
    (x : Site d) :
    pActiveAt E (pState E t) t x
      = if (pState E t).pos u = x then insert u (pActiveAt D (pState D t) t x)
        else pActiveAt D (pState D t) t x := by
  classical
  ext p
  rw [mem_pActiveAt_iff]
  by_cases hpu : p = u
  · subst hpu
    by_cases hx : (pState E t).pos p = x
    · simp [hx, hu']
    · simp only [hx, if_false, hu', true_and]
      exact ((iff_false _).mpr (notMem_pActiveAt hu x)).symm
  · have hactp : (pState E t).active p = (pState D t).active p := hother p hpu
    have hiff : ((pState E t).active p = true ∧ (pState E t).pos p = x)
        ↔ p ∈ pActiveAt D (pState D t) t x := by
      rw [mem_pActiveAt_iff, hactp]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by rwa [hpos p h1]⟩, fun ⟨h1, h2⟩ => ⟨h1, by rwa [← hpos p h1]⟩⟩
    by_cases hx : (pState E t).pos u = x
    · rw [if_pos hx, Finset.mem_insert]
      simp only [hpu, false_or]
      exact hiff
    · rw [if_neg hx]
      exact hiff

/-! ### The one-particle discrepancy -/

/-- The two shapes the discrepancy of the one-particle coupling can take after
a round.  In the first the second process has one active particle the first has
not and the holes agree; in the second the actives agree and the first process
has one unfilled hole the second has not. -/
def OneParticleInv (D : PDriver d) (x₀ : Site d) (t : ℕ) : Prop :=
  (∃ u : Label d, (pState (addParticleDriver x₀ D) t).active u = true ∧
      (pState D t).active u = false ∧
      (∀ p, p ≠ u → (pState (addParticleDriver x₀ D) t).active p = (pState D t).active p) ∧
      ∀ x, pHoleCount (addParticleDriver x₀ D) t x = pHoleCount D t x) ∨
  ((∀ p, (pState (addParticleDriver x₀ D) t).active p = (pState D t).active p) ∧
    ∃ z : Site d, pHoleCount D t z = pHoleCount (addParticleDriver x₀ D) t z + 1 ∧
      ∀ x, x ≠ z → pHoleCount D t x = pHoleCount (addParticleDriver x₀ D) t x)

/-- A particle is active after round `t + 1` iff it lies among the arrivals at its
next position that the order `prec X.rank t` does not settle there. -/
theorem active_succ_iff_mem (X : PDriver d) (t : ℕ) (p : Label d) :
    (pState X (t + 1)).active p = true
      ↔ p ∈ pArrivalsAt X (pState X t) t (pNextPos X (pState X t) t p)
          \ settledIn (pArrivalsAt X (pState X t) t (pNextPos X (pState X t) t p))
              (prec X.rank t) (pHoleCount X t (pNextPos X (pState X t) t p)) := by
  rw [← pActiveAt_succ_eq', mem_pActiveAt_iff]
  exact ⟨fun hp => ⟨hp, rfl⟩, fun hp => hp.1⟩

/-- A particle active after round `t + 1` was already active at `t`. -/
theorem pActive_of_succ (X : PDriver d) (t : ℕ) (p : Label d)
    (h : (pState X (t + 1)).active p = true) : (pState X t).active p = true :=
  ((pActive_succ_iff X t p).mp h).1

/-- A particle inactive at `t` stays inactive at `t + 1`. -/
theorem pActive_succ_eq_false (X : PDriver d) (t : ℕ) (p : Label d)
    (hf : (pState X t).active p = false) : (pState X (t + 1)).active p = false := by
  cases hb : (pState X (t + 1)).active p with
  | false => rfl
  | true => exact absurd (pActive_of_succ X t p hb) (by rw [hf]; simp)

/-- One round of the one-particle coupling. -/
theorem oneParticleInv_succ (h : LabelOrder d) (D : PDriver d) (x₀ : Site d) (t : ℕ)
    (hinv : OneParticleInv D x₀ t) : OneParticleInv D x₀ (t + 1) := by
  classical
  have htag := (tagged_invariant D x₀ t).1
  have hpos : ∀ p, (pState D t).active p = true →
      (pState D t).pos p = (pState (addParticleDriver x₀ D) t).pos p := fun p hp => (htag p hp).2
  have hprec : ∀ y : Site d, ∀ X : PDriver d, X.rank = D.rank →
      prec X.rank t = prec D.rank t := fun _ _ hr => by rw [hr]
  have hirr := prec_irrefl h D.rank t
  have htr := prec_trans h D.rank t
  have htot := prec_total h D.rank t
  have hEholes : ∀ (X : PDriver d) (y : Site d), pHoleCount X (t + 1) y
      = pHoleCount X t y - (pArrivalsAt X (pState X t) t y).card := fun X y => rfl
  rcases hinv with ⟨u, hu', hu, hother, hholes⟩ | ⟨hactEq, z, hz, hzo⟩
  · -- the second process has one extra active particle
    set E := addParticleDriver x₀ D with hEdef
    set w := pNextPos E (pState E t) t u with hwdef
    have harr : ∀ x, pArrivalsAt E (pState E t) t x
        = if w = x then insert u (pArrivalsAt D (pState D t) t x)
          else pArrivalsAt D (pState D t) t x :=
      pArrivalsAt_insert (D := D) (E := E) rfl t u hu' hu hother hpos
    have hunot : ∀ x, u ∉ pArrivalsAt D (pState D t) t x := fun x => notMem_pArrivalsAt hu x
    have hnext : ∀ p, p ≠ u → (pState D t).active p = true →
        pNextPos E (pState E t) t p = pNextPos D (pState D t) t p := fun p hpu hp =>
      pNextPos_congr (D := D) (E := E) rfl hp (by rw [hother p hpu]; exact hp) (hpos p hp)
    have hoffarr : ∀ y, y ≠ w →
        pArrivalsAt E (pState E t) t y = pArrivalsAt D (pState D t) t y := by
      intro y hy
      rw [harr y, if_neg (fun hc => hy hc.symm)]
    have hatw : pArrivalsAt E (pState E t) t w
        = insert u (pArrivalsAt D (pState D t) t w) := by rw [harr w, if_pos rfl]
    have hoffsurv : ∀ y, y ≠ w → ∀ p,
        (p ∈ pArrivalsAt E (pState E t) t y
            \ settledIn (pArrivalsAt E (pState E t) t y) (prec E.rank t) (pHoleCount E t y)
          ↔ p ∈ pArrivalsAt D (pState D t) t y
            \ settledIn (pArrivalsAt D (pState D t) t y) (prec D.rank t) (pHoleCount D t y)) := by
      intro y hy p
      rw [hoffarr y hy, hholes y]
      rfl
    have hact_gen : ∀ p, p ≠ u → (pState D t).active p = false →
        (pState E (t + 1)).active p = (pState D (t + 1)).active p := by
      intro p hpu hp
      rw [pActive_succ_eq_false _ _ _ hp,
        pActive_succ_eq_false _ _ _ (by rw [hother p hpu]; exact hp)]
    set a := (pArrivalsAt D (pState D t) t w).card with hadef
    have hcardE : (pArrivalsAt E (pState E t) t w).card = a + 1 := by
      rw [hatw, Finset.card_insert_of_notMem (hunot w)]
    by_cases hcase : a + 1 ≤ pHoleCount D t w
    · -- every arrival at `w` settles in both, and the second process loses one more hole
      have hsD : settledIn (pArrivalsAt D (pState D t) t w) (prec D.rank t) (pHoleCount D t w)
          = pArrivalsAt D (pState D t) t w :=
        settledIn_eq_self hirr htr htot (by omega)
      have hsE : settledIn (pArrivalsAt E (pState E t) t w) (prec E.rank t) (pHoleCount E t w)
          = pArrivalsAt E (pState E t) t w := by
        rw [hholes w]
        exact settledIn_eq_self hirr htr htot (by rw [hcardE]; omega)
      refine Or.inr ⟨fun p => ?_, w, ?_, ?_⟩
      · by_cases hpu : p = u
        · subst hpu
          rw [pActive_succ_eq_false _ _ _ hu]
          cases hb : (pState E (t + 1)).active p with
          | false => rfl
          | true =>
              exfalso
              have := (active_succ_iff_mem E t p).mp hb
              rw [← hwdef, hsE] at this
              exact (Finset.mem_sdiff.mp this).2 (Finset.mem_sdiff.mp this).1
        · by_cases hp : (pState D t).active p = true
          · have hy : pNextPos E (pState E t) t p = pNextPos D (pState D t) t p := hnext p hpu hp
            by_cases hyw : pNextPos D (pState D t) t p = w
            · have h1 : (pState D (t + 1)).active p = false := by
                cases hb : (pState D (t + 1)).active p with
                | false => rfl
                | true =>
                    exfalso
                    have := (active_succ_iff_mem D t p).mp hb
                    rw [hyw, hsD] at this
                    exact (Finset.mem_sdiff.mp this).2 (Finset.mem_sdiff.mp this).1
              have h2 : (pState E (t + 1)).active p = false := by
                cases hb : (pState E (t + 1)).active p with
                | false => rfl
                | true =>
                    exfalso
                    have := (active_succ_iff_mem E t p).mp hb
                    rw [hy, hyw, hsE] at this
                    exact (Finset.mem_sdiff.mp this).2 (Finset.mem_sdiff.mp this).1
              rw [h1, h2]
            · have := hoffsurv (pNextPos D (pState D t) t p) hyw p
              rw [Bool.eq_iff_iff, active_succ_iff_mem E t p, active_succ_iff_mem D t p, hy]
              exact this
          · exact hact_gen p hpu (by simpa using hp)
      · rw [hEholes D w, hEholes E w, hholes w, hcardE]
        omega
      · intro x hx
        rw [hEholes D x, hEholes E x, hholes x, hoffarr x hx]
    · -- the holes at `w` run out, and one particle is left over
      have hEr : E.rank = D.rank := rfl
      have hle : pHoleCount D t w ≤ a := by omega
      set SD := pArrivalsAt D (pState D t) t w
        \ settledIn (pArrivalsAt D (pState D t) t w) (prec D.rank t) (pHoleCount D t w) with hSD
      set SE := pArrivalsAt E (pState E t) t w
        \ settledIn (pArrivalsAt E (pState E t) t w) (prec E.rank t) (pHoleCount E t w) with hSE
      have hsub : SD ⊆ SE := by
        rw [hSD, hSE, hatw, hholes w, hEr]
        exact survivors_subset_insert u _
      have hcardSD : SD.card = a - pHoleCount D t w := by
        rw [hSD, Finset.card_sdiff_of_subset (settledIn_subset _ _),
          card_settledIn hirr htr htot]
        omega
      have hcardSE : SE.card = a + 1 - pHoleCount D t w := by
        rw [hSE, Finset.card_sdiff_of_subset (settledIn_subset _ _), hEr,
          card_settledIn hirr htr htot, hcardE, hholes w]
        omega
      obtain ⟨v, hvnot, hveq⟩ :=
        eq_insert_of_card_succ hsub (by rw [hcardSE, hcardSD]; omega)
      have hvSE : v ∈ SE := by rw [hveq]; exact Finset.mem_insert_self _ _
      have hvarr : v ∈ pArrivalsAt E (pState E t) t w := (Finset.mem_sdiff.mp hvSE).1
      have hvinfo := (mem_pArrivalsAt_iff E t w v).mp hvarr
      have hunotSE : u ∉ SE ∨ u = v := by
        by_cases hc : u = v
        · exact Or.inr hc
        · refine Or.inl fun hmem => hc ?_
          rw [hveq, Finset.mem_insert] at hmem
          rcases hmem with hmem | hmem
          · exact hmem
          · exact absurd (Finset.mem_sdiff.mp (hSD ▸ hmem)).1 (hunot w)
      refine Or.inl ⟨v, ?_, ?_, ?_, ?_⟩
      · rw [active_succ_iff_mem E t v, hvinfo.2, ← hSE]
        exact hvSE
      · cases hb : (pState D (t + 1)).active v with
        | false => rfl
        | true =>
            exfalso
            have hactD : (pState D t).active v = true := pActive_of_succ D t v hb
            have hvu : v ≠ u := by rintro rfl; rw [hu] at hactD; exact Bool.noConfusion hactD
            have hy : pNextPos D (pState D t) t v = w := by
              rw [← hnext v hvu hactD, hvinfo.2]
            have := (active_succ_iff_mem D t v).mp hb
            rw [hy, ← hSD] at this
            exact hvnot this
      · intro p hpv
        by_cases hpu : p = u
        · subst hpu
          have huE : (pState E (t + 1)).active p = false := by
            cases hb : (pState E (t + 1)).active p with
            | false => rfl
            | true =>
                exfalso
                have := (active_succ_iff_mem E t p).mp hb
                rw [← hwdef, ← hSE] at this
                rcases hunotSE with hc | hc
                · exact hc this
                · exact hpv hc
          rw [huE, pActive_succ_eq_false _ _ _ hu]
        · by_cases hp : (pState D t).active p = true
          · have hy : pNextPos E (pState E t) t p = pNextPos D (pState D t) t p := hnext p hpu hp
            by_cases hyw : pNextPos D (pState D t) t p = w
            · rw [Bool.eq_iff_iff, active_succ_iff_mem E t p, active_succ_iff_mem D t p, hy,
                hyw, ← hSD, ← hSE, hveq, Finset.mem_insert]
              exact ⟨fun hc => hc.resolve_left hpv, Or.inr⟩
            · rw [Bool.eq_iff_iff, active_succ_iff_mem E t p, active_succ_iff_mem D t p, hy]
              exact hoffsurv (pNextPos D (pState D t) t p) hyw p
          · exact hact_gen p hpu (by simpa using hp)
      · intro x
        by_cases hx : x = w
        · rw [hx, hEholes D w, hEholes E w, hholes w, hcardE]
          omega
        · rw [hEholes D x, hEholes E x, hholes x, hoffarr x hx]
  · -- the first process has one extra unfilled hole
    set E := addParticleDriver x₀ D with hEdef
    have hEr : E.rank = D.rank := rfl
    have hnext : ∀ p, (pState D t).active p = true →
        pNextPos E (pState E t) t p = pNextPos D (pState D t) t p := fun p hp =>
      pNextPos_congr (D := D) (E := E) rfl hp (by rw [hactEq p]; exact hp) (hpos p hp)
    have harr : ∀ x, pArrivalsAt E (pState E t) t x = pArrivalsAt D (pState D t) t x :=
      pArrivalsAt_congr (D := D) (E := E) rfl t hactEq hpos
    have hoffsurv : ∀ y, y ≠ z → ∀ p,
        (p ∈ pArrivalsAt E (pState E t) t y
            \ settledIn (pArrivalsAt E (pState E t) t y) (prec E.rank t) (pHoleCount E t y)
          ↔ p ∈ pArrivalsAt D (pState D t) t y
            \ settledIn (pArrivalsAt D (pState D t) t y) (prec D.rank t) (pHoleCount D t y)) := by
      intro y hy p
      rw [harr y, hEr, ← hzo y hy]
    have hact_gen : ∀ p, (pState D t).active p = false →
        (pState E (t + 1)).active p = (pState D (t + 1)).active p := by
      intro p hp
      rw [pActive_succ_eq_false _ _ _ hp,
        pActive_succ_eq_false _ _ _ (by rw [hactEq p]; exact hp)]
    set a := (pArrivalsAt D (pState D t) t z).card with hadef
    by_cases hcase : a ≤ pHoleCount E t z
    · have hsE : settledIn (pArrivalsAt E (pState E t) t z) (prec E.rank t) (pHoleCount E t z)
          = pArrivalsAt E (pState E t) t z := by
        rw [harr z, hEr]
        exact settledIn_eq_self hirr htr htot (by omega)
      have hsD : settledIn (pArrivalsAt D (pState D t) t z) (prec D.rank t) (pHoleCount D t z)
          = pArrivalsAt D (pState D t) t z :=
        settledIn_eq_self hirr htr htot (by omega)
      refine Or.inr ⟨fun p => ?_, z, ?_, ?_⟩
      · by_cases hp : (pState D t).active p = true
        · have hy : pNextPos E (pState E t) t p = pNextPos D (pState D t) t p := hnext p hp
          by_cases hyz : pNextPos D (pState D t) t p = z
          · have h1 : (pState D (t + 1)).active p = false := by
              cases hb : (pState D (t + 1)).active p with
              | false => rfl
              | true =>
                  exfalso
                  have := (active_succ_iff_mem D t p).mp hb
                  rw [hyz, hsD] at this
                  exact (Finset.mem_sdiff.mp this).2 (Finset.mem_sdiff.mp this).1
            have h2 : (pState E (t + 1)).active p = false := by
              cases hb : (pState E (t + 1)).active p with
              | false => rfl
              | true =>
                  exfalso
                  have := (active_succ_iff_mem E t p).mp hb
                  rw [hy, hyz, hsE] at this
                  exact (Finset.mem_sdiff.mp this).2 (Finset.mem_sdiff.mp this).1
            rw [h1, h2]
          · rw [Bool.eq_iff_iff, active_succ_iff_mem E t p, active_succ_iff_mem D t p, hy]
            exact hoffsurv (pNextPos D (pState D t) t p) hyz p
        · exact hact_gen p (by simpa using hp)
      · rw [hEholes D z, hEholes E z, harr z]
        omega
      · intro x hx
        rw [hEholes D x, hEholes E x, harr x, hzo x hx]
    · have hle : pHoleCount E t z + 1 ≤ a := by omega
      set SD := pArrivalsAt D (pState D t) t z
        \ settledIn (pArrivalsAt D (pState D t) t z) (prec D.rank t) (pHoleCount D t z) with hSD
      set SE := pArrivalsAt E (pState E t) t z
        \ settledIn (pArrivalsAt E (pState E t) t z) (prec E.rank t) (pHoleCount E t z) with hSE
      have hsub : SD ⊆ SE := by
        rw [hSD, hSE, harr z, hEr]
        exact survivors_subset_holes (by omega)
      have hcardSD : SD.card = a - pHoleCount D t z := by
        rw [hSD, Finset.card_sdiff_of_subset (settledIn_subset _ _),
          card_settledIn hirr htr htot]
        omega
      have hcardSE : SE.card = a - pHoleCount E t z := by
        rw [hSE, Finset.card_sdiff_of_subset (settledIn_subset _ _), hEr, harr z,
          card_settledIn hirr htr htot]
        omega
      obtain ⟨v, hvnot, hveq⟩ :=
        eq_insert_of_card_succ hsub (by rw [hcardSE, hcardSD]; omega)
      have hvSE : v ∈ SE := by rw [hveq]; exact Finset.mem_insert_self _ _
      have hvarr : v ∈ pArrivalsAt E (pState E t) t z := (Finset.mem_sdiff.mp hvSE).1
      have hvinfo := (mem_pArrivalsAt_iff E t z v).mp hvarr
      refine Or.inl ⟨v, ?_, ?_, ?_, ?_⟩
      · rw [active_succ_iff_mem E t v, hvinfo.2, ← hSE]
        exact hvSE
      · cases hb : (pState D (t + 1)).active v with
        | false => rfl
        | true =>
            exfalso
            have hactD : (pState D t).active v = true := pActive_of_succ D t v hb
            have hy : pNextPos D (pState D t) t v = z := by
              rw [← hnext v hactD, hvinfo.2]
            have := (active_succ_iff_mem D t v).mp hb
            rw [hy, ← hSD] at this
            exact hvnot this
      · intro p hpv
        by_cases hp : (pState D t).active p = true
        · have hy : pNextPos E (pState E t) t p = pNextPos D (pState D t) t p := hnext p hp
          by_cases hyz : pNextPos D (pState D t) t p = z
          · rw [Bool.eq_iff_iff, active_succ_iff_mem E t p, active_succ_iff_mem D t p, hy,
              hyz, ← hSD, ← hSE, hveq, Finset.mem_insert]
            exact ⟨fun hc => hc.resolve_left hpv, Or.inr⟩
          · rw [Bool.eq_iff_iff, active_succ_iff_mem E t p, active_succ_iff_mem D t p, hy]
            exact hoffsurv (pNextPos D (pState D t) t p) hyz p
        · exact hact_gen p (by simpa using hp)
      · intro x
        by_cases hx : x = z
        · rw [hx, hEholes D z, hEholes E z, harr z]
          omega
        · rw [hEholes D x, hEholes E x, harr x, hzo x hx]

/-- The base case of the one-particle coupling: raising a nonnegative count
adds a particle, raising a negative one cancels a hole. -/
theorem oneParticleInv_zero (D : PDriver d) (x₀ : Site d) : OneParticleInv D x₀ 0 := by
  classical
  have hact : ∀ (η : Site d → ℤ) (p : Label d),
      (initial η).active p = decide (p.2 < (η p.1).toNat) := fun _ _ => rfl
  have hhol : ∀ (η : Site d → ℤ) (x : Site d),
      (initial η).holes x = (-η x).toNat := fun _ _ => rfl
  by_cases hsign : 0 ≤ D.eta x₀
  · refine Or.inl ⟨(x₀, (D.eta x₀).toNat), ?_, ?_, ?_, ?_⟩
    · show (initial (addParticle x₀ D.eta)).active (x₀, (D.eta x₀).toNat) = true
      rw [hact]
      simp only [decide_eq_true_eq]
      simp only [addParticle, if_pos]
      omega
    · show (initial D.eta).active (x₀, (D.eta x₀).toNat) = false
      rw [hact]
      simp only [decide_eq_false_iff_not, not_lt, le_refl]
    · intro p hp
      show (initial (addParticle x₀ D.eta)).active p = (initial D.eta).active p
      rw [hact, hact, decide_eq_decide]
      by_cases hx : p.1 = x₀
      · have hne : p.2 ≠ (D.eta x₀).toNat := fun hc => hp (Prod.ext hx hc)
        rw [hx]
        simp [addParticle]
        omega
      · simp only [addParticle, if_neg hx]
    · intro x
      show (initial (addParticle x₀ D.eta)).holes x = (initial D.eta).holes x
      rw [hhol, hhol]
      by_cases hx : x = x₀
      · rw [hx]; simp [addParticle]; omega
      · simp only [addParticle, if_neg hx]
  · refine Or.inr ⟨?_, x₀, ?_, ?_⟩
    · intro p
      show (initial (addParticle x₀ D.eta)).active p = (initial D.eta).active p
      rw [hact, hact, decide_eq_decide]
      by_cases hx : p.1 = x₀
      · rw [hx]; simp [addParticle]; omega
      · simp only [addParticle, if_neg hx]
    · show (initial D.eta).holes x₀ = (initial (addParticle x₀ D.eta)).holes x₀ + 1
      rw [hhol, hhol]
      simp [addParticle]
      omega
    · intro x hx
      show (initial D.eta).holes x = (initial (addParticle x₀ D.eta)).holes x
      rw [hhol, hhol]
      simp only [addParticle, if_neg hx]

/-- `OneParticleInv` holds at every time `t`, by induction from the base case
`oneParticleInv_zero` and the one-round step `oneParticleInv_succ`. -/
theorem oneParticleInv_all (h : LabelOrder d) (D : PDriver d) (x₀ : Site d) :
    ∀ t : ℕ, OneParticleInv D x₀ t := by
  intro t
  induction t with
  | zero => exact oneParticleInv_zero D x₀
  | succ t ih => exact oneParticleInv_succ h D x₀ t ih

/-- Lemma 3.3 of the paper: the one-particle coupling differs by one active
particle at one site, or by one unfilled hole at one site, and never by both. -/
theorem one_particle_of_labelOrder (h : LabelOrder d) (D : PDriver d) (x₀ : Site d)
    (t : ℕ) :
    ((∀ x, pHoleCount (addParticleDriver x₀ D) t x = pHoleCount D t x) ∧
      ∃ z, pActiveCount (addParticleDriver x₀ D) t z = pActiveCount D t z + 1 ∧
        ∀ x, x ≠ z → pActiveCount (addParticleDriver x₀ D) t x = pActiveCount D t x) ∨
    ((∀ x, pActiveCount (addParticleDriver x₀ D) t x = pActiveCount D t x) ∧
      ∃ z, pHoleCount D t z = pHoleCount (addParticleDriver x₀ D) t z + 1 ∧
        ∀ x, x ≠ z → pHoleCount D t x = pHoleCount (addParticleDriver x₀ D) t x) := by
  classical
  have hpos : ∀ p, (pState D t).active p = true →
      (pState D t).pos p = (pState (addParticleDriver x₀ D) t).pos p :=
    fun p hp => ((tagged_invariant D x₀ t).1 p hp).2
  rcases oneParticleInv_all h D x₀ t with ⟨u, hu', hu, hother, hholes⟩ | ⟨hactEq, z, hz, hzo⟩
  · refine Or.inl ⟨hholes, (pState (addParticleDriver x₀ D) t).pos u, ?_, ?_⟩
    · unfold pActiveCount
      rw [pActiveAt_insert t u hu' hu hother hpos, if_pos rfl,
        Finset.card_insert_of_notMem (notMem_pActiveAt hu _)]
    · intro x hx
      unfold pActiveCount
      rw [pActiveAt_insert t u hu' hu hother hpos, if_neg (fun hc => hx hc.symm)]
  · refine Or.inr ⟨fun x => ?_, z, hz, hzo⟩
    unfold pActiveCount
    rw [pActiveAt_congr t hactEq hpos]

end LatticeProb.ParticleDrivenAgree

end
