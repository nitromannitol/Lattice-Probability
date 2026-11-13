/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.ParticleMeasurability at commit 66d817d. The module paths and the namespace `Parking`
   are renamed (to `LatticeProb.ParticleDrivenAgree`), and proofs are adapted to the Lean and Mathlib
   versions of this repository where needed. -/
import LatticeProb.ParticleDriven
import LatticeProb.ParticleDrivenAgree.Reads

/-!
# Measurability of the particle-driven state

Every field of the particle-driven state is a measurable function of its data.

`LatticeProb.ParticleDrivenAgree.Measurability` proves this for the stack construction.  The
passage between the two constructions is an equality of pushforward measures,
and a pushforward along a map that is not measurable is zero, so the same has
to be known of the particle-driven construction before the equality can even be
stated non-vacuously.

The argument is the one of the stack construction with one simplification: a
particle moves by its own displacement rather than by the next unread
instruction at its site, so no instruction index enters.  The two helpers that
read the candidate set off the configuration are generalized here to an
arbitrary space carrying a measurable configuration, since the two
constructions have different data types.
-/

open LatticeProb (measurable_decide measurable_eval_var measurable_from_countable'
  measurable_of_countable_partition)

noncomputable section

open MeasureTheory

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {d : ℕ} {α : Type*} [MeasurableSpace α]

/-! ### The candidate helpers, for any data carrying a configuration -/

/-- The generalization of `measurable_of_candidates` to any measurable-space-valued
configuration `e : α → Site d → ℤ`: anything computed from the candidate set
`candidates (e a) z r` is measurable, because that set is a function of `e a` restricted
to a box. -/
theorem measurable_of_candidates' (e : α → Site d → ℤ) (he : Measurable e) (z : Site d)
    (r : ℕ) {X : Type*} [MeasurableSpace X] (f : α → X) (g : Finset (Label d) → α → X)
    (hg : ∀ F, Measurable (g F)) (h : ∀ a, f a = g (candidates (e a) z r) a) :
    Measurable f := by
  refine measurable_of_countable_partition
    (fun a : α => (fun x : ↥(boxFinset z r) => e a (x : Site d)))
    (Measurable.of_eval fun x => (measurable_pi_apply (x : Site d)).comp he)
    f (fun c a => g (candidatesOf z r c) a) (fun c => hg _) fun a => ?_
  rw [h a, candidates_eq_candidatesOf]

/-- The generalization of `measurable_card_filter_candidates` to an arbitrary
measurable-space-valued configuration `e`: the cardinality of a filtered candidate set is
measurable when the filter is. -/
theorem measurable_card_filter_candidates' (e : α → Site d → ℤ) (he : Measurable e)
    (y : Site d) (r : ℕ) (P : α → Label d → Bool) (hP : ∀ q, Measurable fun a => P a q) :
    Measurable fun a : α => ((candidates (e a) y r).filter fun q => P a q = true).card := by
  classical
  refine measurable_of_candidates' e he y r _
    (fun F a => (F.filter fun q => P a q = true).card) (fun F => ?_) fun a => rfl
  have hsum : ∀ a : α, (F.filter fun q => P a q = true).card
      = ∑ q ∈ F, if P a q = true then 1 else 0 := by
    intro a
    rw [Finset.card_filter]
  simp only [hsum]
  refine Finset.measurable_sum F fun q _ => ?_
  exact (measurable_from_countable' (fun b : Bool => if b = true then 1 else 0)).comp (hP q)

/-! ### The particle-driven state -/

/-- Every field of the particle-driven state after `t` rounds is a measurable
function of the driving data. -/
theorem measurable_pState (t : ℕ) :
    (∀ p : Label d, Measurable fun ω : LatticeProb.PData d =>
      (LatticeProb.pState (LatticeProb.toPDriver ω) t).active p) ∧
    (∀ p : Label d, Measurable fun ω : LatticeProb.PData d =>
      (LatticeProb.pState (LatticeProb.toPDriver ω) t).pos p) ∧
    (∀ x : Site d, Measurable fun ω : LatticeProb.PData d =>
      (LatticeProb.pState (LatticeProb.toPDriver ω) t).holes x) ∧
    (∀ x : Site d, Measurable fun ω : LatticeProb.PData d =>
      (LatticeProb.pState (LatticeProb.toPDriver ω) t).departures x) := by
  classical
  have heta : Measurable fun ω : LatticeProb.PData d => ω.1 := measurable_fst
  induction t with
  | zero =>
      refine ⟨fun p => ?_, fun p => ?_, fun x => ?_, fun x => ?_⟩
      · show Measurable fun ω : LatticeProb.PData d => decide (p.2 < (ω.1 p.1).toNat)
        exact (measurable_from_countable' fun z : ℤ => decide (p.2 < z.toNat)).comp
          ((measurable_pi_apply p.1).comp measurable_fst)
      · exact measurable_const
      · show Measurable fun ω : LatticeProb.PData d => (-(ω.1 x)).toNat
        exact (measurable_from_countable' fun z : ℤ => (-z).toNat).comp
          ((measurable_pi_apply x).comp measurable_fst)
      · exact measurable_const
  | succ t ih =>
      obtain ⟨hact, hpos, hhol, hdep⟩ := ih
      have hbool : ∀ (f g : LatticeProb.PData d → Bool), Measurable f → Measurable g →
          Measurable fun ω => (f ω && g ω) := by
        intro f g hf hg
        exact (measurable_from_countable' fun b : Bool × Bool => b.1 && b.2).comp (hf.prodMk hg)
      have hposeq : ∀ (q : Label d) (y : Site d),
          Measurable fun ω : LatticeProb.PData d =>
            decide ((LatticeProb.pState (LatticeProb.toPDriver ω) t).pos q = y) := by
        intro q y
        exact (measurable_from_countable' fun z : Site d => decide (z = y)).comp (hpos q)
      have hActFilter : ∀ (y : Site d) (R : Label d → Bool),
          Measurable fun ω : LatticeProb.PData d =>
            ((LatticeProb.pActiveAt (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t y).filter
                fun q => R q = true).card := by
        intro y R
        have hrw : ∀ ω : LatticeProb.PData d,
            ((LatticeProb.pActiveAt (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t y).filter
                fun q => R q = true).card
              = ((candidates ω.1 y t).filter fun q =>
                  (((LatticeProb.pState (LatticeProb.toPDriver ω) t).active q
                    && decide ((LatticeProb.pState (LatticeProb.toPDriver ω) t).pos q = y))
                    && R q) = true).card := by
          intro ω
          unfold LatticeProb.pActiveAt
          rw [Finset.filter_filter]
          congr 1
        simp only [hrw]
        exact measurable_card_filter_candidates' (fun ω : LatticeProb.PData d => ω.1) heta y t _
          fun q => hbool _ _ (hbool _ _ (hact q) (hposeq q y)) measurable_const
      have hActCard : ∀ y : Site d,
          Measurable fun ω : LatticeProb.PData d =>
            (LatticeProb.pActiveAt (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t y).card := by
        intro y
        have := hActFilter y (fun _ => true)
        simpa using this
      have hNext : ∀ p : Label d,
          Measurable fun ω : LatticeProb.PData d =>
            LatticeProb.pNextPos (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p := by
        intro p
        have hset : MeasurableSet {ω : LatticeProb.PData d |
            (LatticeProb.pState (LatticeProb.toPDriver ω) t).active p = true} :=
          (hact p) (measurableSet_singleton true)
        have hmove : Measurable fun ω : LatticeProb.PData d => ω.2.1 (p, t) :=
          (measurable_pi_apply (p, t)).comp (measurable_fst.comp measurable_snd)
        have hthen : Measurable fun ω : LatticeProb.PData d =>
            (LatticeProb.pState (LatticeProb.toPDriver ω) t).pos p + ω.2.1 (p, t) :=
          (measurable_from_countable' fun z : Site d × Site d => z.1 + z.2).comp
            ((hpos p).prodMk hmove)
        exact Measurable.ite hset hthen (hpos p)
      have hArrFilter : ∀ (x : Site d) (R : LatticeProb.PData d → Label d → Bool),
          (∀ q, Measurable fun ω => R ω q) →
          Measurable fun ω : LatticeProb.PData d =>
            ((LatticeProb.pArrivalsAt (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t x).filter
                fun q => R ω q = true).card := by
        intro x R hR
        have hrw : ∀ ω : LatticeProb.PData d,
            ((LatticeProb.pArrivalsAt (LatticeProb.toPDriver ω)
                (LatticeProb.pState (LatticeProb.toPDriver ω) t) t x).filter
                  fun q => R ω q = true).card
              = ((candidates ω.1 x (t + 1)).filter fun q =>
                  (((LatticeProb.pState (LatticeProb.toPDriver ω) t).active q &&
                    decide (LatticeProb.pNextPos (LatticeProb.toPDriver ω)
                      (LatticeProb.pState (LatticeProb.toPDriver ω) t) t q = x))
                    && R ω q) = true).card := by
          intro ω
          unfold LatticeProb.pArrivalsAt
          rw [Finset.filter_filter]
          congr 1
        simp only [hrw]
        refine measurable_card_filter_candidates' (fun ω : LatticeProb.PData d => ω.1) heta
          x (t + 1) _ fun q => ?_
        refine hbool _ _ (hbool _ _ (hact q) ?_) (hR q)
        exact (measurable_from_countable' fun z : Site d => decide (z = x)).comp (hNext q)
      have hArrCard : ∀ x : Site d,
          Measurable fun ω : LatticeProb.PData d =>
            (LatticeProb.pArrivalsAt (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t x).card := by
        intro x
        have := hArrFilter x (fun _ _ => true) fun _ => measurable_const
        simpa using this
      have hRank : ∀ (p q : Label d),
          Measurable fun ω : LatticeProb.PData d =>
            decide (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
              (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p)) := by
        intro p q
        refine measurable_decide _ ?_
        have hq : Measurable fun ω : LatticeProb.PData d => ω.2.2 (q, t) :=
          (measurable_pi_apply (q, t)).comp (measurable_snd.comp measurable_snd)
        have hp : Measurable fun ω : LatticeProb.PData d => ω.2.2 (p, t) :=
          (measurable_pi_apply (p, t)).comp (measurable_snd.comp measurable_snd)
        by_cases hlab : labelLT q p
        · have hs : {ω : LatticeProb.PData d | ω.2.2 (q, t) < ω.2.2 (p, t) ∨
              (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p)}
              = {ω : LatticeProb.PData d | ω.2.2 (q, t) < ω.2.2 (p, t)}
                ∪ {ω : LatticeProb.PData d | ω.2.2 (q, t) = ω.2.2 (p, t)} := by
            ext ω; simp [hlab]
          rw [hs]
          exact (measurableSet_lt hq hp).union (measurableSet_eq_fun hq hp)
        · have hs : {ω : LatticeProb.PData d | ω.2.2 (q, t) < ω.2.2 (p, t) ∨
              (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p)}
              = {ω : LatticeProb.PData d | ω.2.2 (q, t) < ω.2.2 (p, t)} := by
            ext ω; simp [hlab]
          rw [hs]
          exact measurableSet_lt hq hp
      have hSettles : ∀ p : Label d,
          Measurable fun ω : LatticeProb.PData d =>
            LatticeProb.pSettles (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p := by
        intro p
        have hcard : Measurable fun ω : LatticeProb.PData d =>
            ((LatticeProb.pArrivalsAt (LatticeProb.toPDriver ω)
                (LatticeProb.pState (LatticeProb.toPDriver ω) t) t
                  (LatticeProb.pNextPos (LatticeProb.toPDriver ω)
                    (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p)).filter
              fun q => (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
                (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p))).card := by
          refine measurable_eval_var
            (fun ω => LatticeProb.pNextPos (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p) (hNext p)
            (fun ω x => ((LatticeProb.pArrivalsAt (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t x).filter
              fun q => (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
                (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p))).card) fun x => ?_
          have := hArrFilter x (fun ω q => decide (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
            (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p))) (hRank p)
          simpa using this
        have hholes : Measurable fun ω : LatticeProb.PData d =>
            (LatticeProb.pState (LatticeProb.toPDriver ω) t).holes
              (LatticeProb.pNextPos (LatticeProb.toPDriver ω)
                (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p) :=
          measurable_eval_var (fun ω => LatticeProb.pNextPos (LatticeProb.toPDriver ω)
            (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p)
            (hNext p) (fun ω x => (LatticeProb.pState (LatticeProb.toPDriver ω) t).holes x) hhol
        have hrw : ∀ ω : LatticeProb.PData d,
            LatticeProb.pSettles (LatticeProb.toPDriver ω)
              (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p
            = ((LatticeProb.pState (LatticeProb.toPDriver ω) t).active p &&
              decide (((LatticeProb.pArrivalsAt (LatticeProb.toPDriver ω)
                  (LatticeProb.pState (LatticeProb.toPDriver ω) t) t
                    (LatticeProb.pNextPos (LatticeProb.toPDriver ω)
                      (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p)).filter
                fun q => (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
                  (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p))).card
                < (LatticeProb.pState (LatticeProb.toPDriver ω) t).holes
                  (LatticeProb.pNextPos (LatticeProb.toPDriver ω)
                    (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p))) := by
          intro ω
          simp [LatticeProb.pSettles]
          rfl
        simp only [hrw]
        exact (measurable_from_countable' fun z : Bool × ℕ × ℕ =>
          (z.1 && decide (z.2.1 < z.2.2))).comp ((hact p).prodMk (hcard.prodMk hholes))
      refine ⟨fun p => ?_, fun p => ?_, fun x => ?_, fun x => ?_⟩
      · have hrw : ∀ ω : LatticeProb.PData d,
            (LatticeProb.pState (LatticeProb.toPDriver ω) (t + 1)).active p
            = ((LatticeProb.pState (LatticeProb.toPDriver ω) t).active p
              && !LatticeProb.pSettles (LatticeProb.toPDriver ω)
                (LatticeProb.pState (LatticeProb.toPDriver ω) t) t p) := by
          intro ω; simp [LatticeProb.pState, LatticeProb.pStep]
        simp only [hrw]
        exact (measurable_from_countable' fun z : Bool × Bool => (z.1 && !z.2)).comp
          ((hact p).prodMk (hSettles p))
      · exact hNext p
      · exact (measurable_from_countable' fun z : ℕ × ℕ => z.1 - z.2).comp
          ((hhol x).prodMk (hArrCard x))
      · exact (measurable_from_countable' fun z : ℕ × ℕ => z.1 + z.2).comp
          ((hdep x).prodMk (hActCard x))

/-! ### The observables of the two constructions -/

/-- The observable bundle `stackObservables` of the stack construction (the odometer,
the active count, the hole count, and the active flag) is measurable, assembling the
already-known measurability of each of its four component fields. -/
theorem measurable_stackObservables :
    Measurable (LatticeProb.stackObservables (d := d)) := by
  refine Measurable.prodMk (Measurable.of_eval fun tx => ?_)
    (Measurable.prodMk (Measurable.of_eval fun tx => ?_)
      (Measurable.prodMk (Measurable.of_eval fun tx => ?_)
        (Measurable.of_eval fun ti => ?_)))
  · exact measurable_particleOdometer tx.1 tx.2
  · exact measurable_activeCount tx.1 tx.2
  · exact measurable_holeCount tx.1 tx.2
  · exact (measurable_state (d := d) ti.1).1 ti.2

/-- The corresponding observable bundle `pObservables` of the particle-driven
construction is measurable: three of its four fields follow directly from
`measurable_pState`, and the active count is computed from a filtered candidate set via
`measurable_card_filter_candidates'`. -/
theorem measurable_pObservables :
    Measurable (LatticeProb.pObservables (d := d)) := by
  obtain ⟨hact, -, hhol, hdep⟩ := measurable_pState (d := d) 0
  refine Measurable.prodMk (Measurable.of_eval fun tx => ?_)
    (Measurable.prodMk (Measurable.of_eval fun tx => ?_)
      (Measurable.prodMk (Measurable.of_eval fun tx => ?_)
        (Measurable.of_eval fun ti => ?_)))
  · exact (measurable_pState (d := d) tx.1).2.2.2 tx.2
  · exact by
      have := measurable_pState (d := d) tx.1
      classical
      have hbool : ∀ (f g : LatticeProb.PData d → Bool), Measurable f → Measurable g →
          Measurable fun ω => (f ω && g ω) := by
        intro f g hf hg
        exact (measurable_from_countable' fun b : Bool × Bool => b.1 && b.2).comp (hf.prodMk hg)
      obtain ⟨hact', hpos', -, -⟩ := this
      have hrw : ∀ ω : LatticeProb.PData d,
          LatticeProb.pActiveCount (LatticeProb.toPDriver ω) tx.1 tx.2
            = ((candidates ω.1 tx.2 tx.1).filter fun q =>
                ((LatticeProb.pState (LatticeProb.toPDriver ω) tx.1).active q
                  && decide ((LatticeProb.pState (LatticeProb.toPDriver ω) tx.1).pos q
                    = tx.2)) = true).card := by
        intro ω
        show (LatticeProb.pActiveAt (LatticeProb.toPDriver ω)
          (LatticeProb.pState (LatticeProb.toPDriver ω) tx.1) tx.1 tx.2).card = _
        unfold LatticeProb.pActiveAt
        congr 1
      simp only [hrw]
      exact measurable_card_filter_candidates' (fun ω : LatticeProb.PData d => ω.1)
        measurable_fst tx.2 tx.1 _ fun q =>
          hbool _ _ (hact' q)
            ((measurable_from_countable' fun z : Site d => decide (z = tx.2)).comp (hpos' q))
  · exact (measurable_pState (d := d) tx.1).2.2.1 tx.2
  · exact (measurable_pState (d := d) ti.1).1 ti.2

end LatticeProb.ParticleDrivenAgree

end
