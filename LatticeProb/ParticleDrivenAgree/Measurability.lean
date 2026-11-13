/- Adapted from Parking-Sharpness (https://github.com/nitromannitol/Parking-Sharpness),
   source module Parking.Support.Measurability at commit 66d817d. The module paths and the namespace `Parking`
   are renamed (to `LatticeProb.ParticleDrivenAgree`), and proofs are adapted to the Lean and Mathlib
   versions of this repository where needed. -/
import LatticeProb.ParticleDrivenAgree.Transport
import LatticeProb.Invariance
import LatticeProb.Prob.CountableMeasurable

/-!
# Measurability from a countable partition

Measurability from a countable partition.

Every measurability question about the particle-hole process has the same shape: the answer
at time `t` is a function of finitely many coordinates, but which coordinates depends on the
configuration.  Splitting on the value of a countable-valued observable reduces it to
countably many questions with a fixed finite dependence, which is what
`measurable_of_countable_partition` does, and the induction on the rounds is then mechanical:
every field of the state is a countable-valued function of finitely many coordinates once the
candidate set at the site is fixed, and the candidate set is a function of the configuration
on a box.

The last two results are the other half of what the law supplies: the instructions of the
model are neighbours of the site carrying them almost surely, which is the hypothesis the
pathwise lemmas of `lem:parallel`, `lem:deferred` and `lem:pathwise-comparison` carry.
-/

open LatticeProb (instructionLaw_isProbability measurable_decide measurable_eval_var
    measurable_from_countable' measurable_of_countable_partition)

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.ParticleDrivenAgree

open LatticeProb Finset

variable {d : ℕ}

/-- A finite family of integer coordinates, as a countable observable. -/
instance instMeasurableSingletonPi (s : Finset (Site d)) :
    MeasurableSingletonClass (s → ℤ) := by
  constructor
  intro c
  have : ({c} : Set (s → ℤ)) = ⋂ x : s, {f : s → ℤ | f x = c x} := by
    ext f
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h x => by rw [h], fun h => funext h⟩
  rw [this]
  exact MeasurableSet.iInter fun x => measurableSet_eq_fun (measurable_pi_apply x) measurable_const

/-- Restricting the initial field to a finite set of sites is a measurable operation. -/
theorem measurable_restrict_eta (s : Finset (Site d)) :
    Measurable fun ω : Data d => (fun x : s => ω.1 (x : Site d)) :=
  Measurable.of_eval fun x => (measurable_pi_apply (x : Site d)).comp measurable_fst

/-- The candidate set computed from the configuration on the box alone. -/
def candidatesOf (z : Site d) (r : ℕ) (c : ↥(boxFinset z r) → ℤ) :
    Finset (Label d) :=
  Finset.univ.biUnion fun x : ↥(boxFinset z r) =>
    (Finset.range (c x).toNat).map ⟨fun i => ((x : Site d), i), by
      intro a b h; simpa using h⟩

/-- The candidate set at a site is the same whether it is read off the full field `η` or its
restriction to the box, since `candidatesOf` only uses the restricted coordinates. -/
theorem candidates_eq_candidatesOf (η : Site d → ℤ) (z : Site d) (r : ℕ) :
    candidates η z r = candidatesOf z r (fun x => η (x : Site d)) := by
  ext p
  simp only [candidates, candidatesOf, Finset.mem_biUnion, Finset.mem_map, Finset.mem_range,
    Function.Embedding.coeFn_mk, true_and, Finset.univ_eq_attach, Finset.mem_attach,
    Subtype.exists]
  constructor
  · rintro ⟨x, hx, i, hi, rfl⟩
    exact ⟨x, hx, i, hi, rfl⟩
  · rintro ⟨x, hx, i, hi, rfl⟩
    exact ⟨x, hx, i, hi, rfl⟩

/-- Anything computed from the candidate set at a fixed site and radius is
measurable, because that set is a function of the configuration on a box. -/
theorem measurable_of_candidates {X : Type*} [MeasurableSpace X] (z : Site d) (r : ℕ)
    (f : Data d → X) (g : Finset (Label d) → Data d → X)
    (hg : ∀ F, Measurable (g F)) (h : ∀ ω, f ω = g (candidates ω.1 z r) ω) :
    Measurable f := by
  refine measurable_of_countable_partition
    (fun ω : Data d => (fun x : ↥(boxFinset z r) => ω.1 (x : Site d)))
    (measurable_restrict_eta _) f (fun c ω => g (candidatesOf z r c) ω)
    (fun c => hg _) fun ω => ?_
  rw [h ω, candidates_eq_candidatesOf]

/-- The cardinality of a filtered candidate set is measurable when the filter is. -/
theorem measurable_card_filter_candidates (y : Site d) (r : ℕ)
    (P : Data d → Label d → Bool)
    (hP : ∀ q, Measurable fun ω => P ω q) :
    Measurable fun ω : Data d => ((candidates ω.1 y r).filter fun q => P ω q).card := by
  classical
  refine measurable_of_candidates y r _
    (fun F ω => (F.filter fun q => P ω q).card) (fun F => ?_) fun ω => rfl
  have hsum : ∀ ω : Data d, (F.filter fun q => P ω q).card
      = ∑ q ∈ F, if P ω q = true then 1 else 0 := by
    intro ω
    rw [Finset.card_filter]
  simp only [hsum]
  refine Finset.measurable_sum F fun q _ => ?_
  exact (measurable_from_countable' (fun b : Bool => if b = true then 1 else 0)).comp (hP q)

/-- Every field of the state after `t` rounds is a measurable function of the
driving data. -/
theorem measurable_state (t : ℕ) :
    (∀ p : Label d, Measurable fun ω : Data d => (state (toDriver ω) t).active p) ∧
    (∀ p : Label d, Measurable fun ω : Data d => (state (toDriver ω) t).pos p) ∧
    (∀ x : Site d, Measurable fun ω : Data d => (state (toDriver ω) t).holes x) ∧
    (∀ x : Site d, Measurable fun ω : Data d => (state (toDriver ω) t).departures x) := by
  classical
  induction t with
  | zero =>
      refine ⟨fun p => ?_, fun p => ?_, fun x => ?_, fun x => ?_⟩
      · show Measurable fun ω : Data d => decide (p.2 < (ω.1 p.1).toNat)
        exact (measurable_from_countable' fun z : ℤ => decide (p.2 < z.toNat)).comp
          ((measurable_pi_apply p.1).comp measurable_fst)
      · exact measurable_const
      · show Measurable fun ω : Data d => (-(ω.1 x)).toNat
        exact (measurable_from_countable' fun z : ℤ => (-z).toNat).comp
          ((measurable_pi_apply x).comp measurable_fst)
      · exact measurable_const
  | succ t ih =>
      obtain ⟨hact, hpos, hhol, hdep⟩ := ih
      have hbool : ∀ (f g : Data d → Bool), Measurable f → Measurable g →
          Measurable fun ω => (f ω && g ω) := by
        intro f g hf hg
        exact (measurable_from_countable' fun b : Bool × Bool => b.1 && b.2).comp (hf.prodMk hg)
      have hposeq : ∀ (q : Label d) (y : Site d),
          Measurable fun ω : Data d => decide ((state (toDriver ω) t).pos q = y) := by
        intro q y
        exact (measurable_from_countable' fun z : Site d => decide (z = y)).comp (hpos q)
      -- the active particles at a site, filtered by a measurable predicate
      have hActFilter : ∀ (y : Site d) (R : Label d → Bool),
          Measurable fun ω : Data d =>
            ((activeAt (toDriver ω) (state (toDriver ω) t) t y).filter
                fun q => R q = true).card := by
        intro y R
        have hrw : ∀ ω : Data d,
            ((activeAt (toDriver ω) (state (toDriver ω) t) t y).filter fun q => R q = true).card
              = ((candidates ω.1 y t).filter fun q =>
                  (((state (toDriver ω) t).active q && decide ((state (toDriver ω) t).pos q = y))
                    && R q) = true).card := by
          intro ω
          unfold activeAt
          rw [Finset.filter_filter]
          congr 1
        simp only [hrw]
        exact measurable_card_filter_candidates y t _ fun q =>
          hbool _ _ (hbool _ _ (hact q) (hposeq q y)) measurable_const
      have hActCard : ∀ y : Site d,
          Measurable fun ω : Data d => (activeAt (toDriver ω) (state (toDriver ω) t) t y).card := by
        intro y
        have := hActFilter y (fun _ => true)
        simpa using this
      have hIdx : ∀ p : Label d,
          Measurable fun ω : Data d =>
            instructionIndex (toDriver ω) (state (toDriver ω) t) t p := by
        intro p
        refine Measurable.add ?_ ?_
        · exact measurable_eval_var (fun ω => (state (toDriver ω) t).pos p) (hpos p)
            (fun ω y => (state (toDriver ω) t).departures y) hdep
        · exact measurable_eval_var (fun ω => (state (toDriver ω) t).pos p) (hpos p)
            (fun ω y => ((activeAt (toDriver ω) (state (toDriver ω) t) t y).filter
              fun q => labelLT q p).card)
            (fun y => by simpa using hActFilter y (fun q => decide (labelLT q p)))
      have hNext : ∀ p : Label d,
          Measurable fun ω : Data d => nextPos (toDriver ω) (state (toDriver ω) t) t p := by
        intro p
        have hset : MeasurableSet {ω : Data d | (state (toDriver ω) t).active p = true} :=
          (hact p) (measurableSet_singleton true)
        have hthen : Measurable fun ω : Data d =>
            ω.2.1 ((state (toDriver ω) t).pos p,
              instructionIndex (toDriver ω) (state (toDriver ω) t) t p) :=
          measurable_eval_var
            (fun ω => ((state (toDriver ω) t).pos p,
              instructionIndex (toDriver ω) (state (toDriver ω) t) t p))
            ((hpos p).prodMk (hIdx p)) (fun ω q => ω.2.1 q)
            (fun q => (measurable_pi_apply q).comp (measurable_fst.comp measurable_snd))
        exact Measurable.ite hset hthen (hpos p)
      have hArrFilter : ∀ (x : Site d) (R : Data d → Label d → Bool),
          (∀ q, Measurable fun ω => R ω q) →
          Measurable fun ω : Data d =>
            ((arrivalsAt (toDriver ω) (state (toDriver ω) t) t x).filter
              fun q => R ω q = true).card := by
        intro x R hR
        have hrw : ∀ ω : Data d,
            ((arrivalsAt (toDriver ω) (state (toDriver ω) t) t x).filter
                fun q => R ω q = true).card
              = ((candidates ω.1 x (t + 1)).filter fun q =>
                  (((state (toDriver ω) t).active q &&
                    decide (nextPos (toDriver ω) (state (toDriver ω) t) t q = x))
                    && R ω q) = true).card := by
          intro ω
          unfold arrivalsAt
          rw [Finset.filter_filter]
          congr 1
        simp only [hrw]
        refine measurable_card_filter_candidates x (t + 1) _ fun q => ?_
        refine hbool _ _ (hbool _ _ (hact q) ?_) (hR q)
        exact (measurable_from_countable' fun z : Site d => decide (z = x)).comp (hNext q)
      have hArrCard : ∀ x : Site d,
          Measurable fun ω : Data d =>
            (arrivalsAt (toDriver ω) (state (toDriver ω) t) t x).card := by
        intro x
        have := hArrFilter x (fun _ _ => true) fun _ => measurable_const
        simpa using this
      have hRank : ∀ (p q : Label d),
          Measurable fun ω : Data d => decide (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
            (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p)) := by
        intro p q
        refine measurable_decide _ ?_
        have hq : Measurable fun ω : Data d => ω.2.2 (q, t) :=
          (measurable_pi_apply (q, t)).comp (measurable_snd.comp measurable_snd)
        have hp : Measurable fun ω : Data d => ω.2.2 (p, t) :=
          (measurable_pi_apply (p, t)).comp (measurable_snd.comp measurable_snd)
        by_cases hlab : labelLT q p
        · have : {ω : Data d | ω.2.2 (q, t) < ω.2.2 (p, t) ∨
              (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p)}
              = {ω : Data d | ω.2.2 (q, t) < ω.2.2 (p, t)}
                ∪ {ω : Data d | ω.2.2 (q, t) = ω.2.2 (p, t)} := by
            ext ω; simp [hlab]
          rw [this]
          exact (measurableSet_lt hq hp).union (measurableSet_eq_fun hq hp)
        · have : {ω : Data d | ω.2.2 (q, t) < ω.2.2 (p, t) ∨
              (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p)}
              = {ω : Data d | ω.2.2 (q, t) < ω.2.2 (p, t)} := by
            ext ω; simp [hlab]
          rw [this]
          exact measurableSet_lt hq hp
      have hSettles : ∀ p : Label d,
          Measurable fun ω : Data d => settles (toDriver ω) (state (toDriver ω) t) t p := by
        intro p
        have hcard : Measurable fun ω : Data d =>
            ((arrivalsAt (toDriver ω) (state (toDriver ω) t) t
                (nextPos (toDriver ω) (state (toDriver ω) t) t p)).filter
              fun q => (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
                (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p))).card := by
          refine measurable_eval_var
            (fun ω => nextPos (toDriver ω) (state (toDriver ω) t) t p) (hNext p)
            (fun ω x => ((arrivalsAt (toDriver ω) (state (toDriver ω) t) t x).filter
              fun q => (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
                (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p))).card) fun x => ?_
          have := hArrFilter x (fun ω q => decide (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
            (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p))) (hRank p)
          simpa using this
        have hholes : Measurable fun ω : Data d =>
            (state (toDriver ω) t).holes (nextPos (toDriver ω) (state (toDriver ω) t) t p) :=
          measurable_eval_var (fun ω => nextPos (toDriver ω) (state (toDriver ω) t) t p)
            (hNext p) (fun ω x => (state (toDriver ω) t).holes x) hhol
        have hrw : ∀ ω : Data d, settles (toDriver ω) (state (toDriver ω) t) t p
            = ((state (toDriver ω) t).active p &&
              decide (((arrivalsAt (toDriver ω) (state (toDriver ω) t) t
                  (nextPos (toDriver ω) (state (toDriver ω) t) t p)).filter
                fun q => (ω.2.2 (q, t) < ω.2.2 (p, t) ∨
                  (ω.2.2 (q, t) = ω.2.2 (p, t) ∧ labelLT q p))).card
                < (state (toDriver ω) t).holes
                  (nextPos (toDriver ω) (state (toDriver ω) t) t p))) := by
          intro ω
          simp [settles]
          rfl
        simp only [hrw]
        exact (measurable_from_countable' fun z : Bool × ℕ × ℕ =>
          (z.1 && decide (z.2.1 < z.2.2))).comp ((hact p).prodMk (hcard.prodMk hholes))
      refine ⟨fun p => ?_, fun p => ?_, fun x => ?_, fun x => ?_⟩
      · have hrw : ∀ ω : Data d, (state (toDriver ω) (t + 1)).active p
            = ((state (toDriver ω) t).active p
              && !settles (toDriver ω) (state (toDriver ω) t) t p) := by
          intro ω; simp [state, step]
        simp only [hrw]
        exact (measurable_from_countable' fun z : Bool × Bool => (z.1 && !z.2)).comp
          ((hact p).prodMk (hSettles p))
      · exact hNext p
      · exact (measurable_from_countable' fun z : ℕ × ℕ => z.1 - z.2).comp
          ((hhol x).prodMk (hArrCard x))
      · exact (measurable_from_countable' fun z : ℕ × ℕ => z.1 + z.2).comp
          ((hdep x).prodMk (hActCard x))

/-- The number of active labels at a site after `t` rounds is measurable, by unfolding
to a filtered candidate-set cardinality and applying `measurable_card_filter_candidates`. -/
theorem measurable_activeAt_card (t : ℕ) (y : Site d) :
    Measurable fun ω : Data d => (activeAt (toDriver ω) (state (toDriver ω) t) t y).card := by
  classical
  obtain ⟨hact, hpos, -, -⟩ := measurable_state (d := d) t
  have hrw : ∀ ω : Data d, (activeAt (toDriver ω) (state (toDriver ω) t) t y).card
      = ((candidates ω.1 y t).filter fun q =>
          ((state (toDriver ω) t).active q
            && decide ((state (toDriver ω) t).pos q = y)) = true).card := by
    intro ω
    unfold activeAt
    congr 1
  simp only [hrw]
  refine measurable_card_filter_candidates y t _ fun q => ?_
  exact (measurable_from_countable' fun b : Bool × Bool => b.1 && b.2).comp
    ((hact q).prodMk
      ((measurable_from_countable' fun z : Site d => decide (z = y)).comp (hpos q)))

/-- The particle-driven odometer is measurable, as the departures field of
`measurable_state`. -/
theorem measurable_particleOdometer (t : ℕ) (x : Site d) :
    Measurable fun ω : Data d => particleOdometer (toDriver ω) t x :=
  (measurable_state (d := d) t).2.2.2 x

/-- The particle-driven hole count is measurable, as the holes field of `measurable_state`. -/
theorem measurable_holeCount (t : ℕ) (x : Site d) :
    Measurable fun ω : Data d => holeCount (toDriver ω) t x :=
  (measurable_state (d := d) t).2.2.1 x

/-- The particle-driven active count is measurable, by `measurable_activeAt_card`. -/
theorem measurable_activeCount (t : ℕ) (x : Site d) :
    Measurable fun ω : Data d => activeCount (toDriver ω) t x :=
  measurable_activeAt_card t x

/-- The number of survivors from a site by round `t` is measurable, via the countable
partition on the initial hole count `(ω.1 y).toNat` and a filtered-cardinality sum over the
labels active there. -/
theorem measurable_survivorsFrom (t : ℕ) (y : Site d) :
    Measurable fun ω : Data d => survivorsFrom (toDriver ω) t y := by
  classical
  obtain ⟨hact, -, -, -⟩ := measurable_state (d := d) t
  refine measurable_of_countable_partition (fun ω : Data d => (ω.1 y).toNat)
    ((measurable_from_countable' fun z : ℤ => z.toNat).comp
      ((measurable_pi_apply y).comp measurable_fst)) _
    (fun N ω => ((Finset.range N).filter fun i => (state (toDriver ω) t).active (y, i) = true).card)
    (fun N => ?_) fun ω => rfl
  have hsum : ∀ ω : Data d,
      ((Finset.range N).filter fun i => (state (toDriver ω) t).active (y, i) = true).card
        = ∑ i ∈ Finset.range N, if (state (toDriver ω) t).active (y, i) = true then 1 else 0 := by
    intro ω; rw [Finset.card_filter]
  simp only [hsum]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_from_countable' fun b : Bool => if b = true then 1 else 0).comp (hact (y, i))

/-- The `U`, `A` and `H` of `LatticeProb.ParticleDrivenAgree.Basic` are measurable. -/
theorem measurable_U (t : ℕ) (x : Site d) : Measurable fun ω : Data d => U ω t x :=
  measurable_particleOdometer t x

/-- `LatticeProb.ParticleDrivenAgree.Basic`'s `A` (the active count) is measurable, by `measurable_activeCount`. -/
theorem measurable_A (t : ℕ) (x : Site d) : Measurable fun ω : Data d => A ω t x :=
  measurable_activeCount t x

/-- `LatticeProb.ParticleDrivenAgree.Basic`'s `H` (the hole count) is measurable, by `measurable_holeCount`. -/
theorem measurable_H (t : ℕ) (x : Site d) : Measurable fun ω : Data d => H ω t x :=
  measurable_holeCount t x

/-! ### The instructions of the model are neighbours -/

/-- The forward neighbour `y + unit i` lies in `nbrFinset y`. -/
theorem mem_nbrFinset_add (y : Site d) (i : Fin d) : y + unit i ∈ nbrFinset y := by
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  exact ⟨i, Or.inl rfl⟩

/-- The backward neighbour `y - unit i` lies in `nbrFinset y`. -/
theorem mem_nbrFinset_sub (y : Site d) (i : Fin d) : y - unit i ∈ nbrFinset y := by
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  exact ⟨i, Or.inr rfl⟩

/-- The instruction law at a site puts zero mass on the complement of its neighbour set,
since both Dirac summands `y + unit i` and `y - unit i` lie inside `nbrFinset y`
(`mem_nbrFinset_add`, `mem_nbrFinset_sub`). -/
theorem instructionLaw_compl_nbr (y : Site d) :
    instructionLaw y (((nbrFinset y : Finset (Site d)) : Set (Site d))ᶜ) = 0 := by
  simp only [instructionLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.coe_add, Pi.add_apply, Measure.dirac_apply]
  have hzero : ∀ i : Fin d,
      Set.indicator (((nbrFinset y : Finset (Site d)) : Set (Site d))ᶜ) (1 : Site d → ℝ≥0∞)
          (y + unit i)
        + Set.indicator (((nbrFinset y : Finset (Site d)) : Set (Site d))ᶜ)
          (1 : Site d → ℝ≥0∞) (y - unit i) = 0 := by
    intro i
    rw [Set.indicator_of_notMem (by simpa using mem_nbrFinset_add y i),
      Set.indicator_of_notMem (by simpa using mem_nbrFinset_sub y i)]
    simp
  rw [Finset.sum_congr rfl fun i _ => hzero i]
  simp

/-- Almost surely under the stack law, every instruction `σ q` points to a neighbour of its
site `q.1`, by pushing `instructionLaw_compl_nbr` forward along the coordinate evaluation
map. -/
theorem stackLaw_ae_nbr (hd : 1 ≤ d) :
    ∀ᵐ σ ∂(stackLaw d), ∀ q : Site d × ℕ, σ q ∈ nbrFinset q.1 := by
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => instructionLaw_isProbability hd q.1
  rw [MeasureTheory.ae_all_iff]
  intro q
  refine MeasureTheory.ae_iff.mpr ?_
  have hset : MeasurableSet (((nbrFinset q.1 : Finset (Site d)) : Set (Site d))ᶜ) :=
    (Finset.measurableSet _).compl
  have hrw : {σ : Site d × ℕ → Site d | ¬ σ q ∈ nbrFinset q.1}
      = (fun σ : Site d × ℕ → Site d => σ q) ⁻¹'
        (((nbrFinset q.1 : Finset (Site d)) : Set (Site d))ᶜ) := rfl
  rw [hrw, ← Measure.map_apply (measurable_pi_apply q) hset,
    show (stackLaw d).map (fun σ : Site d × ℕ → Site d => σ q) = instructionLaw q.1 from
      Measure.infinitePi_map_eval _ q]
  exact instructionLaw_compl_nbr q.1

end LatticeProb.ParticleDrivenAgree

end
