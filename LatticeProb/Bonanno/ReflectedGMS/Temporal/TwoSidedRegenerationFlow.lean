/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TwoSidedRegenerationFlow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TrajectoryCoding
import LatticeProb.Bonanno.ReflectedGMS.Temporal.ScaledConditionalTemporalAveraging
import LatticeProb.Bonanno.ReflectedGMS.Spatial.MarkedSimilarityActionLaws
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LabelBijectionProducer
import LatticeProb.Bonanno.ReflectedGMS.Environment.CanonicalSimilarityMeasurable
import LatticeProb.Bonanno.ReflectedWalk.Theorem16Statement
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Instances.ENat

/-!
# The exact re-rooting flow `θΩ` and the parabolic scaling `SΩ` of the regeneration lane

`p:lem:regeninvariant` (Lean: `GridAveragedConstantReduction.RegenerativeInvariance`) and the
root-chain system (`ScaledRootChain.ScaledRootChainSystem`) need, on the carrier `Env × X` of the
annealed law `νenv ⊗ₘ κ`,

* a time flow `θΩ` that is a flow **at every point** (`TemporalBlockSystem.flow_zero`,
  `flow_add` are pointwise), jointly measurable in `(ω, t)` (`measurable_flow`), and that
  **re-roots the environment** (Verdict B of `outputs/fable-regenerative-invariance-handoff.md`:
  a flow fixing the environment coordinate is refuted);
* a parabolic scaling `SΩ` with `θΩ (C² t) ∘ SΩ C = SΩ C ∘ θΩ t`
  (`ScaledConditionalTemporalAveraging.FlowScaleIntertwine`).

## The convention at non-vertex times (the design question)

A re-rooting flow translates the environment by the walker's displacement.  At a time where the
label path is at the cemetery `∞` (explosion / accumulation of jumps; such times exist and are
Lebesgue-null) there is no current cell.  Three candidates were examined.

1. **A position functional of the shifted label path**, e.g. the coordinatewise `limsup` of the
   cell centroids `c(y q)` over rational `q ↓ 0`.  The time-shift part of the cocycle is
   automatic, but the cocycle ALSO needs exact equivariance
   `p(translateEnv u e, relabel y) = p(e, y) - u` at every point, and a real-valued `limsup`
   returns the junk value `0` whenever the centroids are unbounded near a cemetery time; then
   `p(translate) = 0 ≠ 0 - u` and `θ a ∘ θ b ≠ θ (a + b)` at that point.  Repairing it needs a
   gate "the right limit exists at every real cemetery time", an uncountable quantifier whose
   measurability is a Skorokhod-type regularity theorem.  Rejected.
2. **The vertex of the earliest longest holding interval in `(t - 1, t)`**: a pure path
   functional, hence a cocycle, but the fixed window `1` is not scale-covariant, so
   `FlowScaleIntertwine` fails (the window becomes `C²` after scaling).  Rejected.
3. **CHOSEN: carry the planar position path as a coordinate.**  The carrier trajectory is a pair
   `(Y, P)`: the two-sided label path `Y : CadlagPath ℕ∞` (labels = code slots, `⊤` = the
   cemetery, `ℕ∞` = the one-point compactification of the labels, whose order topology is the
   manuscript's) and the two-sided position path `P : CadlagPath Plane` — exactly the
   manuscript's trajectory `(X_t)_t` in the plane, on which `S_C Ω = (C𝓗, (C X_{t/C²})_t)` acts.
   The flow never recomputes a position from the labels: it *transports* `P`,
   ```
   θΩ t (e, Y, P) = (translateEnv d e, σ ∘ Y(· + t), P(· + t) - d),   d = P t - P 0,
   ```
   with `σ = simLabel 1 d e` the canonical relabelling.  The cocycle is pure algebra
   (`reRootFlow_add`), valid at every point, cemetery times included; joint measurability is the
   càdlàg coding's (`measurable_reRootFlow`); and on the measurable, flow- and scale-invariant set
   `Coupled rep` where `P` reads the representative field `rep` at vertex times, the
   displacement IS `rep(Y t) - rep(Y 0)` at vertex times (`displacement_eq_of_coupled`): the
   centroid re-rooting for `rep` = the centroid.  What the cemetery times cost is moved to the
   kernel: `P` must be càdlàg, i.e. the representative path must extend to the cemetery times
   (`p:prop:pathsextend`), which is an almost-sure statement about the law, not a pointwise one
   about the flow.

The environment translation accepts an arbitrary real vector (`translateEnv w e =
similarityTargetEnv 1 w e`, jointly measurable `measurable_translateEnv`), and the relabelling
does not need the new origin to be a cell centroid, so nothing forces the displacement to be a
difference of centroids.

## The relabelling on ALL labels

`θΩ 0 = id` at every point forces the relabelling at `u = 0` to be the identity on every label,
including labels inactive in `e` (a trajectory of the carrier is not constrained by `e`: the
carrier is a product `Env × X`).  The existing `LabelBijectionProducer.labelEquiv` glues the
active relabelling to a `Classical.choice` bijection of the inactive labels, which does not
compose.  `simLabel s u hs e : ℕ → ℕ` instead uses the canonical `similarityRelabel` on active
labels and the ORDER isomorphism `Nat.nth (inactive e') ∘ Nat.count (inactive e)` on inactive ones
(both inactive sets are infinite, `LabelBijectionProducer.infinite_inactive_set`), so that
`simLabel_simLabel` (composition, from uniqueness of `LeastInteriorLabel` and
`similarityTargetEnv_similarityTargetEnv`), `simLabel_one_zero` (identity) and
`simLabel_injective` hold exactly, and `measurable_simLabel` holds jointly in
`(scale, centre, environment)`.

## Why not the raw `TwoSidedCoding`

`TwoSidedRegenerationCoding.TwoSidedCoding = Trajectory ℕ × Trajectory ℕ` carries the product
σ-algebra over the real time index, on which `(x, t) ↦ x t` is not jointly measurable, so no flow
that shifts the label path is jointly measurable there (checked separately in
`Temporal/TwoSidedRegenerationFlowRawObstruction`).  The line coding here is linked to the raw
coding by `ofLine` (forward half `Y s`, backward half `Y (-s)`): `twoSidedRead_ofLine` shows that
the two-sided reading of `DirectionalBracketLLNGatesCoding.codingDensity` (forward half for
`s ≥ 0`, backward half in reversed time for `s < 0`) is `Y s` at every `s`, and
`ofLine_reRootFlow_snd_of_le` shows that the flow pushes the first `t` of the forward half,
reversed, onto the front of the backward half.

Nothing here is probabilistic.  Nothing here constructs the kernel on this carrier, certifies
`p:lem:regeninvariant`, `p:prop:pathsextend`, `ScaledRootChainSystem`, or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.TwoSidedRegenerationFlow

open Code EnvironmentLaws
open ReflectedGMS.TrajectoryCoding
open ReflectedGMS.ActualMarkedBlockTransport
open ReflectedGMS.MarkedSimilarityActionLaws
open ReflectedGMS.CanonicalSimilarity
open ReflectedGMS.ScaledConditionalTemporalAveraging

/-! ### 0. The label state space `ℕ∞` -/

/-- The label state space `ℕ∞` (labels, with the cemetery `⊤`) is a Borel space: its σ-algebra is
discrete, and so is the Borel σ-algebra of a countable `T0` space. -/
instance instBorelSpaceENat : BorelSpace ℕ∞ := ⟨borel_eq_top_of_countable.symm⟩

/-! ### 1. The canonical label map of a similarity, on all labels -/

/-- The inactive labels of an environment. -/
def Inact (e : Env) (n : ℕ) : Prop := ¬ (e.val.1 n).isSome

instance instDecidablePredInact (e : Env) : DecidablePred (Inact e) := fun n => by
  unfold Inact
  infer_instance

theorem infinite_inact (e : Env) : (Set.ofPred (Inact e)).Infinite :=
  LabelBijectionProducer.infinite_inactive_set e

/-- **The canonical label map of the similarity `z ↦ s • (z - u)`**: the canonical relabelling
`similarityRelabel` on the active labels of `e`, and the order isomorphism of the (infinite)
inactive label sets on the inactive ones. -/
noncomputable def simLabel (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) (n : ℕ) : ℕ :=
  if h : (e.val.1 n).isSome then (LabelBijectionProducer.similarityRelabel s u hs e ⟨n, h⟩).val
  else Nat.nth (Inact (similarityTargetEnv s u hs e)) (Nat.count (Inact e) n)

theorem simLabel_of_isSome {s : ℝ} {u : Plane} {hs : 0 < s} {e : Env} {n : ℕ}
    (h : (e.val.1 n).isSome) :
    simLabel s u hs e n = (LabelBijectionProducer.similarityRelabel s u hs e ⟨n, h⟩).val :=
  dif_pos h

theorem simLabel_of_inact {s : ℝ} {u : Plane} {hs : 0 < s} {e : Env} {n : ℕ} (h : Inact e n) :
    simLabel s u hs e n = Nat.nth (Inact (similarityTargetEnv s u hs e)) (Nat.count (Inact e) n) :=
  dif_neg h

theorem leastInteriorLabel_unique {K : CompactCell} {n m : ℕ} (hn : LeastInteriorLabel K n)
    (hm : LeastInteriorLabel K m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact absurd hn.1 (hm.2 n h)
  · exact h
  · exact absurd hm.1 (hn.2 m h)

/-- On an active label the image is the least interior label of the transformed cell. -/
theorem leastInteriorLabel_simLabel (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) {n : ℕ}
    (h : (e.val.1 n).isSome) :
    LeastInteriorLabel (transformCell s u hs ((decode e).cell ⟨n, h⟩)) (simLabel s u hs e n) := by
  rw [simLabel_of_isSome h]
  exact leastInteriorLabel_canonicalLabel (transformIndexedCells s u hs (decode e))
    (geometry_transformIndexedCells s u hs (decode_geometry e)) ⟨n, h⟩

theorem isSome_simLabel {s : ℝ} {u : Plane} {hs : 0 < s} {e : Env} {n : ℕ}
    (h : (e.val.1 n).isSome) :
    ((similarityTargetEnv s u hs e).val.1 (simLabel s u hs e n)).isSome := by
  rw [simLabel_of_isSome h]
  exact (LabelBijectionProducer.similarityRelabel s u hs e ⟨n, h⟩).property

theorem inact_simLabel {s : ℝ} {u : Plane} {hs : 0 < s} {e : Env} {n : ℕ} (h : Inact e n) :
    Inact (similarityTargetEnv s u hs e) (simLabel s u hs e n) := by
  rw [simLabel_of_inact h]
  exact Nat.nth_mem_of_infinite (infinite_inact _) _

/-- The cell of the image label is the transformed cell. -/
theorem cell_simLabel {s : ℝ} {u : Plane} {hs : 0 < s} {e : Env} {n : ℕ}
    (h : (e.val.1 n).isSome) :
    (decode (similarityTargetEnv s u hs e)).cell ⟨simLabel s u hs e n, isSome_simLabel h⟩
      = transformCell s u hs ((decode e).cell ⟨n, h⟩) := by
  have h1 := (LabelBijectionProducer.isSimilarityRelabel_similarityRelabel s u hs e).1 ⟨n, h⟩
  have h2 : (⟨simLabel s u hs e n, isSome_simLabel h⟩ : Vertex (similarityTargetEnv s u hs e).val)
      = LabelBijectionProducer.similarityRelabel s u hs e ⟨n, h⟩ :=
    Subtype.ext (simLabel_of_isSome h)
  rw [h2]
  exact h1

/-- **Composition law of the label maps**, on every label. -/
theorem simLabel_simLabel (s t : ℝ) (u v : Plane) (hs : 0 < s) (ht : 0 < t) (e : Env) (n : ℕ) :
    simLabel s u hs (similarityTargetEnv t v ht e) (simLabel t v ht e n)
      = simLabel (s * t) (v + t⁻¹ • u) (mul_pos hs ht) e n := by
  by_cases h : (e.val.1 n).isSome
  · have h1 := isSome_simLabel (s := t) (u := v) (hs := ht) h
    have hL := leastInteriorLabel_simLabel s u hs (similarityTargetEnv t v ht e) h1
    rw [cell_simLabel h, transformCell_transformCell] at hL
    exact leastInteriorLabel_unique hL
      (leastInteriorLabel_simLabel (s * t) (v + t⁻¹ • u) (mul_pos hs ht) e h)
  · have h' : Inact e n := h
    have h1 : Inact (similarityTargetEnv t v ht e) (simLabel t v ht e n) := inact_simLabel h'
    rw [simLabel_of_inact h1, simLabel_of_inact (s := t) (u := v) (hs := ht) h',
      simLabel_of_inact (s := s * t) (u := v + t⁻¹ • u) (hs := mul_pos hs ht) h',
      Nat.count_nth_of_infinite (infinite_inact _), similarityTargetEnv_similarityTargetEnv]

theorem simLabel_congr {s s' : ℝ} {u u' : Plane} (hs : 0 < s) (hs' : 0 < s') (h₁ : s = s')
    (h₂ : u = u') (e : Env) : simLabel s u hs e = simLabel s' u' hs' e := by
  subst h₁
  subst h₂
  rfl

theorem transformCell_one_zero (K : CompactCell) : transformCell 1 0 one_pos K = K := by
  apply SetLike.coe_injective
  rw [coe_transformCell]
  have hid : positiveSimilarity 1 (0 : Plane) = id := funext fun z => by simp [positiveSimilarity]
  rw [hid, Set.image_id]

/-- **The identity similarity relabels nothing**, on every label. -/
theorem simLabel_one_zero (e : Env) (n : ℕ) : simLabel 1 0 one_pos e n = n := by
  by_cases h : (e.val.1 n).isSome
  · have hL := leastInteriorLabel_simLabel 1 0 one_pos e h
    rw [transformCell_one_zero] at hL
    exact leastInteriorLabel_unique hL (decode_canonicalLabels e ⟨n, h⟩)
  · have h' : Inact e n := h
    rw [simLabel_of_inact h']
    have he : similarityTargetEnv 1 0 one_pos e = e := translateEnv_zero e
    rw [he]
    exact Nat.nth_count h'

/-- The label map is injective (active labels go to active labels injectively, inactive ones to
inactive ones injectively). -/
theorem simLabel_injective (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) :
    Function.Injective (simLabel s u hs e) := by
  intro a b hab
  by_cases ha : (e.val.1 a).isSome <;> by_cases hb : (e.val.1 b).isSome
  · rw [simLabel_of_isSome ha, simLabel_of_isSome hb] at hab
    exact congrArg Subtype.val
      ((LabelBijectionProducer.similarityRelabel s u hs e).injective (Subtype.ext hab))
  · have h1 := isSome_simLabel (s := s) (u := u) (hs := hs) ha
    rw [hab] at h1
    exact absurd h1 (inact_simLabel hb)
  · have h1 := isSome_simLabel (s := s) (u := u) (hs := hs) hb
    rw [← hab] at h1
    exact absurd h1 (inact_simLabel ha)
  · have ha' : Inact e a := ha
    have hb' : Inact e b := hb
    rw [simLabel_of_inact ha', simLabel_of_inact hb'] at hab
    exact Nat.count_injective ha' hb' (Nat.nth_injective (infinite_inact _) hab)

/-! ### 2. Measurability of the label map -/

theorem measurable_isSome_slot (n : ℕ) : Measurable fun e : Env => (e.val.1 n).isSome := by
  refine measurable_to_bool ?_
  have hslot : Measurable fun e : Env => e.val.1 n :=
    (measurable_pi_apply n).comp (measurable_fst.comp measurable_subtype_coe)
  have hpre : (fun e : Env => (e.val.1 n).isSome) ⁻¹' {true}
      = (fun e : Env => e.val.1 n) ⁻¹' {o | o.isSome} := by
    ext e
    simp
  rw [hpre]
  exact hslot Spatial.measurableSet_slotIsSome

theorem measurableSet_inact (n : ℕ) : MeasurableSet {e : Env | Inact e n} := by
  have h := ((measurable_isSome_slot n) (measurableSet_singleton true)).compl
  have hset : {e : Env | Inact e n} = ((fun e : Env => (e.val.1 n).isSome) ⁻¹' {true})ᶜ := by
    ext e
    simp [Inact]
  rw [hset]
  exact h

theorem measurable_count_inact (n : ℕ) : Measurable fun e : Env => Nat.count (Inact e) n := by
  induction n with
  | zero =>
    simp only [Nat.count_zero]
    exact measurable_const
  | succ n ih =>
    have hpair : Measurable fun e : Env => (Nat.count (Inact e) n, (e.val.1 n).isSome) :=
      ih.prodMk (measurable_isSome_slot n)
    have hg : Measurable fun p : ℕ × Bool => p.1 + (if p.2 then 0 else 1) :=
      measurable_of_countable _
    have heq : (fun e : Env => Nat.count (Inact e) (n + 1))
        = (fun p : ℕ × Bool => p.1 + (if p.2 then 0 else 1))
          ∘ (fun e : Env => (Nat.count (Inact e) n, (e.val.1 n).isSome)) := by
      funext e
      show Nat.count (Inact e) (n + 1)
        = Nat.count (Inact e) n + (if (e.val.1 n).isSome then 0 else 1)
      rw [Nat.count_succ]
      congr 1
      by_cases h : (e.val.1 n).isSome
      · have hn : ¬ Inact e n := fun h' => h' h
        rw [if_neg hn, if_pos h]
      · have hn : Inact e n := h
        rw [if_pos hn, if_neg h]
    rw [heq]
    exact hg.comp hpair

theorem measurableSet_eq_nat {α : Type*} [MeasurableSpace α] {f g : α → ℕ} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {a | f a = g a} := by
  have hset : {a | f a = g a} = ⋃ k : ℕ, f ⁻¹' {k} ∩ g ⁻¹' {k} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨f a, rfl, h.symm⟩, fun ⟨_, h1, h2⟩ => h1.trans h2.symm⟩
  rw [hset]
  exact MeasurableSet.iUnion fun k =>
    (hf (measurableSet_singleton k)).inter (hg (measurableSet_singleton k))

theorem nth_eq_iff {p : ℕ → Prop} [DecidablePred p] (hp : (Set.ofPred p).Infinite) {k m : ℕ} :
    Nat.nth p k = m ↔ p m ∧ Nat.count p m = k := by
  constructor
  · rintro rfl
    exact ⟨Nat.nth_mem_of_infinite hp k, Nat.count_nth_of_infinite hp k⟩
  · rintro ⟨hm, rfl⟩
    exact Nat.nth_count hm

theorem imageCell_eq {s : ℝ} {hs : 0 < s} {u : Plane} {e : Env} {n : ℕ}
    (h : (e.val.1 n).isSome) :
    imageCell n ((⟨s, hs⟩ : PositiveScale), u, e) = transformCell s u hs ((decode e).cell ⟨n, h⟩) := by
  rw [decode_cell_eq_getD e ⟨n, h⟩, ← similarityCell_eq_transformCell s u hs]
  rfl

/-- **The label map is jointly measurable in the scale, the centre and the environment.** -/
theorem measurable_simLabel (n : ℕ) :
    Measurable fun a : ActionDomain => simLabel a.1.val a.2.1 a.1.property a.2.2 n := by
  refine measurable_to_countable' fun m => ?_
  have hA : MeasurableSet (SlotLabelEvent m n) := measurableSet_slotLabelEvent m n
  have hIn : MeasurableSet {a : ActionDomain | Inact a.2.2 n} :=
    (measurable_snd.comp measurable_snd) (measurableSet_inact n)
  have h1 : Measurable fun a : ActionDomain => Nat.count (Inact (similarityActionEnv a)) m :=
    (measurable_count_inact m).comp measurable_similarityActionEnv
  have h2 : Measurable fun a : ActionDomain => Nat.count (Inact a.2.2) n :=
    (measurable_count_inact n).comp (measurable_snd.comp measurable_snd)
  have hB : MeasurableSet {a : ActionDomain | Inact (similarityActionEnv a) m ∧
      Nat.count (Inact (similarityActionEnv a)) m = Nat.count (Inact a.2.2) n} :=
    (measurable_similarityActionEnv (measurableSet_inact m)).inter (measurableSet_eq_nat h1 h2)
  have heq : (fun a : ActionDomain => simLabel a.1.val a.2.1 a.1.property a.2.2 n) ⁻¹' {m}
      = SlotLabelEvent m n ∪ ({a : ActionDomain | Inact a.2.2 n} ∩
        {a : ActionDomain | Inact (similarityActionEnv a) m ∧
          Nat.count (Inact (similarityActionEnv a)) m = Nat.count (Inact a.2.2) n}) := by
    ext a
    obtain ⟨⟨s, hs⟩, u, e⟩ := a
    show simLabel s u hs e n = m ↔
      ((e.val.1 n).isSome ∧ LeastInteriorLabel (imageCell n ((⟨s, hs⟩ : PositiveScale), u, e)) m)
      ∨ (Inact e n ∧ (Inact (similarityTargetEnv s u hs e) m ∧
          Nat.count (Inact (similarityTargetEnv s u hs e)) m = Nat.count (Inact e) n))
    by_cases h : (e.val.1 n).isSome
    · have hn : ¬ Inact e n := fun h' => h' h
      rw [imageCell_eq h]
      constructor
      · intro hm
        refine Or.inl ⟨h, ?_⟩
        rw [← hm]
        exact leastInteriorLabel_simLabel s u hs e h
      · rintro (⟨_, hL⟩ | ⟨hi, _⟩)
        · exact leastInteriorLabel_unique (leastInteriorLabel_simLabel s u hs e h) hL
        · exact absurd hi hn
    · have hn : Inact e n := h
      rw [simLabel_of_inact hn, nth_eq_iff (infinite_inact _)]
      constructor
      · intro hm
        exact Or.inr ⟨hn, hm⟩
      · rintro (⟨hs', _⟩ | ⟨_, hm⟩)
        · exact absurd hs' h
        · exact hm
  rw [heq]
  exact hA.union (hIn.inter hB)

/-! ### 3. Lifting the label map to the label state space `ℕ∞` -/

/-- A label map acting on `ℕ∞`, fixing the cemetery `⊤`. -/
def liftLabel (σ : ℕ → ℕ) (x : ℕ∞) : ℕ∞ := ENat.recTopCoe ⊤ (fun n => ((σ n : ℕ) : ℕ∞)) x

@[simp] theorem liftLabel_top (σ : ℕ → ℕ) : liftLabel σ ⊤ = ⊤ := ENat.recTopCoe_top _ _

@[simp] theorem liftLabel_natCast (σ : ℕ → ℕ) (n : ℕ) : liftLabel σ n = σ n :=
  ENat.recTopCoe_natCast _ _ n

theorem liftLabel_liftLabel (σ τ : ℕ → ℕ) (x : ℕ∞) :
    liftLabel σ (liftLabel τ x) = liftLabel (fun n => σ (τ n)) x := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe n => simp

theorem liftLabel_congr {σ τ : ℕ → ℕ} (h : ∀ n, σ n = τ n) (x : ℕ∞) :
    liftLabel σ x = liftLabel τ x := by
  rw [funext h]

theorem liftLabel_eq_self {σ : ℕ → ℕ} (h : ∀ n, σ n = n) (x : ℕ∞) : liftLabel σ x = x := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe n => simp [h]

/-- An injective label map is continuous on the one-point compactification `ℕ∞`. -/
theorem continuous_liftLabel {σ : ℕ → ℕ} (hσ : Function.Injective σ) :
    Continuous (liftLabel σ) := by
  have htend : Tendsto σ atTop atTop := by
    have h := hσ.tendsto_cofinite
    rwa [Nat.cofinite_eq_atTop] at h
  refine continuous_iff_continuousAt.2 fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    show Tendsto (liftLabel σ) (𝓝 ⊤) (𝓝 (liftLabel σ ⊤))
    rw [liftLabel_top, ENat.tendsto_nhds_top_iff_natCast_lt]
    intro N
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (htend.eventually_gt_atTop N)
    filter_upwards [Ioi_mem_nhds (ENat.natCast_lt_top M)] with y hy
    induction y using ENat.recTopCoe with
    | top =>
      rw [liftLabel_top]
      exact ENat.natCast_lt_top N
    | coe n =>
      rw [liftLabel_natCast]
      have hy' : (M : ℕ∞) < n := hy
      have hn : M < n := by exact_mod_cast hy'
      exact_mod_cast hM n hn.le
  | coe n =>
    show Tendsto (liftLabel σ) (𝓝 (n : ℕ∞)) (𝓝 (liftLabel σ n))
    rw [ENat.nhds_natCast]
    exact tendsto_pure_nhds _ _

/-- The lifted label map along the joint action is jointly measurable. -/
theorem measurable_liftLabel_simLabel :
    Measurable fun x : ActionDomain × ℕ∞ =>
      liftLabel (simLabel x.1.1.val x.1.2.1 x.1.1.property x.1.2.2) x.2 := by
  refine measurable_from_prod_countable_left fun y => ?_
  induction y using ENat.recTopCoe with
  | top =>
    simp only [liftLabel_top]
    exact measurable_const
  | coe n =>
    simp only [liftLabel_natCast]
    exact (Measurable.of_discrete (f := (Nat.cast : ℕ → ℕ∞))).comp (measurable_simLabel n)

/-! ### 4. Path operations -/

/-- Relabelling a label path by an injective label map. -/
def relabelPath (σ : ℕ → ℕ) (hσ : Function.Injective σ) (Y : CadlagPath ℕ∞) : CadlagPath ℕ∞ where
  toFun t := liftLabel σ (Y.toFun t)
  isCadlag' := Y.isCadlag'.continuous_comp (continuous_liftLabel hσ)

/-- Translating a position path by a constant vector. -/
def translatePath (d : Plane) (P : CadlagPath Plane) : CadlagPath Plane where
  toFun t := P.toFun t - d
  isCadlag' := P.isCadlag'.continuous_comp (continuous_sub_right d)

/-! ### 5. The carrier, the flow and the scaling -/

/-- **The trajectory coding of the flow**: the two-sided label path and the two-sided position
path. -/
abbrev FlowCoding : Type := CadlagPath ℕ∞ × CadlagPath Plane

/-- **The carrier** `Env × X` of the annealed law. -/
abbrev FlowSpace : Type := Env × FlowCoding

/-- The displacement of the walker between times `0` and `t`. -/
def displacement (ω : FlowSpace) (t : ℝ) : Plane := ω.2.2.toFun t - ω.2.2.toFun 0

/-- **The exact re-rooting flow** `θΩ`: shift both paths by `t`, translate the environment by the
displacement `d = P t - P 0`, relabel the labels canonically, and re-centre the position path. -/
noncomputable def reRootFlow (t : ℝ) (ω : FlowSpace) : FlowSpace :=
  (translateEnv (displacement ω t) ω.1,
    relabelPath (simLabel 1 (displacement ω t) one_pos ω.1) (simLabel_injective _ _ _ _)
      (CadlagPath.timeShift t ω.2.1),
    translatePath (displacement ω t) (CadlagPath.timeShift t ω.2.2))

/-- **The parabolic scaling** `SΩ C`: the environment by the canonical dilation
`similarityTargetEnv C 0`, the labels relabelled canonically, both paths slowed by `C²`, the
positions multiplied by `C`.  The identity for `C ≤ 0`, where it is never used. -/
noncomputable def reScale (C : ℝ) (ω : FlowSpace) : FlowSpace :=
  if hC : 0 < C then
    (similarityTargetEnv C 0 hC ω.1,
      CadlagPath.parabolicDilate (continuous_liftLabel (simLabel_injective C 0 hC ω.1))
        (pow_pos hC 2) ω.2.1,
      CadlagPath.parabolicDilate (continuous_const_smul C) (pow_pos hC 2) ω.2.2)
  else ω

@[simp] theorem reRootFlow_fst (t : ℝ) (ω : FlowSpace) :
    (reRootFlow t ω).1 = translateEnv (displacement ω t) ω.1 := rfl

@[simp] theorem reRootFlow_label (t : ℝ) (ω : FlowSpace) (s : ℝ) :
    (reRootFlow t ω).2.1.toFun s
      = liftLabel (simLabel 1 (displacement ω t) one_pos ω.1) (ω.2.1.toFun (s + t)) := rfl

@[simp] theorem reRootFlow_pos (t : ℝ) (ω : FlowSpace) (s : ℝ) :
    (reRootFlow t ω).2.2.toFun s = ω.2.2.toFun (s + t) - displacement ω t := rfl

theorem reScale_fst {C : ℝ} (hC : 0 < C) (ω : FlowSpace) :
    (reScale C ω).1 = similarityTargetEnv C 0 hC ω.1 := by
  rw [reScale, dif_pos hC]

theorem reScale_label {C : ℝ} (hC : 0 < C) (ω : FlowSpace) (s : ℝ) :
    (reScale C ω).2.1.toFun s = liftLabel (simLabel C 0 hC ω.1) (ω.2.1.toFun ((C ^ 2)⁻¹ * s)) := by
  rw [reScale, dif_pos hC]
  rfl

theorem reScale_pos {C : ℝ} (hC : 0 < C) (ω : FlowSpace) (s : ℝ) :
    (reScale C ω).2.2.toFun s = C • ω.2.2.toFun ((C ^ 2)⁻¹ * s) := by
  rw [reScale, dif_pos hC]
  rfl

theorem displacement_zero (ω : FlowSpace) : displacement ω 0 = 0 := sub_self _

/-- The displacement is an additive cocycle along the flow. -/
theorem displacement_reRootFlow (a b : ℝ) (ω : FlowSpace) :
    displacement (reRootFlow b ω) a = displacement ω (a + b) - displacement ω b := by
  show (ω.2.2.toFun (a + b) - displacement ω b) - (ω.2.2.toFun (0 + b) - displacement ω b)
    = displacement ω (a + b) - displacement ω b
  rw [zero_add]
  simp only [displacement]
  abel

/-! ### 6. The flow laws, at every point -/

/-- **`θΩ 0 = id`, at every point.** -/
theorem reRootFlow_zero (ω : FlowSpace) : reRootFlow 0 ω = ω := by
  obtain ⟨e, Y, P⟩ := ω
  have hd : displacement (e, Y, P) 0 = 0 := displacement_zero _
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show translateEnv (displacement (e, Y, P) 0) e = e
    rw [hd, translateEnv_zero]
  · refine CadlagPath.ext' (funext fun s => ?_)
    show liftLabel (simLabel 1 (displacement (e, Y, P) 0) one_pos e) (Y.toFun (s + 0)) = Y.toFun s
    rw [hd, add_zero]
    exact liftLabel_eq_self (simLabel_one_zero e) _
  · refine CadlagPath.ext' (funext fun s => ?_)
    show P.toFun (s + 0) - displacement (e, Y, P) 0 = P.toFun s
    rw [hd, add_zero, sub_zero]

/-- Composition of the translation label maps. -/
theorem simLabel_translate (w v : Plane) (e : Env) (n : ℕ) :
    simLabel 1 v one_pos (translateEnv w e) (simLabel 1 w one_pos e n)
      = simLabel 1 (w + v) one_pos e n := by
  have h := simLabel_simLabel 1 1 v w one_pos one_pos e n
  rw [simLabel_congr (mul_pos one_pos one_pos) one_pos (mul_one 1)
    (by rw [inv_one, one_smul]) e] at h
  exact h

/-- **`θΩ a ∘ θΩ b = θΩ (a + b)`, at every point** (cemetery times included: the flow transports
the position path, it never recomputes it). -/
theorem reRootFlow_add (a b : ℝ) (ω : FlowSpace) :
    reRootFlow a (reRootFlow b ω) = reRootFlow (a + b) ω := by
  obtain ⟨e, Y, P⟩ := ω
  have hd := displacement_reRootFlow a b (e, Y, P)
  have hsum : displacement (e, Y, P) b + displacement (reRootFlow b (e, Y, P)) a
      = displacement (e, Y, P) (a + b) := by
    rw [hd]
    abel
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show translateEnv (displacement (reRootFlow b (e, Y, P)) a)
        (translateEnv (displacement (e, Y, P) b) e)
      = translateEnv (displacement (e, Y, P) (a + b)) e
    rw [translateEnv_translateEnv, hsum]
  · refine CadlagPath.ext' (funext fun s => ?_)
    show liftLabel (simLabel 1 (displacement (reRootFlow b (e, Y, P)) a) one_pos
          (translateEnv (displacement (e, Y, P) b) e))
        (liftLabel (simLabel 1 (displacement (e, Y, P) b) one_pos e) (Y.toFun (s + a + b)))
      = liftLabel (simLabel 1 (displacement (e, Y, P) (a + b)) one_pos e) (Y.toFun (s + (a + b)))
    rw [liftLabel_liftLabel, add_assoc]
    refine liftLabel_congr (fun n => ?_) _
    rw [simLabel_translate, hsum]
  · refine CadlagPath.ext' (funext fun s => ?_)
    show (P.toFun (s + a + b) - displacement (e, Y, P) b) - displacement (reRootFlow b (e, Y, P)) a
      = P.toFun (s + (a + b)) - displacement (e, Y, P) (a + b)
    rw [← hsum, add_assoc]
    abel

/-! ### 7. Joint measurability of the flow -/

theorem measurable_displacement :
    Measurable fun p : FlowSpace × ℝ => displacement p.1 p.2 := by
  have hP : Measurable fun p : FlowSpace × ℝ => p.1.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have h1 : Measurable fun p : FlowSpace × ℝ => p.1.2.2.toFun p.2 :=
    CadlagPath.measurable_eval_uncurry.comp (hP.prodMk measurable_snd)
  have h0 : Measurable fun p : FlowSpace × ℝ => p.1.2.2.toFun 0 :=
    (CadlagPath.measurable_eval 0).comp hP
  exact h1.sub h0

/-- **The flow is jointly measurable** (field `measurable_flow` of
`ConditionalTemporalAveraging.TemporalBlockSystem`, on the `Env × X` factor). -/
theorem measurable_reRootFlow : Measurable fun p : FlowSpace × ℝ => reRootFlow p.2 p.1 := by
  have hd := measurable_displacement
  have he : Measurable fun p : FlowSpace × ℝ => p.1.1 := measurable_fst.comp measurable_fst
  have hY : Measurable fun p : FlowSpace × ℝ => p.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hP : Measurable fun p : FlowSpace × ℝ => p.1.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hact : Measurable fun p : FlowSpace × ℝ =>
      (((⟨1, one_pos⟩ : PositiveScale), displacement p.1 p.2, p.1.1) : ActionDomain) :=
    measurable_const.prodMk (hd.prodMk he)
  -- the environment component
  have h1c : Measurable ((fun q : Env × Plane => translateEnv q.2 q.1)
      ∘ fun p : FlowSpace × ℝ => (p.1.1, displacement p.1 p.2)) :=
    measurable_translateEnv.comp (he.prodMk hd)
  have h1 : Measurable fun p : FlowSpace × ℝ => translateEnv (displacement p.1 p.2) p.1.1 := by
    simpa only [Function.comp_def] using h1c
  -- the label component
  have h2 : Measurable fun p : FlowSpace × ℝ =>
      relabelPath (simLabel 1 (displacement p.1 p.2) one_pos p.1.1) (simLabel_injective _ _ _ _)
        (CadlagPath.timeShift p.2 p.1.2.1) := by
    refine CadlagPath.measurable_of_ratEval fun q => ?_
    have hYq : Measurable fun p : FlowSpace × ℝ => p.1.2.1.toFun ((q : ℝ) + p.2) :=
      CadlagPath.measurable_eval_uncurry.comp (hY.prodMk (measurable_const.add measurable_snd))
    have hc : Measurable ((fun x : ActionDomain × ℕ∞ =>
          liftLabel (simLabel x.1.1.val x.1.2.1 x.1.1.property x.1.2.2) x.2)
        ∘ fun p : FlowSpace × ℝ =>
          ((((⟨1, one_pos⟩ : PositiveScale), displacement p.1 p.2, p.1.1) : ActionDomain),
            p.1.2.1.toFun ((q : ℝ) + p.2))) :=
      measurable_liftLabel_simLabel.comp (hact.prodMk hYq)
    have hc' : Measurable fun p : FlowSpace × ℝ =>
        liftLabel (simLabel 1 (displacement p.1 p.2) one_pos p.1.1) (p.1.2.1.toFun ((q : ℝ) + p.2)) := by
      simpa only [Function.comp_def] using hc
    exact hc'
  -- the position component
  have h3 : Measurable fun p : FlowSpace × ℝ =>
      translatePath (displacement p.1 p.2) (CadlagPath.timeShift p.2 p.1.2.2) := by
    refine CadlagPath.measurable_of_ratEval fun q => ?_
    have hPq : Measurable fun p : FlowSpace × ℝ => p.1.2.2.toFun ((q : ℝ) + p.2) :=
      CadlagPath.measurable_eval_uncurry.comp (hP.prodMk (measurable_const.add measurable_snd))
    exact hPq.sub hd
  have hfun : (fun p : FlowSpace × ℝ => reRootFlow p.2 p.1) = fun p : FlowSpace × ℝ =>
      (translateEnv (displacement p.1 p.2) p.1.1,
        relabelPath (simLabel 1 (displacement p.1 p.2) one_pos p.1.1) (simLabel_injective _ _ _ _)
          (CadlagPath.timeShift p.2 p.1.2.1),
        translatePath (displacement p.1 p.2) (CadlagPath.timeShift p.2 p.1.2.2)) := rfl
  rw [hfun]
  exact h1.prodMk (h2.prodMk h3)

/-! ### 8. The flow and the scaling intertwine parabolically -/

/-- **`θΩ (C² t) ∘ SΩ C = SΩ C ∘ θΩ t`, at every point**: the field `flowScale` of
`ScaledRootChainSystem` on the `Env × X` factor. -/
theorem flowScaleIntertwine_reRootFlow : FlowScaleIntertwine reRootFlow reScale := by
  intro C hC t ω
  obtain ⟨e, Y, P⟩ := ω
  have hC2 : C ^ 2 ≠ 0 := pow_ne_zero 2 hC.ne'
  set d := displacement (e, Y, P) t with hd_def
  have hdisp : displacement (reScale C (e, Y, P)) (C ^ 2 * t) = C • d := by
    show (reScale C (e, Y, P)).2.2.toFun (C ^ 2 * t) - (reScale C (e, Y, P)).2.2.toFun 0 = C • d
    rw [reScale_pos hC, reScale_pos hC, inv_mul_cancel_left₀ hC2, mul_zero, hd_def, displacement,
      smul_sub]
  have htime : ∀ s : ℝ, (C ^ 2)⁻¹ * (s + C ^ 2 * t) = (C ^ 2)⁻¹ * s + t := by
    intro s
    rw [mul_add, inv_mul_cancel_left₀ hC2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show translateEnv (displacement (reScale C (e, Y, P)) (C ^ 2 * t)) (reScale C (e, Y, P)).1
      = (reScale C (reRootFlow t (e, Y, P))).1
    rw [reScale_fst hC, reScale_fst hC, hdisp]
    show translateEnv (C • d) (similarityTargetEnv C 0 hC e)
      = similarityTargetEnv C 0 hC (translateEnv d e)
    rw [similarityTargetEnv_zero_translateEnv_eq_translateEnv]
  · refine CadlagPath.ext' (funext fun s => ?_)
    show liftLabel (simLabel 1 (displacement (reScale C (e, Y, P)) (C ^ 2 * t)) one_pos
          (reScale C (e, Y, P)).1) ((reScale C (e, Y, P)).2.1.toFun (s + C ^ 2 * t))
      = (reScale C (reRootFlow t (e, Y, P))).2.1.toFun s
    rw [reScale_label hC, reScale_label hC, reScale_fst hC, hdisp, htime]
    show liftLabel (simLabel 1 (C • d) one_pos (similarityTargetEnv C 0 hC e))
        (liftLabel (simLabel C 0 hC e) (Y.toFun ((C ^ 2)⁻¹ * s + t)))
      = liftLabel (simLabel C 0 hC (translateEnv d e))
        (liftLabel (simLabel 1 d one_pos e) (Y.toFun ((C ^ 2)⁻¹ * s + t)))
    rw [liftLabel_liftLabel, liftLabel_liftLabel]
    refine liftLabel_congr (fun n => ?_) _
    have hL := simLabel_simLabel 1 C (C • d) 0 one_pos hC e n
    have hR := simLabel_simLabel C 1 0 d hC one_pos e n
    have hL' : simLabel (1 * C) (0 + C⁻¹ • (C • d)) (mul_pos one_pos hC) e
        = simLabel C d hC e :=
      simLabel_congr _ _ (one_mul C) (by rw [zero_add, inv_smul_smul₀ hC.ne']) e
    have hR' : simLabel (C * 1) (d + (1 : ℝ)⁻¹ • (0 : Plane)) (mul_pos hC one_pos) e
        = simLabel C d hC e :=
      simLabel_congr _ _ (mul_one C) (by rw [smul_zero, add_zero]) e
    rw [hL'] at hL
    rw [hR'] at hR
    exact hL.trans hR.symm
  · refine CadlagPath.ext' (funext fun s => ?_)
    show (reScale C (e, Y, P)).2.2.toFun (s + C ^ 2 * t)
        - displacement (reScale C (e, Y, P)) (C ^ 2 * t)
      = (reScale C (reRootFlow t (e, Y, P))).2.2.toFun s
    rw [reScale_pos hC, reScale_pos hC, hdisp, htime]
    show C • P.toFun ((C ^ 2)⁻¹ * s + t) - C • d = C • (P.toFun ((C ^ 2)⁻¹ * s + t) - d)
    rw [smul_sub]

/-! ### 9. Vertex times: the displacement is the representative displacement -/

/-- **The coupling of the two paths by a representative field** `rep`: at every rational time at
which the label path sits at an active label `n`, the position path is at `rep e n`.  (For the
kernel of the regeneration lane, `rep` is the cell centroid and `P` its extension to the
cemetery times.) -/
def Coupled (rep : Env → ℕ → Plane) : Set FlowSpace :=
  {ω | ∀ (q : ℚ) (n : ℕ), ω.2.1.toFun q = n → (ω.1.val.1 n).isSome →
    ω.2.2.toFun q = rep ω.1 n}

theorem measurableSet_coupled {rep : Env → ℕ → Plane} (hrep : ∀ n, Measurable fun e => rep e n) :
    MeasurableSet (Coupled rep) := by
  have hset : Coupled rep = ⋂ (q : ℚ) (n : ℕ),
      ({ω : FlowSpace | ω.2.1.toFun q = n}ᶜ ∪ {ω : FlowSpace | ¬ (ω.1.val.1 n).isSome})
        ∪ {ω : FlowSpace | ω.2.2.toFun q = rep ω.1 n} := by
    ext ω
    simp only [Coupled, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    constructor
    · intro h q n
      by_cases h1 : ω.2.1.toFun q = n
      · by_cases h2 : (ω.1.val.1 n).isSome
        · exact Or.inr (h q n h1 h2)
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl h1)
    · intro h q n h1 h2
      rcases h q n with (h3 | h3) | h3
      · exact absurd h1 h3
      · exact absurd h2 h3
      · exact h3
  rw [hset]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun n => ?_
  have hY : Measurable fun ω : FlowSpace => ω.2.1.toFun q :=
    (CadlagPath.measurable_eval _).comp (measurable_fst.comp measurable_snd)
  have hP : Measurable fun ω : FlowSpace => ω.2.2.toFun q :=
    (CadlagPath.measurable_eval _).comp (measurable_snd.comp measurable_snd)
  refine ((hY (measurableSet_singleton _)).compl.union ?_).union ?_
  · exact measurable_fst (measurableSet_inact n)
  · exact measurableSet_eq_fun hP ((hrep n).comp measurable_fst)

/-- Translation covariance of a representative field along the canonical relabelling. -/
def RepTranslationCovariant (rep : Env → ℕ → Plane) : Prop :=
  ∀ (u : Plane) (e : Env) (n : ℕ), (e.val.1 n).isSome →
    rep (translateEnv u e) (simLabel 1 u one_pos e n) = rep e n - u

/-- Dilation covariance of a representative field along the canonical relabelling. -/
def RepDilationCovariant (rep : Env → ℕ → Plane) : Prop :=
  ∀ (C : ℝ) (hC : 0 < C) (e : Env) (n : ℕ), (e.val.1 n).isSome →
    rep (similarityTargetEnv C 0 hC e) (simLabel C 0 hC e n) = C • rep e n

/-- A label of a relabelled path that is finite comes from a finite label. -/
theorem exists_of_liftLabel_eq {σ : ℕ → ℕ} {x : ℕ∞} {m : ℕ} (h : liftLabel σ x = m) :
    ∃ n : ℕ, x = n ∧ σ n = m := by
  induction x using ENat.recTopCoe with
  | top =>
    rw [liftLabel_top] at h
    exact absurd h.symm (ENat.natCast_ne_top m)
  | coe n =>
    rw [liftLabel_natCast] at h
    exact ⟨n, rfl, by exact_mod_cast h⟩

/-! ### 10. Frames, the plain shift and the rooting map

The regeneration lane's laws are started at the root cell `H_0` in the environment's own frame
(`TwoSidedRegenerationCoding.rootedLaw`), and the time-transport computation of
`outputs/area-clock-reversibility-handoff.2026-09-18.md` (item T2) asks for a rooting map
`root` with `θΩ t ∘ root = root ∘ (id × timeShift t)` and `SΩ C ∘ root = root ∘ (dilation)`.
Both hold here, for EVERY reference point `c : Env → Plane` (`reRootFlow_rootMap`) and every
dilation-covariant one (`reScale_rootMap`): the rooted flow is conjugate to the plain shift, which
keeps the environment. -/

/-- **Moving the frame by `u`**: translate the environment by `u`, relabel canonically,
translate the positions by `-u`. -/
noncomputable def reFrame (u : Plane) (ω : FlowSpace) : FlowSpace :=
  (translateEnv u ω.1, relabelPath (simLabel 1 u one_pos ω.1) (simLabel_injective _ _ _ _) ω.2.1,
    translatePath u ω.2.2)

/-- **The plain (unrooted) time shift**: the environment is kept, both paths are shifted. -/
def plainShift (t : ℝ) (ω : FlowSpace) : FlowSpace :=
  (ω.1, CadlagPath.timeShift t ω.2.1, CadlagPath.timeShift t ω.2.2)

/-- The re-rooting flow is the plain shift followed by the frame change by the displacement. -/
theorem reRootFlow_eq_reFrame (t : ℝ) (ω : FlowSpace) :
    reRootFlow t ω = reFrame (displacement ω t) (plainShift t ω) := rfl

theorem plainShift_reFrame (t : ℝ) (u : Plane) (ω : FlowSpace) :
    plainShift t (reFrame u ω) = reFrame u (plainShift t ω) := rfl

theorem displacement_reFrame (u : Plane) (ω : FlowSpace) (t : ℝ) :
    displacement (reFrame u ω) t = displacement ω t := by
  show (ω.2.2.toFun t - u) - (ω.2.2.toFun 0 - u) = ω.2.2.toFun t - ω.2.2.toFun 0
  exact sub_sub_sub_cancel_right _ _ _

theorem reFrame_reFrame (u v : Plane) (ω : FlowSpace) :
    reFrame v (reFrame u ω) = reFrame (u + v) ω := by
  obtain ⟨e, Y, P⟩ := ω
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact translateEnv_translateEnv u v e
  · refine CadlagPath.ext' (funext fun s => ?_)
    show liftLabel (simLabel 1 v one_pos (translateEnv u e))
        (liftLabel (simLabel 1 u one_pos e) (Y.toFun s))
      = liftLabel (simLabel 1 (u + v) one_pos e) (Y.toFun s)
    rw [liftLabel_liftLabel]
    exact liftLabel_congr (fun n => simLabel_translate u v e n) _
  · refine CadlagPath.ext' (funext fun s => ?_)
    show P.toFun s - u - v = P.toFun s - (u + v)
    rw [sub_sub]

/-- The dilation and translation label maps commute (both are the label map of
`z ↦ C • (z - u)`). -/
theorem simLabel_dilate_translate {C : ℝ} (hC : 0 < C) (u : Plane) (e : Env) (n : ℕ) :
    simLabel C 0 hC (translateEnv u e) (simLabel 1 u one_pos e n)
      = simLabel 1 (C • u) one_pos (similarityTargetEnv C 0 hC e) (simLabel C 0 hC e n) := by
  have hR := simLabel_simLabel C 1 0 u hC one_pos e n
  have hL := simLabel_simLabel 1 C (C • u) 0 one_pos hC e n
  have hR' : simLabel (C * 1) (u + (1 : ℝ)⁻¹ • (0 : Plane)) (mul_pos hC one_pos) e
      = simLabel C u hC e :=
    simLabel_congr _ _ (mul_one C) (by rw [smul_zero, add_zero]) e
  have hL' : simLabel (1 * C) (0 + C⁻¹ • (C • u)) (mul_pos one_pos hC) e = simLabel C u hC e :=
    simLabel_congr _ _ (one_mul C) (by rw [zero_add, inv_smul_smul₀ hC.ne']) e
  rw [hR'] at hR
  rw [hL'] at hL
  exact hR.trans hL.symm

/-- **The scaling moves frames covariantly**: `SΩ C ∘ reFrame u = reFrame (C • u) ∘ SΩ C`. -/
theorem reScale_reFrame {C : ℝ} (hC : 0 < C) (u : Plane) (ω : FlowSpace) :
    reScale C (reFrame u ω) = reFrame (C • u) (reScale C ω) := by
  obtain ⟨e, Y, P⟩ := ω
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [reScale_fst hC]
    show similarityTargetEnv C 0 hC (translateEnv u e)
      = translateEnv (C • u) (reScale C (e, Y, P)).1
    rw [reScale_fst hC]
    exact similarityTargetEnv_zero_translateEnv_eq_translateEnv C hC u e
  · refine CadlagPath.ext' (funext fun s => ?_)
    rw [reScale_label hC]
    show liftLabel (simLabel C 0 hC (translateEnv u e))
        (liftLabel (simLabel 1 u one_pos e) (Y.toFun ((C ^ 2)⁻¹ * s)))
      = liftLabel (simLabel 1 (C • u) one_pos (reScale C (e, Y, P)).1)
        ((reScale C (e, Y, P)).2.1.toFun s)
    rw [reScale_label hC, reScale_fst hC, liftLabel_liftLabel, liftLabel_liftLabel]
    exact liftLabel_congr (fun n => simLabel_dilate_translate hC u e n) _
  · refine CadlagPath.ext' (funext fun s => ?_)
    rw [reScale_pos hC]
    show C • (P.toFun ((C ^ 2)⁻¹ * s) - u) = (reScale C (e, Y, P)).2.2.toFun s - C • u
    rw [reScale_pos hC, smul_sub]

/-- **The rooting map** at a reference point `c e` of the environment: the frame in which the
walker's time-`0` position sits where `c e` sat. -/
noncomputable def rootMap (c : Env → Plane) (ω : FlowSpace) : FlowSpace :=
  reFrame (ω.2.2.toFun 0 - c ω.1) ω

/-- **T2, flow half**: `θΩ t ∘ rootMap c = rootMap c ∘ plainShift t`, for every reference point. -/
theorem reRootFlow_rootMap (c : Env → Plane) (t : ℝ) (ω : FlowSpace) :
    reRootFlow t (rootMap c ω) = rootMap c (plainShift t ω) := by
  rw [rootMap, rootMap, reRootFlow_eq_reFrame, displacement_reFrame, plainShift_reFrame,
    reFrame_reFrame]
  congr 1
  show ω.2.2.toFun 0 - c ω.1 + (ω.2.2.toFun t - ω.2.2.toFun 0) = ω.2.2.toFun (0 + t) - c ω.1
  rw [zero_add]
  abel

/-- **T2, scaling half**: `SΩ C ∘ rootMap c = rootMap c ∘ SΩ C` for a dilation-covariant
reference point. -/
theorem reScale_rootMap {c : Env → Plane}
    (hc : ∀ (C : ℝ) (hC : 0 < C) (e : Env), c (similarityTargetEnv C 0 hC e) = C • c e)
    {C : ℝ} (hC : 0 < C) (ω : FlowSpace) :
    reScale C (rootMap c ω) = rootMap c (reScale C ω) := by
  rw [rootMap, rootMap, reScale_reFrame hC]
  congr 1
  rw [reScale_pos hC, reScale_fst hC, mul_zero, hc C hC, smul_sub]

theorem measurable_rootMap {c : Env → Plane} (hc : Measurable c) : Measurable (rootMap c) := by
  have he : Measurable fun ω : FlowSpace => ω.1 := measurable_fst
  have hY : Measurable fun ω : FlowSpace => ω.2.1 := measurable_fst.comp measurable_snd
  have hP : Measurable fun ω : FlowSpace => ω.2.2 := measurable_snd.comp measurable_snd
  have hu : Measurable fun ω : FlowSpace => ω.2.2.toFun 0 - c ω.1 :=
    ((CadlagPath.measurable_eval 0).comp hP).sub (hc.comp he)
  have hact : Measurable fun ω : FlowSpace =>
      (((⟨1, one_pos⟩ : PositiveScale), ω.2.2.toFun 0 - c ω.1, ω.1) : ActionDomain) :=
    measurable_const.prodMk (hu.prodMk he)
  have h1c : Measurable ((fun q : Env × Plane => translateEnv q.2 q.1)
      ∘ fun ω : FlowSpace => (ω.1, ω.2.2.toFun 0 - c ω.1)) :=
    measurable_translateEnv.comp (he.prodMk hu)
  have h1 : Measurable fun ω : FlowSpace => translateEnv (ω.2.2.toFun 0 - c ω.1) ω.1 := by
    simpa only [Function.comp_def] using h1c
  have h2 : Measurable fun ω : FlowSpace =>
      relabelPath (simLabel 1 (ω.2.2.toFun 0 - c ω.1) one_pos ω.1) (simLabel_injective _ _ _ _)
        ω.2.1 := by
    refine CadlagPath.measurable_of_ratEval fun q => ?_
    have hYq : Measurable fun ω : FlowSpace => ω.2.1.toFun (q : ℝ) :=
      (CadlagPath.measurable_eval _).comp hY
    have hc2 : Measurable ((fun x : ActionDomain × ℕ∞ =>
          liftLabel (simLabel x.1.1.val x.1.2.1 x.1.1.property x.1.2.2) x.2)
        ∘ fun ω : FlowSpace =>
          ((((⟨1, one_pos⟩ : PositiveScale), ω.2.2.toFun 0 - c ω.1, ω.1) : ActionDomain),
            ω.2.1.toFun (q : ℝ))) :=
      measurable_liftLabel_simLabel.comp (hact.prodMk hYq)
    have hc2' : Measurable fun ω : FlowSpace =>
        liftLabel (simLabel 1 (ω.2.2.toFun 0 - c ω.1) one_pos ω.1) (ω.2.1.toFun (q : ℝ)) := by
      simpa only [Function.comp_def] using hc2
    exact hc2'
  have h3 : Measurable fun ω : FlowSpace => translatePath (ω.2.2.toFun 0 - c ω.1) ω.2.2 := by
    refine CadlagPath.measurable_of_ratEval fun q => ?_
    exact ((CadlagPath.measurable_eval _).comp hP).sub hu
  have hfun : rootMap c = fun ω : FlowSpace =>
      (translateEnv (ω.2.2.toFun 0 - c ω.1) ω.1,
        relabelPath (simLabel 1 (ω.2.2.toFun 0 - c ω.1) one_pos ω.1) (simLabel_injective _ _ _ _)
          ω.2.1,
        translatePath (ω.2.2.toFun 0 - c ω.1) ω.2.2) := rfl
  rw [hfun]
  exact h1.prodMk (h2.prodMk h3)

/-! ### 11. The link with the raw two-sided label coding -/

open ReflectedWalk

/-- `ℕ∞` back to the raw label alphabet `Option ℕ` (`⊤ ↦ none`). -/
def toOptLabel (x : ℕ∞) : Option ℕ := ENat.recTopCoe none some x

@[simp] theorem toOptLabel_top : toOptLabel ⊤ = none := ENat.recTopCoe_top _ _

@[simp] theorem toOptLabel_natCast (n : ℕ) : toOptLabel n = some n := ENat.recTopCoe_natCast _ _ n

end ReflectedGMS.TwoSidedRegenerationFlow
