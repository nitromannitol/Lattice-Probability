/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.TwoSidedCycleSplice at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CadlagRegenerationCoding
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CadlagRegenerationActual
import LatticeProb.Bonanno.ReflectedGMS.Temporal.BernoulliCycleInvariant

/-!
# The two-sided cycle splice (regeneration lane, milestone 2(a))

Handoff `outputs/fable-regenerative-invariance-handoff.md`, "Milestones 2–3", item (a).  On the
two-sided label coding `Trajectory ℕ × Trajectory ℕ` (`TwoSidedRegenerationCoding.TwoSidedCoding`:
forward half, backward half read in reversed time) the re-rooting at the first complete return
of the forward half is

  `ρ (x⁺, x⁻) = (x⁺ after τ, rev (x⁺|[0,τ]) ⊕ x⁻)`,   `τ` = first complete return of `x⁺`.

This module builds the splice `(ℤ → Cyc v) → TwoSidedReg` of a two-sided sequence of complete
cycles and proves `splice ∘ cycleShift = ρ ∘ splice` **for every sequence**, then
`CycleErgodic (entranceLaw ν) ρ` for the entrance-rooted i.i.d.-cycle law of ANY cycle law `ν`
(two-sided Bernoulli ergodicity).

## The regularity subtype

`TwoSidedReg` is the subtype of pairs whose halves are both right-regular (properties (ii)+(R)
of `IsReflectedWalk`, `RightRegularAt`) with left limits (`HasLeftLimits`: every vertex
indicator is locally constant immediately to the left of every positive time — the pointwise
content of `Forms/VertexIndicatorLeftLimits`).  Left limits are what make the reversed first
cycle right-regular (`isRegLL_revPiece`), and right regularity is what makes the reversal have
left limits again, so the subtype is `ρ`-stable (`isTwoSidedRegular_rhoRaw`).

The reversal of a piece is the right-continuous one, `revPiece x T u = x((T − u)−)` (`leftLim`).

## Measurability

On the subtype the evaluation at a random time is jointly measurable
(`CadlagRegenerationCoding.measurable_regTraj_eval`), and so is the left limit at a random time
(`measurable_leftLim_at`, read along `T − 1/(n+1)`).  Hence `splice` (`measurable_splice`) and
`ρ` (`measurable_rho`, through the dense-hitting-time form of the first return) are measurable.

Nothing here is probabilistic beyond the last composition with
`Temporal/BernoulliCycleInvariant.ae_eq_const_of_cycleShift_invariant`.
-/

-- Merged from `ReflectedGMS/Temporal/CadlagRegenerationTransfer.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_CadlagRegenerationTransfer

/-!
# Ergodicity transfers along absolute continuity (the consumption shape of clauses 3 and 4)

Clauses 3 and 4 of the regeneration handoff are absolute-continuity statements:

* clause 3 (`L_v/h_v` size-biasing): the **vertex-rooted** two-sided law, re-rooted once at the
  next return to the root, is absolutely continuous with respect to the **entrance-rooted**
  i.i.d.-cycle law (the re-rooted law differs from it only in the size-biased law of one cycle);
* clause 4 (start-vertex independence, a.c. route): the law of the path after a random time is
  absolutely continuous with respect to the law from the vertex occupied then.

Neither needs the measures to agree; ergodicity is all that has to move, and it moves along
absolute continuity, before or after one application of the invariance map.  This module
proves exactly that, for the cycle shift and for the annealed joint flow of
`RegenerativeInvarianceErgodic.JointErgodic`.

* `cycleErgodic_of_absolutelyContinuous`, `cycleErgodic_of_map_absolutelyContinuous`;
* `jointErgodic_of_absolutelyContinuous`, `jointErgodic_of_map_absolutelyContinuous`.

These are unconditional measure theory; the absolute-continuity inputs are the open clauses.
-/

set_option autoImplicit false

open MeasureTheory Filter Set

namespace ReflectedGMS.CadlagRegeneration

open ReflectedGMS.RegenerativeInvarianceFiberwise

variable {X : Type*} [MeasurableSpace X]

/-- **Cycle ergodicity passes to a law that is absolutely continuous after one cycle shift.**
This is how the vertex-rooted law inherits ergodicity from the entrance-rooted law (clause 3):
only `P.map ρ ≪ Q` is needed, never `P ≪ Q`. -/
theorem cycleErgodic_of_map_absolutelyContinuous {ρ : X → X} {P Q : Measure X}
    (hρ : Measurable ρ) (hQ : CycleErgodic Q ρ) (hac : P.map ρ ≪ Q) : CycleErgodic P ρ := by
  intro g hg hb hinv
  obtain ⟨c, hc⟩ := hQ g hg hb hinv
  refine ⟨c, ?_⟩
  have h1 : ∀ᵐ y ∂P.map ρ, g y = c := hac.ae_le hc
  have h2 : ∀ᵐ x ∂P, g (ρ x) = c := ae_of_ae_map hρ.aemeasurable h1
  filter_upwards [h2] with x hx
  rw [← hinv x]
  exact hx

end ReflectedGMS.CadlagRegeneration

end Merged_CadlagRegenerationTransfer

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.TwoSidedCycleSplice

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.RegenerativeInvarianceFiberwise

/-! ### 1. Right regularity with explicit right endpoints -/

theorem rightRegularAt_of {x : Trajectory ℕ}
    (h1 : ∀ t w, x t = some w → ∃ b, t < b ∧ ∀ s, t ≤ s → s < b → x s = some w)
    (h2 : ∀ t, x t = none → ∀ y : ℕ, ∃ b, t < b ∧ ∀ s, t < s → s < b → x s ≠ some y) :
    RightRegularAt (coord (V := ℕ)) x := by
  refine ⟨fun t ht => ?_, fun t ht y => ?_⟩
  · obtain ⟨w, hw⟩ := ht
    obtain ⟨b, htb, hb⟩ := h1 t w hw
    refine ⟨b - t, tsub_pos_of_lt htb, fun s hs => ?_⟩
    have hsb : s < b := by
      have h := hs.2
      rwa [add_tsub_cancel_of_le htb.le] at h
    show x s = x t
    rw [show x t = some w from hw]
    exact hb s hs.1 hsb
  · obtain ⟨b, htb, hb⟩ := h2 t ht y
    refine ⟨b - t, tsub_pos_of_lt htb, fun s hs => ?_⟩
    have hsb : s < b := by
      have h := hs.2
      rwa [add_tsub_cancel_of_le htb.le] at h
    exact hb s hs.1 hsb

theorem rr_some {x : Trajectory ℕ} (hx : RightRegularAt (coord (V := ℕ)) x) {t : ℝ≥0} {w : ℕ}
    (h : x t = some w) : ∃ b, t < b ∧ ∀ s, t ≤ s → s < b → x s = some w := by
  obtain ⟨ε, hε, hs⟩ := hx.1 t ⟨w, h⟩
  refine ⟨t + ε, lt_add_of_pos_right t hε, fun s h1 h2 => ?_⟩
  have h3 : x s = x t := hs s ⟨h1, h2⟩
  rw [h3, h]

theorem rr_none {x : Trajectory ℕ} (hx : RightRegularAt (coord (V := ℕ)) x) {t : ℝ≥0}
    (h : x t = none) (y : ℕ) : ∃ b, t < b ∧ ∀ s, t < s → s < b → x s ≠ some y := by
  obtain ⟨ε, hε, hs⟩ := hx.2 t h y
  exact ⟨t + ε, lt_add_of_pos_right t hε, fun s h1 h2 => hs s ⟨h1, h2⟩⟩

/-! ### 2. Left limits -/

/-- **Left limits** in the one-point compactification of the labels: every label indicator is
locally constant immediately to the left of every positive time. -/
def HasLeftLimits (x : Trajectory ℕ) : Prop :=
  ∀ (y : ℕ) (t : ℝ≥0), 0 < t → ∃ a < t,
    (∀ s ∈ Ioo a t, x s = some y) ∨ (∀ s ∈ Ioo a t, x s ≠ some y)

/-- Right regularity together with left limits. -/
structure IsRegLL (x : Trajectory ℕ) : Prop where
  regular : RightRegularAt (coord (V := ℕ)) x
  leftLimits : HasLeftLimits x

open Classical in
/-- The left limit of a trajectory at `t` (`none` when no label is attained on a left
neighbourhood). -/
noncomputable def leftLim (x : Trajectory ℕ) (t : ℝ≥0) : Option ℕ :=
  if h : ∃ y : ℕ, ∃ a < t, ∀ s ∈ Ioo a t, x s = some y then some h.choose else none

theorem leftLim_eq_some_iff {x : Trajectory ℕ} {t : ℝ≥0} {y : ℕ} :
    leftLim x t = some y ↔ ∃ a < t, ∀ s ∈ Ioo a t, x s = some y := by
  constructor
  · intro h
    unfold leftLim at h
    split_ifs at h with hex
    · have hy : hex.choose = y := Option.some_inj.1 h
      rw [← hy]
      exact hex.choose_spec
  · rintro ⟨a, hat, ha⟩
    have hex : ∃ y : ℕ, ∃ a < t, ∀ s ∈ Ioo a t, x s = some y := ⟨y, a, hat, ha⟩
    unfold leftLim
    rw [dif_pos hex]
    obtain ⟨a', hat', ha'⟩ := hex.choose_spec
    obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt hat hat')
    have h1 := ha s ⟨lt_of_le_of_lt (le_max_left _ _) hs1, hs2⟩
    have h2 := ha' s ⟨lt_of_le_of_lt (le_max_right _ _) hs1, hs2⟩
    rw [h2] at h1
    exact h1

theorem leftLim_ne_some_of {x : Trajectory ℕ} {a t : ℝ≥0} {y : ℕ} (hat : a < t)
    (h : ∀ s ∈ Ioo a t, x s ≠ some y) : leftLim x t ≠ some y := by
  intro hl
  obtain ⟨a', hat', ha'⟩ := leftLim_eq_some_iff.1 hl
  obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt hat hat')
  exact h s ⟨lt_of_le_of_lt (le_max_left _ _) hs1, hs2⟩
    (ha' s ⟨lt_of_le_of_lt (le_max_right _ _) hs1, hs2⟩)

/-- The left limit only reads a left neighbourhood. -/
theorem leftLim_congr {x x' : Trajectory ℕ} {a t : ℝ≥0} (hat : a < t)
    (h : ∀ s ∈ Ioo a t, x s = x' s) : leftLim x t = leftLim x' t := by
  refine Option.ext fun y => ?_
  rw [leftLim_eq_some_iff, leftLim_eq_some_iff]
  constructor
  · rintro ⟨a', hat', ha'⟩
    refine ⟨max a a', max_lt hat hat', fun s hs => ?_⟩
    rw [← h s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩]
    exact ha' s ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, hs.2⟩
  · rintro ⟨a', hat', ha'⟩
    refine ⟨max a a', max_lt hat hat', fun s hs => ?_⟩
    rw [h s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩]
    exact ha' s ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, hs.2⟩

theorem leftLim_Ioc_of_some {x : Trajectory ℕ} {t : ℝ≥0} {w : ℕ} (h : leftLim x t = some w) :
    ∃ a < t, ∀ r ∈ Ioc a t, leftLim x r = some w := by
  obtain ⟨a, hat, ha⟩ := leftLim_eq_some_iff.1 h
  refine ⟨a, hat, fun r hr => ?_⟩
  rcases eq_or_lt_of_le hr.2 with hrt | hrt
  · rw [hrt]; exact h
  · exact leftLim_eq_some_iff.2 ⟨a, hr.1, fun s hs => ha s ⟨hs.1, hs.2.trans hrt⟩⟩

theorem leftLim_Ioc_of_ne {x : Trajectory ℕ} (hx : HasLeftLimits x) {t : ℝ≥0} (ht : 0 < t)
    {y : ℕ} (h : leftLim x t ≠ some y) : ∃ a < t, ∀ r ∈ Ioc a t, leftLim x r ≠ some y := by
  obtain ⟨a, hat, hor⟩ := hx y t ht
  rcases hor with heq | hne
  · exact absurd (leftLim_eq_some_iff.2 ⟨a, hat, heq⟩) h
  · refine ⟨a, hat, fun r hr => ?_⟩
    rcases eq_or_lt_of_le hr.2 with hrt | hrt
    · rw [hrt]; exact h
    · exact leftLim_ne_some_of hr.1 fun s hs => hne s ⟨hs.1, hs.2.trans hrt⟩

/-- Right regularity at `r` makes the left limits just right of `r` locally constant. -/
theorem leftLim_Ioo_alt {x : Trajectory ℕ} (hx : RightRegularAt (coord (V := ℕ)) x) (r : ℝ≥0)
    (y : ℕ) : ∃ b, r < b ∧ ((∀ q ∈ Ioo r b, leftLim x q = some y) ∨
      (∀ q ∈ Ioo r b, leftLim x q ≠ some y)) := by
  rcases hxr : x r with _ | w
  · obtain ⟨b, hrb, hb⟩ := rr_none hx hxr y
    exact ⟨b, hrb, Or.inr fun q hq =>
      leftLim_ne_some_of hq.1 fun s hs => hb s hs.1 (hs.2.trans hq.2)⟩
  · obtain ⟨b, hrb, hb⟩ := rr_some hx hxr
    have hq : ∀ q ∈ Ioo r b, leftLim x q = some w := fun q hq =>
      leftLim_eq_some_iff.2 ⟨r, hq.1, fun s hs => hb s hs.1.le (hs.2.trans hq.2)⟩
    by_cases hwy : w = y
    · subst hwy
      exact ⟨b, hrb, Or.inl hq⟩
    · refine ⟨b, hrb, Or.inr fun q hq' h => hwy ?_⟩
      rw [hq q hq'] at h
      exact Option.some_inj.1 h

/-! ### 3. The cemetery, shifts, glueing and reversal -/

/-- The cemetery trajectory (constantly `∞`). -/
def cem : Trajectory ℕ := fun _ => none

theorem isRegLL_cem : IsRegLL cem where
  regular := rightRegularAt_of (fun _ _ h => by simp [cem] at h)
    (fun t _ _ => ⟨t + 1, lt_add_one t, fun _ _ _ h => by simp [cem] at h⟩)
  leftLimits := fun _ _ ht => ⟨0, ht, Or.inr fun _ _ h => by simp [cem] at h⟩

theorem hasLeftLimits_shiftBy {x : Trajectory ℕ} (hx : HasLeftLimits x) (T : ℝ≥0) :
    HasLeftLimits (shiftBy T x) := by
  intro y t ht
  obtain ⟨a, hat, hor⟩ := hx y (t + T) (lt_of_lt_of_le ht le_self_add)
  have hat' : a - T < t := by
    by_cases hTa : T ≤ a
    · exact (tsub_lt_iff_right hTa).2 hat
    · rw [tsub_eq_zero_of_le (not_le.1 hTa).le]
      exact ht
  have hmem : ∀ s ∈ Ioo (a - T) t, s + T ∈ Ioo a (t + T) := fun s hs =>
    ⟨lt_add_of_tsub_lt_right hs.1, (add_lt_add_iff_right T).2 hs.2⟩
  refine ⟨a - T, hat', ?_⟩
  rcases hor with h | h
  · exact Or.inl fun s hs => h (s + T) (hmem s hs)
  · exact Or.inr fun s hs => h (s + T) (hmem s hs)

theorem isRegLL_shiftBy {x : Trajectory ℕ} (hx : IsRegLL x) (T : ℝ≥0) :
    IsRegLL (shiftBy T x) :=
  ⟨regular_shiftBy hx.regular T, hasLeftLimits_shiftBy hx.leftLimits T⟩

/-- Glue `p` on `[0,T)` to `q` started at time `T`. -/
noncomputable def glue (p : Trajectory ℕ) (T : ℝ≥0) (q : Trajectory ℕ) : Trajectory ℕ :=
  fun s => if s < T then p s else q (s - T)

theorem glue_of_lt {p q : Trajectory ℕ} {T s : ℝ≥0} (h : s < T) : glue p T q s = p s := if_pos h

theorem glue_of_le {p q : Trajectory ℕ} {T s : ℝ≥0} (h : T ≤ s) : glue p T q s = q (s - T) :=
  if_neg (not_lt.2 h)

theorem isRegLL_glue {p q : Trajectory ℕ} (hp : IsRegLL p) (hq : IsRegLL q) (T : ℝ≥0) :
    IsRegLL (glue p T q) := by
  refine ⟨rightRegularAt_of (fun t w ht => ?_) (fun t ht y => ?_), fun y t ht => ?_⟩
  · by_cases htT : t < T
    · rw [glue_of_lt htT] at ht
      obtain ⟨b, htb, hb⟩ := rr_some hp.regular ht
      refine ⟨min b T, lt_min htb htT, fun s h1 h2 => ?_⟩
      rw [glue_of_lt (lt_of_lt_of_le h2 (min_le_right _ _))]
      exact hb s h1 (lt_of_lt_of_le h2 (min_le_left _ _))
    · have hTt : T ≤ t := not_lt.1 htT
      rw [glue_of_le hTt] at ht
      obtain ⟨b, htb, hb⟩ := rr_some hq.regular ht
      refine ⟨b + T, (tsub_lt_iff_right hTt).1 htb, fun s h1 h2 => ?_⟩
      have hTs : T ≤ s := hTt.trans h1
      rw [glue_of_le hTs]
      exact hb (s - T) (tsub_le_tsub_right h1 T) ((tsub_lt_iff_right hTs).2 h2)
  · by_cases htT : t < T
    · rw [glue_of_lt htT] at ht
      obtain ⟨b, htb, hb⟩ := rr_none hp.regular ht y
      refine ⟨min b T, lt_min htb htT, fun s h1 h2 => ?_⟩
      rw [glue_of_lt (lt_of_lt_of_le h2 (min_le_right _ _))]
      exact hb s h1 (lt_of_lt_of_le h2 (min_le_left _ _))
    · have hTt : T ≤ t := not_lt.1 htT
      rw [glue_of_le hTt] at ht
      obtain ⟨b, htb, hb⟩ := rr_none hq.regular ht y
      refine ⟨b + T, (tsub_lt_iff_right hTt).1 htb, fun s h1 h2 => ?_⟩
      have hTs : T ≤ s := hTt.trans h1.le
      rw [glue_of_le hTs]
      exact hb (s - T) ((tsub_lt_tsub_iff_right hTt).2 h1) ((tsub_lt_iff_right hTs).2 h2)
  · by_cases htT : t ≤ T
    · obtain ⟨a, hat, hor⟩ := hp.leftLimits y t ht
      refine ⟨a, hat, ?_⟩
      have hs : ∀ s ∈ Ioo a t, glue p T q s = p s := fun s hs =>
        glue_of_lt (lt_of_lt_of_le hs.2 htT)
      rcases hor with h | h
      · exact Or.inl fun s hs' => (hs s hs').trans (h s hs')
      · exact Or.inr fun s hs' => by rw [hs s hs']; exact h s hs'
    · have hTt : T < t := not_le.1 htT
      obtain ⟨a, hat, hor⟩ := hq.leftLimits y (t - T) (tsub_pos_of_lt hTt)
      refine ⟨a + T, lt_tsub_iff_right.1 hat, ?_⟩
      have hmem : ∀ s ∈ Ioo (a + T) t, glue p T q s = q (s - T) ∧ s - T ∈ Ioo a (t - T) := by
        intro s hs
        have hTs : T ≤ s := le_trans le_add_self hs.1.le
        exact ⟨glue_of_le hTs, lt_tsub_iff_right.2 hs.1, (tsub_lt_tsub_iff_right hTs).2 hs.2⟩
      rcases hor with h | h
      · exact Or.inl fun s hs => (hmem s hs).1.trans (h _ (hmem s hs).2)
      · exact Or.inr fun s hs => by rw [(hmem s hs).1]; exact h _ (hmem s hs).2

/-- The right-continuous time reversal of `x` on `[0,T)`: `u ↦ x((T − u)−)`, then `∞`. -/
noncomputable def revPiece (x : Trajectory ℕ) (T : ℝ≥0) : Trajectory ℕ :=
  fun u => if u < T then leftLim x (T - u) else none

theorem revPiece_of_lt {x : Trajectory ℕ} {T u : ℝ≥0} (h : u < T) :
    revPiece x T u = leftLim x (T - u) := if_pos h

theorem revPiece_of_le {x : Trajectory ℕ} {T u : ℝ≥0} (h : T ≤ u) : revPiece x T u = none :=
  if_neg (not_lt.2 h)

theorem tsub_lt_of_lt_add' {a b c : ℝ≥0} (hc : 0 < c) (h : a < b + c) : a - b < c := by
  by_cases hba : b ≤ a
  · exact (tsub_lt_iff_left hba).2 h
  · rw [tsub_eq_zero_of_le (not_le.1 hba).le]
    exact hc

/-- **The reversal of a regular path with left limits is again regular with left limits.** -/
theorem isRegLL_revPiece {x : Trajectory ℕ} (hx : IsRegLL x) (T : ℝ≥0) :
    IsRegLL (revPiece x T) := by
  refine ⟨rightRegularAt_of (fun u w hu => ?_) (fun u hu y => ?_), fun y t ht => ?_⟩
  · by_cases huT : u < T
    · rw [revPiece_of_lt huT] at hu
      obtain ⟨a, hat, ha⟩ := leftLim_Ioc_of_some hu
      refine ⟨T - a, lt_tsub_iff_left.2 (lt_tsub_iff_right.1 hat), fun s h1 h2 => ?_⟩
      rw [revPiece_of_lt (lt_of_lt_of_le h2 tsub_le_self)]
      exact ha (T - s) ⟨lt_tsub_iff_right.2 (lt_tsub_iff_left.1 h2), tsub_le_tsub_left h1 T⟩
    · rw [revPiece_of_le (not_lt.1 huT)] at hu
      exact absurd hu (by simp)
  · by_cases huT : u < T
    · rw [revPiece_of_lt huT] at hu
      obtain ⟨a, hat, ha⟩ := leftLim_Ioc_of_ne hx.leftLimits (tsub_pos_of_lt huT)
        (by rw [hu]; simp)
      refine ⟨T - a, lt_tsub_iff_left.2 (lt_tsub_iff_right.1 hat), fun s h1 h2 => ?_⟩
      rw [revPiece_of_lt (lt_of_lt_of_le h2 tsub_le_self)]
      exact ha (T - s) ⟨lt_tsub_iff_right.2 (lt_tsub_iff_left.1 h2), tsub_le_tsub_left h1.le T⟩
    · refine ⟨u + 1, lt_add_one u, fun s h1 _ => ?_⟩
      rw [revPiece_of_le ((not_lt.1 huT).trans h1.le)]
      simp
  · by_cases htT : t ≤ T
    · obtain ⟨b, hrb, hor⟩ := leftLim_Ioo_alt hx.regular (T - t) y
      have hTb : T - b < t := tsub_lt_of_lt_add' ht (lt_add_of_tsub_lt_right hrb)
      refine ⟨T - b, hTb, ?_⟩
      have hmem : ∀ s ∈ Ioo (T - b) t, revPiece x T s = leftLim x (T - s) ∧
          T - s ∈ Ioo (T - t) b := by
        intro s hs
        have hsT : s < T := lt_of_lt_of_le hs.2 htT
        refine ⟨revPiece_of_lt hsT, (tsub_lt_tsub_iff_left_of_le htT).2 hs.2, ?_⟩
        exact (tsub_lt_iff_left hsT.le).2 (lt_add_of_tsub_lt_right hs.1)
      rcases hor with h | h
      · exact Or.inl fun s hs => (hmem s hs).1.trans (h _ (hmem s hs).2)
      · exact Or.inr fun s hs => by rw [(hmem s hs).1]; exact h _ (hmem s hs).2
    · refine ⟨T, not_le.1 htT, Or.inr fun s hs => ?_⟩
      rw [revPiece_of_le hs.1.le]
      simp

/-! ### 4. Concatenation of a sequence of pieces -/

/-- Partial sums of the piece lengths. -/
def psum (len : ℕ → ℝ≥0) (k : ℕ) : ℝ≥0 := ∑ j ∈ Finset.range k, len j

theorem psum_zero (len : ℕ → ℝ≥0) : psum len 0 = 0 := by simp [psum]

theorem psum_succ (len : ℕ → ℝ≥0) (k : ℕ) : psum len (k + 1) = psum len k + len k :=
  Finset.sum_range_succ _ _

theorem psum_mono (len : ℕ → ℝ≥0) : Monotone (psum len) := fun _ _ hab =>
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

theorem psum_succ' (len : ℕ → ℝ≥0) (k : ℕ) :
    psum len (k + 1) = len 0 + psum (fun j => len (j + 1)) k := by
  rw [psum, Finset.sum_range_succ', add_comm]
  rfl

/-- `t` lies in the `k`-th piece. -/
def Bracket (len : ℕ → ℝ≥0) (k : ℕ) (t : ℝ≥0) : Prop := psum len k ≤ t ∧ t < psum len (k + 1)

theorem bracket_unique {len : ℕ → ℝ≥0} {k k' : ℕ} {t : ℝ≥0} (h : Bracket len k t)
    (h' : Bracket len k' t) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (lt_of_lt_of_le h.2 (psum_mono len (Nat.succ_le_of_lt hlt))) (not_lt.2 h'.1)
  · exact absurd (lt_of_lt_of_le h'.2 (psum_mono len (Nat.succ_le_of_lt hlt))) (not_lt.2 h.1)

open Classical in
/-- **Concatenation**: at time `t` the piece `k` with `S_k ≤ t < S_{k+1}`, at local time
`t − S_k`; `∞` beyond all pieces. -/
noncomputable def concat (piece : ℕ → Trajectory ℕ) (len : ℕ → ℝ≥0) : Trajectory ℕ := fun t =>
  if h : ∃ k, Bracket len k t then piece h.choose (t - psum len h.choose) else none

theorem concat_of_bracket {piece : ℕ → Trajectory ℕ} {len : ℕ → ℝ≥0} {k : ℕ} {t : ℝ≥0}
    (h : Bracket len k t) : concat piece len t = piece k (t - psum len k) := by
  have hex : ∃ k, Bracket len k t := ⟨k, h⟩
  have hk : hex.choose = k := bracket_unique hex.choose_spec h
  unfold concat
  rw [dif_pos hex, hk]

theorem concat_of_not {piece : ℕ → Trajectory ℕ} {len : ℕ → ℝ≥0} {t : ℝ≥0}
    (h : ¬ ∃ k, Bracket len k t) : concat piece len t = none := by
  unfold concat
  rw [dif_neg h]

theorem exists_bracket {len : ℕ → ℝ≥0} {t : ℝ≥0} (h : ∃ k, t < psum len k) :
    ∃ k, Bracket len k t := by
  classical
  have hm : t < psum len (Nat.find h) := Nat.find_spec h
  have hm0 : Nat.find h ≠ 0 := by
    intro h0
    rw [h0, psum_zero] at hm
    exact absurd hm (not_lt.2 (zero_le : (0 : ℝ≥0) ≤ t))
  obtain ⟨k, hk⟩ : ∃ k, Nat.find h = k + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨k, not_lt.1 (Nat.find_min h (by omega)), ?_⟩
  rw [← hk]
  exact hm

theorem exists_bracket_Ioc {len : ℕ → ℝ≥0} {t : ℝ≥0} (h0 : 0 < t) (h : ∃ k, t ≤ psum len k) :
    ∃ k, psum len k < t ∧ t ≤ psum len (k + 1) := by
  classical
  have hm : t ≤ psum len (Nat.find h) := Nat.find_spec h
  have hm0 : Nat.find h ≠ 0 := by
    intro hz
    rw [hz, psum_zero] at hm
    exact absurd h0 (not_lt.2 hm)
  obtain ⟨k, hk⟩ : ∃ k, Nat.find h = k + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨k, not_le.1 (Nat.find_min h (by omega)), ?_⟩
  rw [← hk]
  exact hm

/-- **Concatenation is the glueing of the first piece to the concatenation of the rest.** -/
theorem concat_cons (piece : ℕ → Trajectory ℕ) (len : ℕ → ℝ≥0) :
    concat piece len =
      glue (piece 0) (len 0) (concat (fun k => piece (k + 1)) (fun k => len (k + 1))) := by
  funext t
  by_cases ht : t < len 0
  · have hb : Bracket len 0 t :=
      ⟨by rw [psum_zero]; exact zero_le, by rw [psum_succ, psum_zero, zero_add]; exact ht⟩
    rw [glue_of_lt ht, concat_of_bracket hb, psum_zero, tsub_zero]
  · have h0t : len 0 ≤ t := not_lt.1 ht
    rw [glue_of_le h0t]
    have key : ∀ k, Bracket len (k + 1) t ↔ Bracket (fun j => len (j + 1)) k (t - len 0) := by
      intro k
      unfold Bracket
      rw [psum_succ' len k, psum_succ' len (k + 1), le_tsub_iff_left h0t, tsub_lt_iff_left h0t]
    by_cases hex : ∃ k, Bracket len k t
    · obtain ⟨k, hk⟩ := hex
      cases k with
      | zero => exact absurd hk.2 (by rw [psum_succ, psum_zero, zero_add]; exact ht)
      | succ k =>
        rw [concat_of_bracket hk, concat_of_bracket ((key k).1 hk), psum_succ' len k,
          tsub_add_eq_tsub_tsub]
    · rw [concat_of_not hex, concat_of_not]
      rintro ⟨k, hk⟩
      exact hex ⟨k + 1, (key k).2 hk⟩

/-- The partial sums are unbounded. -/
def Unbounded (len : ℕ → ℝ≥0) : Prop := ∀ n : ℕ, ∃ k, (n : ℝ≥0) < psum len k

theorem Unbounded.exists_gt {len : ℕ → ℝ≥0} (h : Unbounded len) (t : ℝ≥0) :
    ∃ k, t < psum len k := by
  obtain ⟨n, hn⟩ := exists_nat_gt t
  obtain ⟨k, hk⟩ := h n
  exact ⟨k, hn.trans hk⟩

theorem unbounded_succ_iff {len : ℕ → ℝ≥0} :
    Unbounded (fun k => len (k + 1)) ↔ Unbounded len := by
  constructor
  · intro h n
    obtain ⟨k, hk⟩ := h n
    refine ⟨k + 1, lt_of_lt_of_le hk ?_⟩
    rw [psum_succ' len k]
    exact le_add_self
  · intro h n
    obtain ⟨k, hk⟩ := h.exists_gt ((n : ℝ≥0) + len 0)
    cases k with
    | zero =>
      rw [psum_zero] at hk
      exact absurd hk (not_lt.2 zero_le)
    | succ k =>
      refine ⟨k, ?_⟩
      rw [psum_succ' len k, add_comm] at hk
      exact lt_of_add_lt_add_left hk

/-- **A concatenation of regular pieces with left limits and unbounded total length is regular
with left limits.** -/
theorem isRegLL_concat {piece : ℕ → Trajectory ℕ} {len : ℕ → ℝ≥0} (hp : ∀ k, IsRegLL (piece k))
    (hlen : Unbounded len) : IsRegLL (concat piece len) := by
  refine ⟨rightRegularAt_of (fun t w ht => ?_) (fun t ht y => ?_), fun y t ht => ?_⟩
  · obtain ⟨k, hk⟩ := exists_bracket (hlen.exists_gt t)
    rw [concat_of_bracket hk] at ht
    obtain ⟨b, hb1, hb2⟩ := rr_some (hp k).regular ht
    refine ⟨min (b + psum len k) (psum len (k + 1)),
      lt_min ((tsub_lt_iff_right hk.1).1 hb1) hk.2, fun s h1 h2 => ?_⟩
    have hks : Bracket len k s := ⟨hk.1.trans h1, lt_of_lt_of_le h2 (min_le_right _ _)⟩
    rw [concat_of_bracket hks]
    exact hb2 (s - psum len k) (tsub_le_tsub_right h1 _)
      ((tsub_lt_iff_right hks.1).2 (lt_of_lt_of_le h2 (min_le_left _ _)))
  · obtain ⟨k, hk⟩ := exists_bracket (hlen.exists_gt t)
    rw [concat_of_bracket hk] at ht
    obtain ⟨b, hb1, hb2⟩ := rr_none (hp k).regular ht y
    refine ⟨min (b + psum len k) (psum len (k + 1)),
      lt_min ((tsub_lt_iff_right hk.1).1 hb1) hk.2, fun s h1 h2 => ?_⟩
    have hks : Bracket len k s := ⟨hk.1.trans h1.le, lt_of_lt_of_le h2 (min_le_right _ _)⟩
    rw [concat_of_bracket hks]
    exact hb2 (s - psum len k) ((tsub_lt_tsub_iff_right hk.1).2 h1)
      ((tsub_lt_iff_right hks.1).2 (lt_of_lt_of_le h2 (min_le_left _ _)))
  · obtain ⟨k₀, hk₀⟩ := hlen.exists_gt t
    obtain ⟨k, hk1, hk2⟩ := exists_bracket_Ioc ht ⟨k₀, hk₀.le⟩
    obtain ⟨a, hat, hor⟩ := (hp k).leftLimits y (t - psum len k) (tsub_pos_of_lt hk1)
    refine ⟨a + psum len k, lt_tsub_iff_right.1 hat, ?_⟩
    have hmem : ∀ s ∈ Ioo (a + psum len k) t,
        concat piece len s = piece k (s - psum len k) ∧ s - psum len k ∈ Ioo a (t - psum len k) := by
      intro s hs
      have hks : psum len k ≤ s := le_trans le_add_self hs.1.le
      exact ⟨concat_of_bracket ⟨hks, lt_of_lt_of_le hs.2 hk2⟩, lt_tsub_iff_right.2 hs.1,
        (tsub_lt_tsub_iff_right hks).2 hs.2⟩
    rcases hor with h | h
    · exact Or.inl fun s hs => (hmem s hs).1.trans (h _ (hmem s hs).2)
    · exact Or.inr fun s hs => by rw [(hmem s hs).1]; exact h _ (hmem s hs).2

/-! ### 5. Complete cycles and the first return -/

/-- **A complete cycle from `v` of length `L`**: a regular path with left limits, killed at `L`,
that holds at `v` on `[0,h)` and is off `v` on `[h, L)` — the holding at `v` followed by the
excursion, the return to `v` happening at time `L` (in the next cycle). -/
structure IsCycle (v : ℕ) (c : Trajectory ℕ) (L : ℝ≥0) : Prop where
  start : c 0 = some v
  regLL : IsRegLL c
  killed : ∀ t, L ≤ t → c t = none
  hold : ∃ h : ℝ≥0, 0 < h ∧ h < L ∧ (∀ t, t < h → c t = some v) ∧
    ∀ t, h ≤ t → t < L → c t ≠ some v

/-- The cycle space: complete cycles from `v` with their lengths. -/
abbrev Cyc (v : ℕ) : Type := {p : Trajectory ℕ × ℝ≥0 // IsCycle v p.1 p.2}

theorem Cyc.len_pos {v : ℕ} (c : Cyc v) : 0 < c.1.2 := by
  obtain ⟨h, h0, hL, -⟩ := c.2.hold
  exact h0.trans hL

/-- The first complete return time of a path to its starting vertex (`⊤` if it starts at `∞`). -/
noncomputable def fwdReturn (x : Trajectory ℕ) : WithTop ℝ≥0 := (x 0).elim ⊤ fun v => retTime v x

theorem hittingAfter_eq {x : Trajectory ℕ} {S : Set (Option ℕ)} {n t : ℝ≥0} (hnt : n ≤ t)
    (ht : x t ∈ S) (hbefore : ∀ j, n ≤ j → j < t → x j ∉ S) :
    MeasureTheory.hittingAfter (coord (V := ℕ)) S n x = t := by
  apply le_antisymm (MeasureTheory.hittingAfter_le_of_mem hnt ht)
  by_contra hlt
  rw [not_le, MeasureTheory.hittingAfter_lt_iff] at hlt
  obtain ⟨j, hj, hjS⟩ := hlt
  exact hbefore j hj.1 hj.2 hjS

/-- **The first return of a cycle glued to a path restarting at `v` is the cycle length.** -/
theorem fwdReturn_glue {v : ℕ} {c q : Trajectory ℕ} {L : ℝ≥0} (hc : IsCycle v c L)
    (hq : q 0 = some v) : fwdReturn (glue c L q) = L := by
  obtain ⟨a, ha0, haL, hbef, haft⟩ := hc.hold
  have hxc : ∀ t, t < L → glue c L q t = c t := fun t ht => glue_of_lt ht
  have hx0 : glue c L q 0 = some v := by rw [hxc 0 (ha0.trans haL), hc.start]
  have hexit : exitAfter (coord (V := ℕ)) (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) (glue c L q)
      = a := by
    rw [exitAfter_zero_eq]
    refine hittingAfter_eq zero_le ?_ ?_
    · show glue c L q a ≠ glue c L q 0
      rw [hx0, hxc a haL]
      exact haft a le_rfl haL
    · intro j _ hja hmem
      exact hmem (show glue c L q j = glue c L q 0 by rw [hx0, hxc j (hja.trans haL)]; exact hbef j hja)
  have hret : retTime v (glue c L q) = L := by
    rw [retTime_eq, hitAfter_coe hexit]
    refine hittingAfter_eq haL.le ?_ ?_
    · show glue c L q L ∈ some '' (({v} : Finset ℕ) : Set ℕ)
      rw [glue_of_le le_rfl, tsub_self, hq]
      exact ⟨v, by simp, rfl⟩
    · intro j haj hjL hmem
      obtain ⟨w, hw, hxw⟩ := hmem
      have hwv : w = v := by simpa using hw
      have hxw' : glue c L q j = some w := hxw.symm
      rw [hxc j hjL, hwv] at hxw'
      exact haft j haj hjL hxw'
  unfold fwdReturn
  rw [hx0]
  exact hret

/-! ### 6. The regularity subtype, the splice and the re-rooting -/

/-- **The regularity subtype of the two-sided coding**: both halves right-regular with left
limits. -/
structure IsTwoSidedRegular (p : Trajectory ℕ × Trajectory ℕ) : Prop where
  fwd : IsRegLL p.1
  bwd : IsRegLL p.2

/-- The two-sided coding restricted to its regularity subtype. -/
abbrev TwoSidedReg : Type := {p : Trajectory ℕ × Trajectory ℕ // IsTwoSidedRegular p}

/-- The index of the `k`-th backward cycle, `-(k+1)`. -/
def bwdIdx (k : ℕ) : ℤ := -((k : ℤ) + 1)

theorem bwdIdx_zero_add_one : bwdIdx 0 + 1 = 0 := by
  simp [bwdIdx]

theorem bwdIdx_succ_add_one (k : ℕ) : bwdIdx (k + 1) + 1 = bwdIdx k := by
  unfold bwdIdx
  push_cast
  ring

variable {v : ℕ}

/-- Forward pieces: the cycles `ω 0, ω 1, …`. -/
def fwdPieces (ω : ℤ → Cyc v) (k : ℕ) : Trajectory ℕ := (ω k).1.1

/-- Forward lengths. -/
def fwdLens (ω : ℤ → Cyc v) (k : ℕ) : ℝ≥0 := (ω k).1.2

/-- Backward pieces: the reversed cycles `rev (ω (-1)), rev (ω (-2)), …`. -/
noncomputable def bwdPieces (ω : ℤ → Cyc v) (k : ℕ) : Trajectory ℕ :=
  revPiece (ω (bwdIdx k)).1.1 (ω (bwdIdx k)).1.2

/-- Backward lengths. -/
def bwdLens (ω : ℤ → Cyc v) (k : ℕ) : ℝ≥0 := (ω (bwdIdx k)).1.2

/-- The forward half of the splice. -/
noncomputable def fwdPath (ω : ℤ → Cyc v) : Trajectory ℕ := concat (fwdPieces ω) (fwdLens ω)

/-- The backward half of the splice (read in reversed time). -/
noncomputable def bwdPath (ω : ℤ → Cyc v) : Trajectory ℕ := concat (bwdPieces ω) (bwdLens ω)

/-- Both total lengths are infinite (a full-measure event under any i.i.d. law of cycles). -/
def GoodSeq (ω : ℤ → Cyc v) : Prop := Unbounded (fwdLens ω) ∧ Unbounded (bwdLens ω)

open Classical in
/-- The splice on the raw coding (the cemetery pair off `GoodSeq`). -/
noncomputable def spliceRaw (ω : ℤ → Cyc v) : Trajectory ℕ × Trajectory ℕ :=
  if GoodSeq ω then (fwdPath ω, bwdPath ω) else (cem, cem)

theorem isTwoSidedRegular_spliceRaw (ω : ℤ → Cyc v) : IsTwoSidedRegular (spliceRaw ω) := by
  unfold spliceRaw
  split_ifs with h
  · exact ⟨isRegLL_concat (fun k => (ω k).2.regLL) h.1,
      isRegLL_concat (fun k => isRegLL_revPiece (ω (bwdIdx k)).2.regLL _) h.2⟩
  · exact ⟨isRegLL_cem, isRegLL_cem⟩

/-- **The splice** of a two-sided cycle sequence into the regularity subtype. -/
noncomputable def splice (ω : ℤ → Cyc v) : TwoSidedReg :=
  ⟨spliceRaw ω, isTwoSidedRegular_spliceRaw ω⟩

/-- The re-rooting length: the first return of the forward half (`0` if there is none). -/
noncomputable def retLen (x : Trajectory ℕ) : ℝ≥0 := WithTop.untopD 0 (fwdReturn x)

open Classical in
/-- **The re-rooting at the first complete return of the forward half**:
`(x⁺, x⁻) ↦ (x⁺ after τ, rev (x⁺|[0,τ)) ⊕ x⁻)`; the identity when the forward half never
returns. -/
noncomputable def rhoRaw (p : Trajectory ℕ × Trajectory ℕ) : Trajectory ℕ × Trajectory ℕ :=
  if fwdReturn p.1 = ⊤ then p
  else (shiftBy (retLen p.1) p.1, glue (revPiece p.1 (retLen p.1)) (retLen p.1) p.2)

theorem isTwoSidedRegular_rhoRaw {p : Trajectory ℕ × Trajectory ℕ} (hp : IsTwoSidedRegular p) :
    IsTwoSidedRegular (rhoRaw p) := by
  unfold rhoRaw
  split_ifs
  · exact hp
  · exact ⟨isRegLL_shiftBy hp.fwd _, isRegLL_glue (isRegLL_revPiece hp.fwd _) hp.bwd _⟩

/-- **The re-rooting map `ρ` on the regularity subtype.** -/
noncomputable def rho (p : TwoSidedReg) : TwoSidedReg :=
  ⟨rhoRaw p.1, isTwoSidedRegular_rhoRaw p.2⟩

/-! ### 7. The intertwining `splice ∘ cycleShift = ρ ∘ splice` -/

theorem fwdPieces_shift (ω : ℤ → Cyc v) :
    fwdPieces (Temporal.cycleShift ω) = fun k => fwdPieces ω (k + 1) := by
  funext k
  simp [fwdPieces, Temporal.cycleShift]

theorem fwdLens_shift (ω : ℤ → Cyc v) :
    fwdLens (Temporal.cycleShift ω) = fun k => fwdLens ω (k + 1) := by
  funext k
  simp [fwdLens, Temporal.cycleShift]

theorem bwdLens_shift_succ (ω : ℤ → Cyc v) :
    (fun k => bwdLens (Temporal.cycleShift ω) (k + 1)) = bwdLens ω := by
  funext k
  simp only [bwdLens, Temporal.cycleShift, bwdIdx_succ_add_one]

theorem goodSeq_shift_iff (ω : ℤ → Cyc v) : GoodSeq (Temporal.cycleShift ω) ↔ GoodSeq ω := by
  unfold GoodSeq
  rw [fwdLens_shift, unbounded_succ_iff, ← unbounded_succ_iff (len := bwdLens _),
    bwdLens_shift_succ]

theorem fwdPath_eq_glue (ω : ℤ → Cyc v) :
    fwdPath ω = glue (ω 0).1.1 (ω 0).1.2 (fwdPath (Temporal.cycleShift ω)) := by
  simp only [fwdPath]
  rw [concat_cons, fwdPieces_shift, fwdLens_shift]
  rfl

theorem bwdPath_shift (ω : ℤ → Cyc v) :
    bwdPath (Temporal.cycleShift ω) =
      glue (revPiece (ω 0).1.1 (ω 0).1.2) (ω 0).1.2 (bwdPath ω) := by
  simp only [bwdPath]
  rw [concat_cons]
  simp only [bwdPieces, bwdLens, Temporal.cycleShift, bwdIdx_zero_add_one, bwdIdx_succ_add_one]
  rfl

theorem fwdPath_zero (ω : ℤ → Cyc v) : fwdPath ω 0 = some v := by
  rw [fwdPath_eq_glue, glue_of_lt (Cyc.len_pos _)]
  exact (ω 0).2.start

theorem fwdReturn_fwdPath (ω : ℤ → Cyc v) : fwdReturn (fwdPath ω) = (ω 0).1.2 := by
  rw [fwdPath_eq_glue]
  exact fwdReturn_glue (ω 0).2 (fwdPath_zero _)

theorem fwdReturn_cem : fwdReturn cem = ⊤ := rfl

/-- **The intertwining on the raw coding, for every cycle sequence.** -/
theorem rhoRaw_spliceRaw (ω : ℤ → Cyc v) :
    rhoRaw (spliceRaw ω) = spliceRaw (Temporal.cycleShift ω) := by
  by_cases hg : GoodSeq ω
  · have hg' : GoodSeq (Temporal.cycleShift ω) := (goodSeq_shift_iff ω).2 hg
    have hret := fwdReturn_fwdPath ω
    have hlen : retLen (fwdPath ω) = (ω 0).1.2 := by
      rw [retLen, hret]
      rfl
    have hL := Cyc.len_pos (ω 0)
    rw [spliceRaw, if_pos hg, spliceRaw, if_pos hg']
    unfold rhoRaw
    rw [if_neg (by simp only; rw [hret]; exact WithTop.coe_ne_top)]
    have e1 : shiftBy (ω 0).1.2 (fwdPath ω) = fwdPath (Temporal.cycleShift ω) := by
      funext s
      show fwdPath ω (s + (ω 0).1.2) = fwdPath (Temporal.cycleShift ω) s
      rw [fwdPath_eq_glue ω, glue_of_le le_add_self, add_tsub_cancel_right]
    have e2 : revPiece (fwdPath ω) (ω 0).1.2 = revPiece (ω 0).1.1 (ω 0).1.2 := by
      funext u
      by_cases hu : u < (ω 0).1.2
      · rw [revPiece_of_lt hu, revPiece_of_lt hu]
        refine leftLim_congr (a := 0) (tsub_pos_of_lt hu) fun s hs => ?_
        rw [fwdPath_eq_glue ω, glue_of_lt (lt_of_lt_of_le hs.2 tsub_le_self)]
      · rw [revPiece_of_le (not_lt.1 hu), revPiece_of_le (not_lt.1 hu)]
    simp only [hlen, e1, e2, bwdPath_shift]
  · have hg' : ¬ GoodSeq (Temporal.cycleShift ω) := fun h => hg ((goodSeq_shift_iff ω).1 h)
    rw [spliceRaw, if_neg hg, spliceRaw, if_neg hg']
    unfold rhoRaw
    rw [if_pos fwdReturn_cem]

/-- **`splice ∘ cycleShift = ρ ∘ splice`**, for every two-sided cycle sequence. -/
theorem rho_splice (ω : ℤ → Cyc v) : rho (splice ω) = splice (Temporal.cycleShift ω) :=
  Subtype.ext (rhoRaw_spliceRaw ω)

/-! ### 8. Measurability -/

theorem measurable_nnreal_sub {α : Type*} [MeasurableSpace α] {f g : α → ℝ≥0}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a - g a :=
  continuous_sub.measurable.comp (hf.prodMk hg)

/-- Evaluation of right-regular paths at a measurable random time. -/
theorem measurable_eval_at {α : Type*} [MeasurableSpace α] {f : α → Trajectory ℕ}
    (hf : Measurable f) (hreg : ∀ a, RightRegularAt (coord (V := ℕ)) (f a)) {T : α → ℝ≥0}
    (hT : Measurable T) : Measurable fun a => f a (T a) := by
  have hR : Measurable fun a => (⟨f a, hreg a⟩ : RegTraj ℕ) := hf.subtype_mk
  exact (measurable_regTraj_eval (V := ℕ)).comp (hR.prodMk hT)

/-- **The left limit at a measurable random time is measurable** on regular paths with left
limits: it is the eventual value along `T − 1/(n+1)`. -/
theorem measurable_leftLim_at {α : Type*} [MeasurableSpace α] {f : α → Trajectory ℕ}
    (hf : Measurable f) (hx : ∀ a, IsRegLL (f a)) {T : α → ℝ≥0} (hT : Measurable T) :
    Measurable fun a => leftLim (f a) (T a) := by
  set δ : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1) with hδ
  have hδpos : ∀ n, 0 < δ n := fun n => by rw [hδ]; positivity
  have hδanti : ∀ {m n : ℕ}, m ≤ n → δ n ≤ δ m := by
    intro m n hmn
    rw [hδ]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hev : ∀ n, Measurable fun a => f a (T a - δ n) := fun n =>
    measurable_eval_at hf (fun a => (hx a).regular) (measurable_nnreal_sub hT measurable_const)
  have key : ∀ (a : α) (y : ℕ), leftLim (f a) (T a) = some y ↔
      0 < T a ∧ ∃ N : ℕ, ∀ n, N ≤ n → f a (T a - δ n) = some y := by
    intro a y
    constructor
    · intro h
      obtain ⟨b, hbT, hb⟩ := leftLim_eq_some_iff.1 h
      have hT0 : 0 < T a := lt_of_le_of_lt zero_le hbT
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hbT)
      refine ⟨hT0, N, fun n hn => hb _ ⟨?_, tsub_lt_self hT0 (hδpos n)⟩⟩
      have h1 : δ n < T a - b := lt_of_le_of_lt (hδanti hn) hN
      exact lt_tsub_iff_right.2 (lt_tsub_iff_left.1 h1)
    · rintro ⟨hT0, N, hN⟩
      obtain ⟨b, hbT, hor⟩ := (hx a).leftLimits y (T a) hT0
      rcases hor with heq | hne
      · exact leftLim_eq_some_iff.2 ⟨b, hbT, heq⟩
      · exfalso
        obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hbT)
        set n := max N n₀
        have h1 : δ n < T a - b := lt_of_le_of_lt (hδanti (le_max_right N n₀)) hn₀
        exact hne _ ⟨lt_tsub_iff_right.2 (lt_tsub_iff_left.1 h1), tsub_lt_self hT0 (hδpos n)⟩
          (hN n (le_max_left _ _))
  have hsome : ∀ y : ℕ, MeasurableSet ((fun a => leftLim (f a) (T a)) ⁻¹' {some y}) := by
    intro y
    have hset : (fun a => leftLim (f a) (T a)) ⁻¹' {some y} = {a | 0 < T a} ∩
        ⋃ N : ℕ, ⋂ n : ℕ, {a | N ≤ n → f a (T a - δ n) = some y} := by
      ext a
      simp only [mem_preimage, mem_singleton_iff, key, mem_inter_iff, mem_setOf_eq, mem_iUnion,
        mem_iInter]
    rw [hset]
    refine (measurableSet_lt measurable_const hT).inter
      (MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => ?_)
    by_cases hNn : N ≤ n
    · simp only [hNn, true_implies]
      exact hev n (measurableSet_option {some y})
    · simp only [hNn, false_implies, setOf_true]
      exact MeasurableSet.univ
  refine measurable_to_countable' fun o => ?_
  cases o with
  | some y => exact hsome y
  | none =>
    have hset : (fun a => leftLim (f a) (T a)) ⁻¹' {none} =
        (⋃ y : ℕ, (fun a => leftLim (f a) (T a)) ⁻¹' {some y})ᶜ := by
      ext a
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, not_exists]
      constructor
      · intro h y hy
        rw [h] at hy
        exact absurd hy (by simp)
      · intro h
        cases hl : leftLim (f a) (T a) with
        | none => rfl
        | some y => exact absurd hl (h y)
    rw [hset]
    exact (MeasurableSet.iUnion hsome).compl

/-- Coordinates of a concatenation are measurable when the pieces' evaluations are. -/
theorem measurable_concat_apply {α : Type*} [MeasurableSpace α] {piece : α → ℕ → Trajectory ℕ}
    {len : α → ℕ → ℝ≥0} (hlen : ∀ k, Measurable fun a => len a k) (t : ℝ≥0)
    (hpiece : ∀ k, Measurable fun a => piece a k (t - psum (len a) k)) :
    Measurable fun a => concat (piece a) (len a) t := by
  have hps : ∀ k, Measurable fun a => psum (len a) k := fun k =>
    Finset.measurable_sum _ fun j _ => hlen j
  have hbr : ∀ k, MeasurableSet {a | Bracket (len a) k t} := fun k => by
    have h1 : MeasurableSet {a | psum (len a) k ≤ t} := measurableSet_le (hps k) measurable_const
    have h2 : MeasurableSet {a | t < psum (len a) (k + 1)} :=
      measurableSet_lt measurable_const (hps (k + 1))
    exact h1.inter h2
  refine measurable_to_countable' fun o => ?_
  have hset : (fun a => concat (piece a) (len a) t) ⁻¹' {o} =
      (⋃ k, {a | Bracket (len a) k t} ∩ (fun a => piece a k (t - psum (len a) k)) ⁻¹' {o}) ∪
        ((⋃ k, {a | Bracket (len a) k t})ᶜ ∩ {_a | (none : Option ℕ) = o}) := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_iUnion, mem_inter_iff,
      mem_setOf_eq, mem_compl_iff, not_exists]
    constructor
    · intro h
      by_cases hex : ∃ k, Bracket (len a) k t
      · obtain ⟨k, hk⟩ := hex
        exact Or.inl ⟨k, hk, by rw [← concat_of_bracket (piece := piece a) hk]; exact h⟩
      · exact Or.inr ⟨fun k hk => hex ⟨k, hk⟩,
          by rw [← concat_of_not (piece := piece a) hex]; exact h⟩
    · rintro (⟨k, hk, h⟩ | ⟨hex, h⟩)
      · rw [concat_of_bracket hk]; exact h
      · rw [concat_of_not fun ⟨k, hk⟩ => hex k hk]; exact h
  rw [hset]
  exact (MeasurableSet.iUnion fun k => (hbr k).inter (hpiece k (measurableSet_option _))).union
    ((MeasurableSet.iUnion hbr).compl.inter (MeasurableSet.const _))

theorem measurable_cyc_len (j : ℤ) : Measurable fun ω : ℤ → Cyc v => (ω j).1.2 :=
  (measurable_snd.comp measurable_subtype_coe).comp (measurable_pi_apply j)

theorem measurable_cyc_path (j : ℤ) : Measurable fun ω : ℤ → Cyc v => (ω j).1.1 :=
  (measurable_fst.comp measurable_subtype_coe).comp (measurable_pi_apply j)

theorem measurable_cyc_eval (j : ℤ) {T : (ℤ → Cyc v) → ℝ≥0} (hT : Measurable T) :
    Measurable fun ω : ℤ → Cyc v => (ω j).1.1 (T ω) :=
  measurable_eval_at (measurable_cyc_path j) (fun ω => (ω j).2.regLL.regular) hT

theorem measurable_cyc_rev (j : ℤ) {T : (ℤ → Cyc v) → ℝ≥0} (hT : Measurable T) :
    Measurable fun ω : ℤ → Cyc v => revPiece (ω j).1.1 (ω j).1.2 (T ω) := by
  show Measurable fun ω : ℤ → Cyc v =>
    if T ω < (ω j).1.2 then leftLim (ω j).1.1 ((ω j).1.2 - T ω) else none
  exact Measurable.ite (measurableSet_lt hT (measurable_cyc_len j))
    (measurable_leftLim_at (measurable_cyc_path j) (fun ω => (ω j).2.regLL)
      (measurable_nnreal_sub (measurable_cyc_len j) hT)) measurable_const

theorem measurableSet_unbounded {α : Type*} [MeasurableSpace α] {len : α → ℕ → ℝ≥0}
    (hlen : ∀ k, Measurable fun a => len a k) : MeasurableSet {a | Unbounded (len a)} := by
  have hps : ∀ k, Measurable fun a => psum (len a) k := fun k =>
    Finset.measurable_sum _ fun j _ => hlen j
  have hset : {a | Unbounded (len a)} = ⋂ n : ℕ, ⋃ k : ℕ, {a | (n : ℝ≥0) < psum (len a) k} := by
    ext a
    simp [Unbounded]
  rw [hset]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k =>
    measurableSet_lt measurable_const (hps k)

theorem measurableSet_goodSeq : MeasurableSet {ω : ℤ → Cyc v | GoodSeq ω} :=
  (measurableSet_unbounded (len := fwdLens) fun k => measurable_cyc_len _).inter
    (measurableSet_unbounded (len := bwdLens) fun k => measurable_cyc_len _)

theorem measurable_fwdPath : Measurable (fwdPath (v := v)) := by
  refine measurable_pi_iff.2 fun t => ?_
  have hps : ∀ k, Measurable fun ω : ℤ → Cyc v => psum (fwdLens ω) k := fun k =>
    Finset.measurable_sum _ fun j _ => measurable_cyc_len _
  exact measurable_concat_apply (piece := fwdPieces) (len := fwdLens)
    (fun k => measurable_cyc_len _) t
    (fun k => measurable_cyc_eval _ (measurable_nnreal_sub measurable_const (hps k)))

theorem measurable_bwdPath : Measurable (bwdPath (v := v)) := by
  refine measurable_pi_iff.2 fun t => ?_
  have hps : ∀ k, Measurable fun ω : ℤ → Cyc v => psum (bwdLens ω) k := fun k =>
    Finset.measurable_sum _ fun j _ => measurable_cyc_len _
  exact measurable_concat_apply (piece := bwdPieces) (len := bwdLens)
    (fun k => measurable_cyc_len _) t
    (fun k => measurable_cyc_rev _ (measurable_nnreal_sub measurable_const (hps k)))

theorem measurable_spliceRaw : Measurable (spliceRaw (v := v)) := by
  classical
  have h : Measurable fun ω : ℤ → Cyc v =>
      if ω ∈ {ω : ℤ → Cyc v | GoodSeq ω} then (fwdPath ω, bwdPath ω) else (cem, cem) :=
    Measurable.ite measurableSet_goodSeq (measurable_fwdPath.prodMk measurable_bwdPath)
      measurable_const
  exact h

/-- **The splice is measurable.** -/
theorem measurable_splice : Measurable (splice (v := v)) :=
  measurable_spliceRaw.subtype_mk

/-- The first return of the forward half is measurable on the regularity subtype (dense hitting
times, start vertex by start vertex). -/
theorem measurable_fwdReturn : Measurable fun p : TwoSidedReg => fwdReturn p.1.1 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let Xs : ℝ≥0 → TwoSidedReg → Option ℕ := fun t p => p.1.1 t
  have hXm : ∀ t, Measurable (Xs t) := fun t =>
    (measurable_pi_apply t).comp (measurable_fst.comp measurable_subtype_coe)
  let R : ℕ → TwoSidedReg → WithTop ℝ≥0 := fun w =>
    denseHitAfter Xs (some '' (({w} : Finset ℕ) : Set ℕ))
      (denseHitAfter Xs {s : Option ℕ | s ≠ some w} (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) D) D
  have hR : ∀ w, Measurable (R w) := fun w =>
    measurable_denseHitAfter hXm (measurable_denseHitAfter hXm measurable_const hDc) hDc
  have heq : ∀ p : TwoSidedReg, fwdReturn p.1.1 = (p.1.1 0).elim ⊤ fun w => R w p := by
    intro p
    cases h0 : p.1.1 0 with
    | none =>
      unfold fwdReturn
      rw [h0]
      rfl
    | some w =>
      unfold fwdReturn
      rw [h0]
      show retTime w p.1.1 = R w p
      have hreg : RightRegularAt Xs p := p.2.fwd.regular
      have hexit : exitAfter Xs (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) p =
          denseHitAfter Xs {s : Option ℕ | s ≠ some w} (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) D p := by
        have h1 : exitAfter Xs (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) p =
            hitAfter Xs {s : Option ℕ | s ≠ some w} (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) p := by
          show hitAfter Xs {s : Option ℕ | s ≠ p.1.1 0}
            (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) p = _
          rw [h0]
        rw [h1]
        exact hitAfter_eq_denseHitAfter_of_rightRegular hreg (admissibleTarget_ne w) rfl hDd
      show hitAfter Xs (some '' (({w} : Finset ℕ) : Set ℕ))
        (exitAfter Xs (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0))) p = _
      exact hitAfter_eq_denseHitAfter_of_rightRegular hreg (admissibleTarget_image {w}) hexit hDd
  haveI : MeasurableSingletonClass (Option ℕ) := ⟨fun _ => measurableSet_option _⟩
  have hG : Measurable fun q : TwoSidedReg × Option ℕ => q.2.elim ⊤ fun w => R w q.1 := by
    refine measurable_from_prod_countable_left fun o => ?_
    cases o with
    | none => exact measurable_const
    | some w => exact hR w
  have hfun : (fun p : TwoSidedReg => fwdReturn p.1.1) =
      (fun q : TwoSidedReg × Option ℕ => q.2.elim ⊤ fun w => R w q.1) ∘ fun p => (p, Xs 0 p) :=
    funext heq
  rw [hfun]
  exact hG.comp (measurable_id.prodMk (hXm 0))

theorem measurable_retLen : Measurable fun p : TwoSidedReg => retLen p.1.1 :=
  ENNReal.measurable_toNNReal.comp measurable_fwdReturn

theorem measurable_rhoRaw : Measurable fun p : TwoSidedReg => rhoRaw p.1 := by
  classical
  have hT := measurable_retLen
  have hfwd : Measurable fun p : TwoSidedReg => p.1.1 := measurable_fst.comp measurable_subtype_coe
  have hbwd : Measurable fun p : TwoSidedReg => p.1.2 := measurable_snd.comp measurable_subtype_coe
  have h1 : Measurable fun p : TwoSidedReg => shiftBy (retLen p.1.1) p.1.1 :=
    measurable_pi_iff.2 fun s =>
      measurable_eval_at hfwd (fun p => p.2.fwd.regular) (measurable_const.add hT)
  have h2 : Measurable fun p : TwoSidedReg =>
      glue (revPiece p.1.1 (retLen p.1.1)) (retLen p.1.1) p.1.2 := by
    refine measurable_pi_iff.2 fun s => ?_
    show Measurable fun p : TwoSidedReg => if s < retLen p.1.1 then
      (if s < retLen p.1.1 then leftLim p.1.1 (retLen p.1.1 - s) else none)
      else p.1.2 (s - retLen p.1.1)
    exact Measurable.ite (measurableSet_lt measurable_const hT)
      (Measurable.ite (measurableSet_lt measurable_const hT)
        (measurable_leftLim_at hfwd (fun p => p.2.fwd) (measurable_nnreal_sub hT measurable_const))
        measurable_const)
      (measurable_eval_at hbwd (fun p => p.2.bwd.regular) (measurable_nnreal_sub measurable_const hT))
  have h : Measurable fun p : TwoSidedReg =>
      if p ∈ (fun p : TwoSidedReg => fwdReturn p.1.1) ⁻¹' {⊤} then p.1
      else (shiftBy (retLen p.1.1) p.1.1, glue (revPiece p.1.1 (retLen p.1.1)) (retLen p.1.1) p.1.2) :=
    Measurable.ite (measurable_fwdReturn (measurableSet_singleton ⊤)) measurable_subtype_coe
      (h1.prodMk h2)
  have heq : (fun p : TwoSidedReg => rhoRaw p.1) = fun p : TwoSidedReg =>
      if p ∈ (fun p : TwoSidedReg => fwdReturn p.1.1) ⁻¹' {⊤} then p.1
      else (shiftBy (retLen p.1.1) p.1.1,
        glue (revPiece p.1.1 (retLen p.1.1)) (retLen p.1.1) p.1.2) := by
    funext p
    unfold rhoRaw
    by_cases hp : fwdReturn p.1.1 = ⊤
    · rw [if_pos hp, if_pos (show p ∈ (fun p : TwoSidedReg => fwdReturn p.1.1) ⁻¹' {⊤} from hp)]
    · rw [if_neg hp, if_neg (show p ∉ (fun p : TwoSidedReg => fwdReturn p.1.1) ⁻¹' {⊤} from hp)]
  rw [heq]
  exact h

/-- **`ρ` is measurable.** -/
theorem measurable_rho : Measurable rho :=
  measurable_rhoRaw.subtype_mk

/-! ### 9. Cycle ergodicity of the entrance-rooted i.i.d.-cycle law -/

/-- **The entrance-rooted i.i.d.-cycle law**: the splice of a two-sided i.i.d. sequence of
complete cycles with cycle law `ν`. -/
noncomputable def entranceLaw (ν : Measure (Cyc v)) : Measure TwoSidedReg :=
  (Temporal.iidCycleLaw ν).map splice

/-- **Milestone 2(a): the entrance-rooted i.i.d.-cycle law is ergodic under `ρ`**, for every
probability law `ν` of complete cycles.  Two-sided Bernoulli ergodicity
(`BernoulliCycleInvariant.ae_eq_const_of_cycleShift_invariant`) pulled back along the
intertwining `rho_splice`. -/
theorem cycleErgodic_entranceLaw (ν : Measure (Cyc v)) [IsProbabilityMeasure ν] :
    CycleErgodic (entranceLaw ν) rho := by
  intro g hg _ hinv
  obtain ⟨c, hc⟩ := Temporal.ae_eq_const_of_cycleShift_invariant ν (hg.comp measurable_splice)
    (fun ω => by
      show g (splice (Temporal.cycleShift ω)) = g (splice ω)
      rw [← rho_splice, hinv])
  refine ⟨c, ?_⟩
  rw [entranceLaw, ae_map_iff measurable_splice.aemeasurable
    (measurableSet_eq_fun hg measurable_const)]
  exact hc

end ReflectedGMS.TwoSidedCycleSplice
