/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.PsiBundle at commit 31e7483; only the module paths of local imports are changed.
   v4.35 port: replace deprecated if-then-else lemmas.
   v4.35 port: use simp where simpa closes the goal. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCoord
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTSideCond

/-!
# The Peanosphere data and the sheared strip map

This is the intermediate interface for the strip construction in TF3, Route M. It is not
a frozen theorem hypothesis: the SLE/mating-of-trees layer is responsible for producing a
bundle satisfying these deterministic properties.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology unitInterval

namespace MatedCRTHarmonic.RouteM

variable {ω : MatedCRT.Path2} {η : ℝ → ℂ}

/-- A direct L- or R-identification of two times. -/
def directRel (X : ℝ → ℝ) (s t : ℝ) : Prop :=
  s < t ∧ X s = X t ∧ ∀ u ∈ Ioo s t, X s < X u

/-- The deterministic Peanosphere bundle from TF2 Details (a): the area-parametrized
space-filling curve, its two continuous boundary-length coordinates, the direct merge rule,
the converse strip relation of DMS Lemma 8.14, Brownian lower excursions at both ends, and
distinct local-minimum values. -/
structure Peanosphere (ω : MatedCRT.Path2) (η : ℝ → ℂ) : Prop where
  cont : Continuous η
  surj : Function.Surjective η
  transient : Filter.Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ)
  merge : ∀ s t,
    (directRel (fun u => (ω u).1) s t ∨ directRel (fun u => (ω u).2) s t) → η s = η t
  onlyMerge : ∀ s t, η s = η t →
    Relation.EqvGen
      (fun a b => directRel (fun u => (ω u).1) a b ∨ directRel (fun u => (ω u).2) a b) s t
  liminf_L : ∀ M T : ℝ,
    (∃ t ≥ T, (ω t).1 < M) ∧ (∃ t ≤ -T, (ω t).1 < M)
  liminf_R : ∀ M T : ℝ,
    (∃ t ≥ T, (ω t).2 < M) ∧ (∃ t ≤ -T, (ω t).2 < M)
  locMinDistinct : ∀ i : Fin 2, ∀ a b, a ≠ b →
    IsLocalMin (MatedCRT.lrCoord i · ω) a → IsLocalMin (MatedCRT.lrCoord i · ω) b →
    MatedCRT.lrCoord i a ω ≠ MatedCRT.lrCoord i b ω

/-- The strict form of the side condition (1.1) of [18], used to choose distinct chord heights. -/
def SideStrict (ε : ℝ) (ω : MatedCRT.Path2) : Prop :=
  ∀ (b : Bool) (x y : ℤ), x + 1 < y →
    MatedCRT.SideCond ε (fun t => if b then (ω t).2 else (ω t).1) x y →
    max
        (MatedCRT.intervalInf (fun t => if b then (ω t).2 else (ω t).1)
          (ε * ((x : ℝ) - 1)) (ε * x))
        (MatedCRT.intervalInf (fun t => if b then (ω t).2 else (ω t).1)
          (ε * ((y : ℝ) - 1)) (ε * y))
      < MatedCRT.intervalInf (fun t => if b then (ω t).2 else (ω t).1)
          (ε * x) (ε * ((y : ℝ) - 1))

def lCoord (ω : MatedCRT.Path2) (t : ℝ) : ℝ := (ω t).1
def rCoord (ω : MatedCRT.Path2) (t : ℝ) : ℝ := (ω t).2

@[fun_prop] theorem continuous_lCoord : Continuous (lCoord ω) :=
  continuous_fst.comp ω.continuous

@[fun_prop] theorem continuous_rCoord : Continuous (rCoord ω) :=
  continuous_snd.comp ω.continuous

/-- The last time no later than `t` at which the L-coordinate is at most `λ`. -/
noncomputable def ellMinus (ω : MatedCRT.Path2) (t level : ℝ) : ℝ :=
  sSup {s | s ≤ t ∧ lCoord ω s ≤ level}

/-- The first time no earlier than `t` at which the L-coordinate is at most `λ`. -/
noncomputable def ellPlus (ω : MatedCRT.Path2) (t level : ℝ) : ℝ :=
  sInf {s | t ≤ s ∧ lCoord ω s ≤ level}

/-- The last time no later than `t` at which the R-coordinate is at most `λ`. -/
noncomputable def rhoMinus (ω : MatedCRT.Path2) (t level : ℝ) : ℝ :=
  sSup {s | s ≤ t ∧ rCoord ω s ≤ level}

/-- The first time no earlier than `t` at which the R-coordinate is at most `λ`. -/
noncomputable def rhoPlus (ω : MatedCRT.Path2) (t level : ℝ) : ℝ :=
  sInf {s | t ≤ s ∧ rCoord ω s ≤ level}

/-- The last L-contact exists and lies at or below the target level. -/
theorem ellMinus_mem (P : Peanosphere ω η) (t level : ℝ) :
    ellMinus ω t level ≤ t ∧ lCoord ω (ellMinus ω t level) ≤ level := by
  let A : Set ℝ := {s | s ≤ t ∧ lCoord ω s ≤ level}
  have hnonempty : A.Nonempty := by
    obtain ⟨s, hs, hLs⟩ := (P.liminf_L level |t|).2
    refine ⟨s, ?_⟩
    exact ⟨le_trans hs (neg_abs_le t), hLs.le⟩
  have hbounded : BddAbove A := ⟨t, fun s hs => hs.1⟩
  have hclosed : IsClosed A := by
    change IsClosed {s : ℝ | s ≤ t ∧ lCoord ω s ≤ level}
    exact (isClosed_Iic.preimage continuous_id).inter
      (isClosed_Iic.preimage continuous_lCoord)
  have hmax : ellMinus ω t level ∈ A := by
    exact hclosed.csSup_mem hnonempty hbounded
  exact hmax

/-- At a level strictly below `L_t`, the last L-contact is exactly at that level. -/
theorem ellMinus_level (P : Peanosphere ω η) {t level : ℝ}
    (hlevel : level < lCoord ω t) :
    lCoord ω (ellMinus ω t level) = level := by
  have hmax := ellMinus_mem P t level
  have hst : ellMinus ω t level < t := by
    apply lt_of_le_of_ne hmax.1
    intro heq
    rw [heq] at hmax
    exact (not_le_of_gt hlevel) hmax.2
  by_contra hne
  have hlt : lCoord ω (ellMinus ω t level) < level := lt_of_le_of_ne hmax.2 hne
  have hopen : IsOpen {s : ℝ | lCoord ω s < level} :=
    isOpen_Iio.preimage continuous_lCoord
  have hnhds : {s : ℝ | lCoord ω s < level} ∈ 𝓝 (ellMinus ω t level) :=
    hopen.mem_nhds hlt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let d : ℝ := min ε (t - ellMinus ω t level) / 2
  let s : ℝ := ellMinus ω t level + d
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hdeps : d < ε := by
    dsimp [d]
    linarith [min_le_left ε (t - ellMinus ω t level)]
  have hdst : d < t - ellMinus ω t level := by
    dsimp [d]
    linarith [min_le_right ε (t - ellMinus ω t level)]
  have hsball : s ∈ Metric.ball (ellMinus ω t level) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [s]
    rw [add_sub_cancel_left]
    rw [abs_of_pos hdpos]
    exact hdeps
  have hslevel : lCoord ω s < level := hball hsball
  have hsA : s ∈ {x | x ≤ t ∧ lCoord ω x ≤ level} := by
    exact ⟨by dsimp [s]; linarith, hslevel.le⟩
  have hsupper := le_csSup (show BddAbove {x : ℝ | x ≤ t ∧ lCoord ω x ≤ level} from
    ⟨t, fun x hx => hx.1⟩) hsA
  change s ≤ ellMinus ω t level at hsupper
  dsimp [s] at hsupper
  linarith

/-- The last R-contact version of `ellMinus_mem`. -/
theorem rhoMinus_mem (P : Peanosphere ω η) (t level : ℝ) :
    rhoMinus ω t level ≤ t ∧ rCoord ω (rhoMinus ω t level) ≤ level := by
  let A : Set ℝ := {s | s ≤ t ∧ rCoord ω s ≤ level}
  have hnonempty : A.Nonempty := by
    obtain ⟨s, hs, hRs⟩ := (P.liminf_R level |t|).2
    refine ⟨s, ?_⟩
    exact ⟨le_trans hs (neg_abs_le t), hRs.le⟩
  have hbounded : BddAbove A := ⟨t, fun s hs => hs.1⟩
  have hclosed : IsClosed A := by
    change IsClosed {s : ℝ | s ≤ t ∧ rCoord ω s ≤ level}
    exact (isClosed_Iic.preimage continuous_id).inter
      (isClosed_Iic.preimage continuous_rCoord)
  have hmax : rhoMinus ω t level ∈ A := by
    exact hclosed.csSup_mem hnonempty hbounded
  exact hmax

/-- At a level strictly below `R_t`, the last R-contact is exactly at that level. -/
theorem rhoMinus_level (P : Peanosphere ω η) {t level : ℝ}
    (hlevel : level < rCoord ω t) :
    rCoord ω (rhoMinus ω t level) = level := by
  have hmax := rhoMinus_mem P t level
  have hst : rhoMinus ω t level < t := by
    apply lt_of_le_of_ne hmax.1
    intro heq
    rw [heq] at hmax
    exact (not_le_of_gt hlevel) hmax.2
  by_contra hne
  have hlt : rCoord ω (rhoMinus ω t level) < level := lt_of_le_of_ne hmax.2 hne
  have hopen : IsOpen {s : ℝ | rCoord ω s < level} :=
    isOpen_Iio.preimage continuous_rCoord
  have hnhds : {s : ℝ | rCoord ω s < level} ∈ 𝓝 (rhoMinus ω t level) :=
    hopen.mem_nhds hlt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let d : ℝ := min ε (t - rhoMinus ω t level) / 2
  let s : ℝ := rhoMinus ω t level + d
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hdeps : d < ε := by
    dsimp [d]
    linarith [min_le_left ε (t - rhoMinus ω t level)]
  have hdst : d < t - rhoMinus ω t level := by
    dsimp [d]
    linarith [min_le_right ε (t - rhoMinus ω t level)]
  have hsball : s ∈ Metric.ball (rhoMinus ω t level) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [s]
    rw [add_sub_cancel_left]
    rw [abs_of_pos hdpos]
    exact hdeps
  have hslevel : rCoord ω s < level := hball hsball
  have hsA : s ∈ {x | x ≤ t ∧ rCoord ω x ≤ level} := by
    exact ⟨by dsimp [s]; linarith, hslevel.le⟩
  have hsupper := le_csSup (show BddAbove {x : ℝ | x ≤ t ∧ rCoord ω x ≤ level} from
    ⟨t, fun x hx => hx.1⟩) hsA
  change s ≤ rhoMinus ω t level at hsupper
  dsimp [s] at hsupper
  linarith

/-- The first L-contact exists and lies at or after the target time. -/
theorem ellPlus_mem (P : Peanosphere ω η) (t level : ℝ) :
    t ≤ ellPlus ω t level ∧ lCoord ω (ellPlus ω t level) ≤ level := by
  let A : Set ℝ := {s | t ≤ s ∧ lCoord ω s ≤ level}
  have hnonempty : A.Nonempty := by
    obtain ⟨s, hs, hLs⟩ := (P.liminf_L level |t|).1
    refine ⟨s, ?_⟩
    exact ⟨le_trans (le_abs_self t) hs, hLs.le⟩
  have hbounded : BddBelow A := ⟨t, fun s hs => hs.1⟩
  have hclosed : IsClosed A := by
    change IsClosed {s : ℝ | t ≤ s ∧ lCoord ω s ≤ level}
    exact (isClosed_Ici.preimage continuous_id).inter
      (isClosed_Iic.preimage continuous_lCoord)
  have hmin : ellPlus ω t level ∈ A := by
    exact hclosed.csInf_mem hnonempty hbounded
  exact hmin

/-- At a level strictly below `L_t`, the first L-contact to the right is exactly at that level. -/
theorem ellPlus_level (P : Peanosphere ω η) {t level : ℝ}
    (hlevel : level < lCoord ω t) :
    lCoord ω (ellPlus ω t level) = level := by
  have hmin := ellPlus_mem P t level
  have hst : t < ellPlus ω t level := by
    apply lt_of_le_of_ne hmin.1
    intro heq
    rw [← heq] at hmin
    exact (not_le_of_gt hlevel) hmin.2
  by_contra hne
  have hlt : lCoord ω (ellPlus ω t level) < level := lt_of_le_of_ne hmin.2 hne
  have hopen : IsOpen {s : ℝ | lCoord ω s < level} :=
    isOpen_Iio.preimage continuous_lCoord
  have hnhds : {s : ℝ | lCoord ω s < level} ∈ 𝓝 (ellPlus ω t level) :=
    hopen.mem_nhds hlt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let d : ℝ := min ε (ellPlus ω t level - t) / 2
  let s : ℝ := ellPlus ω t level - d
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hdeps : d < ε := by
    dsimp [d]
    linarith [min_le_left ε (ellPlus ω t level - t)]
  have hdst : d < ellPlus ω t level - t := by
    dsimp [d]
    linarith [min_le_right ε (ellPlus ω t level - t)]
  have hsball : s ∈ Metric.ball (ellPlus ω t level) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [s]
    rw [sub_sub_cancel_left]
    rw [abs_of_neg (by linarith)]
    linarith
  have hslevel : lCoord ω s < level := hball hsball
  have hsA : s ∈ {x | t ≤ x ∧ lCoord ω x ≤ level} := by
    exact ⟨by dsimp [s]; linarith, hslevel.le⟩
  have hslower := csInf_le
    (show BddBelow {x : ℝ | t ≤ x ∧ lCoord ω x ≤ level} from
      ⟨t, fun x hx => hx.1⟩) hsA
  change ellPlus ω t level ≤ s at hslower
  dsimp [s] at hslower
  linarith

/-- The first R-contact exists and lies at or after the target time. -/
theorem rhoPlus_mem (P : Peanosphere ω η) (t level : ℝ) :
    t ≤ rhoPlus ω t level ∧ rCoord ω (rhoPlus ω t level) ≤ level := by
  let A : Set ℝ := {s | t ≤ s ∧ rCoord ω s ≤ level}
  have hnonempty : A.Nonempty := by
    obtain ⟨s, hs, hRs⟩ := (P.liminf_R level |t|).1
    refine ⟨s, ?_⟩
    exact ⟨le_trans (le_abs_self t) hs, hRs.le⟩
  have hbounded : BddBelow A := ⟨t, fun s hs => hs.1⟩
  have hclosed : IsClosed A := by
    change IsClosed {s : ℝ | t ≤ s ∧ rCoord ω s ≤ level}
    exact (isClosed_Ici.preimage continuous_id).inter
      (isClosed_Iic.preimage continuous_rCoord)
  have hmin : rhoPlus ω t level ∈ A := by
    exact hclosed.csInf_mem hnonempty hbounded
  exact hmin

/-- At a level strictly below `R_t`, the first R-contact to the right is exactly at that level. -/
theorem rhoPlus_level (P : Peanosphere ω η) {t level : ℝ}
    (hlevel : level < rCoord ω t) :
    rCoord ω (rhoPlus ω t level) = level := by
  have hmin := rhoPlus_mem P t level
  have hst : t < rhoPlus ω t level := by
    apply lt_of_le_of_ne hmin.1
    intro heq
    rw [← heq] at hmin
    exact (not_le_of_gt hlevel) hmin.2
  by_contra hne
  have hlt : rCoord ω (rhoPlus ω t level) < level := lt_of_le_of_ne hmin.2 hne
  have hopen : IsOpen {s : ℝ | rCoord ω s < level} :=
    isOpen_Iio.preimage continuous_rCoord
  have hnhds : {s : ℝ | rCoord ω s < level} ∈ 𝓝 (rhoPlus ω t level) :=
    hopen.mem_nhds hlt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let d : ℝ := min ε (rhoPlus ω t level - t) / 2
  let s : ℝ := rhoPlus ω t level - d
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hdeps : d < ε := by
    dsimp [d]
    linarith [min_le_left ε (rhoPlus ω t level - t)]
  have hdst : d < rhoPlus ω t level - t := by
    dsimp [d]
    linarith [min_le_right ε (rhoPlus ω t level - t)]
  have hsball : s ∈ Metric.ball (rhoPlus ω t level) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [s]
    rw [sub_sub_cancel_left]
    rw [abs_of_neg (by linarith)]
    linarith
  have hslevel : rCoord ω s < level := hball hsball
  have hsA : s ∈ {x | t ≤ x ∧ rCoord ω x ≤ level} := by
    exact ⟨by dsimp [s]; linarith, hslevel.le⟩
  have hslower := csInf_le
    (show BddBelow {x : ℝ | t ≤ x ∧ rCoord ω x ≤ level} from
      ⟨t, fun x hx => hx.1⟩) hsA
  change rhoPlus ω t level ≤ s at hslower
  dsimp [s] at hslower
  linarith

/-- Within the strict interior of an L-level chord, every vertical slice uses its left endpoint. -/
theorem ellMinus_eq_left_of_above (a b level : ℝ) (hlevel : lCoord ω a = level)
    (habove : ∀ v ∈ Ioo a b, level < lCoord ω v) {u : ℝ}
    (hau : a ≤ u) (hub : u < b) : ellMinus ω u level = a := by
  have hmem : a ∈ {s | s ≤ u ∧ lCoord ω s ≤ level} := by
    exact ⟨hau, by simp [hlevel]⟩
  have hupper : ∀ s ∈ {s | s ≤ u ∧ lCoord ω s ≤ level}, s ≤ a := by
    intro s hs
    by_contra hsa
    have has : a < s := lt_of_not_ge hsa
    have hsb : s < b := lt_of_le_of_lt hs.1 hub
    have hle : lCoord ω s ≤ lCoord ω a := hs.2.trans_eq hlevel.symm
    have hlt : lCoord ω a < lCoord ω s := by simpa [hlevel] using habove s ⟨has, hsb⟩
    exact (not_lt_of_ge hle) hlt
  apply le_antisymm
  · exact csSup_le ⟨a, hmem⟩ hupper
  · exact le_csSup ⟨u, fun s hs => hs.1⟩ hmem

/-- The upper-coordinate counterpart of `ellMinus_eq_left_of_above`. -/
theorem rhoMinus_eq_left_of_above (a b level : ℝ) (hlevel : rCoord ω a = level)
    (habove : ∀ v ∈ Ioo a b, level < rCoord ω v) {u : ℝ}
    (hau : a ≤ u) (hub : u < b) : rhoMinus ω u level = a := by
  have hmem : a ∈ {s | s ≤ u ∧ rCoord ω s ≤ level} := by
    exact ⟨hau, by simp [hlevel]⟩
  have hupper : ∀ s ∈ {s | s ≤ u ∧ rCoord ω s ≤ level}, s ≤ a := by
    intro s hs
    by_contra hsa
    have has : a < s := lt_of_not_ge hsa
    have hsb : s < b := lt_of_le_of_lt hs.1 hub
    have hle : rCoord ω s ≤ rCoord ω a := hs.2.trans_eq hlevel.symm
    have hlt : rCoord ω a < rCoord ω s := by simpa [hlevel] using habove s ⟨has, hsb⟩
    exact (not_lt_of_ge hle) hlt
  apply le_antisymm
  · exact csSup_le ⟨a, hmem⟩ hupper
  · exact le_csSup ⟨u, fun s hs => hs.1⟩ hmem

/-- Restricting a last-contact supremum to an earlier subinterval does not change it. -/
theorem ellMinus_eq_on_left_interval (P : Peanosphere ω η) {t level s u : ℝ}
    (hs : ellMinus ω t level = s) (hsu : s ≤ u) (hut : u ≤ t) :
    ellMinus ω u level = s := by
  have hglobal := ellMinus_mem P t level
  rw [hs] at hglobal
  have hmem : s ∈ {x | x ≤ u ∧ lCoord ω x ≤ level} := ⟨hsu, hglobal.2⟩
  have hupper : ∀ x ∈ {x | x ≤ u ∧ lCoord ω x ≤ level}, x ≤ s := by
    intro x hx
    have hxglobal : x ∈ {x | x ≤ t ∧ lCoord ω x ≤ level} := ⟨le_trans hx.1 hut, hx.2⟩
    have hxle : x ≤ ellMinus ω t level :=
      le_csSup (show BddAbove {x : ℝ | x ≤ t ∧ lCoord ω x ≤ level} from
        ⟨t, fun x hx => hx.1⟩) hxglobal
    simpa [hs] using hxle
  apply le_antisymm
  · exact csSup_le ⟨s, hmem⟩ hupper
  · exact le_csSup ⟨u, fun x hx => hx.1⟩ hmem

/-- R-coordinate version of `ellMinus_eq_on_left_interval`. -/
theorem rhoMinus_eq_on_left_interval (P : Peanosphere ω η) {t level s u : ℝ}
    (hs : rhoMinus ω t level = s) (hsu : s ≤ u) (hut : u ≤ t) :
    rhoMinus ω u level = s := by
  have hglobal := rhoMinus_mem P t level
  rw [hs] at hglobal
  have hmem : s ∈ {x | x ≤ u ∧ rCoord ω x ≤ level} := ⟨hsu, hglobal.2⟩
  have hupper : ∀ x ∈ {x | x ≤ u ∧ rCoord ω x ≤ level}, x ≤ s := by
    intro x hx
    have hxglobal : x ∈ {x | x ≤ t ∧ rCoord ω x ≤ level} := ⟨le_trans hx.1 hut, hx.2⟩
    have hxle : x ≤ rhoMinus ω t level :=
      le_csSup (show BddAbove {x : ℝ | x ≤ t ∧ rCoord ω x ≤ level} from
        ⟨t, fun x hx => hx.1⟩) hxglobal
    simpa [hs] using hxle
  apply le_antisymm
  · exact csSup_le ⟨s, hmem⟩ hupper
  · exact le_csSup ⟨u, fun x hx => hx.1⟩ hmem

/-- The strip point with horizontal coordinate `t` and vertical coordinate `y`. -/
def stripPoint (t y : ℝ) : ℂ := Complex.mk t y

@[fun_prop] theorem continuous_stripPoint_pair :
    Continuous (fun p : ℝ × ℝ => stripPoint p.1 p.2) := by
  have hEq : (fun p : ℝ × ℝ => stripPoint p.1 p.2) =
      fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    funext p
    apply Complex.ext <;> simp [stripPoint, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
  rw [hEq]
  fun_prop

/-- The Route M sheared strip map. The central strip is `ℝ × [0,1]`; below it the map
uses the last L-level contact, and above it the last R-level contact. -/
noncomputable def shearedStripMap (_P : Peanosphere ω η) (w : ℂ) : ℂ :=
  if 0 ≤ w.im ∧ w.im ≤ 1 then η w.re
  else if w.im < 0 then η (ellMinus ω w.re (lCoord ω w.re + w.im))
  else η (rhoMinus ω w.re (rCoord ω w.re - (w.im - 1)))

/-- The real time representative used to read off the image under `shearedStripMap`. -/
noncomputable def stripRepresentative (_P : Peanosphere ω η) (w : ℂ) : ℝ :=
  if 0 ≤ w.im ∧ w.im ≤ 1 then w.re
  else if w.im < 0 then ellMinus ω w.re (lCoord ω w.re + w.im)
  else rhoMinus ω w.re (rCoord ω w.re - (w.im - 1))

/-- A finite label for the three regions of the sheared strip. -/
def stripRegion (w : ℂ) : Fin 3 :=
  if 0 ≤ w.im ∧ w.im ≤ 1 then 0 else if w.im < 0 then 1 else 2

@[simp] theorem shearedStripMap_eq_eta_representative (P : Peanosphere ω η) (w : ℂ) :
    shearedStripMap P w = η (stripRepresentative P w) := by
  by_cases hmid : 0 ≤ w.im ∧ w.im ≤ 1
  · simp [shearedStripMap, stripRepresentative, hmid]
  · by_cases hbelow : w.im < 0
    · simp [shearedStripMap, stripRepresentative, hmid, hbelow]
    · simp [shearedStripMap, stripRepresentative, hmid, hbelow]

@[simp] theorem shearedStripMap_stripPoint_mid (P : Peanosphere ω η) {t y : ℝ}
    (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) :
    shearedStripMap P (stripPoint t y) = η t := by
  simp [shearedStripMap, stripPoint, hy₀, hy₁]

/-- The sheared map is constant on the L-chord associated with a direct L-relation. -/
theorem shearedStripMap_lowerChord (P : Peanosphere ω η)
    (a b : ℝ)
    (h : directRel (lCoord ω) a b) {u : ℝ} (hu : u ∈ Icc a b) :
    shearedStripMap P (stripPoint u (lCoord ω a - lCoord ω u)) = η a := by
  rcases h with ⟨hab, hval, hinside⟩
  have hη : η a = η b := P.merge a b (Or.inl ⟨hab, hval, hinside⟩)
  rcases hu with ⟨hau, hub⟩
  by_cases hleft : u = a
  · subst u
    simp [shearedStripMap, stripPoint]
  by_cases hright : u = b
  · subst u
    simp [shearedStripMap, stripPoint, hval, hη]
  have hau' : a < u := lt_of_le_of_ne hau (Ne.symm hleft)
  have hub' : u < b := lt_of_le_of_ne hub hright
  have hdown : lCoord ω a - lCoord ω u < 0 := by
    linarith [hinside u ⟨hau', hub'⟩]
  have hlevel : lCoord ω u + (lCoord ω a - lCoord ω u) = lCoord ω a := by ring
  rw [shearedStripMap]
  change (if 0 ≤ lCoord ω a - lCoord ω u ∧ lCoord ω a - lCoord ω u ≤ 1 then η u else
      if lCoord ω a - lCoord ω u < 0 then
        η (ellMinus ω u (lCoord ω u + (lCoord ω a - lCoord ω u)))
      else η (rhoMinus ω u (rCoord ω u - (lCoord ω a - lCoord ω u - 1)))) = η a
  rw [ite_eq_right (by simp [not_le_of_gt hdown])]
  rw [ite_eq_left hdown]
  rw [hlevel, ellMinus_eq_left_of_above a b (lCoord ω a) rfl hinside
    (le_of_lt hau') hub']

/-- The sheared map is constant on the R-chord associated with a direct R-relation. -/
theorem shearedStripMap_upperChord (P : Peanosphere ω η)
    (a b : ℝ)
    (h : directRel (rCoord ω) a b) {u : ℝ} (hu : u ∈ Icc a b) :
    shearedStripMap P (stripPoint u (1 + rCoord ω u - rCoord ω a)) = η a := by
  rcases h with ⟨hab, hval, hinside⟩
  have hη : η a = η b := P.merge a b (Or.inr ⟨hab, hval, hinside⟩)
  rcases hu with ⟨hau, hub⟩
  by_cases hleft : u = a
  · subst u
    simp [shearedStripMap, stripPoint]
  by_cases hright : u = b
  · subst u
    simp [shearedStripMap, stripPoint, hval, hη]
  have hau' : a < u := lt_of_le_of_ne hau (Ne.symm hleft)
  have hub' : u < b := lt_of_le_of_ne hub hright
  have hup : 1 < 1 + rCoord ω u - rCoord ω a := by
    linarith [hinside u ⟨hau', hub'⟩]
  have hlevel : rCoord ω u - ((1 + rCoord ω u - rCoord ω a) - 1) = rCoord ω a := by ring
  rw [shearedStripMap]
  change (if 0 ≤ 1 + rCoord ω u - rCoord ω a ∧ 1 + rCoord ω u - rCoord ω a ≤ 1 then η u else
      if 1 + rCoord ω u - rCoord ω a < 0 then
        η (ellMinus ω u (lCoord ω u + (1 + rCoord ω u - rCoord ω a)))
      else η (rhoMinus ω u (rCoord ω u - ((1 + rCoord ω u - rCoord ω a) - 1)))) = η a
  rw [ite_eq_right (by simp [not_le_of_gt hup])]
  rw [ite_eq_right (by linarith)]
  rw [hlevel, rhoMinus_eq_left_of_above a b (rCoord ω a) rfl hinside
    (le_of_lt hau') hub']

/-- The lower half of a fibre is attached to its left mid-strip time by its L-chord. -/
theorem shearedStripMap_on_lastLChord (P : Peanosphere ω η) {t level : ℝ}
    (hlevel : level < lCoord ω t) {u : ℝ}
    (hu : ellMinus ω t level ≤ u ∧ u ≤ t) :
    shearedStripMap P (stripPoint u (level - lCoord ω u)) =
      η (ellMinus ω t level) := by
  let s := ellMinus ω t level
  have hs : lCoord ω s = level := by
    simpa [s] using ellMinus_level P hlevel
  have hsu : s ≤ u := hu.1
  have hut : u ≤ t := hu.2
  by_cases heq : u = s
  · subst u
    rw [hs]
    exact shearedStripMap_stripPoint_mid P (by norm_num) (by norm_num)
  have hsu' : s < u := lt_of_le_of_ne hsu (Ne.symm heq)
  have hstrict : level < lCoord ω u := by
    by_contra hnot
    have hle : lCoord ω u ≤ level := le_of_not_gt hnot
    have hsup : u ≤ ellMinus ω t level :=
      le_csSup (show BddAbove {x : ℝ | x ≤ t ∧ lCoord ω x ≤ level} from
        ⟨t, fun x hx => hx.1⟩) ⟨hut, hle⟩
    exact (not_le_of_gt hsu') (by simpa [s] using hsup)
  have hbelow : level - lCoord ω u < 0 := by linarith
  have hcancel : lCoord ω u + (level - lCoord ω u) = level := by ring
  rw [shearedStripMap]
  change (if 0 ≤ level - lCoord ω u ∧ level - lCoord ω u ≤ 1 then η u else
      if level - lCoord ω u < 0 then
        η (ellMinus ω u (lCoord ω u + (level - lCoord ω u)))
      else η (rhoMinus ω u (rCoord ω u - (level - lCoord ω u - 1)))) =
    η (ellMinus ω t level)
  rw [ite_eq_right (by simp [not_le_of_gt hbelow])]
  rw [ite_eq_left hbelow, hcancel]
  rw [ellMinus_eq_on_left_interval P (by dsimp [s]) hsu hut]

/-- The upper half of a fibre is attached to its left mid-strip time by its R-chord. -/
theorem shearedStripMap_on_lastRChord (P : Peanosphere ω η) {t level : ℝ}
    (hlevel : level < rCoord ω t) {u : ℝ}
    (hu : rhoMinus ω t level ≤ u ∧ u ≤ t) :
    shearedStripMap P (stripPoint u (1 + rCoord ω u - level)) =
      η (rhoMinus ω t level) := by
  let s := rhoMinus ω t level
  have hs : rCoord ω s = level := by
    simpa [s] using rhoMinus_level P hlevel
  have hsu : s ≤ u := hu.1
  have hut : u ≤ t := hu.2
  by_cases heq : u = s
  · subst u
    rw [hs]
    exact shearedStripMap_stripPoint_mid P (by norm_num) (by norm_num)
  have hsu' : s < u := lt_of_le_of_ne hsu (Ne.symm heq)
  have hstrict : level < rCoord ω u := by
    by_contra hnot
    have hle : rCoord ω u ≤ level := le_of_not_gt hnot
    have hsup : u ≤ rhoMinus ω t level :=
      le_csSup (show BddAbove {x : ℝ | x ≤ t ∧ rCoord ω x ≤ level} from
        ⟨t, fun x hx => hx.1⟩) ⟨hut, hle⟩
    exact (not_le_of_gt hsu') (by simpa [s] using hsup)
  have habove : 1 < 1 + rCoord ω u - level := by linarith
  have hcancel : rCoord ω u - ((1 + rCoord ω u - level) - 1) = level := by ring
  rw [shearedStripMap]
  change (if 0 ≤ 1 + rCoord ω u - level ∧ 1 + rCoord ω u - level ≤ 1 then η u else
      if 1 + rCoord ω u - level < 0 then
        η (ellMinus ω u (lCoord ω u + (1 + rCoord ω u - level)))
      else η (rhoMinus ω u (rCoord ω u - ((1 + rCoord ω u - level) - 1)))) =
    η (rhoMinus ω t level)
  rw [ite_eq_right (by simp [not_le_of_gt habove])]
  rw [ite_eq_right (by linarith)]
  rw [hcancel]
  rw [rhoMinus_eq_on_left_interval P (by dsimp [s]) hsu hut]

/-- A vertical segment in the middle strip stays in one fibre. -/
theorem joined_mid_vertical (P : Peanosphere ω η) {q : ℂ} {t y₀ y₁ : ℝ}
    (hη : η t = q) (hy₀ : y₀ ∈ Icc (0 : ℝ) 1) (hy₁ : y₁ ∈ Icc (0 : ℝ) 1) :
    JoinedIn (shearedStripMap P ⁻¹' {q}) (stripPoint t y₀) (stripPoint t y₁) := by
  let f : ℝ → ℂ := fun v => stripPoint t (y₀ + v * (y₁ - y₀))
  have hfPair : Continuous (fun v : ℝ => (t, y₀ + v * (y₁ - y₀))) := by fun_prop
  have hf' : Continuous f := by
    change Continuous ((fun p : ℝ × ℝ => stripPoint p.1 p.2) ∘
      fun v : ℝ => (t, y₀ + v * (y₁ - y₀)))
    exact continuous_stripPoint_pair.comp hfPair
  have hf : ContinuousOn f I := hf'.continuousOn
  have h0 : f 0 = stripPoint t y₀ := by simp [f, stripPoint]
  have h1 : f 1 = stripPoint t y₁ := by
    simp [f, stripPoint]
  apply JoinedIn.ofLine hf h0 h1
  rintro z ⟨v, hv, rfl⟩
  apply Set.mem_preimage.mpr
  rw [shearedStripMap_stripPoint_mid P]
  · exact hη
  · nlinarith [hv.1, hv.2, hy₀.1, hy₀.2, hy₁.1, hy₁.2]
  · nlinarith [hv.1, hv.2, hy₀.1, hy₀.2, hy₁.1, hy₁.2]

/-- A direct L-relation gives a path in the strip map's fibre between the chord endpoints. -/
theorem joined_lower_direct (P : Peanosphere ω η) (a b : ℝ)
    (h : directRel (lCoord ω) a b) :
    JoinedIn (shearedStripMap P ⁻¹' {η a}) (stripPoint a 0) (stripPoint b 0) := by
  let f : ℝ → ℂ := fun v =>
    stripPoint (a + v * (b - a)) (lCoord ω a - lCoord ω (a + v * (b - a)))
  have hfPair : Continuous (fun v : ℝ =>
      (a + v * (b - a), lCoord ω a - lCoord ω (a + v * (b - a)))) := by fun_prop
  have hf' : Continuous f := by
    change Continuous ((fun p : ℝ × ℝ => stripPoint p.1 p.2) ∘ fun v : ℝ =>
      (a + v * (b - a), lCoord ω a - lCoord ω (a + v * (b - a))))
    exact continuous_stripPoint_pair.comp hfPair
  have hf : ContinuousOn f I := hf'.continuousOn
  rcases h with ⟨hab, hval, hinside⟩
  have h0 : f 0 = stripPoint a 0 := by simp [f, stripPoint]
  have h1 : f 1 = stripPoint b 0 := by simp [f, stripPoint, hval]
  apply JoinedIn.ofLine hf h0 h1
  rintro z ⟨v, hv, rfl⟩
  apply Set.mem_preimage.mpr
  have htime : a + v * (b - a) ∈ Icc a b := by
    constructor <;> nlinarith [hv.1, hv.2, hab]
  exact shearedStripMap_lowerChord P a b ⟨hab, hval, hinside⟩ htime

/-- A direct R-relation gives a path in the strip map's fibre between the chord endpoints. -/
theorem joined_upper_direct (P : Peanosphere ω η) (a b : ℝ)
    (h : directRel (rCoord ω) a b) :
    JoinedIn (shearedStripMap P ⁻¹' {η a}) (stripPoint a 1) (stripPoint b 1) := by
  let f : ℝ → ℂ := fun v =>
    stripPoint (a + v * (b - a)) (1 + rCoord ω (a + v * (b - a)) - rCoord ω a)
  have hfPair : Continuous (fun v : ℝ =>
      (a + v * (b - a), 1 + rCoord ω (a + v * (b - a)) - rCoord ω a)) := by fun_prop
  have hf' : Continuous f := by
    change Continuous ((fun p : ℝ × ℝ => stripPoint p.1 p.2) ∘ fun v : ℝ =>
      (a + v * (b - a), 1 + rCoord ω (a + v * (b - a)) - rCoord ω a))
    exact continuous_stripPoint_pair.comp hfPair
  have hf : ContinuousOn f I := hf'.continuousOn
  rcases h with ⟨hab, hval, hinside⟩
  have h0 : f 0 = stripPoint a 1 := by simp [f, stripPoint]
  have h1 : f 1 = stripPoint b 1 := by simp [f, stripPoint, hval]
  apply JoinedIn.ofLine hf h0 h1
  rintro z ⟨v, hv, rfl⟩
  apply Set.mem_preimage.mpr
  have htime : a + v * (b - a) ∈ Icc a b := by
    constructor <;> nlinarith [hv.1, hv.2, hab]
  exact shearedStripMap_upperChord P a b ⟨hab, hval, hinside⟩ htime

/-- Every point in a sheared fibre can be joined inside that fibre to a mid-strip point. -/
theorem joined_point_to_mid (P : Peanosphere ω η) {q w : ℂ}
    (hw : shearedStripMap P w = q) :
    ∃ t, η t = q ∧ JoinedIn (shearedStripMap P ⁻¹' {q}) w
      (stripPoint t (1 / 2)) := by
  by_cases hmid : 0 ≤ w.im ∧ w.im ≤ 1
  · have hη : η w.re = q := by simpa [shearedStripMap, hmid] using hw
    refine ⟨w.re, hη, ?_⟩
    have hpoint : w = stripPoint w.re w.im := by
      apply Complex.ext <;> simp [stripPoint]
    rw [hpoint]
    exact joined_mid_vertical P hη hmid (by norm_num [Icc])
  · by_cases hbelow : w.im < 0
    · let t : ℝ := w.re
      let level : ℝ := lCoord ω t + w.im
      let s : ℝ := ellMinus ω t level
      have hlevel : level < lCoord ω t := by
        dsimp [level]
        linarith
      have hη : η s = q := by
        have h := hw
        simp only [shearedStripMap, ite_eq_right hmid, ite_eq_left hbelow] at h
        simpa [s, t, level] using h
      have hslevel : lCoord ω s = level := by
        simpa [s] using ellMinus_level P hlevel
      have hstle : s ≤ t := by
        simpa [s] using (ellMinus_mem P t level).1
      have hstne : s ≠ t := by
        intro heq
        rw [heq] at hslevel
        exact (ne_of_lt hlevel) hslevel.symm
      have hst : s < t := lt_of_le_of_ne hstle hstne
      let f : ℝ → ℂ := fun v =>
        stripPoint (s + v * (t - s))
          (level - lCoord ω (s + v * (t - s)))
      have hfPair : Continuous (fun v : ℝ =>
          (s + v * (t - s), level - lCoord ω (s + v * (t - s)))) := by fun_prop
      have hf' : Continuous f := by
        change Continuous ((fun p : ℝ × ℝ => stripPoint p.1 p.2) ∘ fun v : ℝ =>
          (s + v * (t - s), level - lCoord ω (s + v * (t - s))))
        exact continuous_stripPoint_pair.comp hfPair
      have hf : ContinuousOn f I := hf'.continuousOn
      have h0 : f 0 = stripPoint s 0 := by
        apply Complex.ext <;> simp [f, stripPoint, hslevel]
      have h1 : f 1 = w := by
        apply Complex.ext
        · simp [f, stripPoint, t, s]
        · simp [f, stripPoint, t, level]
      have hchord : JoinedIn (shearedStripMap P ⁻¹' {q}) (stripPoint s 0) w := by
        apply JoinedIn.ofLine hf h0 h1
        rintro z ⟨v, hv, rfl⟩
        apply Set.mem_preimage.mpr
        have hu : s + v * (t - s) ∈ Icc s t := by
          constructor <;> nlinarith [hv.1, hv.2, hst]
        have hmap := shearedStripMap_on_lastLChord P hlevel hu
        simpa [s, hη] using hmap
      have hvertical := joined_mid_vertical P (q := q) (t := s)
        (y₀ := 0) (y₁ := (1 / 2 : ℝ)) hη (by norm_num [Icc]) (by norm_num [Icc])
      exact ⟨s, hη, hchord.symm.trans hvertical⟩
    · have him0 : 0 ≤ w.im := le_of_not_gt hbelow
      have him1 : ¬ w.im ≤ 1 := by
        intro hle
        exact hmid ⟨him0, hle⟩
      have hhigh : 1 < w.im := lt_of_not_ge him1
      let t : ℝ := w.re
      let level : ℝ := rCoord ω t - (w.im - 1)
      let s : ℝ := rhoMinus ω t level
      have hlevel : level < rCoord ω t := by
        dsimp [level]
        linarith
      have hη : η s = q := by
        have h := hw
        simp only [shearedStripMap, ite_eq_right hmid, ite_eq_right (not_lt_of_ge him0)] at h
        simpa [s, t, level] using h
      have hslevel : rCoord ω s = level := by
        simpa [s] using rhoMinus_level P hlevel
      have hstle : s ≤ t := by
        simpa [s] using (rhoMinus_mem P t level).1
      have hstne : s ≠ t := by
        intro heq
        rw [heq] at hslevel
        exact (ne_of_lt hlevel) hslevel.symm
      have hst : s < t := lt_of_le_of_ne hstle hstne
      let f : ℝ → ℂ := fun v =>
        stripPoint (s + v * (t - s))
          (1 + rCoord ω (s + v * (t - s)) - level)
      have hfPair : Continuous (fun v : ℝ =>
          (s + v * (t - s), 1 + rCoord ω (s + v * (t - s)) - level)) := by fun_prop
      have hf' : Continuous f := by
        change Continuous ((fun p : ℝ × ℝ => stripPoint p.1 p.2) ∘ fun v : ℝ =>
          (s + v * (t - s), 1 + rCoord ω (s + v * (t - s)) - level))
        exact continuous_stripPoint_pair.comp hfPair
      have hf : ContinuousOn f I := hf'.continuousOn
      have h0 : f 0 = stripPoint s 1 := by
        apply Complex.ext <;> simp [f, stripPoint, hslevel]
      have h1 : f 1 = w := by
        apply Complex.ext
        · simp [f, stripPoint, t, s]
        · simp [f, stripPoint, t, level]
          ring
      have hchord : JoinedIn (shearedStripMap P ⁻¹' {q}) (stripPoint s 1) w := by
        apply JoinedIn.ofLine hf h0 h1
        rintro z ⟨v, hv, rfl⟩
        apply Set.mem_preimage.mpr
        have hu : s + v * (t - s) ∈ Icc s t := by
          constructor <;> nlinarith [hv.1, hv.2, hst]
        have hmap := shearedStripMap_on_lastRChord P hlevel hu
        simpa [s, hη] using hmap
      have hvertical := joined_mid_vertical P (q := q) (t := s)
        (y₀ := 1) (y₁ := (1 / 2 : ℝ)) hη (by norm_num [Icc]) (by norm_num [Icc])
      exact ⟨s, hη, hchord.symm.trans hvertical⟩

/-- The relation generated by the two direct chord types connects the corresponding
mid-strip representatives inside a single fibre. -/
theorem eta_eq_of_eqvGen (P : Peanosphere ω η) {s t : ℝ}
    (h : Relation.EqvGen
      (fun a b => directRel (lCoord ω) a b ∨ directRel (rCoord ω) a b) s t) :
    η s = η t := by
  induction h with
  | rel a b hab => exact P.merge a b hab
  | refl a => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ => exact ih₁.trans ih₂

/-- Equal-level contacts with no excursion below the level are connected by direct chords.
Distinct local-minimum values ensure there is at most one interior contact. -/
theorem eqvGen_contacts_of_L_above (P : Peanosphere ω η) {a b level : ℝ}
    (hab : a ≤ b) (ha : lCoord ω a = level) (hb : lCoord ω b = level)
    (habove : ∀ u ∈ Ioo a b, level ≤ lCoord ω u) :
    Relation.EqvGen
      (fun s t => directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) a b := by
  by_cases hEq : a = b
  · subst b
    exact Relation.EqvGen.refl a
  have hab' : a < b := lt_of_le_of_ne hab hEq
  have hdistinct : ∀ x y, x ≠ y → IsLocalMin (lCoord ω) x → IsLocalMin (lCoord ω) y →
      lCoord ω x ≠ lCoord ω y := by
    intro x y hxy hx hy
    have hx' : IsLocalMin (MatedCRT.lrCoord (0 : Fin 2) · ω) x := by
      change IsLocalMin (fun t => (ω t).1) x
      exact hx
    have hy' : IsLocalMin (MatedCRT.lrCoord (0 : Fin 2) · ω) y := by
      change IsLocalMin (fun t => (ω t).1) y
      exact hy
    exact P.locMinDistinct 0 x y hxy hx' hy'
  have hlocal : ∀ x, x ∈ Ioo a b → lCoord ω x = level → IsLocalMin (lCoord ω) x := by
    intro x hx hxval
    change ∀ᶠ y in 𝓝 x, lCoord ω x ≤ lCoord ω y
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [hxval]
    exact habove y hy
  have hunique : ∀ x y, x ∈ Ioo a b → y ∈ Ioo a b →
      lCoord ω x = level → lCoord ω y = level → x = y := by
    intro x y hx hy hxval hyval
    by_contra hxy
    have hne := hdistinct x y hxy (hlocal x hx hxval) (hlocal y hy hyval)
    exact hne (hxval.trans hyval.symm)
  by_cases htouch : ∃ x ∈ Ioo a b, lCoord ω x = level
  · obtain ⟨m, hm, hmval⟩ := htouch
    have hleft : directRel (lCoord ω) a m := by
      refine ⟨hm.1, ha.trans hmval.symm, ?_⟩
      intro x hx
      have hge := habove x ⟨hx.1, lt_trans hx.2 hm.2⟩
      have hge' : lCoord ω a ≤ lCoord ω x := by rw [← ha] at hge; exact hge
      apply lt_of_le_of_ne hge'
      intro heq
      have hxval : lCoord ω x = level := heq.symm.trans ha
      have hxm : x = m := hunique x m ⟨hx.1, lt_trans hx.2 hm.2⟩ hm hxval hmval
      exact (ne_of_lt hx.2) hxm
    have hright : directRel (lCoord ω) m b := by
      refine ⟨hm.2, hmval.trans hb.symm, ?_⟩
      intro x hx
      have hge := habove x ⟨lt_trans hm.1 hx.1, hx.2⟩
      have hge' : lCoord ω m ≤ lCoord ω x := by rw [← hmval] at hge; exact hge
      apply lt_of_le_of_ne hge'
      intro heq
      have hxval : lCoord ω x = level := heq.symm.trans hmval
      have hxm : x = m := hunique x m ⟨lt_trans hm.1 hx.1, hx.2⟩ hm hxval hmval
      exact (ne_of_gt hx.1) hxm
    exact Relation.EqvGen.trans a m b
      (Relation.EqvGen.rel a m (Or.inl hleft))
      (Relation.EqvGen.rel m b (Or.inl hright))
  · have hstrict : ∀ x, x ∈ Ioo a b → lCoord ω a < lCoord ω x := by
      intro x hx
      have hge := habove x hx
      have hge' : lCoord ω a ≤ lCoord ω x := by rw [← ha] at hge; exact hge
      apply lt_of_le_of_ne hge'
      intro heq
      exact htouch ⟨x, hx, heq.symm.trans ha⟩
    exact Relation.EqvGen.rel a b (Or.inl ⟨hab', ha.trans hb.symm, hstrict⟩)

/-- R-coordinate counterpart of `eqvGen_contacts_of_L_above`. -/
theorem eqvGen_contacts_of_R_above (P : Peanosphere ω η) {a b level : ℝ}
    (hab : a ≤ b) (ha : rCoord ω a = level) (hb : rCoord ω b = level)
    (habove : ∀ u ∈ Ioo a b, level ≤ rCoord ω u) :
    Relation.EqvGen
      (fun s t => directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) a b := by
  by_cases hEq : a = b
  · subst b
    exact Relation.EqvGen.refl a
  have hab' : a < b := lt_of_le_of_ne hab hEq
  have hdistinct : ∀ x y, x ≠ y → IsLocalMin (rCoord ω) x → IsLocalMin (rCoord ω) y →
      rCoord ω x ≠ rCoord ω y := by
    intro x y hxy hx hy
    have hx' : IsLocalMin (MatedCRT.lrCoord (1 : Fin 2) · ω) x := by
      change IsLocalMin (fun t => (ω t).2) x
      exact hx
    have hy' : IsLocalMin (MatedCRT.lrCoord (1 : Fin 2) · ω) y := by
      change IsLocalMin (fun t => (ω t).2) y
      exact hy
    exact P.locMinDistinct 1 x y hxy hx' hy'
  have hlocal : ∀ x, x ∈ Ioo a b → rCoord ω x = level → IsLocalMin (rCoord ω) x := by
    intro x hx hxval
    change ∀ᶠ y in 𝓝 x, rCoord ω x ≤ rCoord ω y
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [hxval]
    exact habove y hy
  have hunique : ∀ x y, x ∈ Ioo a b → y ∈ Ioo a b →
      rCoord ω x = level → rCoord ω y = level → x = y := by
    intro x y hx hy hxval hyval
    by_contra hxy
    have hne := hdistinct x y hxy (hlocal x hx hxval) (hlocal y hy hyval)
    exact hne (hxval.trans hyval.symm)
  by_cases htouch : ∃ x ∈ Ioo a b, rCoord ω x = level
  · obtain ⟨m, hm, hmval⟩ := htouch
    have hleft : directRel (rCoord ω) a m := by
      refine ⟨hm.1, ha.trans hmval.symm, ?_⟩
      intro x hx
      have hge := habove x ⟨hx.1, lt_trans hx.2 hm.2⟩
      have hge' : rCoord ω a ≤ rCoord ω x := by rw [← ha] at hge; exact hge
      apply lt_of_le_of_ne hge'
      intro heq
      have hxval : rCoord ω x = level := heq.symm.trans ha
      have hxm : x = m := hunique x m ⟨hx.1, lt_trans hx.2 hm.2⟩ hm hxval hmval
      exact (ne_of_lt hx.2) hxm
    have hright : directRel (rCoord ω) m b := by
      refine ⟨hm.2, hmval.trans hb.symm, ?_⟩
      intro x hx
      have hge := habove x ⟨lt_trans hm.1 hx.1, hx.2⟩
      have hge' : rCoord ω m ≤ rCoord ω x := by rw [← hmval] at hge; exact hge
      apply lt_of_le_of_ne hge'
      intro heq
      have hxval : rCoord ω x = level := heq.symm.trans hmval
      have hxm : x = m := hunique x m ⟨lt_trans hm.1 hx.1, hx.2⟩ hm hxval hmval
      exact (ne_of_gt hx.1) hxm
    exact Relation.EqvGen.trans a m b
      (Relation.EqvGen.rel a m (Or.inr hleft))
      (Relation.EqvGen.rel m b (Or.inr hright))
  · have hstrict : ∀ x, x ∈ Ioo a b → rCoord ω a < rCoord ω x := by
      intro x hx
      have hge := habove x hx
      have hge' : rCoord ω a ≤ rCoord ω x := by rw [← ha] at hge; exact hge
      apply lt_of_le_of_ne hge'
      intro heq
      exact htouch ⟨x, hx, heq.symm.trans ha⟩
    exact Relation.EqvGen.rel a b (Or.inr ⟨hab', ha.trans hb.symm, hstrict⟩)

/-- On a one-sided interval above a common L-level, the Peanosphere curve has equal endpoint values. -/
theorem eta_eq_of_L_level_interval (P : Peanosphere ω η) {a b level : ℝ}
    (hab : a ≤ b) (ha : lCoord ω a = level) (hb : lCoord ω b = level)
    (habove : ∀ u ∈ Ioo a b, level ≤ lCoord ω u) : η a = η b := by
  exact eta_eq_of_eqvGen P (eqvGen_contacts_of_L_above P hab ha hb habove)

/-- R-coordinate version of `eta_eq_of_L_level_interval`. -/
theorem eta_eq_of_R_level_interval (P : Peanosphere ω η) {a b level : ℝ}
    (hab : a ≤ b) (ha : rCoord ω a = level) (hb : rCoord ω b = level)
    (habove : ∀ u ∈ Ioo a b, level ≤ rCoord ω u) : η a = η b := by
  exact eta_eq_of_eqvGen P (eqvGen_contacts_of_R_above P hab ha hb habove)

theorem joined_mid_of_eqvGen (P : Peanosphere ω η) {s t : ℝ}
    (h : Relation.EqvGen
      (fun a b => directRel (lCoord ω) a b ∨ directRel (rCoord ω) a b) s t) :
    JoinedIn (shearedStripMap P ⁻¹' {η s}) (stripPoint s (1 / 2))
      (stripPoint t (1 / 2)) := by
  induction h with
  | rel a b hab =>
      rcases hab with hL | hR
      · have hdown := joined_mid_vertical P (q := η a) (t := a)
          (y₀ := (1 / 2 : ℝ)) (y₁ := 0) rfl (by norm_num [Icc]) (by norm_num [Icc])
        have hchord := joined_lower_direct P a b hL
        have hup := joined_mid_vertical P (q := η a) (t := b)
          (y₀ := 0) (y₁ := (1 / 2 : ℝ)) (P.merge a b (Or.inl hL)).symm
          (by norm_num [Icc]) (by norm_num [Icc])
        have hpath := hdown.trans hchord
        exact hpath.trans hup
      · have htop := joined_mid_vertical P (q := η a) (t := a)
          (y₀ := (1 / 2 : ℝ)) (y₁ := 1) rfl (by norm_num [Icc]) (by norm_num [Icc])
        have hchord := joined_upper_direct P a b hR
        have hbottom := joined_mid_vertical P (q := η a) (t := b)
          (y₀ := 1) (y₁ := (1 / 2 : ℝ)) (P.merge a b (Or.inr hR)).symm
          (by norm_num [Icc]) (by norm_num [Icc])
        have hpath := htop.trans hchord
        exact hpath.trans hbottom
  | refl a =>
      apply JoinedIn.refl
      change shearedStripMap P (stripPoint a (1 / 2)) = η a
      exact shearedStripMap_stripPoint_mid P (by norm_num) (by norm_num)
  | symm a b hab ih =>
      have hη := eta_eq_of_eqvGen P hab
      simpa [hη] using ih.symm
  | trans a b c hab hbc ih₁ ih₂ =>
      have hη := eta_eq_of_eqvGen P hab
      exact ih₁.trans (by simpa [hη] using ih₂)

/-- Every fibre of the sheared strip map is path-connected, hence the map is monotone. -/
theorem shearedStripMap_fiber_isPathConnected (P : Peanosphere ω η) (q : ℂ) :
    IsPathConnected (shearedStripMap P ⁻¹' {q}) := by
  rw [isPathConnected_iff]
  constructor
  · obtain ⟨t, ht⟩ := P.surj q
    refine ⟨stripPoint t (1 / 2), ?_⟩
    change shearedStripMap P (stripPoint t (1 / 2)) = q
    rw [shearedStripMap_stripPoint_mid P (by norm_num) (by norm_num), ht]
  · intro x hx y hy
    have hxq : shearedStripMap P x = q := by simpa using hx
    have hyq : shearedStripMap P y = q := by simpa using hy
    obtain ⟨s, hsη, hxs⟩ := joined_point_to_mid P hxq
    obtain ⟨t, htη, hyt⟩ := joined_point_to_mid P hyq
    have hη : η s = η t := hsη.trans htη.symm
    have hgen := P.onlyMerge s t hη
    have hmid := joined_mid_of_eqvGen P hgen
    have hmidQ : JoinedIn (shearedStripMap P ⁻¹' {q})
        (stripPoint s (1 / 2)) (stripPoint t (1 / 2)) := by
      simpa [hsη] using hmid
    exact hxs.trans (hmidQ.trans hyt.symm)

/-- The central strip over a time interval maps exactly to the corresponding cell trace. -/
theorem image_stripPoint_mid (P : Peanosphere ω η) (a b : ℝ) :
    shearedStripMap P ''
        ((fun p : ℝ × ℝ => stripPoint p.1 p.2) ''
          (Icc a b ×ˢ Icc (0 : ℝ) 1)) =
      η '' Icc a b := by
  ext q
  constructor
  · rintro ⟨w, ⟨⟨t, y⟩, hxy, rfl⟩, rfl⟩
    rcases hxy with ⟨ht, hy⟩
    exact ⟨t, ht, (shearedStripMap_stripPoint_mid P hy.1 hy.2).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨stripPoint t (1 / 2 : ℝ), ?_, ?_⟩
    · exact ⟨((t, (1 / 2 : ℝ)) : ℝ × ℝ), ⟨ht, by norm_num [Icc]⟩, rfl⟩
    · exact shearedStripMap_stripPoint_mid P (t := t) (y := (1 / 2 : ℝ)) (by norm_num) (by norm_num)

/-- Mid-strip representatives show that the sheared map is onto whenever the Peanosphere
curve is onto. -/
theorem shearedStripMap_surjective (P : Peanosphere ω η) :
    Function.Surjective (shearedStripMap P) := by
  intro q
  obtain ⟨t, ht⟩ := P.surj q
  refine ⟨stripPoint t (1 / 2 : ℝ), ?_⟩
  rw [shearedStripMap_stripPoint_mid P (t := t) (y := (1 / 2 : ℝ)) (by norm_num) (by norm_num), ht]

end MatedCRTHarmonic.RouteM
