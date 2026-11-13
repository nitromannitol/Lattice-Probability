import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Successive displacement times of a continuous path

For a path `f : ℝ≥0 → E` in a normed group and a displacement `r`, the successive displacement
times are `σ₀ = 0` and `σ_{k+1}` the first time `t ≥ σ_k` at which `‖f t - f σ_k‖ ≥ r`, with value
`⊤` when there is no such time (`stepTime`).

Two deterministic counting statements compare `σ_k` with a time grid of mesh `s`.

* `stepTime_card_le`: if `f` is continuous and the increment of `f` over `((j s), (j+1) s]` has norm
  at least `2 r` for every `j` in a set `J ⊆ [0, m)`, then `σ_{#J} ≤ m s`.
* `min_le_stepTime`: if every increment of `f` over a window of length `s` starting at a time
  `≤ T` has norm `< r`, then `min T (k s) ≤ σ_k`.
-/

open Set Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb

section StepTimes

variable {E : Type*} [NormedAddCommGroup E] (f : ℝ≥0 → E) (r : ℝ)

/-- The times `t ≥ a` at which `f` has moved by at least `r` from its value at `a`. -/
def stepSet (a : ℝ≥0) : Set ℝ≥0 := {t | a ≤ t ∧ r ≤ ‖f t - f a‖}

open Classical in
/-- The first time `t ≥ a` with `r ≤ ‖f t - f a‖`, or `⊤` if there is none. -/
noncomputable def nextStep (a : ℝ≥0) : ℝ≥0∞ :=
  if (stepSet f r a).Nonempty then ((sInf (stepSet f r a) : ℝ≥0) : ℝ≥0∞) else ⊤

/-- The successive displacement times of `f` of size `r`: `σ₀ = 0`, and `σ_{k+1}` is the first time
after `σ_k` at which `f` has moved by `r` from `f σ_k` (`⊤` if there is none). -/
noncomputable def stepTime : ℕ → ℝ≥0∞
  | 0 => 0
  | k + 1 => if stepTime k = ⊤ then ⊤ else nextStep f r (stepTime k).toNNReal

variable {f r}

lemma nextStep_le_of_mem {a t : ℝ≥0} (ht : t ∈ stepSet f r a) : nextStep f r a ≤ t := by
  have hne : (stepSet f r a).Nonempty := ⟨t, ht⟩
  unfold nextStep
  split_ifs
  exact_mod_cast csInf_le (OrderBot.bddBelow _) ht

lemma le_nextStep (a : ℝ≥0) : (a : ℝ≥0∞) ≤ nextStep f r a := by
  unfold nextStep
  split_ifs with hne
  · exact_mod_cast le_csInf hne fun t ht => ht.1
  · exact le_top

lemma norm_lt_of_lt_nextStep {a u : ℝ≥0} (hau : a ≤ u) (hu : (u : ℝ≥0∞) < nextStep f r a) :
    ‖f u - f a‖ < r := by
  by_contra hcon
  exact absurd (nextStep_le_of_mem (f := f) (r := r) ⟨hau, not_lt.1 hcon⟩) (not_le.2 hu)

lemma exists_mem_of_nextStep_lt {a x : ℝ≥0} (h : nextStep f r a < (x : ℝ≥0∞)) :
    ∃ t ∈ stepSet f r a, t < x := by
  unfold nextStep at h
  split_ifs at h with hne
  · obtain ⟨t, ht, hlt⟩ := exists_lt_of_csInf_lt hne (by exact_mod_cast h : sInf (stepSet f r a) < x)
    exact ⟨t, ht, hlt⟩
  · exact absurd h (not_lt.2 le_top)

lemma nextStep_spec (hf : Continuous f) {a : ℝ≥0} (h : nextStep f r a < ⊤) :
    ∃ t : ℝ≥0, nextStep f r a = t ∧ a ≤ t ∧ r ≤ ‖f t - f a‖ ∧
      ∀ u, a ≤ u → u < t → ‖f u - f a‖ < r := by
  have hne : (stepSet f r a).Nonempty := by
    unfold nextStep at h
    split_ifs at h with hne
    · exact hne
    · exact absurd h (lt_irrefl _)
  have hclosed : IsClosed (stepSet f r a) := by
    show IsClosed (Ici a ∩ {t | r ≤ ‖f t - f a‖})
    exact isClosed_Ici.inter (isClosed_le continuous_const ((hf.sub continuous_const).norm))
  have hmem := hclosed.csInf_mem hne (OrderBot.bddBelow _)
  refine ⟨sInf (stepSet f r a), ?_, hmem.1, hmem.2, ?_⟩
  · simp [nextStep, hne]
  · intro u hau hu
    by_contra hcon
    have hmem' : u ∈ stepSet f r a := ⟨hau, not_lt.1 hcon⟩
    exact absurd (csInf_le (s := stepSet f r a) (OrderBot.bddBelow _) hmem') (not_le.2 hu)

@[simp] lemma stepTime_zero : stepTime f r 0 = 0 := rfl

lemma stepTime_succ_of_ne_top {k : ℕ} (h : stepTime f r k ≠ ⊤) :
    stepTime f r (k + 1) = nextStep f r (stepTime f r k).toNNReal := by
  simp [stepTime, h]

lemma stepTime_succ_of_eq_top {k : ℕ} (h : stepTime f r k = ⊤) : stepTime f r (k + 1) = ⊤ := by
  simp [stepTime, h]

lemma stepTime_le_succ (k : ℕ) : stepTime f r k ≤ stepTime f r (k + 1) := by
  by_cases h : stepTime f r k = ⊤
  · rw [stepTime_succ_of_eq_top h]; exact le_top
  · rw [stepTime_succ_of_ne_top h]
    have := le_nextStep (f := f) (r := r) (stepTime f r k).toNNReal
    rwa [ENNReal.coe_toNNReal h] at this

lemma monotone_stepTime : Monotone (stepTime f r) := monotone_nat_of_le_succ stepTime_le_succ

lemma stepTime_succ_spec (hf : Continuous f) (hr : 0 < r) {k : ℕ}
    (h : stepTime f r (k + 1) < ⊤) :
    ∃ a t : ℝ≥0, stepTime f r k = a ∧ stepTime f r (k + 1) = t ∧ a < t ∧ r ≤ ‖f t - f a‖ ∧
      ∀ u, a ≤ u → u < t → ‖f u - f a‖ < r := by
  have hk : stepTime f r k ≠ ⊤ := by
    intro hk
    rw [stepTime_succ_of_eq_top hk] at h
    exact absurd h (lt_irrefl _)
  rw [stepTime_succ_of_ne_top hk] at h
  obtain ⟨t, ht, hat, hrt, hu⟩ := nextStep_spec hf h
  refine ⟨(stepTime f r k).toNNReal, t, (ENNReal.coe_toNNReal hk).symm, ?_, ?_, hrt, hu⟩
  · rw [stepTime_succ_of_ne_top hk]; exact ht
  · refine lt_of_le_of_ne hat ?_
    intro heq
    rw [← heq, sub_self, norm_zero] at hrt
    exact absurd hr (not_lt.2 hrt)

/-- The successive displacement times of a continuous path are unbounded. -/
lemma exists_lt_stepTime (hf : Continuous f) (hr : 0 < r) (L : ℝ≥0) :
    ∃ k, (L : ℝ≥0∞) < stepTime f r k := by
  by_contra hcon
  have hle : ∀ k, stepTime f r k ≤ L := fun k => not_lt.1 fun h => hcon ⟨k, h⟩
  have hfin : ∀ k, stepTime f r k ≠ ⊤ := fun k => ne_top_of_le_ne_top ENNReal.coe_ne_top (hle k)
  set σ : ℕ → ℝ≥0 := fun k => (stepTime f r k).toNNReal with hσ
  have hσle : ∀ k, σ k ≤ L := fun k => by
    have := hle k
    rwa [← ENNReal.coe_toNNReal (hfin k), ENNReal.coe_le_coe] at this
  have hσmono : Monotone σ := fun a b hab =>
    (ENNReal.toNNReal_mono (hfin b) (monotone_stepTime hab))
  have hstep : ∀ k, r ≤ ‖f (σ (k + 1)) - f (σ k)‖ := fun k => by
    obtain ⟨a, t, ha, ht, -, hrt, -⟩ := stepTime_succ_spec hf hr
      (lt_of_le_of_lt (hle (k + 1)) ENNReal.coe_lt_top)
    have h1 : σ k = a := by simp [hσ, ha]
    have h2 : σ (k + 1) = t := by simp [hσ, ht]
    rw [h1, h2]; exact hrt
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Tendsto σ atTop (𝓝 ℓ) :=
    ⟨_, tendsto_atTop_ciSup hσmono ⟨L, by rintro _ ⟨k, rfl⟩; exact hσle k⟩⟩
  have hfσ : Tendsto (fun k => f (σ k)) atTop (𝓝 (f ℓ)) := (hf.tendsto ℓ).comp hℓ
  have hdiff : Tendsto (fun k => f (σ (k + 1)) - f (σ k)) atTop (𝓝 0) := by
    have := (hfσ.comp (tendsto_add_atTop_nat 1)).sub hfσ
    simpa using this
  have hnorm : Tendsto (fun k => ‖f (σ (k + 1)) - f (σ k)‖) atTop (𝓝 0) := by
    exact tendsto_norm_zero.comp hdiff
  obtain ⟨k, hk⟩ := (hnorm.eventually (gt_mem_nhds hr)).exists
  exact absurd (hstep k) (not_le.2 hk)

/-- **Lower count.** If `f` is continuous and its increment over `(j s, (j + 1) s]` has norm at
least `2 r` for every `j` in a finite set `J` of indices below `m`, then the `#J`-th displacement
time of size `r` is at most `m s`. -/
theorem stepTime_card_le (hf : Continuous f) (hr : 0 < r) {s : ℝ≥0} {m : ℕ}
    (J : Finset ℕ) (hJm : ∀ j ∈ J, j < m)
    (hJ : ∀ j ∈ J, 2 * r ≤ ‖f (((j + 1 : ℕ) : ℝ≥0) * s) - f ((j : ℝ≥0) * s)‖) :
    stepTime f r J.card ≤ (((m : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) := by
  have claim : ∀ j ∈ J, ∃ k : ℕ, 1 ≤ k ∧ (((j : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) < stepTime f r k ∧
      stepTime f r k ≤ ((((j + 1 : ℕ) : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) := by
    intro j hj
    classical
    have hex : ∃ k, (((j : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) < stepTime f r k := exists_lt_stepTime hf hr _
    set k := Nat.find hex with hkdef
    have hk : (((j : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) < stepTime f r k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, stepTime_zero] at hk
      exact absurd hk (not_lt.2 bot_le)
    obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hk'le : stepTime f r k' ≤ (((j : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) :=
      not_lt.1 (Nat.find_min hex (by omega : k' < k))
    refine ⟨k, by omega, hk, ?_⟩
    by_contra hcon
    have hgt : ((((j + 1 : ℕ) : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) < stepTime f r k := not_le.1 hcon
    have hfin : stepTime f r k' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hk'le
    have hk1 : stepTime f r (k' + 1) = nextStep f r (stepTime f r k').toNNReal :=
      stepTime_succ_of_ne_top hfin
    have hkk : k = k' + 1 := hk'
    rw [hkk] at hgt hk
    rw [hk1] at hgt hk
    set a := (stepTime f r k').toNNReal with ha
    have haj : a ≤ (j : ℝ≥0) * s := by
      have := hk'le
      rwa [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe] at this
    have hjs : (j : ℝ≥0) * s ≤ ((j + 1 : ℕ) : ℝ≥0) * s := by
      gcongr; exact_mod_cast Nat.le_succ j
    have h1 := norm_lt_of_lt_nextStep (f := f) (r := r) haj hk
    have h2 := norm_lt_of_lt_nextStep (f := f) (r := r) (haj.trans hjs) hgt
    have h3 : ‖f (((j + 1 : ℕ) : ℝ≥0) * s) - f ((j : ℝ≥0) * s)‖ < 2 * r := by
      calc ‖f (((j + 1 : ℕ) : ℝ≥0) * s) - f ((j : ℝ≥0) * s)‖
          = ‖(f (((j + 1 : ℕ) : ℝ≥0) * s) - f a) - (f ((j : ℝ≥0) * s) - f a)‖ := by
            congr 1; abel
        _ ≤ ‖f (((j + 1 : ℕ) : ℝ≥0) * s) - f a‖ + ‖f ((j : ℝ≥0) * s) - f a‖ := norm_sub_le _ _
        _ < r + r := add_lt_add h2 h1
        _ = 2 * r := by ring
    exact absurd (hJ j hj) (not_le.2 h3)
  choose! kf hk1 hkl hku using claim
  classical
  have hinj : Set.InjOn kf (J : Set ℕ) := by
    intro j hj j' hj' hkeq
    have hj1 := hkl j hj
    have hj2 := hku j hj
    have hj1' := hkl j' hj'
    have hj2' := hku j' hj'
    rw [← hkeq] at hj1' hj2'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hle : (((j + 1 : ℕ) : ℝ≥0) * s : ℝ≥0) ≤ (j' : ℝ≥0) * s :=
        by gcongr; exact_mod_cast Nat.succ_le_of_lt hlt
      have : (((j + 1 : ℕ) : ℝ≥0) * s : ℝ≥0) < (((j + 1 : ℕ) : ℝ≥0) * s : ℝ≥0) :=
        ENNReal.coe_lt_coe.1 ((ENNReal.coe_le_coe.2 hle).trans_lt (hj1'.trans_le hj2))
      exact lt_irrefl _ this
    · have hle : (((j' + 1 : ℕ) : ℝ≥0) * s : ℝ≥0) ≤ (j : ℝ≥0) * s :=
        by gcongr; exact_mod_cast Nat.succ_le_of_lt hlt
      have : (((j' + 1 : ℕ) : ℝ≥0) * s : ℝ≥0) < (((j' + 1 : ℕ) : ℝ≥0) * s : ℝ≥0) :=
        ENNReal.coe_lt_coe.1 ((ENNReal.coe_le_coe.2 hle).trans_lt (hj1.trans_le hj2'))
      exact lt_irrefl _ this
  rcases J.eq_empty_or_nonempty with hJe | hJne
  · subst hJe
    simp
  obtain ⟨j₀, hj₀, hsup⟩ := Finset.exists_mem_eq_sup J hJne kf
  have hcard : J.card ≤ J.sup kf := by
    have himg : J.image kf ⊆ Finset.Icc 1 (J.sup kf) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_Icc.2 ⟨hk1 j hj, Finset.le_sup (f := kf) hj⟩
    calc J.card = (J.image kf).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 (J.sup kf)).card := Finset.card_le_card himg
      _ = J.sup kf := by simp
  calc stepTime f r J.card ≤ stepTime f r (J.sup kf) := monotone_stepTime hcard
    _ = stepTime f r (kf j₀) := by rw [hsup]
    _ ≤ ((((j₀ + 1 : ℕ) : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) := hku j₀ hj₀
    _ ≤ (((m : ℝ≥0) * s : ℝ≥0) : ℝ≥0∞) := by
      apply ENNReal.coe_le_coe.2
      gcongr
      exact_mod_cast Nat.succ_le_of_lt (hJm j₀ hj₀)

/-- **Upper count.** If every increment of `f` over a window of length `s` that starts at a time
`≤ T` has norm `< r`, then the `k`-th displacement time of size `r` is at least `min T (k s)`. -/
theorem min_le_stepTime (T s : ℝ≥0)
    (hosc : ∀ t t' : ℝ≥0, t ≤ T → t ≤ t' → t' ≤ t + s → ‖f t' - f t‖ < r) (k : ℕ) :
    min (T : ℝ≥0∞) ((k : ℝ≥0∞) * s) ≤ stepTime f r k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases htop : stepTime f r k = ⊤
    · rw [stepTime_succ_of_eq_top htop]; exact le_top
    by_cases hT : (T : ℝ≥0∞) ≤ stepTime f r k
    · exact (min_le_left _ _).trans (hT.trans (stepTime_le_succ k))
    rw [not_le] at hT
    have hks : (k : ℝ≥0∞) * s ≤ stepTime f r k := by
      by_contra hcon
      exact absurd ih (not_le.2 (lt_min hT (not_le.1 hcon)))
    have hstep : stepTime f r k + s ≤ stepTime f r (k + 1) := by
      rw [stepTime_succ_of_ne_top htop]
      set a := (stepTime f r k).toNNReal with ha
      have haeq : (a : ℝ≥0∞) = stepTime f r k := ENNReal.coe_toNNReal htop
      by_contra hcon
      have hlt : nextStep f r a < ((a + s : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_add, haeq]; exact not_le.1 hcon
      obtain ⟨t, ht, htlt⟩ := exists_mem_of_nextStep_lt hlt
      have haT : a ≤ T := by
        have h1 : (a : ℝ≥0∞) < T := by rw [haeq]; exact hT
        exact (ENNReal.coe_lt_coe.1 h1).le
      exact absurd ht.2 (not_le.2 (hosc a t haT ht.1 htlt.le))
    calc min (T : ℝ≥0∞) (((k + 1 : ℕ) : ℝ≥0∞) * s) ≤ ((k + 1 : ℕ) : ℝ≥0∞) * s := min_le_right _ _
      _ = (k : ℝ≥0∞) * s + s := by push_cast; ring
      _ ≤ stepTime f r k + s := by gcongr
      _ ≤ stepTime f r (k + 1) := hstep

end StepTimes

end LatticeProb
