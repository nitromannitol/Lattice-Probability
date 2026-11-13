import LatticeProb.Analysis.ExcursionCountLadderRational
import LatticeProb.Analysis.ExcursionCountSandwich

/-!
# Measurability of the excursion count of a random continuous path

Let `X : Ω → ℝ → ℝ` be a family of paths on a measurable space `Ω` whose values `ω ↦ X ω q` at rational times `q` are
measurable. For a rational anchor `a`, a level `b`, `ε > 0` and `k : ℕ`, there is a measurable set `S ⊆ Ω` such that,
for every `ω` whose path is continuous, `ω ∈ S` iff at least `k` excursions of `X ω` above its running minimum from
`a`, of length larger than `ε`, are completed before the first passage below `X ω a - b`
(`exists_measurableSet_le_excursionCount`).

No measurability of the set of continuous paths is needed: `S` is a countable combination of conditions on the values
at rational times, and it describes the excursion count correctly at every continuous path. The rational forms used
are the rational witnesses for the excursion count (`le_excursionCount_iff`), the ladder-set conditions at rational
times (`forall_notMem_forwardLadderSet_iff`, `exists_mem_forwardLadderSet_iff`), the running minimum at rational times
(`sInf_image_Icc_eq_iInf_rat_of_le`) and the first-passage time at rational times (`le_firstPassageBelow_iff_rat`,
`exists_passageBelow_iff_rat`).
-/

open Set

namespace LatticeProb.LadderSet

section Deterministic

variable {X : ℝ → ℝ} {a b u : ℝ}

/-- **Passage below a level at rational times.** A continuous path goes below `X a - b` at some time `t ≥ a` iff it
does so at some rational time `q ≥ a`. -/
theorem exists_passageBelow_iff_rat (hX : Continuous X) :
    (∃ s, a ≤ s ∧ X s < X a - b) ↔ ∃ q : ℚ, a ≤ q ∧ X q < X a - b := by
  constructor
  · rintro ⟨s, has, hs⟩
    by_contra h
    push Not at h
    have := le_of_forall_rat_mem_Icc (c := X a - b) hX.continuousOn (by linarith : a < s + 1)
      (fun q hq => h q hq.1) s ⟨has, by linarith⟩
    linarith
  · rintro ⟨q, hq, hlt⟩
    exact ⟨q, hq, hlt⟩

/-- **The first-passage time at rational times.** If a continuous path goes below `X a - b` after `a`, then for
`a < u` the first passage below `X a - b` happens at or after `u` iff `X ≥ X a - b` at the rational points of
`[a, u)`. -/
theorem le_firstPassageBelow_iff_rat (hX : Continuous X) (hne : ∃ s, a ≤ s ∧ X s < X a - b) (hau : a < u) :
    u ≤ firstPassageBelow X a b ↔ ∀ q : ℚ, (q : ℝ) ∈ Ico a u → X a - b ≤ X q := by
  constructor
  · intro hu q hq
    by_contra hlt
    push Not at hlt
    have : firstPassageBelow X a b ≤ q :=
      csInf_le (s := {t | a ≤ t ∧ X t < X a - b}) ⟨a, fun t ht => ht.1⟩ ⟨hq.1, hlt⟩
    linarith [hq.2]
  · intro h
    refine le_csInf hne fun s hs => le_of_not_gt fun hsu => ?_
    have hv : a < max s ((a + u) / 2) := lt_max_of_lt_right (by linarith)
    have hvu : max s ((a + u) / 2) < u := max_lt hsu (by linarith)
    have := le_of_forall_rat_mem_Icc (c := X a - b) hX.continuousOn hv
      (fun q hq => h q ⟨hq.1, hq.2.trans_lt hvu⟩) s ⟨hs.1, le_max_left _ _⟩
    linarith [hs.2]

/-- Without a passage below `X a - b` after `a`, the first-passage time is the junk value `sInf ∅ = 0`. -/
theorem firstPassageBelow_eq_zero_of_not_exists (hne : ¬∃ s, a ≤ s ∧ X s < X a - b) :
    firstPassageBelow X a b = 0 := by
  have : {t | a ≤ t ∧ X t < X a - b} = ∅ := eq_empty_iff_forall_notMem.2 fun t ht => hne ⟨t, ht⟩
  rw [firstPassageBelow, this, Real.sInf_empty]

/-- **The running minimum from a rational anchor at rational times.** For a continuous path and rationals `a ≤ q`,
the infimum of `X` over `[a, q]` is the infimum of `X` over the rational points of `[a, q]`. -/
theorem sInf_image_Icc_eq_iInf_rat_of_le (hX : Continuous X) {a q : ℚ} (haq : (a : ℝ) ≤ q) :
    sInf (X '' Icc (a : ℝ) q) = ⨅ p : {p : ℚ // (p : ℝ) ∈ Icc (a : ℝ) q}, X p := by
  rcases haq.lt_or_eq with h | h
  · exact sInf_image_Icc_eq_iInf_rat hX h
  · have : Nonempty {p : ℚ // (p : ℝ) ∈ Icc (a : ℝ) q} := ⟨⟨q, h.le, le_rfl⟩⟩
    have hc : (fun p : {p : ℚ // (p : ℝ) ∈ Icc (a : ℝ) q} => X p) = fun _ => X q := by
      funext p
      congr 1
      exact le_antisymm p.2.2 (h.symm.trans_le p.2.1)
    rw [hc, ciInf_const, h, Icc_self, image_singleton, csInf_singleton]

end Deterministic

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A predicate on `Ω` agrees on the set `C` with a measurable set. -/
private def AgreesMeasurableOn (C : Set Ω) (P : Ω → Prop) : Prop :=
  ∃ S, MeasurableSet S ∧ ∀ ω ∈ C, (ω ∈ S ↔ P ω)

variable {C : Set Ω} {P Q : Ω → Prop}

private theorem AgreesMeasurableOn.of_measurableSet (h : MeasurableSet {ω | P ω}) : AgreesMeasurableOn C P :=
  ⟨_, h, fun _ _ => Iff.rfl⟩

private theorem AgreesMeasurableOn.const (p : Prop) : AgreesMeasurableOn C fun _ => p :=
  AgreesMeasurableOn.of_measurableSet (MeasurableSet.const p)

private theorem AgreesMeasurableOn.congr (h : AgreesMeasurableOn C P) (hPQ : ∀ ω ∈ C, (P ω ↔ Q ω)) :
    AgreesMeasurableOn C Q := by
  obtain ⟨S, hS, hSP⟩ := h
  exact ⟨S, hS, fun ω hω => (hSP ω hω).trans (hPQ ω hω)⟩

private theorem AgreesMeasurableOn.conj (hP : AgreesMeasurableOn C P) (hQ : AgreesMeasurableOn C Q) :
    AgreesMeasurableOn C fun ω => P ω ∧ Q ω := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ∩ T, hS.inter hT, fun ω hω => and_congr (hSP ω hω) (hTQ ω hω)⟩

private theorem AgreesMeasurableOn.disj (hP : AgreesMeasurableOn C P) (hQ : AgreesMeasurableOn C Q) :
    AgreesMeasurableOn C fun ω => P ω ∨ Q ω := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ∪ T, hS.union hT, fun ω hω => or_congr (hSP ω hω) (hTQ ω hω)⟩

private theorem AgreesMeasurableOn.neg (hP : AgreesMeasurableOn C P) : AgreesMeasurableOn C fun ω => ¬P ω := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨Sᶜ, hS.compl, fun ω hω => not_congr (hSP ω hω)⟩

private theorem AgreesMeasurableOn.iExists {ι : Type*} [Countable ι] {P : ι → Ω → Prop}
    (h : ∀ i, AgreesMeasurableOn C (P i)) : AgreesMeasurableOn C fun ω => ∃ i, P i ω := by
  choose S hS hSP using h
  refine ⟨⋃ i, S i, MeasurableSet.iUnion hS, fun ω hω => ?_⟩
  simp only [mem_iUnion]
  exact exists_congr fun i => hSP i ω hω

private theorem AgreesMeasurableOn.iForall {ι : Type*} [Countable ι] {P : ι → Ω → Prop}
    (h : ∀ i, AgreesMeasurableOn C (P i)) : AgreesMeasurableOn C fun ω => ∀ i, P i ω := by
  choose S hS hSP using h
  refine ⟨⋂ i, S i, MeasurableSet.iInter hS, fun ω hω => ?_⟩
  simp only [mem_iInter]
  exact forall_congr' fun i => hSP i ω hω

private theorem AgreesMeasurableOn.imp (p : Prop) (h : AgreesMeasurableOn C P) :
    AgreesMeasurableOn C fun ω => p → P ω := by
  by_cases hp : p
  · exact AgreesMeasurableOn.congr h fun _ _ => (imp_iff_right hp).symm
  · exact AgreesMeasurableOn.congr (AgreesMeasurableOn.const True) fun _ _ =>
      ⟨fun _ hp' => absurd hp' hp, fun _ => trivial⟩

variable {X : Ω → ℝ → ℝ}

/-- The gap to the running minimum at a rational time, computed from the values at rational times, is measurable. -/
theorem measurable_sub_iInf_rat (hX : ∀ q : ℚ, Measurable fun ω => X ω q) (a q : ℚ) :
    Measurable fun ω => X ω q - ⨅ p : {p : ℚ // (p : ℝ) ∈ Icc (a : ℝ) q}, X ω p :=
  (hX q).sub (Measurable.iInf fun p => hX p.1)

private theorem agrees_forall_notMem (hX : ∀ q : ℚ, Measurable fun ω => X ω q) (a r u : ℚ) (har : (a : ℝ) ≤ r)
    (hru : (r : ℝ) < u) :
    AgreesMeasurableOn {ω | Continuous (X ω)} fun ω => ∀ x ∈ Icc (r : ℝ) u, x ∉ forwardLadderSet (X ω) a := by
  refine AgreesMeasurableOn.congr (P := fun ω => ∃ n : ℕ, ∀ q : ℚ, (q : ℝ) ∈ Icc (r : ℝ) u →
      1 / ((n : ℝ) + 1) ≤ X ω q - ⨅ p : {p : ℚ // (p : ℝ) ∈ Icc (a : ℝ) q}, X ω p) ?_ ?_
  · exact AgreesMeasurableOn.iExists fun n => AgreesMeasurableOn.iForall fun q => AgreesMeasurableOn.imp _
      (AgreesMeasurableOn.of_measurableSet (measurableSet_le measurable_const (measurable_sub_iInf_rat hX a q)))
  · intro ω hω
    rw [forall_notMem_forwardLadderSet_iff hω har hru]
    refine exists_congr fun n => forall_congr' fun q => imp_congr_right fun hq => ?_
    rw [sInf_image_Icc_eq_iInf_rat_of_le hω (har.trans hq.1)]

private theorem agrees_exists_mem (hX : ∀ q : ℚ, Measurable fun ω => X ω q) (a u r : ℚ) (hau : (a : ℝ) ≤ u) :
    AgreesMeasurableOn {ω | Continuous (X ω)} fun ω =>
      ∃ x ∈ forwardLadderSet (X ω) a, (u : ℝ) ≤ x ∧ x ≤ r := by
  rcases lt_trichotomy (u : ℝ) r with hur | hur | hur
  · refine AgreesMeasurableOn.congr (P := fun ω => ∀ n : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc (u : ℝ) r ∧
        X ω q - ⨅ p : {p : ℚ // (p : ℝ) ∈ Icc (a : ℝ) q}, X ω p < 1 / ((n : ℝ) + 1)) ?_ ?_
    · exact AgreesMeasurableOn.iForall fun n => AgreesMeasurableOn.iExists fun q =>
        AgreesMeasurableOn.conj (AgreesMeasurableOn.const _)
          (AgreesMeasurableOn.of_measurableSet (measurableSet_lt (measurable_sub_iInf_rat hX a q) measurable_const))
    · intro ω hω
      rw [exists_mem_forwardLadderSet_iff hω hau hur]
      refine forall_congr' fun n => exists_congr fun q => and_congr_right fun hq => ?_
      rw [sInf_image_Icc_eq_iInf_rat_of_le hω (hau.trans hq.1)]
  · refine AgreesMeasurableOn.congr (P := fun ω => X ω u - ⨅ p : {p : ℚ // (p : ℝ) ∈ Icc (a : ℝ) u}, X ω p = 0)
      (AgreesMeasurableOn.of_measurableSet
        (measurableSet_eq_fun (measurable_sub_iInf_rat hX a u) measurable_const)) ?_
    intro ω hω
    rw [← sInf_image_Icc_eq_iInf_rat_of_le hω hau, ← mem_forwardLadderSet_iff_sub_sInf_eq_zero hω hau]
    constructor
    · intro h
      exact ⟨u, h, le_rfl, hur.le⟩
    · rintro ⟨x, hx, h1, h2⟩
      have hxu : x = u := le_antisymm (h2.trans hur.symm.le) h1
      rwa [hxu] at hx
  · exact AgreesMeasurableOn.congr (AgreesMeasurableOn.const False) fun _ _ =>
      ⟨False.elim, fun ⟨_, _, h1, h2⟩ => absurd (h1.trans h2) (not_le.2 hur)⟩

private theorem agrees_le_firstPassageBelow (hX : ∀ q : ℚ, Measurable fun ω => X ω q) (a u : ℚ) (b : ℝ)
    (hau : (a : ℝ) < u) :
    AgreesMeasurableOn {ω | Continuous (X ω)} fun ω => (u : ℝ) ≤ firstPassageBelow (X ω) a b := by
  have hE : AgreesMeasurableOn {ω | Continuous (X ω)} fun ω => ∃ q : ℚ, (a : ℝ) ≤ q ∧ X ω q < X ω a - b :=
    AgreesMeasurableOn.iExists fun q => AgreesMeasurableOn.conj (AgreesMeasurableOn.const _)
      (AgreesMeasurableOn.of_measurableSet (measurableSet_lt (hX q) ((hX a).sub_const b)))
  refine AgreesMeasurableOn.congr (AgreesMeasurableOn.disj (AgreesMeasurableOn.conj hE
    (AgreesMeasurableOn.iForall fun q : ℚ => AgreesMeasurableOn.imp ((q : ℝ) ∈ Ico (a : ℝ) u)
      (AgreesMeasurableOn.of_measurableSet (measurableSet_le ((hX a).sub_const b) (hX q)))))
    (AgreesMeasurableOn.conj (AgreesMeasurableOn.neg hE) (AgreesMeasurableOn.const ((u : ℝ) ≤ 0)))) ?_
  intro ω hω
  by_cases hne : ∃ s, (a : ℝ) ≤ s ∧ X ω s < X ω a - b
  · have hq := (exists_passageBelow_iff_rat hω).1 hne
    rw [le_firstPassageBelow_iff_rat hω hne hau]
    exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd hq h.1), fun h => Or.inl ⟨hq, h⟩⟩
  · have hq : ¬∃ q : ℚ, (a : ℝ) ≤ q ∧ X ω q < X ω a - b := fun h => hne ((exists_passageBelow_iff_rat hω).2 h)
    rw [firstPassageBelow_eq_zero_of_not_exists hne]
    exact ⟨fun h => h.elim (fun h => absurd h.1 hq) (fun h => h.2), fun h => Or.inr ⟨hq, h⟩⟩

variable (X) in
/-- **Measurability of the excursion count.** Let `X : Ω → ℝ → ℝ` have measurable values `ω ↦ X ω q` at rational
times. For a rational anchor `a`, a level `b`, `ε > 0` and `k : ℕ`, there is a measurable set `S` such that for every
`ω` with a continuous path, `ω ∈ S` iff at least `k` excursions of `X ω` above its running minimum from `a`, of length
larger than `ε`, are completed before the first passage below `X ω a - b`. -/
theorem exists_measurableSet_le_excursionCount (hX : ∀ q : ℚ, Measurable fun ω => X ω q) (a : ℚ) (b ε : ℝ)
    (hε : 0 < ε) (k : ℕ) :
    ∃ S : Set Ω, MeasurableSet S ∧ ∀ ω, Continuous (X ω) →
      (ω ∈ S ↔ k ≤ excursionCount (forwardLadderSet (X ω) a) a (firstPassageBelow (X ω) a b) ε) := by
  suffices h : AgreesMeasurableOn {ω | Continuous (X ω)} fun ω =>
      k ≤ excursionCount (forwardLadderSet (X ω) a) a (firstPassageBelow (X ω) a b) ε by
    obtain ⟨S, hS, hSP⟩ := h
    exact ⟨S, hS, fun ω hω => hSP ω hω⟩
  refine AgreesMeasurableOn.congr (P := fun ω => ∃ r u : Fin k → ℚ,
      (∀ j, (a : ℝ) ≤ r j ∧ (r j : ℝ) + ε < u j ∧ (u j : ℝ) ≤ firstPassageBelow (X ω) a b ∧
        ∀ x ∈ Icc (r j : ℝ) (u j), x ∉ forwardLadderSet (X ω) a) ∧
      ∀ i j, i ≠ j → ∃ x ∈ forwardLadderSet (X ω) a, ((u i : ℝ) ≤ x ∧ x ≤ r j) ∨ ((u j : ℝ) ≤ x ∧ x ≤ r i))
    ?_ fun ω _ => (le_excursionCount_iff hε k).symm
  refine AgreesMeasurableOn.iExists fun r => AgreesMeasurableOn.iExists fun u => ?_
  by_cases hc : ∀ j, (a : ℝ) ≤ r j ∧ (r j : ℝ) + ε < u j
  · have hau : ∀ j, (a : ℝ) < u j := fun j => by linarith [(hc j).1, (hc j).2]
    have hru : ∀ j, (r j : ℝ) < u j := fun j => by linarith [(hc j).2]
    refine AgreesMeasurableOn.congr (P := fun ω =>
        (∀ j, (u j : ℝ) ≤ firstPassageBelow (X ω) a b ∧ ∀ x ∈ Icc (r j : ℝ) (u j), x ∉ forwardLadderSet (X ω) a) ∧
        ∀ i j, i ≠ j → (∃ x ∈ forwardLadderSet (X ω) a, (u i : ℝ) ≤ x ∧ x ≤ r j) ∨
          (∃ x ∈ forwardLadderSet (X ω) a, (u j : ℝ) ≤ x ∧ x ≤ r i))
      (AgreesMeasurableOn.conj
        (AgreesMeasurableOn.iForall fun j => AgreesMeasurableOn.conj
          (agrees_le_firstPassageBelow hX a (u j) b (hau j)) (agrees_forall_notMem hX a (r j) (u j) (hc j).1 (hru j)))
        (AgreesMeasurableOn.iForall fun i => AgreesMeasurableOn.iForall fun j => AgreesMeasurableOn.imp _
          (AgreesMeasurableOn.disj (agrees_exists_mem hX a (u i) (r j) (hau i).le)
            (agrees_exists_mem hX a (u j) (r i) (hau j).le)))) ?_
    intro ω _
    refine and_congr ⟨fun h j => ⟨(hc j).1, (hc j).2, h j⟩, fun h j => (h j).2.2⟩
      (forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ => ?_)
    exact ⟨fun h => h.elim (fun ⟨x, hx, h⟩ => ⟨x, hx, Or.inl h⟩) (fun ⟨x, hx, h⟩ => ⟨x, hx, Or.inr h⟩),
      fun ⟨x, hx, h⟩ => h.elim (fun h => Or.inl ⟨x, hx, h⟩) (fun h => Or.inr ⟨x, hx, h⟩)⟩
  · exact AgreesMeasurableOn.congr (AgreesMeasurableOn.const False) fun _ _ =>
      ⟨False.elim, fun h => hc fun j => ⟨(h.1 j).1, (h.1 j).2.1⟩⟩

end Measurability

end LatticeProb.LadderSet
