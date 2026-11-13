/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.Lemma25TailStopping at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.StrongMarkov
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Markov
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping

/-!
# [18] Lemma 2.5: the record stopping times

Gwynne--Miller, *Harmonic functions on mated-CRT maps*, Lemma 2.5 (source copy
, lines 925--941; corrected proof in
, Details (c1)).

This file is the stopping-time layer of the proof, for an abstract real Brownian motion
`B : ℝ≥0 → Ω → ℝ` with continuous paths and its natural filtration
`QuantumZipper.Williams.pastFilt B`.

For a block `[b, b + 1]` (`b : ℕ`) the *record level* is `inf_{[1, b]} B`, and
`lemma25TailStop B b` is the first time in `[b, b + 1]` at which `B` reaches that level
(`b + 1` if it does not). It is a stopping time (`lemma25Tail_isStoppingTime_stop`): the
hitting time of the closed set `(-∞, 0]` by `s ↦ B (b + s) - inf_{[1, b]} B`, which is adapted to
the filtration shifted by `b`. At this time the strong Markov property gives the uniform
conditional probability of a unit drop of `B` in the next unit of time
(`lemma25Tail_condExp_unitDrop`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Interval infima -/

/-- The infimum of the path `t ↦ B t ω` over the time interval `[a, b]`. -/
def lemma25TailInf (B : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (ω : Ω) : ℝ :=
  sInf ((fun t => B t ω) '' Icc a b)

omit mΩ in
theorem lemma25TailInf_le {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) {a b t : ℝ≥0}
    (ht : t ∈ Icc a b) : lemma25TailInf B a b ω ≤ B t ω :=
  csInf_le ((isCompact_Icc.image hc).bddBelow) ⟨t, ht, rfl⟩

omit mΩ in
theorem lemma25TailInf_exists_eq {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    {a b : ℝ≥0} (hab : a ≤ b) : ∃ t ∈ Icc a b, B t ω = lemma25TailInf B a b ω := by
  have hK : IsCompact ((fun t => B t ω) '' Icc a b) := isCompact_Icc.image hc
  have hne : ((fun t => B t ω) '' Icc a b).Nonempty := ⟨B a ω, a, ⟨le_rfl, hab⟩, rfl⟩
  obtain ⟨t, ht, hval⟩ := hK.sInf_mem hne
  exact ⟨t, ht, hval⟩

omit mΩ in
theorem le_lemma25TailInf {B : ℝ≥0 → Ω → ℝ} {ω : Ω} {a b : ℝ≥0} (hab : a ≤ b) {y : ℝ}
    (hy : ∀ t ∈ Icc a b, y ≤ B t ω) : y ≤ lemma25TailInf B a b ω :=
  le_csInf ⟨B a ω, a, ⟨le_rfl, hab⟩, rfl⟩ (by
    rintro _ ⟨t, ht, rfl⟩
    exact hy t ht)

omit mΩ in
/-- Infima over nested intervals are ordered. -/
theorem lemma25TailInf_anti {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    {a b a' b' : ℝ≥0} (hab : a ≤ b) (ha : a' ≤ a) (hb : b ≤ b') :
    lemma25TailInf B a' b' ω ≤ lemma25TailInf B a b ω :=
  le_lemma25TailInf hab fun _ ht =>
    lemma25TailInf_le hc ⟨ha.trans ht.1, ht.2.trans hb⟩

omit mΩ in
/-- For a continuous function the infimum over a compact interval is the infimum over a dense
subset. -/
theorem lemma25Tail_sInf_image_eq_iInf {f : ℝ≥0 → ℝ} (hf : Continuous f) {a b : ℝ≥0}
    (hab : a ≤ b) {D : Set ℝ≥0} (hD : D ⊆ Icc a b) (hdense : Icc a b ⊆ closure D) :
    sInf (f '' Icc a b) = ⨅ d : D, f d := by
  have hDne : D.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := hdense ⟨le_rfl, hab⟩
    rw [h, closure_empty] at this
    exact this
  have : Nonempty D := hDne.to_subtype
  have hbdd : BddBelow (f '' Icc a b) := (isCompact_Icc.image hf).bddBelow
  have hrange : Set.range (fun d : D => f d) = f '' D := by
    ext y
    simp
  rw [iInf, hrange]
  apply le_antisymm
  · exact csInf_le_csInf hbdd (hDne.image f) (image_mono hD)
  · refine le_csInf ⟨f a, a, ⟨le_rfl, hab⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxcl : f x ∈ closure (f '' D) := image_closure_subset_closure_image hf ⟨x, hdense hx, rfl⟩
    have hclosed : IsClosed {z : ℝ | sInf (f '' D) ≤ z} := isClosed_le continuous_const continuous_id
    have hsub : f '' D ⊆ {z : ℝ | sInf (f '' D) ≤ z} := fun z hz =>
      csInf_le (hbdd.mono (image_mono hD)) hz
    exact (hclosed.closure_subset_iff.mpr hsub) hxcl

/-! ### The natural filtration -/

section Filtration

variable {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t))

theorem lemma25Tail_measurable_eval_pastFilt {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[QuantumZipper.Williams.pastFilt B hBm t] (B s) := by
  change Measurable[MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi]
    (B s)
  have h : Measurable[MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi]
      (fun ω (r : Set.Iic t) => B r ω) := comap_measurable _
  exact (measurable_pi_apply (⟨s, hst⟩ : Set.Iic t)).comp h

/-- The interval infimum `inf_{[a, b]} B` is measurable for the past up to time `b`. -/
theorem lemma25Tail_measurable_inf_pastFilt (hBc : ∀ ω, Continuous (B · ω)) {a b : ℝ≥0}
    (hab : a ≤ b) :
    Measurable[QuantumZipper.Williams.pastFilt B hBm b] (lemma25TailInf B a b) := by
  obtain ⟨D, hDc, hDsub, hDdense⟩ := TopologicalSpace.exists_countable_dense_subset (Icc a b)
  have : Countable D := hDc.to_subtype
  have heq : lemma25TailInf B a b = fun ω => ⨅ d : D, B d ω := by
    funext ω
    exact lemma25Tail_sInf_image_eq_iInf (hBc ω) hab hDsub hDdense
  rw [heq]
  exact Measurable.iInf fun d => lemma25Tail_measurable_eval_pastFilt hBm (hDsub d.2).2

theorem lemma25Tail_adapted_pastFilt :
    Adapted (QuantumZipper.Williams.pastFilt B hBm) B := fun _ =>
  lemma25Tail_measurable_eval_pastFilt hBm le_rfl

end Filtration

/-! ### Stopping-time arithmetic on `ℝ≥0` -/

/-- The filtration shifted by `t₀`: `s ↦ F (t₀ + s)`. -/
def lemma25TailShiftFilt (F : Filtration ℝ≥0 mΩ) (t₀ : ℝ≥0) : Filtration ℝ≥0 mΩ where
  seq s := F (t₀ + s)
  mono' _ _ hst := F.mono (add_le_add_right hst t₀)
  le' s := F.le (t₀ + s)

theorem lemma25TailShiftFilt_apply (F : Filtration ℝ≥0 mΩ) (t₀ s : ℝ≥0) :
    lemma25TailShiftFilt F t₀ s = F (t₀ + s) := rfl

/-- A stopping time of the shifted filtration, translated by `t₀`, is a stopping time. -/
theorem lemma25Tail_isStoppingTime_of_shift {F : Filtration ℝ≥0 mΩ} {t₀ : ℝ≥0} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (lemma25TailShiftFilt F t₀) (fun ω => (σ ω : WithTop ℝ≥0))) :
    IsStoppingTime F (fun ω => ((t₀ + σ ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro u
  by_cases h : t₀ ≤ u
  · have hset : {ω | ((t₀ + σ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
        {ω | (σ ω : WithTop ℝ≥0) ≤ ((u - t₀ : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
      rw [add_comm]
      exact (le_tsub_iff_right h).symm
    rw [hset]
    have hm := hσ (u - t₀)
    rw [lemma25TailShiftFilt_apply, add_tsub_cancel_of_le h] at hm
    exact hm
  · have hset : {ω | ((t₀ + σ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, Set.mem_empty_iff_false, iff_false,
        not_le]
      exact lt_of_lt_of_le (not_le.mp h) le_self_add
    rw [hset]
    exact @MeasurableSet.empty _ (F u)

/-- A finite stopping time plus a constant is a stopping time. -/
theorem lemma25Tail_isStoppingTime_add_const {F : Filtration ℝ≥0 mΩ} {T : Ω → ℝ≥0}
    (hT : IsStoppingTime F (fun ω => (T ω : WithTop ℝ≥0))) (c : ℝ≥0) :
    IsStoppingTime F (fun ω => ((T ω + c : ℝ≥0) : WithTop ℝ≥0)) := by
  intro u
  by_cases hcu : c ≤ u
  · have hset : {ω | ((T ω + c : ℝ≥0) : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
        {ω | (T ω : WithTop ℝ≥0) ≤ ((u - c : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
      exact (le_tsub_iff_right hcu).symm
    rw [hset]
    exact F.mono tsub_le_self _ (hT _)
  · have hset : {ω | ((T ω + c : ℝ≥0) : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, Set.mem_empty_iff_false, iff_false,
        not_le]
      exact lt_of_lt_of_le (not_le.mp hcu) le_add_self
    rw [hset]
    exact @MeasurableSet.empty _ (F u)

/-- The value of a continuous adapted process at a finite stopping time is measurable for the
stopped σ-algebra. -/
theorem lemma25Tail_measurable_stoppedValue {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : Adapted F X) (hXc : ∀ ω, Continuous (X · ω)) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime F (fun ω => (T ω : WithTop ℝ≥0))) :
    Measurable[hT.measurableSpace] (fun ω => X (T ω) ω) := by
  have hprog : IsStronglyProgressive F X :=
    hX.stronglyAdapted.isStronglyProgressive_of_continuous hXc
  have h := measurable_stoppedValue hprog hT
  convert h using 1
  funext ω
  simp only [stoppedValue, QuantumZipper.ItoLite.untopA_coe_nnreal]

/-! ### The record stopping time of a block -/

section Record

variable {B : ℝ≥0 → Ω → ℝ}

/-- The record level of the block `[b, b + 1]`: the running minimum `inf_{[1, b]} B`. -/
def lemma25TailLevel (B : ℝ≥0 → Ω → ℝ) (b : ℕ) (ω : Ω) : ℝ :=
  lemma25TailInf B 1 b ω

/-- The gap `s ↦ B (b + s) - inf_{[1, b]} B` between the path in the block `[b, b + 1]` and the
record level. -/
def lemma25TailGap (B : ℝ≥0 → Ω → ℝ) (b : ℕ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  B ((b : ℝ≥0) + s) ω - lemma25TailLevel B b ω

/-- The first time in `[0, 1]` at which the gap is `≤ 0` (`1` if there is none). -/
def lemma25TailHit (B : ℝ≥0 → Ω → ℝ) (b : ℕ) (ω : Ω) : ℝ≥0 :=
  hittingBtwn (lemma25TailGap B b) (Iic 0) 0 1 ω

/-- **The record stopping time of the block `[b, b + 1]`**: the first time in the block at which
`B` reaches the record level `inf_{[1, b]} B` (`b + 1` if it does not). -/
def lemma25TailStop (B : ℝ≥0 → Ω → ℝ) (b : ℕ) (ω : Ω) : ℝ≥0 :=
  (b : ℝ≥0) + lemma25TailHit B b ω

omit mΩ in
theorem lemma25TailStop_mem (b : ℕ) (ω : Ω) :
    lemma25TailStop B b ω ∈ Icc (b : ℝ≥0) (b + 1) := by
  have h := hittingBtwn_mem_Icc (u := lemma25TailGap B b) (s := Iic (0 : ℝ))
    (zero_le_one' ℝ≥0) ω
  exact ⟨le_self_add, add_le_add_right h.2 _⟩

omit mΩ in
/-- If the path reaches the record level somewhere in the block, it is at or below the level at
the record stopping time. -/
theorem lemma25TailStop_le_level {ω : Ω} (hc : Continuous (B · ω)) {b : ℕ}
    (h : ∃ t ∈ Icc (b : ℝ≥0) (b + 1), B t ω ≤ lemma25TailLevel B b ω) :
    B (lemma25TailStop B b ω) ω ≤ lemma25TailLevel B b ω := by
  obtain ⟨t, ht, hle⟩ := h
  have hex : ∃ j ∈ Icc (0 : ℝ≥0) 1, lemma25TailGap B b j ω ∈ Iic (0 : ℝ) := by
    refine ⟨t - b, ⟨zero_le, ?_⟩, ?_⟩
    · exact tsub_le_iff_left.mpr ht.2
    · simp only [lemma25TailGap, Set.mem_Iic, add_tsub_cancel_of_le ht.1]
      linarith
  set S : Set ℝ≥0 := Icc 0 1 ∩ {s | lemma25TailGap B b s ω ∈ Iic (0 : ℝ)} with hS
  have hgc : Continuous fun s : ℝ≥0 => lemma25TailGap B b s ω :=
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_Iic.preimage hgc)
  have hSne : S.Nonempty := by
    obtain ⟨j, hj, hjK⟩ := hex
    exact ⟨j, hj, hjK⟩
  have hmem := hSc.csInf_mem hSne (OrderBot.bddBelow S)
  have heq : lemma25TailHit B b ω = sInf S := by
    simp only [lemma25TailHit, hittingBtwn, hex, ↓reduceIte, hS]
  have hgap : lemma25TailGap B b (lemma25TailHit B b ω) ω ≤ 0 := by
    rw [heq]
    exact hmem.2
  simp only [lemma25TailGap] at hgap
  simp only [lemma25TailStop]
  linarith

variable (hBm : ∀ t, Measurable (B t))

/-- The record stopping time is a stopping time of the natural filtration of `B`. -/
theorem lemma25Tail_isStoppingTime_stop (hBc : ∀ ω, Continuous (B · ω)) {b : ℕ} (hb : 1 ≤ b) :
    IsStoppingTime (QuantumZipper.Williams.pastFilt B hBm)
      (fun ω => (lemma25TailStop B b ω : WithTop ℝ≥0)) := by
  set F := QuantumZipper.Williams.pastFilt B hBm
  have hb' : (1 : ℝ≥0) ≤ b := by exact_mod_cast hb
  have hlev : Measurable[F b] (lemma25TailLevel B b) :=
    lemma25Tail_measurable_inf_pastFilt hBm hBc hb'
  have hAd : Adapted (lemma25TailShiftFilt F b) (lemma25TailGap B b) := by
    intro s
    change Measurable[F ((b : ℝ≥0) + s)] fun ω => B ((b : ℝ≥0) + s) ω - lemma25TailLevel B b ω
    exact (lemma25Tail_measurable_eval_pastFilt hBm le_rfl).sub
      (hlev.mono (F.mono le_self_add) le_rfl)
  have hgc : ∀ ω, Continuous fun s : ℝ≥0 => lemma25TailGap B b s ω := fun ω =>
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hσ := QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed hAd hgc
    (isClosed_Iic (a := (0 : ℝ))) 1
  exact lemma25Tail_isStoppingTime_of_shift hσ

end Record

/-! ### The unit drop after a stopping time -/

/-- The probability that a standard Gaussian is below `-1`. -/
def lemma25TailDropProb : ℝ := (gaussianReal 0 1 (Iio (-1 : ℝ))).toReal

theorem lemma25TailDropProb_pos : 0 < lemma25TailDropProb := by
  have hvol : volume (Ioo (-2 : ℝ) (-1)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  have habs := gaussianReal_absolutelyContinuous' (μ := 0) (v := (1 : ℝ≥0)) (by norm_num)
  have hne : gaussianReal 0 1 (Ioo (-2 : ℝ) (-1)) ≠ 0 := by
    intro hzero
    exact hvol (habs hzero)
  have hpos : 0 < gaussianReal 0 1 (Iio (-1 : ℝ)) :=
    lt_of_lt_of_le (pos_iff_ne_zero.mpr hne) (measure_mono fun x hx => hx.2)
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)

theorem lemma25TailDropProb_le_one : lemma25TailDropProb ≤ 1 := by
  unfold lemma25TailDropProb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    rw [ENNReal.ofReal_one]
    exact prob_le_one)

/-- **Strong Markov property, unit drop.** At every finite stopping time `T` of the natural
filtration, the conditional probability given `𝓕_T` that `B (T + 1) - B T < -1` is the fixed
Gaussian probability `lemma25TailDropProb`. -/
theorem lemma25Tail_condExp_unitDrop {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (QuantumZipper.Williams.pastFilt B hBm)
      (fun ω => (T ω : WithTop ℝ≥0))) :
    P[{ω | B (T ω + 1) ω - B (T ω) ω < -1}.indicator (fun _ => (1 : ℝ)) |
        hT.measurableSpace] =ᵐ[P] fun _ => lemma25TailDropProb := by
  have hind := QuantumZipper.StrongMarkov.indep_smPath hB hBc hBm
    (fun t => QuantumZipper.StrongMarkov.indep_shift_of_le_past hB (fun _ => le_rfl) t) hT
  have hle₁ : hT.measurableSpace ≤ mΩ := hT.measurableSpace_le
  have hshift : Measurable (QuantumZipper.StrongMarkov.smPath B T) :=
    QuantumZipper.StrongMarkov.measurable_smPath hBc hBm
      (QuantumZipper.StrongMarkov.measurable_of_isStoppingTime hT)
  have hle₂ : MeasurableSpace.comap (QuantumZipper.StrongMarkov.smPath B T)
      MeasurableSpace.pi ≤ mΩ := hshift.comap_le
  let A : Set Ω := {ω | B (T ω + 1) ω - B (T ω) ω < -1}
  have hA₂ : MeasurableSet[MeasurableSpace.comap
      (QuantumZipper.StrongMarkov.smPath B T) MeasurableSpace.pi] A := by
    change MeasurableSet[MeasurableSpace.comap
      (QuantumZipper.StrongMarkov.smPath B T) MeasurableSpace.pi]
        ((fun ω => QuantumZipper.StrongMarkov.smPath B T ω 1) ⁻¹' Iio (-1 : ℝ))
    exact measurableSet_preimage
      ((measurable_pi_apply (1 : ℝ≥0)).comp
        (comap_measurable (QuantumZipper.StrongMarkov.smPath B T))) measurableSet_Iio
  have hAm : MeasurableSet A := hle₂ _ hA₂
  have hf : StronglyMeasurable[MeasurableSpace.comap
      (QuantumZipper.StrongMarkov.smPath B T) MeasurableSpace.pi]
      (A.indicator (fun _ : Ω => (1 : ℝ))) :=
    (measurable_const.indicator hA₂).stronglyMeasurable
  have hInd := MeasureTheory.condExp_indep_eq
    (m₁ := MeasurableSpace.comap (QuantumZipper.StrongMarkov.smPath B T) MeasurableSpace.pi)
    (m₂ := hT.measurableSpace) (m := mΩ) hle₂ hle₁ hf hind.symm
  have hPost := QuantumZipper.StrongMarkov.isBrownianReal_smShift hB hBc hBm
    (fun t => QuantumZipper.StrongMarkov.indep_shift_of_le_past hB (fun _ => le_rfl) t) hT
  have hEval := QuantumZipper.StrongMarkov.measurable_smShift hBc hBm
    (QuantumZipper.StrongMarkov.measurable_of_isStoppingTime hT) (1 : ℝ≥0)
  have hlaw := hPost.toIsPreBrownianReal.hasLaw_eval (1 : ℝ≥0)
  have hp : P A = gaussianReal 0 1 (Iio (-1 : ℝ)) := by
    calc P A = P ((fun ω => QuantumZipper.StrongMarkov.smShift B T 1 ω) ⁻¹' Iio (-1 : ℝ)) := rfl
      _ = (P.map (fun ω => QuantumZipper.StrongMarkov.smShift B T 1 ω)) (Iio (-1 : ℝ)) :=
          (Measure.map_apply hEval measurableSet_Iio).symm
      _ = gaussianReal 0 1 (Iio (-1 : ℝ)) := by
          rw [hlaw.map_eq]
  have hint : ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P = lemma25TailDropProb := by
    calc ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P
        = P.real A := by
          change ∫ ω, A.indicator (1 : Ω → ℝ) ω ∂P = P.real A
          exact integral_indicator_one hAm
      _ = lemma25TailDropProb := by
        rw [MeasureTheory.Measure.real_def, hp]
        rfl
  filter_upwards [hInd] with ω hω
  rw [hω, hint]

end MatedCRTHarmonic.MatedCRT
