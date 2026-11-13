/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.Lemma25TailCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.Lemma25TailStopping
import LatticeProb.Bonanno.MatedCRTHarmonic.Brownian.OneStep
import LatticeProb.Bonanno.LQGMetric.Prob.BinomialDomination
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation

/-!
# [18] Lemma 2.5: the exponential tail of the record-block count

Gwynne--Miller, *Harmonic functions on mated-CRT maps*, Lemma 2.5 (source copy
, lines 925--941; corrected proof in
, Details (c1)).

For a real Brownian motion `B` (continuous paths) let `m₀ = inf_{[0,1]} B`. A block
`[b, b + 1]`, `b ≥ 2`, is *counted* if `m₀ ∨ inf_{[b, b+1]} B ≤ inf_{[1, b]} B`; after the
affine change of time `t ↦ ε (x - 1) + ε t` this is exactly the side condition (1.1) of an edge
between `x` and `x + b` (and similarly to the left after time reversal), so the number of counted
blocks bounds one quarter of the degree. This file proves
`P[#counted blocks > n] ≤ 10 e^{-c n}` with an absolute constant `c > 0`
(`lemma25Tail_count_tail`).

Proof with the non-strict side condition. Fix a parity class `c ∈ {0, 1}` and use the
blocks `b_j = 2 j + 2 + c`. At the record stopping time `τ_j` of the block `b_j`
(`lemma25TailStop`, a stopping time of the natural filtration) the strong Markov property gives
`P[B (τ_j + 1) - B τ_j < -1 | 𝓕_{τ_j}] = p := P[N(0,1) < -1]`. Since `τ_j + 1 ≤ b_{j+1} ≤ τ_{j+1}`,
these are trials adapted to the discrete filtration `𝓕_{τ_j}`. A counted block reaches its
record level at `τ_j`, and a success then lowers the record level by more than `1`; the record
level of a counted block is at least `m₀` and at most `B 1`. Hence among counted blocks of one
parity there are at most `B 1 - m₀ + 1` successes, and the binomial-domination bound
(`LQGMetric.measureReal_binomDom_le`) together with the Gaussian tail of the oscillation of `B`
on `[0, 1]` gives the exponential tail.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-! ### Counted blocks -/

/-- The block `[b, b + 1]` is *counted*: `inf_{[0,1]} B ∨ inf_{[b, b+1]} B ≤ inf_{[1, b]} B`
(the side condition (1.1) of [18] after an affine change of time). -/
def lemma25TailCounted (B : ℝ≥0 → Ω → ℝ) (b : ℕ) (ω : Ω) : Prop :=
  max (lemma25TailInf B 0 1 ω) (lemma25TailInf B b (b + 1) ω) ≤ lemma25TailInf B 1 b ω

/-- The number of counted blocks `[b, b + 1]`, `b ≥ 2`. -/
def lemma25TailCount (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℕ∞ :=
  {b : ℕ | 2 ≤ b ∧ lemma25TailCounted B b ω}.encard

/-! ### The trials of one parity class -/

/-- The block of the `j`-th trial of the parity class `c`: `b_j = 2 j + 2 + c`. -/
def lemma25TailBlock (c j : ℕ) : ℕ := 2 * j + 2 + c

/-- The stopping time of the `j`-th trial of the parity class `c`. -/
def lemma25TailTrialTime (B : ℝ≥0 → Ω → ℝ) (c j : ℕ) (ω : Ω) : ℝ≥0 :=
  lemma25TailStop B (lemma25TailBlock c j) ω

/-- The `j`-th trial is *selected* if the path reaches the record level at the trial time and
the record level is still at least `inf_{[0,1]} B`. -/
def lemma25TailSel (B : ℝ≥0 → Ω → ℝ) (c j : ℕ) : Set Ω :=
  {ω | B (lemma25TailTrialTime B c j ω) ω ≤ lemma25TailLevel B (lemma25TailBlock c j) ω ∧
    lemma25TailInf B 0 1 ω ≤ lemma25TailLevel B (lemma25TailBlock c j) ω}

/-- The `j`-th trial *succeeds* if `B` drops by more than `1` in the unit of time after the
trial time. -/
def lemma25TailSucc (B : ℝ≥0 → Ω → ℝ) (c j : ℕ) : Set Ω :=
  {ω | B (lemma25TailTrialTime B c j ω + 1) ω - B (lemma25TailTrialTime B c j ω) ω < -1}

omit mΩ in
theorem lemma25TailTrialTime_mem (c j : ℕ) (ω : Ω) :
    lemma25TailTrialTime B c j ω ∈
      Icc (lemma25TailBlock c j : ℝ≥0) (lemma25TailBlock c j + 1) :=
  lemma25TailStop_mem _ ω

omit mΩ in
theorem lemma25TailTrialTime_mono (c : ℕ) {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    lemma25TailTrialTime B c i ω ≤ lemma25TailTrialTime B c j ω := by
  rcases hij.lt_or_eq with hlt | rfl
  · have h1 := (lemma25TailTrialTime_mem (B := B) c i ω).2
    have h2 := (lemma25TailTrialTime_mem (B := B) c j ω).1
    have hb : (lemma25TailBlock c i : ℝ≥0) + 1 ≤ lemma25TailBlock c j := by
      have : lemma25TailBlock c i + 1 ≤ lemma25TailBlock c j := by
        unfold lemma25TailBlock
        omega
      exact_mod_cast this
    exact h1.trans (hb.trans h2)
  · exact le_rfl

omit mΩ in
theorem lemma25TailTrialTime_add_one_le (c j : ℕ) (ω : Ω) :
    lemma25TailTrialTime B c j ω + 1 ≤ lemma25TailTrialTime B c (j + 1) ω := by
  have h1 := (lemma25TailTrialTime_mem (B := B) c j ω).2
  have h2 := (lemma25TailTrialTime_mem (B := B) c (j + 1) ω).1
  have hb : (lemma25TailBlock c j : ℝ≥0) + 1 + 1 ≤ lemma25TailBlock c (j + 1) := by
    have : lemma25TailBlock c j + 1 + 1 ≤ lemma25TailBlock c (j + 1) := by
      unfold lemma25TailBlock
      omega
    exact_mod_cast this
  exact (add_le_add h1 (le_refl 1)).trans (hb.trans h2)

/-! ### Deterministic bookkeeping -/

section Deterministic

variable {ω : Ω} (hc : Continuous (B · ω))
include hc

omit mΩ in
/-- A counted block is a selected trial. -/
theorem lemma25Tail_mem_sel_of_counted {c j : ℕ}
    (h : lemma25TailCounted B (lemma25TailBlock c j) ω) : ω ∈ lemma25TailSel B c j := by
  set b := lemma25TailBlock c j
  have h1 : lemma25TailInf B 0 1 ω ≤ lemma25TailLevel B b ω := (le_max_left _ _).trans h
  have h2 : lemma25TailInf B b (b + 1) ω ≤ lemma25TailLevel B b ω := (le_max_right _ _).trans h
  obtain ⟨t, ht, hval⟩ := lemma25TailInf_exists_eq hc (le_self_add : (b : ℝ≥0) ≤ b + 1)
  refine ⟨lemma25TailStop_le_level hc ⟨t, ?_, ?_⟩, h1⟩
  · exact_mod_cast ht
  · rw [hval]
    exact_mod_cast h2

omit mΩ in
/-- The record levels decrease along the trials. -/
theorem lemma25Tail_level_succ_le (c j : ℕ) :
    lemma25TailLevel B (lemma25TailBlock c (j + 1)) ω ≤
      lemma25TailLevel B (lemma25TailBlock c j) ω := by
  have hb1 : (1 : ℝ≥0) ≤ lemma25TailBlock c j := by
    have : 1 ≤ lemma25TailBlock c j := by
      unfold lemma25TailBlock
      omega
    exact_mod_cast this
  have hbb : (lemma25TailBlock c j : ℝ≥0) ≤ lemma25TailBlock c (j + 1) := by
    have : lemma25TailBlock c j ≤ lemma25TailBlock c (j + 1) := by
      unfold lemma25TailBlock
      omega
    exact_mod_cast this
  exact lemma25TailInf_anti hc hb1 le_rfl hbb

omit mΩ in
/-- A success at a selected trial lowers the record level by more than `1`. -/
theorem lemma25Tail_level_drop {c j : ℕ} (hG : ω ∈ lemma25TailSel B c j)
    (hA : ω ∈ lemma25TailSucc B c j) :
    lemma25TailLevel B (lemma25TailBlock c (j + 1)) ω <
      lemma25TailLevel B (lemma25TailBlock c j) ω - 1 := by
  have hmem := lemma25TailTrialTime_mem (B := B) c j ω
  have hT1 : lemma25TailTrialTime B c j ω + 1 ∈
      Icc (1 : ℝ≥0) (lemma25TailBlock c (j + 1)) := by
    constructor
    · exact le_add_self
    · have hb : (lemma25TailBlock c j : ℝ≥0) + 1 + 1 ≤ lemma25TailBlock c (j + 1) := by
        have : lemma25TailBlock c j + 1 + 1 ≤ lemma25TailBlock c (j + 1) := by
          unfold lemma25TailBlock
          omega
        exact_mod_cast this
      exact (add_le_add hmem.2 (le_refl 1)).trans hb
  have hle := lemma25TailInf_le hc hT1
  have hA' : B (lemma25TailTrialTime B c j ω + 1) ω - B (lemma25TailTrialTime B c j ω) ω < -1 :=
    hA
  have hG' := hG.1
  unfold lemma25TailLevel at hG' ⊢
  linarith

omit mΩ in
theorem lemma25Tail_level_zero_le (c : ℕ) :
    lemma25TailLevel B (lemma25TailBlock c 0) ω ≤ B 1 ω := by
  have h1 : (1 : ℝ≥0) ≤ lemma25TailBlock c 0 := by
    have : 1 ≤ lemma25TailBlock c 0 := by
      unfold lemma25TailBlock
      omega
    exact_mod_cast this
  exact lemma25TailInf_le hc ⟨le_rfl, h1⟩

omit mΩ in
theorem lemma25Tail_initInf_le :
    lemma25TailInf B 0 1 ω ≤ B 1 ω :=
  lemma25TailInf_le hc ⟨zero_le, le_rfl⟩

omit mΩ in
/-- **The success count.** Among the first `n` trials of one parity class, at most
`B 1 - inf_{[0,1]} B + 1` are selected and successful. -/
theorem lemma25Tail_hits_le (c n : ℕ) :
    LQGMetric.binomDomHits (lemma25TailSel B c) (lemma25TailSucc B c) n ω ≤
      B 1 ω - lemma25TailInf B 0 1 ω + 1 := by
  set L : ℕ → ℝ := fun j => lemma25TailLevel B (lemma25TailBlock c j) ω
  set H : ℕ → ℝ := fun n =>
    LQGMetric.binomDomHits (lemma25TailSel B c) (lemma25TailSucc B c) n ω
  have hstep : ∀ n, H (n + 1) =
      H n + (lemma25TailSel B c n ∩ lemma25TailSucc B c n).indicator 1 ω := by
    intro n
    simp only [H, LQGMetric.binomDomHits, Finset.sum_range_succ]
  have key : ∀ n, L n + H n ≤ L 0 ∧ H n ≤ B 1 ω - lemma25TailInf B 0 1 ω + 1 := by
    intro n
    induction n with
    | zero =>
      have h0 : H 0 = 0 := by simp [H, LQGMetric.binomDomHits]
      rw [h0]
      have := lemma25Tail_initInf_le hc
      constructor <;> linarith
    | succ n ih =>
      rw [hstep n]
      by_cases hmem : ω ∈ lemma25TailSel B c n ∩ lemma25TailSucc B c n
      · rw [Set.indicator_of_mem hmem, Pi.one_apply]
        have hdrop := lemma25Tail_level_drop hc hmem.1 hmem.2
        have hsel := hmem.1.2
        have hL0 := lemma25Tail_level_zero_le hc c
        change L (n + 1) < L n - 1 at hdrop
        change lemma25TailInf B 0 1 ω ≤ L n at hsel
        change L 0 ≤ B 1 ω at hL0
        constructor <;> linarith [ih.1]
      · rw [Set.indicator_of_notMem hmem]
        have hmono := lemma25Tail_level_succ_le hc c n
        change L (n + 1) ≤ L n at hmono
        constructor <;> linarith [ih.1, ih.2]
  exact (key n).2

end Deterministic

omit mΩ in
/-- **The selected count.** If more than `n` blocks are counted, then for some horizon `N` and
some parity class `c`, at least `(n + 1) / 2` of the first `N` trials of the class are
selected. -/
theorem lemma25Tail_exists_count_ge {ω : Ω} (hc : Continuous (B · ω)) {n : ℕ}
    (h : (n : ℕ∞) < lemma25TailCount B ω) :
    ∃ N : ℕ, ((n : ℝ) + 1) ≤ 2 * LQGMetric.binomDomCount (lemma25TailSel B 0) N ω ∨
      ((n : ℝ) + 1) ≤ 2 * LQGMetric.binomDomCount (lemma25TailSel B 1) N ω := by
  classical
  set S : Set ℕ := {b : ℕ | 2 ≤ b ∧ lemma25TailCounted B b ω}
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ S.encard := by
    have := Order.add_one_le_of_lt h
    exact_mod_cast this
  obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_encard_eq hle
  have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard
  set Tf := hTfin.toFinset
  have hTf_card : Tf.card = n + 1 := by
    have h1 : (Tf : Set ℕ) = T := hTfin.coe_toFinset
    have h2 : ((Tf : Set ℕ)).encard = (Tf.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard Tf
    rw [h1, hTcard] at h2
    exact_mod_cast h2.symm
  set N : ℕ := Tf.sup id + 1
  let J : ℕ → Finset ℕ := fun c =>
    (range N).filter (fun j => lemma25TailCounted B (lemma25TailBlock c j) ω)
  have hcover : Tf ⊆ (J 0).image (lemma25TailBlock 0) ∪ (J 1).image (lemma25TailBlock 1) := by
    intro b hb
    have hbT : b ∈ T := hTfin.mem_toFinset.mp hb
    have hbS := hTS hbT
    have hbN : b < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hb)
    have h2b : 2 ≤ b := hbS.1
    rcases Nat.even_or_odd (b - 2) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hbk : b = lemma25TailBlock 0 k := by
        unfold lemma25TailBlock
        omega
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, ?_, hbk.symm⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      rw [← hbk]
      exact hbS.2
    · have hbk : b = lemma25TailBlock 1 k := by
        unfold lemma25TailBlock
        omega
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, ?_, hbk.symm⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      rw [← hbk]
      exact hbS.2
  have hcard : n + 1 ≤ (J 0).card + (J 1).card := by
    rw [← hTf_card]
    calc Tf.card ≤ ((J 0).image (lemma25TailBlock 0) ∪ (J 1).image (lemma25TailBlock 1)).card :=
          Finset.card_le_card hcover
      _ ≤ ((J 0).image (lemma25TailBlock 0)).card + ((J 1).image (lemma25TailBlock 1)).card :=
          Finset.card_union_le _ _
      _ ≤ (J 0).card + (J 1).card := add_le_add Finset.card_image_le Finset.card_image_le
  have hcount : ∀ c, ((J c).card : ℝ) ≤ LQGMetric.binomDomCount (lemma25TailSel B c) N ω := by
    intro c
    unfold LQGMetric.binomDomCount
    calc ((J c).card : ℝ) = ∑ k ∈ J c, (lemma25TailSel B c k).indicator (1 : Ω → ℝ) ω := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hsel := lemma25Tail_mem_sel_of_counted hc (Finset.mem_filter.mp hk).2
          rw [Set.indicator_of_mem hsel, Pi.one_apply]
      _ ≤ ∑ k ∈ range N, (lemma25TailSel B c k).indicator (1 : Ω → ℝ) ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun k _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have hcard' : (n : ℝ) + 1 ≤ (J 0).card + (J 1).card := by exact_mod_cast hcard
  by_cases h01 : LQGMetric.binomDomCount (lemma25TailSel B 1) N ω ≤
      LQGMetric.binomDomCount (lemma25TailSel B 0) N ω
  · exact ⟨N, Or.inl (by linarith [hcount 0, hcount 1])⟩
  · exact ⟨N, Or.inr (by linarith [hcount 0, hcount 1])⟩

/-! ### The probabilistic estimate -/

section Probability

variable (hBm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (B · ω))
include hBc

theorem lemma25Tail_isStoppingTime_trial (c j : ℕ) :
    IsStoppingTime (QuantumZipper.Williams.pastFilt B hBm)
      (fun ω => (lemma25TailTrialTime B c j ω : WithTop ℝ≥0)) :=
  lemma25Tail_isStoppingTime_stop hBm hBc (by unfold lemma25TailBlock; omega)

/-- The discrete filtration `j ↦ 𝓕_{τ_j}` of the trial times of the parity class `c`. -/
def lemma25TailTrialFilt (c : ℕ) : Filtration ℕ mΩ where
  seq j := (lemma25Tail_isStoppingTime_trial hBm hBc c j).measurableSpace
  mono' _ _ hij := IsStoppingTime.measurableSpace_mono _ _
    (fun ω => WithTop.coe_le_coe.mpr (lemma25TailTrialTime_mono c hij ω))
  le' _ := IsStoppingTime.measurableSpace_le _

theorem lemma25Tail_measurableSet_sel (c j : ℕ) :
    MeasurableSet[lemma25TailTrialFilt hBm hBc c j] (lemma25TailSel B c j) := by
  set F := QuantumZipper.Williams.pastFilt B hBm
  set hτ := lemma25Tail_isStoppingTime_trial hBm hBc c j
  set b := lemma25TailBlock c j
  change MeasurableSet[hτ.measurableSpace] _
  have hb1 : (1 : ℝ≥0) ≤ b := by
    have : 1 ≤ b := by
      simp only [b, lemma25TailBlock]
      omega
    exact_mod_cast this
  have hBτ : Measurable[hτ.measurableSpace] (fun ω => B (lemma25TailTrialTime B c j ω) ω) :=
    lemma25Tail_measurable_stoppedValue (lemma25Tail_adapted_pastFilt hBm) hBc hτ
  have hconst : F b ≤ hτ.measurableSpace := by
    have h := IsStoppingTime.measurableSpace_mono (isStoppingTime_const F (b : ℝ≥0)) hτ
      (fun ω => WithTop.coe_le_coe.mpr (lemma25TailTrialTime_mem c j ω).1)
    rwa [IsStoppingTime.measurableSpace_const] at h
  have hlev : Measurable[hτ.measurableSpace] (lemma25TailLevel B b) :=
    (lemma25Tail_measurable_inf_pastFilt hBm hBc hb1).mono hconst le_rfl
  have hm0 : Measurable[hτ.measurableSpace] (lemma25TailInf B 0 1) :=
    ((lemma25Tail_measurable_inf_pastFilt hBm hBc zero_le_one).mono (F.mono hb1) le_rfl).mono
      hconst le_rfl
  exact (measurableSet_le hBτ hlev).inter (measurableSet_le hm0 hlev)

theorem lemma25Tail_measurableSet_succ (c j : ℕ) :
    MeasurableSet[lemma25TailTrialFilt hBm hBc c (j + 1)] (lemma25TailSucc B c j) := by
  set hτ := lemma25Tail_isStoppingTime_trial hBm hBc c j
  set hτ' := lemma25Tail_isStoppingTime_trial hBm hBc c (j + 1)
  have hτ1 := lemma25Tail_isStoppingTime_add_const hτ 1
  change MeasurableSet[hτ'.measurableSpace] _
  have h1 : hτ1.measurableSpace ≤ hτ'.measurableSpace :=
    IsStoppingTime.measurableSpace_mono hτ1 hτ'
      (fun ω => WithTop.coe_le_coe.mpr (lemma25TailTrialTime_add_one_le c j ω))
  have h0 : hτ.measurableSpace ≤ hτ'.measurableSpace :=
    IsStoppingTime.measurableSpace_mono hτ hτ'
      (fun ω => WithTop.coe_le_coe.mpr (lemma25TailTrialTime_mono c (Nat.le_succ j) ω))
  have hB1 := (lemma25Tail_measurable_stoppedValue (lemma25Tail_adapted_pastFilt hBm) hBc
    hτ1).mono h1 le_rfl
  have hB0 := (lemma25Tail_measurable_stoppedValue (lemma25Tail_adapted_pastFilt hBm) hBc
    hτ).mono h0 le_rfl
  exact measurableSet_lt (hB1.sub hB0) measurable_const

theorem lemma25Tail_condExp_succ {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (c j : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ lemma25TailSel B c j → lemma25TailDropProb ≤
      P[(lemma25TailSucc B c j).indicator (fun _ => (1 : ℝ)) |
        lemma25TailTrialFilt hBm hBc c j] ω := by
  have h := lemma25Tail_condExp_unitDrop hB hBc hBm
    (lemma25Tail_isStoppingTime_trial hBm hBc c j)
  filter_upwards [h] with ω hω _
  exact le_of_eq hω.symm

end Probability

/-! ### The tail bound -/

/-- `φ = 1 - p + p e^{-1}`: the exponential moment factor of one trial of success probability
`p = lemma25TailDropProb`, at the exponent `λ = 1`. -/
def lemma25TailPhi : ℝ := 1 - lemma25TailDropProb + lemma25TailDropProb * Real.exp (-1)

/-- The rate `c = -log φ / 8` of the exponential tail of the record-block count. -/
def lemma25TailRate : ℝ := -Real.log lemma25TailPhi / 8

theorem lemma25TailPhi_pos : 0 < lemma25TailPhi := by
  have hp := lemma25TailDropProb_pos
  have hp1 := lemma25TailDropProb_le_one
  have he := Real.exp_pos (-1)
  unfold lemma25TailPhi
  nlinarith

theorem lemma25TailPhi_lt_one : lemma25TailPhi < 1 := by
  have hp := lemma25TailDropProb_pos
  have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  unfold lemma25TailPhi
  nlinarith

theorem lemma25TailRate_pos : 0 < lemma25TailRate := by
  have hlog : Real.log lemma25TailPhi < 0 :=
    Real.log_neg lemma25TailPhi_pos lemma25TailPhi_lt_one
  unfold lemma25TailRate
  linarith

/-- **The exponential tail of the record-block count.** For a real Brownian motion with
continuous paths, the number of counted blocks satisfies
`P[#counted blocks > n] ≤ 12 e^{-c n}` with the absolute constant `c = lemma25TailRate > 0`. -/
theorem lemma25Tail_count_tail {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (B · ω)) (n : ℕ) :
    P {ω | (n : ℕ∞) < lemma25TailCount B ω} ≤
      ENNReal.ofReal (12 * Real.exp (-(lemma25TailRate * n))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · calc P {ω | ((0 : ℕ) : ℕ∞) < lemma25TailCount B ω} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (12 * Real.exp (-(lemma25TailRate * ((0 : ℕ) : ℝ)))) := by
        rw [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
  set r := lemma25TailRate with hr
  set φ := lemma25TailPhi with hφ
  set a : ℝ := 2 * r * n with ha
  set j0 : ℕ := (n + 1) / 2 with hj0
  have hr0 : 0 < r := lemma25TailRate_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set Sbad : Set Ω := {ω | a < B 1 ω - lemma25TailInf B 0 1 ω} with hSbad
  set E : ℕ → ℕ → Set Ω := fun c N =>
    {ω | ((n : ℝ) + 1) ≤ 2 * LQGMetric.binomDomCount (lemma25TailSel B c) N ω ∧
      B 1 ω - lemma25TailInf B 0 1 ω ≤ a} with hE
  have hcover : {ω | (n : ℕ∞) < lemma25TailCount B ω} ⊆
      Sbad ∪ ((⋃ N, E 0 N) ∪ (⋃ N, E 1 N)) := by
    intro ω hω
    by_cases hbad : a < B 1 ω - lemma25TailInf B 0 1 ω
    · exact Or.inl hbad
    · right
      obtain ⟨N, h0 | h1⟩ := lemma25Tail_exists_count_ge (hBc ω) hω
      · exact Or.inl (mem_iUnion.mpr ⟨N, h0, not_lt.mp hbad⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨N, h1, not_lt.mp hbad⟩)
  set X : ℝ := Real.exp (1 * (a + 1)) *
    (1 - lemma25TailDropProb + lemma25TailDropProb * Real.exp (-1)) ^ j0 with hX
  have hEc : ∀ c N, P (E c N) ≤ ENNReal.ofReal X := by
    intro c N
    have hsub : E c N ⊆ {ω | (j0 : ℝ) ≤ LQGMetric.binomDomCount (lemma25TailSel B c) N ω ∧
        LQGMetric.binomDomHits (lemma25TailSel B c) (lemma25TailSucc B c) N ω ≤ a + 1} := by
      rintro ω ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have h2j : ((2 * j0 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_div_le (n + 1) 2
        push_cast at h2j
        linarith
      · have := lemma25Tail_hits_le (hBc ω) c N
        linarith
    have hbin := LQGMetric.measureReal_binomDom_le (lemma25TailTrialFilt hBm hBc c)
      (lemma25Tail_measurableSet_sel hBm hBc c) (lemma25Tail_measurableSet_succ hBm hBc c)
      lemma25TailDropProb_pos.le lemma25TailDropProb_le_one zero_le_one
      (lemma25Tail_condExp_succ hBm hBc hB c) N j0 (a + 1)
    calc P (E c N) ≤ P {ω | (j0 : ℝ) ≤ LQGMetric.binomDomCount (lemma25TailSel B c) N ω ∧
          LQGMetric.binomDomHits (lemma25TailSel B c) (lemma25TailSucc B c) N ω ≤ a + 1} :=
          measure_mono hsub
      _ = ENNReal.ofReal (P.real {ω | (j0 : ℝ) ≤
            LQGMetric.binomDomCount (lemma25TailSel B c) N ω ∧
            LQGMetric.binomDomHits (lemma25TailSel B c) (lemma25TailSucc B c) N ω ≤ a + 1}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal X := ENNReal.ofReal_le_ofReal hbin
  have hU : ∀ c, P (⋃ N, E c N) ≤ ENNReal.ofReal X := by
    intro c
    have hmono : Monotone (E c) := by
      intro N N' hNN' ω hω
      refine ⟨hω.1.trans ?_, hω.2⟩
      have hle : LQGMetric.binomDomCount (lemma25TailSel B c) N ω ≤
          LQGMetric.binomDomCount (lemma25TailSel B c) N' ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNN')
          (fun k _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
      linarith
    rw [hmono.measure_iUnion]
    exact iSup_le (hEc c)
  have hbad : P Sbad ≤ ENNReal.ofReal (2 * Real.exp (-((r * n) ^ 2) / 2)) := by
    have hsub : Sbad ⊆ {ω | r * n < QuantumZipper.bmOsc B 0 1 ω} := by
      intro ω hω
      have h1 : |B 1 ω - B 0 ω| ≤ QuantumZipper.bmOsc B 0 1 ω :=
        Brownian.abs_sub_le_bmOsc (hBc ω) ⟨zero_le, by simp⟩
      obtain ⟨t, ht, hval⟩ := lemma25TailInf_exists_eq (hBc ω) (zero_le_one' ℝ≥0)
      have h2 : |B t ω - B 0 ω| ≤ QuantumZipper.bmOsc B 0 1 ω :=
        Brownian.abs_sub_le_bmOsc (hBc ω) (by simpa using ht)
      have h1' := (abs_le.mp h1).2
      have h2' := (abs_le.mp h2).1
      change a < B 1 ω - lemma25TailInf B 0 1 ω at hω
      rw [← hval] at hω
      change r * n < QuantumZipper.bmOsc B 0 1 ω
      linarith
    calc P Sbad ≤ P {ω | r * n < QuantumZipper.bmOsc B 0 1 ω} := measure_mono hsub
      _ ≤ ENNReal.ofReal (2 * Real.exp (-((r * n) ^ 2) / (2 * ((1 : ℝ≥0) : ℝ)))) :=
          QuantumZipper.BMOsc.bmOsc_tail hB hBm hBc 0 1 one_pos (by positivity)
      _ = ENNReal.ofReal (2 * Real.exp (-((r * n) ^ 2) / 2)) := by
          rw [NNReal.coe_one, mul_one]
  -- the real-number estimate
  have he3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hgauss : 2 * Real.exp (-((r * n) ^ 2) / 2) ≤ 6 * Real.exp (-(r * n)) := by
    have hexp : Real.exp (-((r * n) ^ 2) / 2) ≤ Real.exp 1 * Real.exp (-(r * n)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (r * n - 1)]
    have hpos := Real.exp_pos (-(r * n))
    nlinarith
  have hXle : X ≤ 3 * Real.exp (-(r * n)) := by
    have hlogφ : Real.log φ = -8 * r := by
      simp only [hr, lemma25TailRate, hφ]
      ring
    have hφpow : (1 - lemma25TailDropProb + lemma25TailDropProb * Real.exp (-1)) ^ j0 =
        Real.exp (j0 * (-8 * r)) := by
      change φ ^ j0 = _
      rw [← hlogφ, Real.exp_nat_mul, Real.exp_log lemma25TailPhi_pos]
    have h2j : (n : ℝ) ≤ 2 * j0 := by
      have h : n ≤ 2 * j0 := by
        simp only [hj0]
        omega
      exact_mod_cast h
    have hexp : X ≤ Real.exp 1 * Real.exp (-(r * n)) := by
      rw [hX, hφpow, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [ha]
      nlinarith
    have hpos := Real.exp_pos (-(r * n))
    nlinarith
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg lemma25TailPhi_pos.le _)
  calc P {ω | (n : ℕ∞) < lemma25TailCount B ω}
      ≤ P (Sbad ∪ ((⋃ N, E 0 N) ∪ (⋃ N, E 1 N))) := measure_mono hcover
    _ ≤ P Sbad + (P (⋃ N, E 0 N) + P (⋃ N, E 1 N)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal (2 * Real.exp (-((r * n) ^ 2) / 2)) +
          (ENNReal.ofReal X + ENNReal.ofReal X) := add_le_add hbad (add_le_add (hU 0) (hU 1))
    _ = ENNReal.ofReal (2 * Real.exp (-((r * n) ^ 2) / 2) + (X + X)) := by
        rw [ENNReal.ofReal_add (by positivity) (by linarith), ENNReal.ofReal_add hX0 hX0]
    _ ≤ ENNReal.ofReal (12 * Real.exp (-(r * n))) := by
        apply ENNReal.ofReal_le_ofReal
        linarith

end MatedCRTHarmonic.MatedCRT
