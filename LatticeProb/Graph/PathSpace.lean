/-
The simple random walk on a general graph, on path space.

`LatticeProb/Walk/Markov.lean` proves the Markov property for the lattice walk
from the fact that its increments are independent of the position, which is
false on a general graph.  What replaces it is the first-step decomposition of
the law itself: the instruction sequence splits into its head and its tail, the
head chooses a neighbour uniformly, and the tail drives the walk from there, so

  `P_x = (1 / deg x) ∑_{y ∼ x} (P_y) ∘ (cons x)⁻¹`

as an identity of measures on path space.  Everything else in this file is read
off it.
-/
import Mathlib
import LatticeProb.Graph.Walk
import LatticeProb.Graph.WalkLemmas
import LatticeProb.Prob.InfinitePiSplit

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The driving instructions -/

instance stepLaw_isProbabilityMeasure : IsProbabilityMeasure (stepLaw) := by
  constructor
  rw [stepLaw, Measure.restrict_apply_univ, Real.volume_Ico]
  norm_num

instance driverLaw_isProbabilityMeasure : IsProbabilityMeasure driverLaw := by
  rw [driverLaw]
  infer_instance

/-! ### Measurability -/

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [MeasurableSingletonClass V] [Countable V] in
theorem measurable_stepTo (x : V) : Measurable (stepTo G x) := by
  have h1 : Measurable fun u : ℝ => ⌊(G.degree x : ℝ) * u⌋₊ :=
    Measurable.comp (_root_.Nat.measurable_floor) (measurable_id.const_mul _)
  have h2 : Measurable fun i : ℕ => ((G.neighborFinset x).toList).getD i x :=
    measurable_from_top
  exact h2.comp h1

theorem measurable_stepTo_uncurry :
    Measurable fun p : V × ℝ => stepTo G p.1 p.2 :=
  measurable_from_prod_countable_right fun y => measurable_stepTo y

theorem measurable_walkPath_apply (x : V) (k : ℕ) :
    Measurable fun ω : ℕ → ℝ => walkPath G x ω k := by
  induction k generalizing x with
  | zero => exact measurable_const
  | succ k ih =>
      have heq : (fun ω : ℕ → ℝ => walkPath G x ω (k + 1))
          = (fun p : V × ℝ => stepTo G p.1 p.2)
            ∘ (fun ω : ℕ → ℝ => ((walkPath G x ω k : V), (ω k : ℝ))) := rfl
      rw [heq]
      exact Measurable.comp (measurable_stepTo_uncurry (G := G))
        (Measurable.prodMk (ih x) (measurable_pi_apply k))

theorem measurable_walkPath (x : V) : Measurable (walkPath G x) :=
  measurable_pi_lambda _ fun k => measurable_walkPath_apply x k

instance walkLaw_isProbabilityMeasure (x : V) : IsProbabilityMeasure (walkLaw G x) := by
  rw [walkLaw]
  exact Measure.isProbabilityMeasure_map (measurable_walkPath x).aemeasurable

omit [MeasurableSingletonClass V] [Countable V] in
theorem measurable_cons (x : V) : Measurable (cons (V := V) x) :=
  measurable_pi_lambda _ fun k => by
    cases k with
    | zero => exact measurable_const
    | succ k => exact measurable_pi_apply k

/-! ### The walk restarts at its first step -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem walkPath_succ_eq (x : V) (ω : ℕ → ℝ) (k : ℕ) :
    walkPath G x ω (k + 1) = walkPath G (stepTo G x (ω 0)) (LatticeProb.tailNat ω) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show stepTo G (walkPath G x ω (k + 1)) (ω (k + 1)) = _
      rw [ih]
      rfl

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem walkPath_eq_cons (x : V) (ω : ℕ → ℝ) :
    walkPath G x ω = cons x (walkPath G (stepTo G x (ω 0)) (LatticeProb.tailNat ω)) := by
  funext k
  cases k with
  | zero => rfl
  | succ k => exact walkPath_succ_eq x ω k

/-! ### The instruction chooses a neighbour uniformly -/

section Uniform

/-- `[0,1)` is the disjoint union of `n` intervals of length `1/n`. -/
theorem Ico_zero_one_eq (n : ℕ) (hn : 0 < n) :
    Set.Ico (0 : ℝ) 1 = ⋃ i ∈ Finset.range n, Set.Ico ((i : ℝ) / n) (((i : ℝ) + 1) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  ext u
  simp only [Set.mem_Ico, Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨h0, h1⟩
    have hnu : (0 : ℝ) ≤ (n : ℝ) * u := mul_nonneg hn'.le h0
    have hfl : ((⌊(n : ℝ) * u⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * u := Nat.floor_le hnu
    have hfu : (n : ℝ) * u < ((⌊(n : ℝ) * u⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    refine ⟨⌊(n : ℝ) * u⌋₊, ?_, ?_, ?_⟩
    · rw [Nat.floor_lt hnu]
      nlinarith
    · rw [div_le_iff₀ hn']
      nlinarith
    · rw [lt_div_iff₀ hn']
      nlinarith
  · rintro ⟨i, hi, h1, h2⟩
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    refine ⟨le_trans (by positivity) h1, ?_⟩
    refine h2.trans_le ?_
    rw [div_le_one hn']
    exact hi'

theorem volume_Ico_div (n i : ℕ) (hn : 0 < n) :
    volume (Set.Ico ((i : ℝ) / n) (((i : ℝ) + 1) / n)) = ENNReal.ofReal ((n : ℝ)⁻¹) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.volume_Ico]
  congr 1
  field_simp
  ring

theorem pairwiseDisjoint_Ico_div (n : ℕ) :
    ((Finset.range n : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i : ℕ => Set.Ico ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
  have key : ∀ i j : ℕ, i < j →
      Disjoint (Set.Ico ((i : ℝ) / n) (((i : ℝ) + 1) / n))
        (Set.Ico ((j : ℝ) / n) (((j : ℝ) + 1) / n)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun u hu hu' => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp at hu
    have hn' : (0 : ℝ) < n := by exact_mod_cast hpos
    have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    have h1 := hu.2
    have h2 := hu'.1
    rw [lt_div_iff₀ hn'] at h1
    rw [div_le_iff₀ hn'] at h2
    nlinarith
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem floor_mul_of_mem_Ico {n i : ℕ} (hn : 0 < n) {u : ℝ}
    (hu : u ∈ Set.Ico ((i : ℝ) / n) (((i : ℝ) + 1) / n)) : ⌊(n : ℝ) * u⌋₊ = i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((i : ℕ) : ℝ) ≤ (n : ℝ) * u := by
    have := hu.1
    rw [div_le_iff₀ hn'] at this
    nlinarith
  have h2 : (n : ℝ) * u < ((i : ℕ) : ℝ) + 1 := by
    have := hu.2
    rw [lt_div_iff₀ hn'] at this
    nlinarith
  rw [Nat.floor_eq_iff (le_trans (Nat.cast_nonneg i) h1)]
  exact ⟨h1, h2⟩

/-- **The floor of `n` times a uniform instruction is uniform on `{0, …, n-1}`.** -/
theorem map_floor_stepLaw (n : ℕ) (hn : 0 < n) :
    stepLaw.map (fun u : ℝ => ⌊(n : ℝ) * u⌋₊)
      = (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac i := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmeas : Measurable fun u : ℝ => ⌊(n : ℝ) * u⌋₊ :=
    Measurable.comp (_root_.Nat.measurable_floor) (measurable_id.const_mul _)
  ext S -
  set T : Finset ℕ := (Finset.range n).filter (fun i => i ∈ S) with hT
  rw [Measure.map_apply hmeas (MeasurableSet.of_discrete), stepLaw,
    Measure.restrict_apply (MeasurableSet.of_discrete.preimage hmeas)]
  have hsplit : (fun u : ℝ => ⌊(n : ℝ) * u⌋₊) ⁻¹' S ∩ Set.Ico (0 : ℝ) 1
      = ⋃ i ∈ T, Set.Ico ((i : ℝ) / n) (((i : ℝ) + 1) / n) := by
    rw [Ico_zero_one_eq n hn]
    ext u
    simp only [hT, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Finset.mem_range,
      Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨hS, i, hi, hu⟩
      exact ⟨i, ⟨hi, by rwa [floor_mul_of_mem_Ico hn hu] at hS⟩, hu⟩
    · rintro ⟨i, ⟨hi, hiS⟩, hu⟩
      exact ⟨by rwa [floor_mul_of_mem_Ico hn hu], i, hi, hu⟩
  have hTsub : (T : Set ℕ) ⊆ ((Finset.range n : Finset ℕ) : Set ℕ) := by
    intro i hi
    simp only [hT, Finset.coe_filter, Set.mem_setOf_eq] at hi
    exact Finset.mem_coe.mpr hi.1
  rw [hsplit, measure_biUnion_finset ((pairwiseDisjoint_Ico_div n).subset hTsub)
    (fun i _ => measurableSet_Ico)]
  simp only [volume_Ico_div n _ hn, Finset.sum_const, nsmul_eq_mul]
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  have hdirac : ∀ i : ℕ, (Measure.dirac i) S = if i ∈ S then 1 else 0 := by
    intro i
    rw [Measure.dirac_apply' _ MeasurableSet.of_discrete]
    simp [Set.indicator_apply]
  simp only [hdirac]
  rw [Finset.sum_boole, ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast, ← hT]
  exact mul_comm _ _

end Uniform

/-! ### The uniform neighbour law -/

section Neighbour

variable [DecidableEq V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem getD_toList_mem (s : Finset V) (x : V) {i : ℕ} (hi : i < s.card) :
    s.toList.getD i x ∈ s := by
  have hlen : i < s.toList.length := by rwa [Finset.length_toList]
  rw [List.getD_eq_getElem _ _ hlen]
  exact Finset.mem_toList.mp (List.getElem_mem hlen)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem getD_toList_injOn (s : Finset V) (x : V) :
    ∀ i ∈ Finset.range s.card, ∀ j ∈ Finset.range s.card,
      s.toList.getD i x = s.toList.getD j x → i = j := by
  intro i hi j hj hij
  rw [Finset.mem_range] at hi hj
  have hi' : i < s.toList.length := by rwa [Finset.length_toList]
  have hj' : j < s.toList.length := by rwa [Finset.length_toList]
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at hij
  exact (List.Nodup.getElem_inj_iff s.nodup_toList).mp hij

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem image_getD_toList (s : Finset V) (x : V) :
    Finset.image (fun i : ℕ => s.toList.getD i x) (Finset.range s.card) = s := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact getD_toList_mem s x (Finset.mem_range.mp hi)
  · rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      exact getD_toList_injOn s x i (by simpa using hi) j (by simpa using hj) hij

omit [MeasurableSingletonClass V] [Countable V] in
/-- **The instruction chooses a uniform neighbour.** -/
theorem map_stepTo (x : V) (hx : 0 < G.degree x) :
    stepLaw.map (stepTo G x)
      = (G.degree x : ℝ≥0∞)⁻¹ • ∑ y ∈ G.neighborFinset x, Measure.dirac y := by
  classical
  set n := G.degree x with hn
  set e : ℕ → V := fun i => ((G.neighborFinset x).toList).getD i x with he
  have hφ : Measurable fun u : ℝ => ⌊(n : ℝ) * u⌋₊ :=
    Measurable.comp (_root_.Nat.measurable_floor) (measurable_id.const_mul _)
  have h1 : stepLaw.map (stepTo G x)
      = (stepLaw.map (fun u : ℝ => ⌊(n : ℝ) * u⌋₊)).map e := by
    rw [Measure.map_map measurable_from_top hφ]
    rfl
  rw [h1, map_floor_stepLaw n hx]
  ext S hS
  rw [Measure.map_apply measurable_from_top hS, Measure.smul_apply, Measure.smul_apply,
    Measure.coe_finsetSum, Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_apply]
  congr 1
  have hL : ∀ i : ℕ, (Measure.dirac i) (e ⁻¹' S) = if e i ∈ S then 1 else 0 := by
    intro i
    rw [Measure.dirac_apply' _ (hS.preimage measurable_from_top)]
    simp [Set.indicator_apply]
  have hR : ∀ y : V, (Measure.dirac y) S = if y ∈ S then 1 else 0 := by
    intro y
    rw [Measure.dirac_apply' _ hS]
    simp [Set.indicator_apply]
  simp only [hL, hR]
  have hcard : (G.neighborFinset x).card = n := by rw [hn, SimpleGraph.degree]
  have himg : Finset.image e (Finset.range n) = G.neighborFinset x := by
    rw [he, ← hcard]
    exact image_getD_toList _ _
  rw [← himg, Finset.sum_image (fun i hi j hj hij =>
    getD_toList_injOn (G.neighborFinset x) x i (by rwa [hcard]) j (by rwa [hcard]) hij)]

end Neighbour

/-! ### The first-step decomposition -/

section FirstStep

variable [DecidableEq V]

omit [DecidableEq V] in
theorem measurable_walkPath_pair :
    Measurable fun p : V × (ℕ → ℝ) => walkPath G p.1 p.2 :=
  measurable_pi_lambda _ fun k =>
    measurable_from_prod_countable_right fun y => measurable_walkPath_apply y k

/-- **The first-step decomposition of the law of the walk**: the head of the
instruction sequence chooses a neighbour uniformly and its tail drives the walk
from there. -/
theorem walkLaw_firstStep (x : V) (hx : 0 < G.degree x) :
    walkLaw G x
      = (G.degree x : ℝ≥0∞)⁻¹ • ∑ y ∈ G.neighborFinset x, (walkLaw G y).map (cons x) := by
  classical
  have hdl : driverLaw = Measure.infinitePi fun _ : ℕ => stepLaw := rfl
  have hwl : ∀ y : V, walkLaw G y = driverLaw.map (walkPath G y) := fun _ => rfl
  have hpair : Measurable fun ω : ℕ → ℝ => ((ω 0 : ℝ), LatticeProb.tailNat ω) :=
    (measurable_pi_apply 0).prodMk LatticeProb.measurable_tailNat
  have hmove : Measurable fun p : ℝ × (ℕ → ℝ) => ((stepTo G x p.1 : V), p.2) :=
    ((measurable_stepTo x).comp measurable_fst).prodMk measurable_snd
  have hΦm : Measurable fun p : ℝ × (ℕ → ℝ) => cons x (walkPath G (stepTo G x p.1) p.2) :=
    ((measurable_cons x).comp measurable_walkPath_pair).comp hmove
  have h1 : walkLaw G x
      = (stepLaw.prod driverLaw).map fun p : ℝ × (ℕ → ℝ) =>
          cons x (walkPath G (stepTo G x p.1) p.2) := by
    rw [hwl, hdl, ← LatticeProb.map_head_tailNat, Measure.map_map hΦm hpair]
    congr 1
    funext ω
    exact walkPath_eq_cons x ω
  rw [h1]
  ext S hS
  set h : V → ℝ≥0∞ := fun y => ((walkLaw G y).map (cons x)) S with hh
  have hhm : Measurable h := measurable_of_countable h
  have hinner : ∀ u : ℝ, driverLaw ((Prod.mk u) ⁻¹'
      ((fun p : ℝ × (ℕ → ℝ) => cons x (walkPath G (stepTo G x p.1) p.2)) ⁻¹' S))
      = h (stepTo G x u) := by
    intro u
    have hb : h (stepTo G x u) = ((walkLaw G (stepTo G x u)).map (cons x)) S := rfl
    rw [hb, hwl (stepTo G x u), Measure.map_map (measurable_cons x) (measurable_walkPath _),
      Measure.map_apply ((measurable_cons x).comp (measurable_walkPath _)) hS]
    rfl
  rw [Measure.map_apply hΦm hS, Measure.prod_apply (hΦm hS)]
  simp only [hinner]
  rw [← lintegral_map hhm (measurable_stepTo x), map_stepTo x hx, lintegral_smul_measure,
    lintegral_finsetSum_measure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [lintegral_dirac, hh]

end FirstStep

/-! ### Integrals against the first step -/

section Integral

variable [DecidableEq V]

theorem integral_walkLaw_firstStep (x : V) (hx : 0 < G.degree x)
    (f : (ℕ → V) → ℝ) (hfm : Measurable f) {C : ℝ} (hC : ∀ X, ‖f X‖ ≤ C) :
    ∫ X, f X ∂(walkLaw G x)
      = (G.degree x : ℝ)⁻¹ * ∑ y ∈ G.neighborFinset x, ∫ X, f (cons x X) ∂(walkLaw G y) := by
  have hint : ∀ y : V, Integrable f ((walkLaw G y).map (cons x)) := by
    intro y
    haveI : IsProbabilityMeasure ((walkLaw G y).map (cons x)) :=
      Measure.isProbabilityMeasure_map (measurable_cons x).aemeasurable
    exact Integrable.mono' (integrable_const C) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  rw [walkLaw_firstStep x hx, integral_smul_measure,
    integral_finsetSum_measure (fun y _ => hint y)]
  have hmap : ∀ y : V, ∫ X, f X ∂((walkLaw G y).map (cons x))
      = ∫ X, f (cons x X) ∂(walkLaw G y) := fun y =>
    integral_map (measurable_cons x).aemeasurable hfm.aestronglyMeasurable
  simp only [hmap, smul_eq_mul]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- The same first-step decomposition of an integral, with INTEGRABILITY in
place of a uniform bound.  A payoff stopped at an exit time is integrable
without being bounded, which is what this form is for. -/
theorem integral_walkLaw_firstStep' (x : V) (hx : 0 < G.degree x)
    (f : (ℕ → V) → ℝ) (hfm : Measurable f) (hf : Integrable f (walkLaw G x)) :
    ∫ X, f X ∂(walkLaw G x)
      = (G.degree x : ℝ)⁻¹ * ∑ y ∈ G.neighborFinset x, ∫ X, f (cons x X) ∂(walkLaw G y) := by
  classical
  have hdne : (G.degree x : ℝ≥0∞) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).2 hx.ne'
  have h0 : ((G.degree x : ℝ≥0∞))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
  have htop : ((G.degree x : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hdne
  rw [walkLaw_firstStep x hx] at hf ⊢
  have hsum : Integrable f (∑ y ∈ G.neighborFinset x, (walkLaw G y).map (cons x)) :=
    (integrable_smul_measure h0 htop).1 hf
  have heach : ∀ y ∈ G.neighborFinset x, Integrable f ((walkLaw G y).map (cons x)) := by
    intro y hy
    refine hsum.mono_measure ?_
    exact Finset.single_le_sum (f := fun y => (walkLaw G y).map (cons x))
      (fun _ _ => bot_le) hy
  rw [integral_smul_measure, integral_finsetSum_measure heach]
  have hmap : ∀ y : V, ∫ X, f X ∂((walkLaw G y).map (cons x))
      = ∫ X, f (cons x X) ∂(walkLaw G y) := fun y =>
    integral_map (measurable_cons x).aemeasurable hfm.aestronglyMeasurable
  simp only [hmap, smul_eq_mul]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]

end Integral

/-! ### The Markov property at a fixed time -/

section Markov

variable [DecidableEq V]

/-- `f` is settled by the positions up to time `n`. -/
def DependsUpTo {α : Type*} (n : ℕ) (f : (ℕ → V) → α) : Prop :=
  ∀ X Y : ℕ → V, (∀ k ≤ n, X k = Y k) → f X = f Y

omit [DecidableEq V] in
theorem measurable_of_dependsUpTo {α : Type*} [MeasurableSpace α] {n : ℕ}
    {f : (ℕ → V) → α} (hf : DependsUpTo n f) : Measurable f := by
  classical
  set g : (Fin (n + 1) → V) → α :=
    fun a => f fun k => if h : k < n + 1 then a ⟨k, h⟩ else a ⟨0, Nat.succ_pos n⟩ with hg
  have hfact : f = g ∘ fun X : ℕ → V => fun i : Fin (n + 1) => X i := by
    funext X
    refine (hf X _ fun k hk => ?_).symm ▸ rfl
    rw [dif_pos (by omega : k < n + 1)]
  rw [hfact]
  exact Measurable.of_discrete.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)

/-- The path shifted by `n`. -/
def shiftPath (n : ℕ) (X : ℕ → V) : ℕ → V := fun k => X (n + k)

omit [DecidableEq V] in
omit [MeasurableSingletonClass V] [Countable V] in
theorem measurable_shiftPath (n : ℕ) : Measurable (shiftPath (V := V) n) :=
  measurable_pi_lambda _ fun k => measurable_pi_apply (n + k)

/-- The expectation of a bounded measurable functional of the path, as a
function of the starting vertex. -/
noncomputable def pathExp (G : SimpleGraph V) [G.LocallyFinite]
    (F : (ℕ → V) → ℝ) (y : V) : ℝ := ∫ Y, F Y ∂(walkLaw G y)

omit [DecidableEq V] in
theorem measurable_pathExp (F : (ℕ → V) → ℝ) : Measurable (pathExp G F) :=
  Measurable.of_discrete

omit [DecidableEq V] in
theorem norm_pathExp_le {F : (ℕ → V) → ℝ} {CF : ℝ} (hFb : ∀ X, ‖F X‖ ≤ CF) (y : V) :
    ‖pathExp G F y‖ ≤ CF := by
  have := norm_integral_le_of_norm_le_const (μ := walkLaw G y) (C := CF)
    (Filter.Eventually.of_forall hFb)
  simpa [pathExp, measureReal_def] using this

omit [DecidableEq V] in
theorem ae_walkLaw_start (x : V) : ∀ᵐ X ∂(walkLaw G x), X 0 = x := by
  rw [ae_iff]
  have hset : MeasurableSet {X : ℕ → V | ¬ X 0 = x} := by
    have he : {X : ℕ → V | ¬ X 0 = x} = ((fun X : ℕ → V => X 0) ⁻¹' {x})ᶜ := rfl
    rw [he]
    exact (measurable_pi_apply 0 (MeasurableSet.singleton x)).compl
  have hwl : walkLaw G x = driverLaw.map (walkPath G x) := rfl
  rw [hwl, Measure.map_apply (measurable_walkPath x) hset]
  have : (walkPath G x) ⁻¹' {X : ℕ → V | ¬ X 0 = x} = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    rfl
  rw [this, measure_empty]

/-- **The Markov property at a fixed time.**  For a bounded measurable `F` on
paths and a bounded `H` settled by the positions up to time `n`,
`E_x[F(θ_n X) H(X)] = E_x[E_{X_n}[F] H(X)]`. -/
theorem markov_fixed (hdeg : ∀ v : V, 0 < G.degree v)
    (F : (ℕ → V) → ℝ) (hFm : Measurable F) (CF : ℝ) (hFb : ∀ X, ‖F X‖ ≤ CF) :
    ∀ (n : ℕ) (x : V) (H : (ℕ → V) → ℝ) (CH : ℝ), (∀ X, ‖H X‖ ≤ CH) → DependsUpTo n H →
      ∫ X, F (shiftPath n X) * H X ∂(walkLaw G x)
        = ∫ X, pathExp G F (X n) * H X ∂(walkLaw G x) := by
  intro n
  induction n with
  | zero =>
      intro x H CH hHb hH
      have hHm : Measurable H := measurable_of_dependsUpTo hH
      have hL : ∀ᵐ X ∂(walkLaw G x),
          F (shiftPath 0 X) * H X = F X * H (fun _ => x) := by
        filter_upwards [ae_walkLaw_start x] with X hX
        have h1 : shiftPath 0 X = X := by funext k; simp [shiftPath]
        have h2 : H X = H (fun _ => x) := hH X _ fun k hk => by
          simpa [Nat.le_zero.mp hk] using hX
        rw [h1, h2]
      have hR : ∀ᵐ X ∂(walkLaw G x),
          pathExp G F (X 0) * H X = pathExp G F x * H (fun _ => x) := by
        filter_upwards [ae_walkLaw_start x] with X hX
        have h2 : H X = H (fun _ => x) := hH X _ fun k hk => by
          simpa [Nat.le_zero.mp hk] using hX
        rw [hX, h2]
      rw [integral_congr_ae hL, integral_congr_ae hR, integral_mul_const, integral_const]
      simp [pathExp, mul_comm]
  | succ n ih =>
      intro x H CH hHb hH
      have hHm : Measurable H := measurable_of_dependsUpTo hH
      have hCF : 0 ≤ CF := le_trans (norm_nonneg _) (hFb fun _ => x)
      have hCH : 0 ≤ CH := le_trans (norm_nonneg _) (hHb fun _ => x)
      have hLm : Measurable fun X : ℕ → V => F (shiftPath (n + 1) X) * H X :=
        (hFm.comp (measurable_shiftPath _)).mul hHm
      have hRm : Measurable fun X : ℕ → V => pathExp G F (X (n + 1)) * H X :=
        ((measurable_pathExp F).comp (measurable_pi_apply (n + 1))).mul hHm
      have hLb : ∀ X : ℕ → V, ‖F (shiftPath (n + 1) X) * H X‖ ≤ CF * CH := fun X => by
        rw [norm_mul]; exact mul_le_mul (hFb _) (hHb _) (norm_nonneg _) hCF
      have hRb : ∀ X : ℕ → V, ‖pathExp G F (X (n + 1)) * H X‖ ≤ CF * CH := fun X => by
        rw [norm_mul]
        exact mul_le_mul (norm_pathExp_le hFb _) (hHb _) (norm_nonneg _) hCF
      rw [integral_walkLaw_firstStep x (hdeg x) _ hLm hLb,
        integral_walkLaw_firstStep x (hdeg x) _ hRm hRb]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      have hshift : ∀ X : ℕ → V, shiftPath (n + 1) (cons x X) = shiftPath n X := by
        intro X
        funext k
        show (cons x X) (n + 1 + k) = X (n + k)
        rw [show n + 1 + k = (n + k) + 1 by omega]
        rfl
      have hcons : ∀ X : ℕ → V, (cons x X) (n + 1) = X n := fun X => rfl
      have hH' : DependsUpTo n (fun X : ℕ → V => H (cons x X)) := by
        intro X Y hXY
        refine hH _ _ fun k hk => ?_
        cases k with
        | zero => rfl
        | succ k => exact hXY k (by omega)
      have := ih y (fun X => H (cons x X)) CH (fun X => hHb _) hH'
      simp only [hshift, hcons]
      exact this

/-! ### The Markov property at a bounded stopping time -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem dependsUpTo_of_isStopping {τ : (ℕ → V) → ℕ} (hτ : IsStopping τ)
    {N : ℕ} (hτN : ∀ X, τ X ≤ N) : DependsUpTo N τ := fun X Y hXY =>
  (hτ (τ X) X Y (fun j hj => hXY j (le_trans hj (hτN X))) rfl).symm

omit [DecidableEq V] in
theorem measurable_isStopping {τ : (ℕ → V) → ℕ} (hτ : IsStopping τ)
    {N : ℕ} (hτN : ∀ X, τ X ≤ N) : Measurable τ :=
  measurable_of_dependsUpTo (dependsUpTo_of_isStopping hτ hτN)

/-- **The strong Markov property at a bounded stopping time.** -/
theorem markov_stopping (hdeg : ∀ v : V, 0 < G.degree v) (N : ℕ) (x : V)
    (τ : (ℕ → V) → ℕ) (hτ : IsStopping τ) (hτN : ∀ X, τ X ≤ N)
    (F : (ℕ → V) → ℝ) (hFm : Measurable F) (CF : ℝ) (hFb : ∀ X, ‖F X‖ ≤ CF)
    (H : (ℕ → V) → ℝ) (CH : ℝ) (hHb : ∀ X, ‖H X‖ ≤ CH)
    (hHdep : ∀ (k : ℕ) (X Y : ℕ → V), (∀ j ≤ k, X j = Y j) → τ X = k → H X = H Y) :
    ∫ X, F (shiftPath (τ X) X) * H X ∂(walkLaw G x)
      = ∫ X, pathExp G F (X (τ X)) * H X ∂(walkLaw G x) := by
  classical
  have hCF : 0 ≤ CF := le_trans (norm_nonneg _) (hFb fun _ => x)
  set Hk : ℕ → (ℕ → V) → ℝ := fun k X => H X * (if τ X = k then 1 else 0) with hHk
  have hHkdep : ∀ k, DependsUpTo k (Hk k) := by
    intro k X Y hXY
    by_cases hk : τ X = k
    · have hkY : τ Y = k := hτ k X Y hXY hk
      have hHH : H X = H Y := hHdep k X Y hXY hk
      simp [hHk, hk, hkY, hHH]
    · have hkY : τ Y ≠ k := fun hc => hk (hτ k Y X (fun j hj => (hXY j hj).symm) hc)
      simp [hHk, hk, hkY]
  have hHkb : ∀ k X, ‖Hk k X‖ ≤ CH := by
    intro k X
    rw [hHk]
    simp only
    by_cases hk : τ X = k
    · simpa [hk] using hHb X
    · simpa [hk] using le_trans (norm_nonneg (H X)) (hHb X)
  have hHkm : ∀ k, Measurable (Hk k) := fun k => measurable_of_dependsUpTo (hHkdep k)
  have hsplitL : ∀ X : ℕ → V,
      F (shiftPath (τ X) X) * H X
        = ∑ k ∈ Finset.range (N + 1), F (shiftPath k X) * Hk k X := by
    intro X
    rw [Finset.sum_eq_single_of_mem (τ X)
      (Finset.mem_range.mpr (by have := hτN X; omega : τ X < N + 1))]
    · simp [hHk]
    · intro b _ hb
      simp [hHk, Ne.symm hb]
  have hsplitR : ∀ X : ℕ → V,
      pathExp G F (X (τ X)) * H X
        = ∑ k ∈ Finset.range (N + 1), pathExp G F (X k) * Hk k X := by
    intro X
    rw [Finset.sum_eq_single_of_mem (τ X)
      (Finset.mem_range.mpr (by have := hτN X; omega : τ X < N + 1))]
    · simp [hHk]
    · intro b _ hb
      simp [hHk, Ne.symm hb]
  have hintL : ∀ k ∈ Finset.range (N + 1),
      Integrable (fun X => F (shiftPath k X) * Hk k X) (walkLaw G x) := by
    intro k _
    refine Integrable.of_bound
      (((hFm.comp (measurable_shiftPath k)).mul (hHkm k)).aestronglyMeasurable)
      (CF * CH) (Filter.Eventually.of_forall fun X => ?_)
    rw [norm_mul]
    exact mul_le_mul (hFb _) (hHkb k X) (norm_nonneg _) hCF
  have hintR : ∀ k ∈ Finset.range (N + 1),
      Integrable (fun X => pathExp G F (X k) * Hk k X) (walkLaw G x) := by
    intro k _
    refine Integrable.of_bound
      ((((measurable_pathExp F).comp (measurable_pi_apply k)).mul
        (hHkm k)).aestronglyMeasurable)
      (CF * CH) (Filter.Eventually.of_forall fun X => ?_)
    rw [norm_mul]
    exact mul_le_mul (norm_pathExp_le hFb _) (hHkb k X) (norm_nonneg _) hCF
  calc ∫ X, F (shiftPath (τ X) X) * H X ∂(walkLaw G x)
      = ∫ X, ∑ k ∈ Finset.range (N + 1), F (shiftPath k X) * Hk k X ∂(walkLaw G x) :=
        integral_congr_ae (Filter.Eventually.of_forall hsplitL)
    _ = ∑ k ∈ Finset.range (N + 1), ∫ X, F (shiftPath k X) * Hk k X ∂(walkLaw G x) :=
        integral_finsetSum _ hintL
    _ = ∑ k ∈ Finset.range (N + 1), ∫ X, pathExp G F (X k) * Hk k X ∂(walkLaw G x) :=
        Finset.sum_congr rfl fun k _ =>
          markov_fixed hdeg F hFm CF hFb k x (Hk k) CH (hHkb k) (hHkdep k)
    _ = ∫ X, ∑ k ∈ Finset.range (N + 1), pathExp G F (X k) * Hk k X ∂(walkLaw G x) :=
        (integral_finsetSum _ hintR).symm
    _ = ∫ X, pathExp G F (X (τ X)) * H X ∂(walkLaw G x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun X => (hsplitR X).symm)

/-! ### The finite-horizon average is the integral against the law -/

/-- **The walk operator and the law of the walk agree** on every bounded
measurable functional settled by the positions up to the horizon.  This is the
general-graph form of `LatticeProb.Graph.walkAverageIsIntegral`. -/
theorem walkExp_eq_integral (hdeg : ∀ v : V, 0 < G.degree v) :
    ∀ (n : ℕ) (x : V) (F : (ℕ → V) → ℝ), Measurable F → ∀ C : ℝ, (∀ X, ‖F X‖ ≤ C) →
      DependsUpTo n F → walkExp G n x F = ∫ X, F X ∂(walkLaw G x) := by
  intro n
  induction n with
  | zero =>
      intro x F hFm C hFb hF
      have hae : ∀ᵐ X ∂(walkLaw G x), F X = F (fun _ => x) := by
        filter_upwards [ae_walkLaw_start x] with X hX
        exact hF X _ fun k hk => by simpa [Nat.le_zero.mp hk] using hX
      rw [integral_congr_ae hae, integral_const]
      simp [walkExp, measureReal_def]
  | succ n ih =>
      intro x F hFm C hFb hF
      have hFdeg : (0 : ℝ) < G.degree x := by exact_mod_cast hdeg x
      rw [walkExp_succ, integral_walkLaw_firstStep x (hdeg x) F hFm hFb]
      have hcons : ∀ y : V, walkExp G n y (fun X => F (cons x X))
          = ∫ X, F (cons x X) ∂(walkLaw G y) := by
        intro y
        refine ih y (fun X => F (cons x X)) (hFm.comp (measurable_cons x)) C
          (fun X => hFb _) ?_
        intro X Y hXY
        refine hF _ _ fun k hk => ?_
        cases k with
        | zero => rfl
        | succ k => exact hXY k (by omega)
      rw [Finset.sum_congr rfl fun y _ => hcons y]
      field_simp

/-! ### The probability of following a prescribed walk -/

omit [Countable V] [DecidableEq V] in
theorem measurableSet_prefix (w : ℕ → V) (m : ℕ) :
    MeasurableSet {X : ℕ → V | ∀ k ≤ m, X k = w k} := by
  have he : {X : ℕ → V | ∀ k ≤ m, X k = w k}
      = ⋂ k ∈ Finset.range (m + 1), (fun X : ℕ → V => X k) ⁻¹' {w k} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h k hk => h k (by omega), fun h k hk => h k (by omega)⟩
  rw [he]
  exact MeasurableSet.biInter (Finset.range (m + 1)).countable_toSet
    fun k _ => (measurable_pi_apply k) (MeasurableSet.singleton (w k))

omit [DecidableEq V] in
theorem walkLaw_prefix_of_ne (x : V) {w : ℕ → V} (hx : x ≠ w 0) (m : ℕ) :
    walkLaw G x {X : ℕ → V | ∀ k ≤ m, X k = w k} = 0 := by
  have hnull : walkLaw G x {X : ℕ → V | ¬ X 0 = x} = 0 := by
    rw [← ae_iff]
    exact ae_walkLaw_start (G := G) x
  refine measure_mono_null (fun X hX => ?_) hnull
  exact fun hc => hx (hc.symm.trans (hX 0 (Nat.zero_le m)))

/-- **The probability of following a prescribed walk** is the product of the
reciprocal degrees along it. -/
theorem walkLaw_prefix (hdeg : ∀ v : V, 0 < G.degree v) :
    ∀ (m : ℕ) (w : ℕ → V), (∀ k < m, G.Adj (w k) (w (k + 1))) →
      walkLaw G (w 0) {X : ℕ → V | ∀ k ≤ m, X k = w k}
        = ∏ k ∈ Finset.range m, ((G.degree (w k) : ℝ≥0∞))⁻¹ := by
  classical
  intro m
  induction m with
  | zero =>
      intro w _
      rw [Finset.range_zero, Finset.prod_empty]
      have hz : walkLaw G (w 0) {X : ℕ → V | ∀ k ≤ 0, X k = w k}ᶜ = 0 := by
        have hset : {X : ℕ → V | ∀ k ≤ 0, X k = w k}ᶜ
            = {X : ℕ → V | ¬ ∀ k ≤ 0, X k = w k} := rfl
        rw [hset, ← ae_iff]
        filter_upwards [ae_walkLaw_start (G := G) (w 0)] with X hX k hk
        rw [Nat.le_zero.mp hk]
        exact hX
      exact (prob_compl_eq_zero_iff (measurableSet_prefix w 0)).mp hz
  | succ m ih =>
      intro w hw
      set x : V := w 0 with hx
      set v : V := w 1 with hv
      have hadj : G.Adj x v := hw 0 (by omega)
      have hmem : v ∈ G.neighborFinset x := (SimpleGraph.mem_neighborFinset G x v).mpr hadj
      rw [walkLaw_firstStep x (hdeg x), Measure.smul_apply, Measure.coe_finsetSum,
        Finset.sum_apply, smul_eq_mul]
      have hpre : ∀ y : V,
          ((walkLaw G y).map (cons x)) {X : ℕ → V | ∀ k ≤ m + 1, X k = w k}
            = walkLaw G y {X : ℕ → V | ∀ k ≤ m, X k = w (k + 1)} := by
        intro y
        rw [Measure.map_apply (measurable_cons x) (measurableSet_prefix w (m + 1))]
        congr 1
        ext X
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · intro h k hk
          exact h (k + 1) (by omega)
        · intro h k hk
          cases k with
          | zero => rfl
          | succ k => exact h k (by omega)
      simp only [hpre]
      have hterm : ∀ y ∈ G.neighborFinset x, y ≠ v →
          walkLaw G y {X : ℕ → V | ∀ k ≤ m, X k = w (k + 1)} = 0 := by
        intro y _ hy
        exact walkLaw_prefix_of_ne y (by simpa [hv] using hy) m
      have hshift : walkLaw G v {X : ℕ → V | ∀ k ≤ m, X k = w (k + 1)}
          = ∏ k ∈ Finset.range m, ((G.degree (w (k + 1)) : ℝ≥0∞))⁻¹ :=
        ih (fun k => w (k + 1)) fun k hk => hw (k + 1) (by omega)
      rw [Finset.sum_eq_single_of_mem v hmem hterm, hshift, Finset.prod_range_succ']
      exact mul_comm _ _

end Markov

end LatticeProb.Graph

end
