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

end LatticeProb.Graph

end
