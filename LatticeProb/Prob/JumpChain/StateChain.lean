import LatticeProb.Prob.JumpChain.Position
import Mathlib.Probability.Independence.Process.Basic

/-!
# Finite-dimensional laws of the embedded state chain

The joint state and clock cylinders factor into the state transition masses and
clock masses. Finite-prefix measure uniqueness then proves independence of the
entire embedded state sequence from the entire clock sequence.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set Preorder

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

namespace BoundedRates

/-- A prescribed finite state history is a measurable event. -/
theorem measurableSet_state_cylinder (n : ℕ) (x : ℕ → S) :
    MeasurableSet {h : History S | ∀ k ≤ n, (h k).1 = x k} := by
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_eq_fun (by fun_prop) measurable_const

/-- Adding one prescribed state multiplies a cylinder probability by its transition mass. -/
theorem historyLaw_state_cylinder_succ (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) (x : ℕ → S) :
    rates.historyLaw μ {h | ∀ k ≤ n + 1, (h k).1 = x k} =
      rates.historyLaw μ {h | ∀ k ≤ n, (h k).1 = x k} *
        ENNReal.ofReal (rates.p (x n) (x (n + 1))) := by
  let a : Set (↥(Finset.Iic n) → S × ℝ) :=
    {h | ∀ k, (h k).1 = x k}
  have ha : MeasurableSet a := by
    dsimp only [a]
    rw [setOf_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  have hb : MeasurableSet ((Prod.fst : S × ℝ → S) ⁻¹' {x (n + 1)}) := by
    exact measurable_fst (measurableSet_singleton _)
  have heq := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ ↦ S × ℝ) (μ₀ := μ.prod rates.clockLaw)
    (κ := rates.historyStep) (a := n)
  change (rates.historyLaw μ).map (frestrictLe n) ⊗ₘ rates.historyStep n =
    (rates.historyLaw μ).map (fun h ↦ (frestrictLe n h, h (n + 1))) at heq
  have hsets : (fun h : History S ↦ (frestrictLe n h, h (n + 1))) ⁻¹'
      (a ×ˢ (Prod.fst ⁻¹' {x (n + 1)})) =
      {h | ∀ k ≤ n + 1, (h k).1 = x k} := by
    ext h
    constructor
    · rintro ⟨hpre, hlast⟩ k hk
      by_cases hkn : k ≤ n
      · exact hpre ⟨k, Finset.mem_Iic.mpr hkn⟩
      · have : k = n + 1 := by omega
        subst k
        exact hlast
    · intro hh
      exact ⟨fun k ↦ hh k (Nat.le_trans (Finset.mem_Iic.mp k.property)
        (Nat.le_succ n)), hh _ le_rfl⟩
  have hpre : frestrictLe n ⁻¹' a = {h : History S | ∀ k ≤ n, (h k).1 = x k} := by
    ext h
    exact ⟨fun hh k hk ↦ hh ⟨k, Finset.mem_Iic.mpr hk⟩,
      fun hh k ↦ hh k (Finset.mem_Iic.mp k.property)⟩
  rw [← hsets, ← Measure.map_apply (by fun_prop) (ha.prod hb), ← heq,
    Measure.compProd_apply_prod ha hb]
  have hstep (h : ↥(Finset.Iic n) → S × ℝ) (hh : h ∈ a) :
      rates.historyStep n h (Prod.fst ⁻¹' {x (n + 1)}) =
        ENNReal.ofReal (rates.p (x n) (x (n + 1))) := by
    rw [historyStep, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply,
      ← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one, hh,
      rates.kernel_singleton]
  rw [setLIntegral_congr_fun ha hstep, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm,
    Measure.map_apply (measurable_frestrictLe n) ha, hpre]

/-- The finite-dimensional state law is the initial mass times the transition masses. -/
theorem historyLaw_state_cylinder (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) (x : ℕ → S) :
    rates.historyLaw μ {h | ∀ k ≤ n, (h k).1 = x k} =
      μ {x 0} * ∏ k ∈ Finset.range n, ENNReal.ofReal (rates.p (x k) (x (k + 1))) := by
  induction n with
  | zero =>
    have heq := congrArg (fun ν : Measure S ↦ ν {x 0})
      (rates.historyLaw_map_initialState μ)
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at heq
    change rates.historyLaw μ {h | (h 0).1 = x 0} = μ {x 0} at heq
    simpa only [Nat.le_zero, forall_eq, Finset.range_zero, Finset.prod_empty,
      mul_one] using heq
  | succ n ih =>
    rw [rates.historyLaw_state_cylinder_succ μ n x, ih, Finset.prod_range_succ,
      mul_assoc]

/-- A joint cylinder gains the next transition mass and the next clock-set mass. -/
theorem historyLaw_joint_cylinder_succ (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) (x : ℕ → S)
    (B : ℕ → Set ℝ) (hB : ∀ k, MeasurableSet (B k)) :
    rates.historyLaw μ {h | ∀ k ≤ n + 1, (h k).1 = x k ∧ (h k).2 ∈ B k} =
      rates.historyLaw μ {h | ∀ k ≤ n, (h k).1 = x k ∧ (h k).2 ∈ B k} *
        (ENNReal.ofReal (rates.p (x n) (x (n + 1))) * rates.clockLaw (B (n + 1))) := by
  let a : Set (↥(Finset.Iic n) → S × ℝ) :=
    {h | ∀ k, (h k).1 = x k ∧ (h k).2 ∈ B k}
  have ha : MeasurableSet a := by
    dsimp only [a]
    rw [setOf_forall]
    apply MeasurableSet.iInter
    intro k
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      ((by fun_prop : Measurable (fun h : ↥(Finset.Iic n) → S × ℝ ↦ (h k).2)) (hB k))
  have hb : MeasurableSet ({x (n + 1)} ×ˢ B (n + 1)) :=
    (measurableSet_singleton _).prod (hB _)
  have heq := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ ↦ S × ℝ) (μ₀ := μ.prod rates.clockLaw)
    (κ := rates.historyStep) (a := n)
  change (rates.historyLaw μ).map (frestrictLe n) ⊗ₘ rates.historyStep n =
    (rates.historyLaw μ).map (fun h ↦ (frestrictLe n h, h (n + 1))) at heq
  have hsets : (fun h : History S ↦ (frestrictLe n h, h (n + 1))) ⁻¹'
      (a ×ˢ ({x (n + 1)} ×ˢ B (n + 1))) =
      {h | ∀ k ≤ n + 1, (h k).1 = x k ∧ (h k).2 ∈ B k} := by
    ext h
    constructor
    · rintro ⟨hpre, hlast⟩ k hk
      by_cases hkn : k ≤ n
      · exact hpre ⟨k, Finset.mem_Iic.mpr hkn⟩
      · have : k = n + 1 := by omega
        subst k
        exact hlast
    · intro hh
      exact ⟨fun k ↦ hh k (Nat.le_trans (Finset.mem_Iic.mp k.property)
        (Nat.le_succ n)), hh _ le_rfl⟩
  have hpre : frestrictLe n ⁻¹' a = {h : History S | ∀ k ≤ n, (h k).1 = x k ∧ (h k).2 ∈ B k} := by
    ext h
    exact ⟨fun hh k hk ↦ hh ⟨k, Finset.mem_Iic.mpr hk⟩,
      fun hh k ↦ hh k (Finset.mem_Iic.mp k.property)⟩
  rw [← hsets, ← Measure.map_apply (by fun_prop) (ha.prod hb), ← heq,
    Measure.compProd_apply_prod ha hb]
  have hstep (h : ↥(Finset.Iic n) → S × ℝ) (hh : h ∈ a) :
      rates.historyStep n h ({x (n + 1)} ×ˢ B (n + 1)) =
        (ENNReal.ofReal (rates.p (x n) (x (n + 1))) * rates.clockLaw (B (n + 1))) := by
    rw [historyStep, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply,
      Measure.prod_prod, (hh _).1,
      rates.kernel_singleton]
  rw [setLIntegral_congr_fun ha hstep, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm,
    Measure.map_apply (measurable_frestrictLe n) ha, hpre]

/-- Joint state and clock cylinders factor into state-path and clock masses. -/
theorem historyLaw_joint_cylinder (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) (x : ℕ → S)
    (B : ℕ → Set ℝ) (hB : ∀ k, MeasurableSet (B k)) :
    rates.historyLaw μ {h | ∀ k ≤ n, (h k).1 = x k ∧ (h k).2 ∈ B k} =
      (μ {x 0} * ∏ k ∈ Finset.range n, ENNReal.ofReal (rates.p (x k) (x (k + 1)))) *
        ∏ k ∈ Finset.range (n + 1), rates.clockLaw (B k) := by
  induction n with
  | zero =>
    have heq := congrArg (fun ν : Measure (S × ℝ) ↦ ν ({x 0} ×ˢ B 0))
      (rates.historyLaw_map_zero μ)
    rw [Measure.map_apply (by fun_prop) ((measurableSet_singleton _).prod (hB 0)),
      Measure.prod_prod] at heq
    change rates.historyLaw μ {h | (h 0).1 = x 0 ∧ (h 0).2 ∈ B 0} = _ at heq
    simpa only [Nat.le_zero, forall_eq, Finset.range_zero, Finset.prod_empty,
      mul_one, Finset.prod_range_succ, zero_add, one_mul] using heq
  | succ n ih =>
    rw [rates.historyLaw_joint_cylinder_succ μ n x B hB, ih]
    simp only [Finset.prod_range_succ]
    ac_rfl

/-- Fixing a finite state path leaves the product clock law, scaled by its state mass. -/
theorem historyLaw_restrict_state_map_clocks (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) (x : ↥(Finset.Iic n) → S) :
    ((rates.historyLaw μ).restrict
      {h | ∀ k : ↥(Finset.Iic n), (h k).1 = x k}).map
        (fun h (k : ↥(Finset.Iic n)) ↦ (h k).2) =
      rates.historyLaw μ {h | ∀ k : ↥(Finset.Iic n), (h k).1 = x k} •
        Measure.pi (fun _ : ↥(Finset.Iic n) ↦ rates.clockLaw) := by
  let clocks : History S → (↥(Finset.Iic n) → ℝ) := fun h k ↦ (h k).2
  have hc : Measurable clocks := by fun_prop
  have hbox (b : ↥(Finset.Iic n) → Set ℝ) (hb : ∀ k, MeasurableSet (b k)) :
      (((rates.historyLaw μ).restrict
        {h : History S | ∀ k : ↥(Finset.Iic n), (h k).1 = x k}).map clocks)
          (Set.pi univ b) =
        rates.historyLaw μ {h | ∀ k : ↥(Finset.Iic n), (h k).1 = x k} *
          ∏ k, rates.clockLaw (b k) := by
    let y : ℕ → S := fun k ↦ x ⟨min k n, Finset.mem_Iic.mpr (min_le_right _ _)⟩
    let B : ℕ → Set ℝ := fun k ↦ b ⟨min k n, Finset.mem_Iic.mpr (min_le_right _ _)⟩
    have hpre : {h : History S | ∀ k : ↥(Finset.Iic n), (h k).1 = x k} =
        {h | ∀ k ≤ n, (h k).1 = y k} := by
      ext h
      simp only [Set.mem_setOf_eq, y]
      constructor
      · intro hh k hk
        simpa only [min_eq_left hk] using hh ⟨k, Finset.mem_Iic.mpr hk⟩
      · intro hh k
        simpa only [min_eq_left (Finset.mem_Iic.mp k.property)] using
          hh k (Finset.mem_Iic.mp k.property)
    have hjoint : clocks ⁻¹' Set.pi univ b ∩
        {h : History S | ∀ k : ↥(Finset.Iic n), (h k).1 = x k} =
        {h | ∀ k ≤ n, (h k).1 = y k ∧ (h k).2 ∈ B k} := by
      ext h
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
        forall_const, Set.mem_setOf_eq, clocks, y, B]
      constructor
      · rintro ⟨hc, hx⟩ k hk
        simpa only [min_eq_left hk] using
          And.intro (hx ⟨k, Finset.mem_Iic.mpr hk⟩) (hc ⟨k, Finset.mem_Iic.mpr hk⟩)
      · intro hh
        constructor <;> intro k
        · simpa only [min_eq_left (Finset.mem_Iic.mp k.property)] using
            (hh k (Finset.mem_Iic.mp k.property)).2
        · simpa only [min_eq_left (Finset.mem_Iic.mp k.property)] using
            (hh k (Finset.mem_Iic.mp k.property)).1
    rw [Measure.map_apply hc (MeasurableSet.pi (Set.to_countable _) (fun k _ ↦ hb k)),
      Measure.restrict_apply (hc (MeasurableSet.pi (Set.to_countable _) (fun k _ ↦ hb k))),
      hjoint, rates.historyLaw_joint_cylinder μ n y B (fun k ↦ hb _), hpre,
      rates.historyLaw_state_cylinder]
    congr 1
    exact Finset.prod_bij (fun k hk ↦ ⟨k, Finset.mem_Iic.mpr (by
      have := Finset.mem_range.mp hk; omega)⟩)
      (by intros; exact Finset.mem_univ _)
      (by intro a _ b _ hab; exact congrArg Subtype.val hab)
      (by intro k _; exact ⟨k, Finset.mem_range.mpr (by
        have := Finset.mem_Iic.mp k.property; omega), rfl⟩)
      (by
        intro k hk
        have hk_le : k ≤ n := by
          have := Finset.mem_range.mp hk
          omega
        simp only [B, min_eq_left hk_le])
  apply ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi
  · rintro _ ⟨b, hb, rfl⟩
    have hb' : ∀ k, MeasurableSet (b k) := fun k ↦ hb k (Set.mem_univ k)
    rw [hbox b hb', Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  · have h := hbox (fun _ ↦ univ) (fun _ ↦ MeasurableSet.univ)
    simpa only [Set.pi_univ, measure_univ, Finset.prod_const_one, mul_one,
      Measure.smul_apply, smul_eq_mul] using h

/-- The finite state prefix and clock prefix have a product law. -/
theorem historyLaw_map_states_clocks_prefix (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (rates.historyLaw μ).map
      (fun h ↦ ((fun k : ↥(Finset.Iic n) ↦ (h k).1),
        (fun k : ↥(Finset.Iic n) ↦ (h k).2))) =
      ((rates.historyLaw μ).map (fun h (k : ↥(Finset.Iic n)) ↦ (h k).1)).prod
        (Measure.pi (fun _ : ↥(Finset.Iic n) ↦ rates.clockLaw)) := by
  let states : History S → (↥(Finset.Iic n) → S) := fun h k ↦ (h k).1
  let clocks : History S → (↥(Finset.Iic n) → ℝ) := fun h k ↦ (h k).2
  have hs : Measurable states := by fun_prop
  have hc : Measurable clocks := by fun_prop
  apply Measure.ext_prod
  intro a b ha hb
  have hmeasure : ((rates.historyLaw μ).restrict (clocks ⁻¹' b)).map states =
      (Measure.pi (fun _ : ↥(Finset.Iic n) ↦ rates.clockLaw)) b •
        (rates.historyLaw μ).map states := by
    apply Measure.ext_of_singleton
    intro x
    have hx := congrArg (fun ν : Measure (↥(Finset.Iic n) → ℝ) ↦ ν b)
      (rates.historyLaw_restrict_state_map_clocks μ n x)
    have hstate : states ⁻¹' {x} =
        {h : History S | ∀ k : ↥(Finset.Iic n), (h k).1 = x k} := by
      ext h
      exact funext_iff
    rw [Measure.map_apply hc hb, Measure.restrict_apply (hc hb),
      Measure.smul_apply, smul_eq_mul, ← hstate] at hx
    rw [Measure.map_apply hs (measurableSet_singleton _),
      Measure.restrict_apply (hs (measurableSet_singleton _)),
      Measure.smul_apply, Measure.map_apply hs (measurableSet_singleton _), smul_eq_mul]
    change rates.historyLaw μ (states ⁻¹' {x} ∩ clocks ⁻¹' b) = _
    rw [Set.inter_comm, mul_comm]
    exact hx
  rw [Measure.map_apply (by fun_prop) (ha.prod hb), Measure.prod_prod]
  have heq := congrArg (fun ν : Measure (↥(Finset.Iic n) → S) ↦ ν a) hmeasure
  rw [Measure.map_apply hs ha, Measure.restrict_apply (hs ha),
    Measure.smul_apply, smul_eq_mul, mul_comm] at heq
  exact heq

/-- Every finite embedded-state prefix is independent of the corresponding clock prefix. -/
theorem indepFun_states_clocks_prefix (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (fun h (k : ↥(Finset.Iic n)) ↦ (h k).1)
      (fun h (k : ↥(Finset.Iic n)) ↦ (h k).2) (rates.historyLaw μ) := by
  have hs : Measurable (fun h : History S ↦ fun k : ↥(Finset.Iic n) ↦ (h k).1) := by
    fun_prop
  have hc : Measurable (fun h : History S ↦ fun k : ↥(Finset.Iic n) ↦ (h k).2) := by
    fun_prop
  letI : IsProbabilityMeasure
      ((rates.historyLaw μ).map (fun h (k : ↥(Finset.Iic n)) ↦ (h k).1)) :=
    Measure.isProbabilityMeasure_map hs.aemeasurable
  have hlaw := rates.historyLaw_map_states_clocks_prefix μ n
  have hclock := congrArg (fun ν ↦ ν.map Prod.snd) hlaw
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod,
    measure_univ, one_smul] at hclock
  change (rates.historyLaw μ).map (fun h (k : ↥(Finset.Iic n)) ↦ (h k).2) =
    Measure.pi (fun _ : ↥(Finset.Iic n) ↦ rates.clockLaw) at hclock
  apply (indepFun_iff_map_prod_eq_prod_map_map hs.aemeasurable hc.aemeasurable).mpr
  rw [hclock]
  exact hlaw

/-- The state at a clock ring is independent of all clocks through that ring. -/
theorem indepFun_state_clocks_prefix (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (fun h : History S ↦ (h n).1)
      (fun h (k : ↥(Finset.Iic n)) ↦ (h k).2) (rates.historyLaw μ) := by
  exact (rates.indepFun_states_clocks_prefix μ n).comp
    (measurable_pi_apply ⟨n, Finset.mem_Iic.mpr le_rfl⟩) measurable_id

/-- The entire embedded state sequence is independent of the entire clock sequence. -/
theorem indepFun_states_clocks (rates : BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] :
    IndepFun (fun h k ↦ (h k).1) (fun h k ↦ (h k).2) (rates.historyLaw μ) := by
  apply IndepFun.process_indepFun_process (fun _ ↦ by fun_prop) (fun _ ↦ by fun_prop)
  intro I J
  let n := max (I.sup id) (J.sup id)
  exact (rates.indepFun_states_clocks_prefix μ n).comp
    (show Measurable (fun x (k : I) ↦ x ⟨k, Finset.mem_Iic.mpr (by
      exact le_trans (Finset.le_sup (f := id) k.property) (le_max_left _ _))⟩) by fun_prop)
    (show Measurable (fun x (k : J) ↦ x ⟨k, Finset.mem_Iic.mpr (by
      exact le_trans (Finset.le_sup (f := id) k.property) (le_max_right _ _))⟩) by fun_prop)

end BoundedRates

end

end LatticeProb.JumpChain
