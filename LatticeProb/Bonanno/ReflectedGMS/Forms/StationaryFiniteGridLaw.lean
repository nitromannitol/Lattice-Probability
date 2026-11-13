/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryFiniteGridLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryReflectedLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedMarkovConditional

/-! Finite-dimensional cylinder masses for the actual reflected process under
the unnormalized stationary speed law. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The vertex cylinder on the first `n + 1` points of a constant-time-step grid. -/
def reflectedGridEvent (PF : ProcessFamily V) (δ : ℝ≥0) (n : ℕ)
    (v : ℕ → V) : Set PF.Ω :=
  {ω | ∀ i ∈ Finset.range (n + 1), PF.X ((i : ℝ≥0) * δ) ω = some (v i)}

lemma measurableSet_reflectedGridEvent (PF : ProcessFamily V) (δ : ℝ≥0) (n : ℕ)
    (v : ℕ → V) : MeasurableSet (reflectedGridEvent PF δ n v) := by
  classical
  rw [show reflectedGridEvent PF δ n v =
      ⋂ i ∈ (Finset.range (n + 1) : Set ℕ),
        {ω | PF.X ((i : ℝ≥0) * δ) ω = some (v i)} by
    ext ω
    simp [reflectedGridEvent]]
  apply MeasurableSet.biInter (Finset.range (n + 1)).countable_toSet
  intro i hi
  exact (PF.measurable_X ((i : ℝ≥0) * δ)) (measurableSet_singleton (some (v i)))

lemma measurableSet_reflectedGridEvent_naturalFiltration
    (PF : ProcessFamily V) (δ : ℝ≥0) (n : ℕ) (v : ℕ → V) :
    MeasurableSet[PF.naturalFiltration ((n : ℝ≥0) * δ)]
      (reflectedGridEvent PF δ n v) := by
  classical
  induction n with
  | zero =>
      convert (ReflectedMarkovConditional.measurableSet_vertexFiber_naturalFiltration
        (PF := PF) 0 (v 0)) using 1 <;> simp [reflectedGridEvent]
  | succ n ih =>
      rw [show reflectedGridEvent PF δ (n + 1) v =
          reflectedGridEvent PF δ n v ∩
            {ω | PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω = some (v (n + 1))} by
        ext ω
        simp only [reflectedGridEvent, mem_ofPred_eq, mem_inter_iff, Finset.mem_range]
        constructor
        · intro h
          exact ⟨fun i hi => h i (by omega), h (n + 1) (by omega)⟩
        · rintro ⟨h, hn⟩ i hi
          by_cases hin : i = n + 1
          · simpa [hin] using hn
          · exact h i (by omega)]
      have ih' : @MeasurableSet PF.Ω
          (PF.naturalFiltration ((n : ℝ≥0) * δ)) (reflectedGridEvent PF δ n v) := ih
      have ih'' : @MeasurableSet PF.Ω
          (PF.naturalFiltration (((n + 1 : ℕ) : ℝ≥0) * δ))
          (reflectedGridEvent PF δ n v) :=
        (PF.naturalFiltration.mono (by gcongr; omega))
          (reflectedGridEvent PF δ n v) ih'
      exact ih''.inter
        (ReflectedMarkovConditional.measurableSet_vertexFiber_naturalFiltration
          (PF := PF) (((n + 1 : ℕ) : ℝ≥0) * δ) (v (n + 1)))

private lemma reflectedGridEvent_succ (PF : ProcessFamily V) (δ : ℝ≥0) (n : ℕ)
    (v : ℕ → V) :
    reflectedGridEvent PF δ (n + 1) v =
      reflectedGridEvent PF δ n v ∩
        {ω | PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω = some (v (n + 1))} := by
  ext ω
  simp only [reflectedGridEvent, mem_setOf_eq, mem_inter_iff, Finset.mem_range]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h (n + 1) (by omega)⟩
  · rintro ⟨h, hn⟩ i hi
    by_cases hin : i = n + 1
    · simpa [hin] using hn
    · exact h i (by omega)

/-- Fixed-start finite-grid cylinder probability.  This includes `δ = 0`. -/
theorem reflected_gridEvent_start_real
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun x => G.pi x / m x) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ x, 0 < m x)
    (hmsum : Summable m) (δ : ℝ≥0) (n : ℕ) (v : ℕ → V) :
    (PF.P (v 0)).real (reflectedGridEvent PF δ n v) =
      ∏ i ∈ Finset.range n, semigroupKernel G m δ (v i) (v (i + 1)) := by
  induction n with
  | zero =>
      rw [show reflectedGridEvent PF δ 0 v =
          {ω | PF.X 0 ω = some (v 0)} by ext ω; simp [reflectedGridEvent]]
      simp only [Finset.range_zero, Finset.prod_empty]
      rw [measureReal_def,
        reflected_vertexProbability_eq_semigroupKernel h hG hm hmsum 0 (v 0) (v 0)]
      rw [semigroupKernel_zero G m hm]
      simp [ConductanceGraph.indic]
  | succ n ih =>
      let F := reflectedGridEvent PF δ n v
      let f : V → ℝ := fun y => if y = v (n + 1) then 1 else 0
      have hf : ∀ y, ‖f y‖ ≤ (1 : ℝ) := by
        intro y
        simp only [f]
        split <;> norm_num
      have hstep := ReflectedMarkovConditional.setIntegral_vertexFiber
        h (v 0) (v n) (s := (n : ℝ≥0) * δ)
        (t := ((n + 1 : ℕ) : ℝ≥0) * δ)
        (by gcongr; omega) f 1 hf
        (measurableSet_reflectedGridEvent_naturalFiltration PF δ n v)
      have hsub : (((n + 1 : ℕ) : ℝ≥0) * δ - (n : ℝ≥0) * δ) = δ := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_left]
      have htransition :
          (∫ ω, (PF.X ((((n + 1 : ℕ) : ℝ≥0) * δ) - (n : ℝ≥0) * δ) ω).elim 0 f
            ∂PF.P (v n)) = semigroupKernel G m δ (v n) (v (n + 1)) := by
        rw [hsub]
        have hmeas := PF.measurable_X δ
        rw [show (fun ω => (PF.X δ ω).elim 0 f) =
            {ω | PF.X δ ω = some (v (n + 1))}.indicator (fun _ => (1 : ℝ)) by
          funext ω
          cases hq : PF.X δ ω with
          | none => simp [f, hq]
          | some y => by_cases hy : y = v (n + 1) <;> simp [f, hq, hy]]
        have hI := integral_indicator_const (μ := PF.P (v n)) (1 : ℝ)
          (hmeas (measurableSet_singleton (some (v (n + 1)))))
        calc
          _ = (PF.P (v n)).real {ω | PF.X δ ω = some (v (n + 1))} := by
            simpa only [Set.preimage, Set.mem_singleton_iff, smul_eq_mul, mul_one] using hI
          _ = _ := by
            rw [measureReal_def,
              reflected_vertexProbability_eq_semigroupKernel h hG hm hmsum]
      rw [htransition] at hstep
      have hF := measurableSet_reflectedGridEvent PF δ n v
      have hnext : MeasurableSet
          {ω | PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω = some (v (n + 1))} :=
        PF.measurable_X _ (measurableSet_singleton _)
      have hleft :
          (∫ ω in F, {ω | PF.X ((n : ℝ≥0) * δ) ω = some (v n)}.indicator
              (fun ω => (PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω).elim 0 f) ω
              ∂PF.P (v 0)) =
            (PF.P (v 0)).real
              (F ∩ {ω | PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω = some (v (n + 1))}) := by
        calc
          _ = ∫ ω in F,
                {ω | PF.X (((n + 1 : ℕ) : ℝ≥0) * δ) ω = some (v (n + 1))}.indicator
                  (fun _ => (1 : ℝ)) ω ∂PF.P (v 0) := by
              apply setIntegral_congr_fun hF
              intro ω hω
              have hn := hω n (by simp [F, reflectedGridEvent])
              simp only [Nat.cast_add, Nat.cast_one]
              cases hq : PF.X (((n : ℝ≥0) + 1) * δ) ω with
              | none => simp [hn, f, hq]
              | some y => by_cases hy : y = v (n + 1) <;> simp [hn, f, hq, hy]
          _ = _ := by
            rw [integral_indicator_const (1 : ℝ) hnext,
              measureReal_restrict_apply hnext, smul_eq_mul, mul_one, inter_comm]
      have hright :
          (∫ ω in F, {ω | PF.X ((n : ℝ≥0) * δ) ω = some (v n)}.indicator
              (fun _ => semigroupKernel G m δ (v n) (v (n + 1))) ω ∂PF.P (v 0)) =
            (PF.P (v 0)).real F * semigroupKernel G m δ (v n) (v (n + 1)) := by
        calc
          _ = ∫ _ in F, semigroupKernel G m δ (v n) (v (n + 1)) ∂PF.P (v 0) := by
            apply setIntegral_congr_fun hF
            intro ω hω
            have hn := hω n (by simp [F, reflectedGridEvent])
            simp [hn]
          _ = _ := by rw [setIntegral_const, smul_eq_mul]
      rw [reflectedGridEvent_succ]
      rw [Finset.prod_range_succ, ← ih]
      exact hleft.symm.trans (hstep.trans hright)

/-- Finite-grid cylinder mass under the unnormalized stationary speed law. -/
theorem reflectedSpeedLaw_reflectedGridEvent_real
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun x => G.pi x / m x) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ x, 0 < m x)
    (hmsum : Summable m) (δ : ℝ≥0) (n : ℕ) (v : ℕ → V) :
    (reflectedSpeedLaw PF m).real (reflectedGridEvent PF δ n v) =
      m (v 0) * ∏ i ∈ Finset.range n,
        semigroupKernel G m δ (v i) (v (i + 1)) := by
  classical
  let E := reflectedGridEvent PF δ n v
  have hE : MeasurableSet E := measurableSet_reflectedGridEvent PF δ n v
  have hstart (z : V) :
      PF.P z E = if z = v 0 then PF.P (v 0) E else 0 := by
    by_cases hz : z = v 0
    · subst z
      simp
    · rw [if_neg hz]
      apply measure_mono_null (t := {ω | PF.X 0 ω ≠ some z})
      · intro ω hω hzero
        apply hz
        have hv := hω 0 (by simp [E, reflectedGridEvent])
        exact Option.some.inj (hzero.symm.trans (by simpa using hv))
      · simpa only [ae_iff, mem_compl_iff, mem_setOf_eq, not_not] using (h z).1
  have hmass :
      reflectedSpeedLaw PF m E = ENNReal.ofReal (m (v 0)) * PF.P (v 0) E := by
    unfold reflectedSpeedLaw
    rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ hE]
    simp only [vertexSpeedMeasure_singleton, Measure.smul_apply, smul_eq_mul]
    change (∑' z, ENNReal.ofReal (m z) * PF.P z E) = _
    rw [tsum_eq_single (v 0)]
    · intro z hz
      rw [hstart, if_neg hz]
      simp
  rw [measureReal_def, hmass, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hm (v 0)).le]
  rw [← measureReal_def, reflected_gridEvent_start_real h hG hm hmsum]

end ReflectedGMS
