/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteTraceRenewal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceTransition
import LatticeProb.Bonanno.ReflectedGMS.Forms.ParameterizedResolvent
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventEquation

/-!
# The finite-trace resolvent as a discounted renewal equation

Testing the genuine finite-trace resolvent against vertex indicators gives its
coordinate equation.  The checked identification of trace conductances with
the induced transition kernel then turns this into the discounted renewal
equation for exponential trials.  The induced kernel includes returns to the
current vertex; in particular, the statement also covers singleton targets.

This is an analytic resolvent identity and uniqueness result.  It does not by
itself identify the resolvent with the occupation law of a path process.
-/

set_option autoImplicit false

open Classical
open scoped BigOperators InnerProductSpace

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- The exponential trial rate at a vertex, before self returns are removed. -/
noncomputable def finiteTraceTrialRate
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {A : Finset V} (x : {v // v ∈ A}) : ℝ :=
  G.pi x.1 / m x.1

/-- The occupation-normalized resolvent on a finite trace. -/
noncomputable def finiteTraceOccupationResolvent
    (G : ReflectedWalk.ConductanceGraph V) (hG : G.toSimpleGraph.Connected)
    (A : Finset V) (hA : A.Nonempty) (m : V → ℝ) (alpha : ℝ)
    (fWeighted : ValueSpace {x // x ∈ A}) : {x // x ∈ A} → ℝ :=
  fun x => (1 / alpha) *
    parameterizedResolventFunction (finiteTargetGraph G hG A hA)
      (fun y => m y.1) (1 / alpha) fWeighted x

private theorem mul_parameterizedResolventFunction_eq_value_mul_sqrt
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (h : ℝ) (f : ValueSpace V) (v : V) :
    m v * parameterizedResolventFunction G m h f v =
      parameterizedResolvent G m h f v * Real.sqrt (m v) := by
  unfold parameterizedResolventFunction unweight
  calc
    m v * (parameterizedResolvent G m h f v / Real.sqrt (m v)) =
        (Real.sqrt (m v) * Real.sqrt (m v)) *
          (parameterizedResolvent G m h f v / Real.sqrt (m v)) := by
      rw [Real.mul_self_sqrt (hm v).le]
    _ = parameterizedResolvent G m h f v * Real.sqrt (m v) := by
      field_simp [Real.sqrt_pos.2 (hm v)]

/-- Delta testing of the genuine parameterized resolvent. -/
theorem parameterizedResolventFunction_vertex_equation
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) {h : ℝ} (hh : 0 < h)
    (f : ValueSpace V) (v : V) :
    m v * parameterizedResolventFunction G m h f v -
        h * (∑' w : V,
          G.lapTerm (parameterizedResolventFunction G m h f) v w) =
      Real.sqrt (m v) * f v := by
  classical
  have hweak := parameterizedResolventFunction_weak G m hm hh f (G.indic v)
    (VertexTest.indic_hasSpeedL2 G m v) (VertexTest.indic_hasFiniteEnergy G v)
  rw [weightedValue_indic_eq_single G m v,
    lp.inner_single_right, lp.inner_single_right] at hweak
  rw [VertexTest.dirichletForm_indic_eq_neg_laplacian G
    (parameterizedResolventFunction G m h f)
    (parameterizedResolventFunction_hasFiniteEnergy G m h f) v] at hweak
  rw [mul_parameterizedResolventFunction_eq_value_mul_sqrt G m hm h f v]
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm] using hweak

private theorem finite_sum_inducedTransProb
    [Nontrivial V] (G : ReflectedWalk.ConductanceGraph V)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (x : {v // v ∈ A}) :
    (∑ y : {v // v ∈ A}, G.inducedTransProb hG A x.1 y.1) = 1 := by
  calc
    (∑ y : {v // v ∈ A}, G.inducedTransProb hG A x.1 y.1) =
        ∑ y ∈ A, G.inducedTransProb hG A x.1 y := Finset.sum_attach A _
    _ = ∑' y : V, G.inducedTransProb hG A x.1 y :=
      (tsum_eq_sum (s := A)
        (fun y hy => G.inducedTransProb_of_not_mem_right hG hy)).symm
    _ = 1 := G.tsum_inducedTransProb hG hA x.1

private theorem finiteTrace_lapTerm_eq
    [Nontrivial V] (G : ReflectedWalk.ConductanceGraph V)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (u : {v // v ∈ A} → ℝ) (x y : {v // v ∈ A}) :
    (finiteTargetGraph G hG A hA).lapTerm u x y =
      G.pi x.1 * G.inducedTransProb hG A x.1 y.1 * (u y - u x) := by
  by_cases hxy : x = y
  · subst y
    simp [ReflectedWalk.ConductanceGraph.lapTerm]
  · rw [ReflectedWalk.ConductanceGraph.lapTerm,
      finiteTargetGraph_c_of_ne G hG A hA hxy,
      ← pi_mul_inducedTransProb G hG hA x.2 y.2]

/-- The finite trace occupation resolvent satisfies the discounted renewal
equation for the actual induced transition kernel, including self returns. -/
theorem finiteTraceOccupationResolvent_renewal
    [Nontrivial V] (G : ReflectedWalk.ConductanceGraph V)
    (hG : G.toSimpleGraph.Connected) (A : Finset V) (hA : A.Nonempty)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) {alpha : ℝ} (halpha : 0 < alpha)
    (fWeighted : ValueSpace {x // x ∈ A}) (x : {v // v ∈ A}) :
    finiteTraceOccupationResolvent G hG A hA m alpha fWeighted x =
      unweight (fun y : {v // v ∈ A} => m y.1) fWeighted x /
          (alpha + finiteTraceTrialRate G m x) +
        ∑ y : {v // v ∈ A},
          (finiteTraceTrialRate G m x /
              (alpha + finiteTraceTrialRate G m x)) *
            G.inducedTransProb hG A x.1 y.1 *
            finiteTraceOccupationResolvent G hG A hA m alpha fWeighted y := by
  let T := finiteTargetGraph G hG A hA
  let mA : {v // v ∈ A} → ℝ := fun y => m y.1
  let r := parameterizedResolventFunction T mA (1 / alpha) fWeighted
  let u := finiteTraceOccupationResolvent G hG A hA m alpha fWeighted
  have haInv : 0 < 1 / alpha := one_div_pos.mpr halpha
  have hpoint := parameterizedResolventFunction_vertex_equation T mA
    (fun y => hm y.1) haInv fWeighted x
  change m x.1 * r x - (1 / alpha) *
      (∑' y : {v // v ∈ A}, T.lapTerm r x y) =
    Real.sqrt (m x.1) * fWeighted x at hpoint
  have hsqrt : Real.sqrt (m x.1) * fWeighted x =
      m x.1 * unweight mA fWeighted x := by
    unfold unweight
    symm
    calc
      m x.1 * (fWeighted x / Real.sqrt (m x.1)) =
          (Real.sqrt (m x.1) * Real.sqrt (m x.1)) *
            (fWeighted x / Real.sqrt (m x.1)) := by
        rw [Real.mul_self_sqrt (hm x.1).le]
      _ = fWeighted x * Real.sqrt (m x.1) := by
        field_simp [Real.sqrt_pos.2 (hm x.1)]
      _ = Real.sqrt (m x.1) * fWeighted x := mul_comm _ _
  have hm0 : m x.1 ≠ 0 := (hm x.1).ne'
  have ha0 : alpha ≠ 0 := halpha.ne'
  have hden : 0 < alpha + finiteTraceTrialRate G m x := by
    exact add_pos_of_pos_of_nonneg halpha
      (div_nonneg (G.pi_nonneg x.1) (hm x.1).le)
  change u x =
    unweight mA fWeighted x / (alpha + finiteTraceTrialRate G m x) +
      ∑ y, (finiteTraceTrialRate G m x /
        (alpha + finiteTraceTrialRate G m x)) *
          G.inducedTransProb hG A x.1 y.1 * u y
  have hu (y : {v // v ∈ A}) : r y = alpha * u y := by
    dsimp [r, u, T, mA, finiteTraceOccupationResolvent]
    field_simp [ha0]
  rw [show (∑' y : {v // v ∈ A}, T.lapTerm r x y) =
      ∑ y : {v // v ∈ A},
        G.pi x.1 * G.inducedTransProb hG A x.1 y.1 * (r y - r x) by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro y hy
      exact finiteTrace_lapTerm_eq G hG hA r x y] at hpoint
  simp_rw [hu] at hpoint
  rw [hsqrt] at hpoint
  have hrow := finite_sum_inducedTransProb G hG hA x
  let S := ∑ y : {v // v ∈ A},
    G.inducedTransProb hG A x.1 y.1 * u y
  have hsumdiff :
      (∑ y : {v // v ∈ A},
        G.inducedTransProb hG A x.1 y.1 * (u y - u x)) = S - u x := by
    dsimp [S]
    calc
      _ = ∑ y : {v // v ∈ A},
          (G.inducedTransProb hG A x.1 y.1 * u y -
            G.inducedTransProb hG A x.1 y.1 * u x) := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (∑ y : {v // v ∈ A},
          G.inducedTransProb hG A x.1 y.1 * u y) -
          ∑ y : {v // v ∈ A},
            G.inducedTransProb hG A x.1 y.1 * u x := by
        exact Finset.sum_sub_distrib
          (s := Finset.univ)
          (fun y : {v // v ∈ A} => G.inducedTransProb hG A x.1 y.1 * u y)
          (fun y : {v // v ∈ A} => G.inducedTransProb hG A x.1 y.1 * u x)
      _ = (∑ y : {v // v ∈ A},
          G.inducedTransProb hG A x.1 y.1 * u y) - u x := by
        rw [← Finset.sum_mul, hrow, one_mul]
  have hlapsum :
      (∑ y : {v // v ∈ A},
        G.pi x.1 * G.inducedTransProb hG A x.1 y.1 *
          (alpha * u y - alpha * u x)) =
        G.pi x.1 * alpha * (S - u x) := by
    calc
      _ = ∑ y : {v // v ∈ A},
          (G.pi x.1 * alpha) *
            (G.inducedTransProb hG A x.1 y.1 * (u y - u x)) := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (G.pi x.1 * alpha) *
          ∑ y : {v // v ∈ A},
            G.inducedTransProb hG A x.1 y.1 * (u y - u x) := by
        rw [Finset.mul_sum]
      _ = G.pi x.1 * alpha * (S - u x) := by rw [hsumdiff]
  rw [hlapsum] at hpoint
  have hbalance :
      (alpha + finiteTraceTrialRate G m x) * u x =
        unweight mA fWeighted x + finiteTraceTrialRate G m x * S := by
    dsimp [finiteTraceTrialRate]
    field_simp [hm0, ha0] at hpoint ⊢
    linear_combination hpoint
  have hsumrenew :
      (∑ y : {v // v ∈ A},
        (finiteTraceTrialRate G m x /
            (alpha + finiteTraceTrialRate G m x)) *
          G.inducedTransProb hG A x.1 y.1 * u y) =
      (finiteTraceTrialRate G m x /
          (alpha + finiteTraceTrialRate G m x)) * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hsumrenew]
  field_simp [hden.ne']
  simpa [mul_comm] using hbalance

/-- The discounted renewal equation has at most one real-valued solution on
the finite target.  This is the finite sup-norm contraction argument. -/
theorem finiteTraceRenewal_unique
    [Nontrivial V] (G : ReflectedWalk.ConductanceGraph V)
    (hG : G.toSimpleGraph.Connected) (A : Finset V) (hA : A.Nonempty)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) {alpha : ℝ} (halpha : 0 < alpha)
    (F u v : {x // x ∈ A} → ℝ)
    (hu : ∀ x, u x = F x / (alpha + finiteTraceTrialRate G m x) +
      ∑ y, (finiteTraceTrialRate G m x /
          (alpha + finiteTraceTrialRate G m x)) *
        G.inducedTransProb hG A x.1 y.1 * u y)
    (hv : ∀ x, v x = F x / (alpha + finiteTraceTrialRate G m x) +
      ∑ y, (finiteTraceTrialRate G m x /
          (alpha + finiteTraceTrialRate G m x)) *
        G.inducedTransProb hG A x.1 y.1 * v y) :
    u = v := by
  classical
  letI : Nonempty {x // x ∈ A} :=
    ⟨⟨hA.choose, hA.choose_spec⟩⟩
  let d : {x // x ∈ A} → ℝ := fun x => u x - v x
  obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image Finset.univ (fun z => |d z|)
    Finset.univ_nonempty
  have hd (z : {x // x ∈ A}) : d z =
      (finiteTraceTrialRate G m z /
          (alpha + finiteTraceTrialRate G m z)) *
        ∑ y, G.inducedTransProb hG A z.1 y.1 * d y := by
    rw [show d z = u z - v z by rfl, hu z, hv z]
    simp only [add_sub_add_left_eq_sub]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    simp only [d]
    ring
  have hw0 (z : {x // x ∈ A}) : 0 ≤ finiteTraceTrialRate G m z :=
    div_nonneg (G.pi_nonneg z.1) (hm z.1).le
  have hden0 (z : {x // x ∈ A}) :
      0 < alpha + finiteTraceTrialRate G m z :=
    add_pos_of_pos_of_nonneg halpha (hw0 z)
  have hq0 : 0 ≤ finiteTraceTrialRate G m x /
      (alpha + finiteTraceTrialRate G m x) := by
    exact div_nonneg (hw0 x) (hden0 x).le
  have hq1 : finiteTraceTrialRate G m x /
      (alpha + finiteTraceTrialRate G m x) < 1 := by
    rw [div_lt_one (hden0 x)]
    linarith
  have hbound : |d x| ≤
      (finiteTraceTrialRate G m x /
        (alpha + finiteTraceTrialRate G m x)) * |d x| := by
    calc
      |d x| = (finiteTraceTrialRate G m x /
          (alpha + finiteTraceTrialRate G m x)) *
          |∑ (y : {x // x ∈ A}), G.inducedTransProb hG A x.1 y.1 * d y| := by
        rw [hd x, abs_mul, abs_of_nonneg hq0]
      _ ≤ (finiteTraceTrialRate G m x /
          (alpha + finiteTraceTrialRate G m x)) *
          ∑ (y : {x // x ∈ A}), |G.inducedTransProb hG A x.1 y.1 * d y| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hq0
      _ = (finiteTraceTrialRate G m x /
          (alpha + finiteTraceTrialRate G m x)) *
          ∑ (y : {x // x ∈ A}), G.inducedTransProb hG A x.1 y.1 * |d y| := by
        congr 1
        apply Finset.sum_congr rfl
        intro (y : {x // x ∈ A}) hy
        rw [abs_mul, abs_of_nonneg (G.inducedTransProb_nonneg hG hA x.1 y.1)]
      _ ≤ (finiteTraceTrialRate G m x /
          (alpha + finiteTraceTrialRate G m x)) *
          ∑ (y : {x // x ∈ A}), G.inducedTransProb hG A x.1 y.1 * |d x| := by
        apply mul_le_mul_of_nonneg_left _ hq0
        apply Finset.sum_le_sum
        intro (y : {x // x ∈ A}) hy
        exact mul_le_mul_of_nonneg_left (hxmax y (by simp))
          (G.inducedTransProb_nonneg hG hA x.1 y.1)
      _ = (finiteTraceTrialRate G m x /
          (alpha + finiteTraceTrialRate G m x)) * |d x| := by
        rw [← Finset.sum_mul, finite_sum_inducedTransProb G hG hA x, one_mul]
  have hdx : d x = 0 := by
    have : |d x| = 0 := by nlinarith [abs_nonneg (d x)]
    exact abs_eq_zero.mp this
  funext z
  have hz : |d z| ≤ |d x| := hxmax z (by simp)
  have habs : |d z| = 0 :=
    le_antisymm (by simpa [hdx] using hz) (abs_nonneg _)
  have : d z = 0 := abs_eq_zero.mp habs
  exact sub_eq_zero.mp this

/-- Consequently, the analytic occupation resolvent is the unique solution of
the finite discounted renewal equation. -/
theorem finiteTraceOccupationResolvent_eq_of_renewal
    [Nontrivial V] (G : ReflectedWalk.ConductanceGraph V)
    (hG : G.toSimpleGraph.Connected) (A : Finset V) (hA : A.Nonempty)
    (m : V → ℝ) (hm : ∀ v, 0 < m v) {alpha : ℝ} (halpha : 0 < alpha)
    (fWeighted : ValueSpace {x // x ∈ A}) (u : {x // x ∈ A} → ℝ)
    (hu : ∀ x, u x =
      unweight (fun y : {v // v ∈ A} => m y.1) fWeighted x /
          (alpha + finiteTraceTrialRate G m x) +
        ∑ y, (finiteTraceTrialRate G m x /
            (alpha + finiteTraceTrialRate G m x)) *
          G.inducedTransProb hG A x.1 y.1 * u y) :
    u = finiteTraceOccupationResolvent G hG A hA m alpha fWeighted := by
  apply finiteTraceRenewal_unique G hG A hA m hm halpha
    (fun x => unweight (fun y : {v // v ∈ A} => m y.1) fWeighted x)
    u (finiteTraceOccupationResolvent G hG A hA m alpha fWeighted) hu
  exact finiteTraceOccupationResolvent_renewal G hG A hA m hm halpha fWeighted

end ReflectedGMS.FullNetworkForm
