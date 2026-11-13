/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2Avoid at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2VisitGen

 







set_option autoImplicit false
noncomputable section

open Matrix Complex

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 
structure IsAvoidHarmonic (A : Set V) (Y : V → ℝ) : Prop where
  zero_on : ∀ a ∈ A, Y a = 0
  harm : ∀ v ∉ A, (G.precision *ᵥ Y) v = G.boundary v

theorem exists_avoidHarmonic (hK : G.precision.PosDef) (A : Set V) [DecidablePred (· ∈ A)] :
    ∃ Y, G.IsAvoidHarmonic A Y := by
  let U := {v : V // v ∉ A}
  let KU : Matrix U U ℝ := G.precision.submatrix Subtype.val Subtype.val
  have hKU : KU.PosDef := hK.submatrix Subtype.val_injective
  let YU : U → ℝ := KU⁻¹ *ᵥ fun u => G.boundary u.1
  have hYU : KU *ᵥ YU = fun u => G.boundary u.1 := by
    simp only [YU, Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hKU.isUnit),
      Matrix.one_mulVec]
  refine ⟨fun v => if h : v ∈ A then 0 else YU ⟨v, h⟩, fun a ha => by simp [ha], ?_⟩
  intro v hv
  have h := congrFun hYU ⟨v, hv⟩
  rw [← h]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w => w ∉ A)]
  have hzero : ∑ w : {w : V // ¬ (w ∉ A)}, G.precision v w.1 *
      (if h : w.1 ∈ A then 0 else YU ⟨w.1, h⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    have : w.1 ∈ A := not_not.mp w.2
    simp [this]
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro w _
  simp only [KU, Matrix.submatrix_apply, w.2, dite_false]

 
def avoidMult (A : Set V) [DecidablePred (· ∈ A)] (v : V) : ℂ := if v ∈ A then 0 else 1

theorem avoidMult_norm_le (A : Set V) [DecidablePred (· ∈ A)] (v : V) :
    ‖avoidMult A v‖ ≤ 1 := by
  unfold avoidMult; split_ifs <;> simp

theorem visitProduct_avoidMult (A : Set V) [DecidablePred (· ∈ A)] (γ : Excursion V) :
    visitProduct (avoidMult A) γ = if ∀ j, γ.2 j ∉ A then 1 else 0 := by
  unfold visitProduct avoidMult
  by_cases h : ∀ j, γ.2 j ∉ A
  · rw [if_pos h]
    exact Finset.prod_eq_one fun j _ => by simp [h j]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

 
theorem hasSum_excursion_avoid (hK : G.precision.PosDef) (A : Set V) [DecidablePred (· ∈ A)]
    (Y : V → ℝ) (hY : G.IsAvoidHarmonic A Y) :
    HasSum (fun γ : Excursion V => if ∀ j, γ.2 j ∉ A then G.excursionWeight γ else 0)
      (∑ i, G.boundary i * Y i) := by
  have hfix : ∀ v, ((Y v : ℝ) : ℂ) = avoidMult A v * (((G.boundary v / G.totalRate v : ℝ) : ℂ) +
      ∑ j, (G.killedTransition v j : ℂ) * (Y j : ℂ)) := by
    intro v
    by_cases hv : v ∈ A
    · simp [avoidMult, hv, hY.zero_on v hv]
    · have := G.fixedPoint_of_precision_at hK (fun _ => 1) Y v one_ne_zero (by
        simp [hY.harm v hv])
      simpa [avoidMult, hv] using this
  have hF := G.hasSum_excursion_visitProduct hK (avoidMult A) (avoidMult_norm_le A)
    (fun v => ((Y v : ℝ) : ℂ)) hfix
  have hre := Complex.hasSum_re hF
  convert hre using 1
  · funext γ
    rw [visitProduct_avoidMult]
    split_ifs <;> simp
  · simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]

 
theorem hasSum_soupMass_avoid_set (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t)
    (A : Set V) [DecidablePred (· ∈ A)] (Y : V → ℝ) (hY : G.IsAvoidHarmonic A Y) :
    HasSum ({s : Soup (Excursion V) | ∀ i, (s.2 i) ∉ {γ : Excursion V | ∃ j, γ.2 j ∈ A}}.indicator
        (G.soupMassAt t))
      (Real.exp (-(t * (G.boundaryTotal - ∑ i, G.boundary i * Y i)))) := by
  have h := hasSum_soupMass_avoid G.excursionWeight_nonneg (G.hasSum_excursionWeight hK) ht
    {γ : Excursion V | ∃ j, γ.2 j ∈ A}
  have hav := G.hasSum_excursion_avoid hK A Y hY
  have hsplit : HasSum ({γ : Excursion V | ∃ j, γ.2 j ∈ A}.indicator G.excursionWeight)
      (G.boundaryTotal - ∑ i, G.boundary i * Y i) := by
    have := (G.hasSum_excursionWeight hK).sub hav
    have hfun : ({γ : Excursion V | ∃ j, γ.2 j ∈ A}.indicator G.excursionWeight) =
        fun γ => G.excursionWeight γ - (if ∀ j, γ.2 j ∉ A then G.excursionWeight γ else 0) := by
      funext γ
      by_cases hγ : ∃ j, γ.2 j ∈ A
      · have : ¬ ∀ j, γ.2 j ∉ A := fun h' => by obtain ⟨j, hj⟩ := hγ; exact h' j hj
        rw [Set.indicator_of_mem (show γ ∈ {γ : Excursion V | ∃ j, γ.2 j ∈ A} from hγ),
          if_neg this, sub_zero]
      · have : ∀ j, γ.2 j ∉ A := fun j hj => hγ ⟨j, hj⟩
        rw [Set.indicator_of_notMem (show γ ∉ {γ : Excursion V | ∃ j, γ.2 j ∈ A} from hγ),
          if_pos this, sub_self]
    rw [hfun]
    exact this
  rw [hsplit.tsum_eq] at h
  exact h

 
theorem isAvoidHarmonic_single (hK : G.precision.PosDef) (x : V) :
    G.IsAvoidHarmonic {x} (fun w => 1 - (1 / G.green x x) * G.green w x) := by
  have hG := (G.green_diag_pos hK x).ne'
  refine ⟨fun a ha => ?_, fun v hv => ?_⟩
  · rw [Set.mem_singleton_iff.mp ha]
    field_simp
    ring
  · rw [G.precision_mulVec_rankOne hK x]
    have : v ≠ x := hv
    simp [this]

theorem sum_boundary_single (hK : G.precision.PosDef) (x : V) :
    ∑ i, G.boundary i * (1 - (1 / G.green x x) * G.green i x) =
      G.boundaryTotal - 1 / G.green x x := by
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [show ∑ i, G.boundary i * (1 / G.green x x * G.green i x) =
      1 / G.green x x * ∑ i, G.boundary i * G.green i x by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring,
    G.sum_boundary_mul_green hK x, mul_one]
  rfl

theorem soupVisitCount_eq_zero_iff (s : Soup (Excursion V)) (x : V) :
    soupVisitCount s x = 0 ↔ ∀ i, (s.2 i) ∉ {γ : Excursion V | ∃ j, γ.2 j ∈ ({x} : Set V)} := by
  unfold soupVisitCount Excursion.visitCount
  rw [Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Set.mem_setOf_eq, Set.mem_singleton_iff, not_exists]

 
theorem hasSum_soupMass_visit_zero (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t) (x : V) :
    HasSum (fun s => if soupVisitCount s x = 0 then G.soupMassAt t s else 0)
      (Real.exp (-(t / G.green x x))) := by
  have h := G.hasSum_soupMass_avoid_set hK ht {x} _ (G.isAvoidHarmonic_single hK x)
  rw [G.sum_boundary_single hK x, show G.boundaryTotal - (G.boundaryTotal - 1 / G.green x x) =
    1 / G.green x x by ring, mul_one_div] at h
  convert h using 1
  funext s
  by_cases hs : soupVisitCount s x = 0
  · rw [if_pos hs, Set.indicator_of_mem (show s ∈ {s : Soup (Excursion V) |
      ∀ i, (s.2 i) ∉ {γ : Excursion V | ∃ j, γ.2 j ∈ ({x} : Set V)}} from
      (soupVisitCount_eq_zero_iff s x).mp hs)]
  · rw [if_neg hs, Set.indicator_of_notMem (show s ∉ {s : Soup (Excursion V) |
      ∀ i, (s.2 i) ∉ {γ : Excursion V | ∃ j, γ.2 j ∈ ({x} : Set V)}} from
      fun h' => hs ((soupVisitCount_eq_zero_iff s x).mpr h'))]

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
