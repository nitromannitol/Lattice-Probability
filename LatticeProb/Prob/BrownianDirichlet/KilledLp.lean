import LatticeProb.Prob.BrownianDirichlet.KilledL2Bound
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The killed Brownian contraction on L²

The bounded measurable kernel descends to L² and extends continuously from a dense
space. Its extension preserves the zero-time identity and the semigroup law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

namespace LatticeProb

noncomputable section

variable {d : ℕ}

/-- Bounded Borel functions, used only as the domain of the dense extension. -/
private def boundedBorel : Submodule ℝ (Euc d → ℝ) where
  carrier := {b | Measurable b ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |b y| ≤ C}
  zero_mem' := ⟨measurable_const, 0, le_rfl, fun _ ↦ by simp⟩
  add_mem' := by
    rintro b c ⟨hb, C, hC, hbC⟩ ⟨hc, D, hD, hcD⟩
    exact ⟨hb.add hc, C + D, add_nonneg hC hD,
      fun y ↦ (abs_add_le _ _).trans (add_le_add (hbC y) (hcD y))⟩
  smul_mem' := by
    rintro a b ⟨hb, C, hC, hbC⟩
    refine ⟨hb.const_smul a, |a| * C, mul_nonneg (abs_nonneg _) hC, ?_⟩
    intro y
    exact (abs_mul a (b y)).le.trans (mul_le_mul_of_nonneg_left (hbC y) (abs_nonneg a))

variable (B : Set (Euc d)) [IsFiniteMeasure (volume.restrict B)]

/-- Bounded Borel functions belong to L² on a finite-volume domain. -/
private lemma boundedBorel_memLp (b : boundedBorel (d := d)) :
    MemLp (b : Euc d → ℝ) 2 (volume.restrict B) := by
  obtain ⟨C, _, hbC⟩ := b.property.2
  exact MemLp.of_bound b.property.1.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y ↦ (Real.norm_eq_abs _).trans_le (hbC y))

/-- The quotient map from bounded Borel functions into L². -/
private def boundedBorelToLp : boundedBorel (d := d) →ₗ[ℝ]
    Lp ℝ 2 (volume.restrict B) where
  toFun b := (boundedBorel_memLp B b).toLp b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Simple functions witness density of the bounded Borel quotient map. -/
private lemma boundedBorelToLp_dense : DenseRange (boundedBorelToLp B) := by
  apply (Lp.simpleFunc.denseRange (E := ℝ) (μ := volume.restrict B)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mono
  rintro _ ⟨f, rfl⟩
  let b := Lp.simpleFunc.toSimpleFunc f
  obtain ⟨C, hC⟩ := b.exists_forall_norm_le
  let g : boundedBorel (d := d) := ⟨b, b.measurable, max C 0, le_max_right _ _,
    fun y ↦ (Real.norm_eq_abs _).symm.trans_le ((hC y).trans (le_max_left _ _))⟩
  refine ⟨g, ?_⟩
  exact congrArg Subtype.val (Lp.simpleFunc.toLp_toSimpleFunc f)

variable {B} (hB : IsOpen B) (σ : ℝ) {μ : Measure (BrownianPath d)}
  (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0)

/-- The killed kernel on bounded Borel functions, with values in L². -/
private def killedBorel : boundedBorel (d := d) →ₗ[ℝ]
    Lp ℝ 2 (volume.restrict B) where
  toFun b := (memLp_killed hB σ hμ t b.property.1
    b.property.2.choose_spec.1 b.property.2.choose_spec.2).toLp (killed B σ μ t b)
  map_add' b c := by
    letI : IsProbabilityMeasure μ := hμ.1
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (killed_add_data hB σ t b.property.1 c.property.1
      b.property.2.choose_spec.1 c.property.2.choose_spec.1
      b.property.2.choose_spec.2 c.property.2.choose_spec.2)
  map_smul' a b := by
    change _ = ((memLp_killed hB σ hμ t b.property.1
      b.property.2.choose_spec.1 b.property.2.choose_spec.2).const_smul a).toLp _
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (killed_smul_data B σ μ t a b)

/-- The norm bound needed for the dense linear extension. -/
private lemma killedBorel_norm (b : boundedBorel (d := d)) :
    ‖killedBorel hB σ hμ t b‖ ≤ 1 * ‖boundedBorelToLp B b‖ := by
  rw [one_mul]
  change ‖(memLp_killed hB σ hμ t b.property.1
    b.property.2.choose_spec.1 b.property.2.choose_spec.2).toLp _‖ ≤
    ‖(boundedBorel_memLp B b).toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono (boundedBorel_memLp B b).2.ne
    (eLpNorm_killed_le hB σ hμ t b.property.1
      b.property.2.choose_spec.1 b.property.2.choose_spec.2)

/-- The unique continuous extension of bounded Borel killed evaluation to L². -/
def killedLp : Lp ℝ 2 (volume.restrict B) →L[ℝ] Lp ℝ 2 (volume.restrict B) :=
  (killedBorel hB σ hμ t).extendOfNorm (boundedBorelToLp B)

/-- Killed Brownian evolution is an L² contraction. -/
lemma norm_killedLp_le : ‖killedLp hB σ hμ t‖ ≤ 1 :=
  LinearMap.opNorm_extendOfNorm_le (boundedBorelToLp_dense B) zero_le_one
    (killedBorel_norm hB σ hμ t)

/-- The L² extension agrees with killed evaluation on every bounded Borel datum. -/
lemma killedLp_toLp {b : Euc d → ℝ} (hb : Measurable b) {C : ℝ}
    (hC : 0 ≤ C) (hbC : ∀ y, |b y| ≤ C)
    (hbLp : MemLp b 2 (volume.restrict B)) :
    killedLp hB σ hμ t (hbLp.toLp b) =
      (memLp_killed hB σ hμ t hb hC hbC).toLp (killed B σ μ t b) := by
  let g : boundedBorel (d := d) := ⟨b, hb, C, hC, hbC⟩
  exact LinearMap.extendOfNorm_eq (boundedBorelToLp_dense B)
    ⟨1, killedBorel_norm hB σ hμ t⟩ g

/-- At time zero the killed L² operator is the identity. -/
lemma killedLp_zero : killedLp hB σ hμ 0 =
    ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict B)) := by
  apply DFunLike.coe_injective
  apply (boundedBorelToLp_dense B).equalizer (killedLp hB σ hμ 0).continuous
    (ContinuousLinearMap.id ℝ (Lp ℝ 2 (volume.restrict B))).continuous
  funext b
  change killedLp hB σ hμ 0 ((boundedBorel_memLp B b).toLp b) =
    (boundedBorel_memLp B b).toLp b
  rw [killedLp_toLp hB σ hμ 0 b.property.1 b.property.2.choose_spec.1
    b.property.2.choose_spec.2 (boundedBorel_memLp B b)]
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
  rw [killed_zero hB σ hμ, indicator_of_mem hx]

/-- Successive killed L² evolutions compose according to addition of time. -/
lemma killedLp_add (s t : ℝ≥0) : killedLp hB σ hμ (s + t) =
    (killedLp hB σ hμ s).comp (killedLp hB σ hμ t) := by
  letI : IsProbabilityMeasure μ := hμ.1
  apply DFunLike.coe_injective
  apply (boundedBorelToLp_dense B).equalizer (killedLp hB σ hμ (s + t)).continuous
    ((killedLp hB σ hμ s).comp (killedLp hB σ hμ t)).continuous
  funext b
  change killedLp hB σ hμ (s + t) ((boundedBorel_memLp B b).toLp b) =
    killedLp hB σ hμ s (killedLp hB σ hμ t ((boundedBorel_memLp B b).toLp b))
  rw [killedLp_toLp hB σ hμ (s + t) b.property.1 b.property.2.choose_spec.1
    b.property.2.choose_spec.2, killedLp_toLp hB σ hμ t b.property.1
    b.property.2.choose_spec.1 b.property.2.choose_spec.2,
    killedLp_toLp hB σ hμ s (measurable_killed hB σ t b.property.1)
      b.property.2.choose_spec.1
      (abs_killed_le σ t b.property.2.choose_spec.1 b.property.2.choose_spec.2)]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (killed_add hB σ hμ s t b.property.1
    b.property.2.choose_spec.1 b.property.2.choose_spec.2)

end

end LatticeProb
