/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CountableMartingaleMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.PotentialGridUpcrossings
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinEnergy
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactVertexDynkin
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Measure.Continuity

/-! Extend the existing sampled Doob bound to unordered finite and countable
observation times. This is the probability estimate needed before taking a
dense-time limit of the energy approximation. -/

-- Merged from `ReflectedGMS/Forms/MartingaleEnergyMaximal.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_MartingaleEnergyMaximal

/-! Finite-grid maximal estimates from the actual martingale energy.
Conditional Jensen and the existing Doob maximal inequality supply the
probabilistic estimate needed for full-domain approximation. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

theorem submartingale_sq_of_martingale_memLp
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) :
    Submartingale (fun t ω ↦ (M t ω) ^ 2) F P := by
  have hsq (t : ι) : Integrable (fun ω ↦ (M t ω) ^ 2) P := by
    apply ((h2 t).integrable_mul (h2 t)).congr
    filter_upwards [] with ω
    exact (pow_two _).symm
  refine ⟨fun t ↦ (hM.stronglyMeasurable t).pow 2, ?_, hsq⟩
  intro s t hst
  have hconvex : ConvexOn ℝ univ (fun x : ℝ ↦ x ^ 2) :=
    (show Even (2 : ℕ) by decide).convexOn_pow
  have hj := hconvex.map_condExp_le_univ (F.le s)
    (continuous_id.pow 2).lowerSemicontinuous (hM.integrable t) (hsq t)
  filter_upwards [hM.condExp_ae_eq hst, hj] with ω hω hJ
  simpa only [Function.comp_def, hω] using hJ

theorem martingale_sq_grid_maximal_ineq
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) (τ : ℕ → ι) (hτ : Monotone τ)
    (ε : ℝ≥0) (n : ℕ) :
    (ε : ℝ≥0∞) * P {ω | (ε : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ (M (τ k) ω) ^ 2)} ≤
      ENNReal.ofReal (∫ ω, (M (τ n) ω) ^ 2 ∂P) := by
  have hS := submartingale_sq_of_martingale_memLp hM h2
  have hSn : Submartingale (fun k ω ↦ (M (τ k) ω) ^ 2)
      (sampledFiltration F τ hτ) P :=
    ⟨fun k ↦ hS.stronglyAdapted (τ k),
      fun i j hij ↦ hS.ae_le_condExp (hτ hij), fun k ↦ hS.integrable (τ k)⟩
  have hm := maximal_ineq hSn (fun _ _ ↦ sq_nonneg _) (ε := ε) n
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  exact setIntegral_le_integral (hS.integrable (τ n))
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))

open ReflectedWalk FullNetworkForm

end ReflectedGMS

end Merged_MartingaleEnergyMaximal

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS

theorem martingale_sq_finset_maximal_ineq
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [LinearOrder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) (s : Finset ι) (T : ι)
    (hsT : ∀ t ∈ s, t ≤ T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | ∃ t ∈ s, (ε : ℝ) ≤ (M t ω) ^ 2} ≤
      ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) := by
  classical
  let S := insert T s
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  have hc : 0 < S.card := Finset.card_pos.mpr hS
  let τ : ℕ → ι := fun n ↦ S.orderEmbOfFin rfl ⟨min n (S.card - 1), by omega⟩
  have hτ : Monotone τ := by
    intro i j hij
    apply (S.orderEmbOfFin rfl).monotone
    exact min_le_min_right _ hij
  have hτT : τ (S.card - 1) = T := by
    have he : τ (S.card - 1) = S.max' hS := by
      simpa only [τ, min_self] using S.orderEmbOfFin_last rfl hc
    rw [he]
    apply le_antisymm
    · apply Finset.max'_le
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact le_rfl
      · exact hsT t ht
    · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hbound := martingale_sq_grid_maximal_ineq hM h2 τ hτ ε (S.card - 1)
  rw [hτT] at hbound
  refine le_trans ?_ hbound
  apply mul_le_mul le_rfl ?_ (by positivity) (by positivity)
  apply measure_mono
  rintro ω ⟨t, ht, hω⟩
  let i := (S.orderIsoOfFin rfl).symm ⟨t, Finset.mem_insert_of_mem ht⟩
  have hi : i.val < S.card := i.isLt
  have he : τ i.val = t := by
    have hmin : min i.val (S.card - 1) = i.val := min_eq_left (by omega)
    simp only [τ, hmin]
    exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply
      ⟨t, Finset.mem_insert_of_mem ht⟩)
  change (ε : ℝ) ≤ _
  apply Finset.le_sup'_of_le _ (b := i.val) (Finset.mem_range.mpr (by omega))
  simpa only [he] using hω

theorem martingale_sq_countable_maximal_ineq
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [LinearOrder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ t, MemLp (M t) 2 P) (τ : ℕ → ι) (T : ι)
    (hτT : ∀ n, τ n ≤ T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * P {ω | ∃ n, (ε : ℝ) ≤ (M (τ n) ω) ^ 2} ≤
      ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) := by
  classical
  let E : ℕ → Set Ω := fun n ↦ {ω | ∃ k ≤ n, (ε : ℝ) ≤ (M (τ k) ω) ^ 2}
  have hE : Monotone E := by
    intro i j hij ω
    rintro ⟨k, hki, hk⟩
    exact ⟨k, hki.trans hij, hk⟩
  have heq : {ω | ∃ n, (ε : ℝ) ≤ (M (τ n) ω) ^ 2} = ⋃ n, E n := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, E]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, n, le_rfl, hn⟩
    · rintro ⟨n, k, _, hk⟩; exact ⟨k, hk⟩
  rw [heq, hE.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro n
  have hb := martingale_sq_finset_maximal_ineq hM h2
    ((Finset.range (n + 1)).image τ) T
    (by intro t ht; obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht; exact hτT k) ε
  have hset : E n = {ω | ∃ t ∈ (Finset.range (n + 1)).image τ,
      (ε : ℝ) ≤ (M t ω) ^ 2} := by
    ext ω
    simp only [E, mem_setOf_eq, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨k, hkn, hk⟩
      exact ⟨τ k, ⟨k, by omega, rfl⟩, hk⟩
    · rintro ⟨t, ⟨k, hkn, rfl⟩, hk⟩
      exact ⟨k, by omega, hk⟩
  rwa [hset]

end ReflectedGMS
