/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepAsm1 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCore
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepZB
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepData
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepRad
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# GM Lemma 2.7, assembly: generic bookkeeping

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 2.7 (l. 972–1004). Small own elementary lemmas used in the assembly
(`SpatialIndep.lean`): a.s. modifications of zero-boundary GFFs, additivity of restriction,
restriction between nested opens, the representation of `𝔥 − c` on a sub-ball, extension of a
bound from a dense set by continuity, and independence of an `𝓕`-measurable variable from a
family of functions of `h̊`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric InnerProductSpace

namespace LQGMetric.GM

open Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- a zero-boundary GFF is preserved under a measurable a.s. modification -/
theorem isZeroBoundaryGFF_of_ae_eq {U : Opens ℂ} {g g' : Ω → DistOn U}
    (hg : IsZeroBoundaryGFF U g P) (hgg : ∀ᵐ ω ∂P, g ω = g' ω) (hm : Measurable g') :
    IsZeroBoundaryGFF U g' P := by
  have hφ : ∀ φ : TestOn U, (fun ω => g ω φ) =ᵐ[P] fun ω => g' ω φ := fun φ => by
    filter_upwards [hgg] with ω hω; rw [hω]
  refine ⟨hm, ⟨fun φ => (measurable_distOn_apply φ).comp hm, hg.process.gaussian.congr hφ,
    fun φ => ?_, fun φ ψ => ?_⟩⟩
  · rw [← integral_congr_ae (hφ φ)]; exact hg.process.centered φ
  · rw [← hg.process.covariance_eq φ ψ]
    unfold covariance
    rw [← integral_congr_ae (hφ φ), ← integral_congr_ae (hφ ψ)]
    refine integral_congr_ae ?_
    filter_upwards [hφ φ, hφ ψ] with ω h1 h2
    rw [h1, h2]

lemma restrictTo_add_gm (V : Opens ℂ) (a b : DistC) :
    restrictTo V (a + b) = restrictTo V a + restrictTo V b := by
  ext φ; rfl

/-- restriction `𝒟'(U) → 𝒟'(V)` -/
def distRes (V U : Opens ℂ) (T : DistOn U) : DistOn V := T.comp (testIncl V U)

lemma measurable_distRes (V U : Opens ℂ) : Measurable (distRes V U) :=
  measurable_distOn_iff.2 fun _ => measurable_distOn_apply _

lemma distRes_restrictTo {V U : Opens ℂ} (hVU : V ≤ U) (h : DistC) :
    distRes V U (restrictTo U h) = restrictTo V h := by
  ext φ
  exact (restrictTo_apply_testIncl hVU h φ).symm

/-- a representation on `U` restricts to `V ≤ U` -/
lemma rep_mono {V U : Opens ℂ} (hVU : V ≤ U) {G : DistC} {g : ℂ → ℝ}
    (hG : ∀ φ : TestOn U, restrictTo U G φ = ∫ y, g y * φ y) (φ : TestOn V) :
    restrictTo V G φ = ∫ y, g y * φ y := by
  rw [restrictTo_apply_testIncl hVU, hG, coe_testIncl hVU]

lemma integrable_mul_testOn {V : Opens ℂ} {g : ℂ → ℝ} (hg : ∀ y ∈ (V : Set ℂ), ContinuousAt g y)
    (φ : TestOn V) : Integrable fun y => g y * φ y := by
  have hK : IsCompact (tsupport (φ : ℂ → ℝ)) := φ.hasCompactSupport
  have hsub : tsupport (φ : ℂ → ℝ) ⊆ V := φ.tsupport_subset
  have hcont : ContinuousOn (fun y => g y * φ y) (tsupport (φ : ℂ → ℝ)) := fun y hy =>
    ((hg y (hsub hy)).mul φ.continuous.continuousAt).continuousWithinAt
  refine (hcont.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero fun y hy => ?_
  rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

/-- the representation of `G − c` from one of `G` -/
lemma rep_addConst {V : Opens ℂ} {G : DistC} {g : ℂ → ℝ}
    (hg : ∀ y ∈ (V : Set ℂ), ContinuousAt g y)
    (hG : ∀ φ : TestOn V, restrictTo V G φ = ∫ y, g y * φ y) (c : ℝ) (φ : TestOn V) :
    restrictTo V (addConst G (-c)) φ = ∫ y, (g y - c) * φ y := by
  have h1 : restrictTo V (addConst G (-c)) φ = restrictTo V G φ + (∫ y, φ y) * (-c) := by
    show addConst G (-c) (TestFunction.monoCLM ℝ φ) = G (TestFunction.monoCLM ℝ φ) + _
    rw [GFFInv.addConst_apply]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [TestFunction.monoCLM_apply]
  have hφi : Integrable fun y => φ y := φ.continuous.integrable_of_hasCompactSupport
    φ.hasCompactSupport
  rw [h1, hG φ]
  have : (fun y => (g y - c) * φ y) = fun y => g y * φ y - c * φ y := by
    funext y; ring
  rw [this, integral_sub (integrable_mul_testOn hg φ) (hφi.const_mul c), integral_const_mul]
  ring

/-- a bound on a dense subset of a ball extends to the ball by continuity -/
lemma abs_sub_le_of_dense {g : ℂ → ℝ} {x : ℂ} {r A c : ℝ} {S : Set ℂ} (hS : Dense S)
    (hg : ∀ u ∈ ball x r, ContinuousAt g u) (hA : ∀ u ∈ S, u ∈ ball x r → |g u - c| ≤ A) :
    ∀ u ∈ ball x r, |g u - c| ≤ A := by
  intro u hu
  have hcl : u ∈ closure (ball x r ∩ S) := hS.open_subset_closure_inter isOpen_ball hu
  have := (((hg u hu).sub continuousAt_const).abs.continuousWithinAt
    (s := ball x r ∩ S)).mem_closure (t := Iic A) hcl (fun v hv => hA v hv.2 hv.1)
  rwa [closure_Iic] at this

lemma fieldSigmaClosed_le_gm {h : Ω → DistC} (hh : Measurable h) (K : Set ℂ) :
    fieldSigmaClosed h K ≤ ‹MeasurableSpace Ω› :=
  (iInf₂_le 1 one_pos).trans ((measurable_restrictTo _).comp hh).comap_le

/-- an `𝓕`-measurable variable is independent of any family of functions of `h̊` when
`σ(h̊) ⟂ 𝓕` (as `indepFun_of_indep_comap`) -/
theorem indepFun_pi_of_indep_comap {F : MeasurableSpace Ω} {hz : Ω → DistC} {α : Type*}
    [MeasurableSpace α] {W : Ω → α} (hind : Indep (MeasurableSpace.comap hz inferInstance) F P)
    (hW : @Measurable Ω α F _ W) {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {f : ∀ i, DistC → β i} (hf : ∀ i, Measurable (f i)) :
    IndepFun W (fun ω i => f i (hz ω)) P := by
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind.symm hW.comap_le) ?_
  have hm : Measurable fun (T : DistC) (i : ι) => f i T := measurable_pi_iff.2 hf
  show MeasurableSpace.comap ((fun (T : DistC) (i : ι) => f i T) ∘ hz) _ ≤ _
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hm.comap_le

/-- the shifted event set `T = {(w, b) | b + w_i|_V ∈ S}` is measurable -/
lemma measurableSet_shiftSet {ι : Type*} (i : ι) (V : Opens ℂ) {S : Set (DistOn V)}
    (hS : MeasurableSet S) :
    MeasurableSet {p : (ι → DistC) × DistOn V | p.2 + restrictTo V (p.1 i) ∈ S} := by
  have hm : Measurable fun p : (ι → DistC) × DistOn V => p.2 + restrictTo V (p.1 i) :=
    measurable_distOn_iff.2 fun φ => by
      show Measurable fun p : (ι → DistC) × DistOn V => p.2 φ + restrictTo V (p.1 i) φ
      exact ((measurable_distOn_apply φ).comp measurable_snd).add
        ((measurable_distOn_apply φ).comp ((measurable_restrictTo V).comp
          ((measurable_pi_apply i).comp measurable_fst)))
  exact hm hS

end LQGMetric.GM
