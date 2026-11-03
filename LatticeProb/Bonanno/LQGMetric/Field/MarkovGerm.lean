/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGerm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovZB
import LatticeProb.Bonanno.LQGMetric.Field.MarkovIndep
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# Independence from `σ(h|_O)` for an open `O ⊇ ∂𝔻` (task P2-MARKOV, part 4)

For a whole-plane GFF normalized by `h_1(0) = 0` (`IsNormalizedWPGFF`) and an open set `O`
containing the unit circle, every pairing `⟨h, χ⟩`, `χ ∈ 𝓓(O)`, is the a.s. limit of the
mean-zero pairings `⟨h, χ − (∫χ) σₙ⟩`, where `σₙ = circBump n 0 1` is the mollified uniform
measure on `∂𝔻` (`ae_tendsto_meanZeroApprox`; `⟨h, σₙ⟩ → h_1(0) = 0`), and these test functions are
supported in `O` for large `n` (`tsupport_circBump_subset`). Hence (`indep_fieldSigma_of_orth`) a
finite family `W` in the Gaussian space of `h` which is orthogonal to every mean-zero pairing
supported in `O` is independent of `σ(h|_O)` (orthogonal ⇒ independent, `MarkovGauss`, then
independence passes to a.s. limits, `MarkovIndep`, and to the directed union over finite sets of
test functions, mathlib `indep_iSup_of_directed_le`).

This is where the hypothesis `V ∩ ∂𝔻 = ∅` of LM Lemma 2.1 (`Blueprint.LMLem2_1`, LM tex
l. 425–429; GMSh arXiv:1807.07511 Lemma 2.2, proof tex l. 603–628: "h̊′ is supported in U so its
∂𝔻-average only sees ∂𝔻 ∩ U") enters: the normalization `h_1(0) = 0` is a function of the field
near `∂𝔻 ⊆ ℂ ∖ V`. Own write-up of this step (GMSh treat it in one sentence).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGerm

open MarkovGauss MarkovIndep MarkovZB CircleAvg Blueprint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the inclusion `𝓓(O) ⊆ 𝓓(ℂ)` -/
abbrev extC (O : Opens ℂ) : TestOn O →L[ℝ] TestC :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤)

lemma coe_extC {O : Opens ℂ} (φ : TestOn O) : ((extC O φ : TestC) : ℂ → ℝ) = φ := by
  simp [extC, TestFunction.monoCLM_apply]

lemma circBump_eq_zero {n : ℕ} {y : ℂ}
    (hy : y ∉ cthickening ((2 : ℝ)⁻¹ ^ n) (sphere (0 : ℂ) 1)) : circBump n 0 1 y = 0 := by
  rw [circBump_apply]
  have : ∀ θ, bumpTest n (circleMap 0 1 θ) y = 0 := by
    intro θ
    rw [bumpTest_apply, ContDiffBump.normed_def, (bumpAt n _).zero_of_le_dist, zero_div]
    show (2 : ℝ)⁻¹ ^ n ≤ dist y (circleMap 0 1 θ)
    by_contra hlt
    exact hy (mem_cthickening_of_dist_le y (circleMap 0 1 θ) _ _
      (circleMap_mem_sphere 0 zero_le_one θ) (not_le.1 hlt).le)
  simp [Real.circleAverage_def, this]

lemma tsupport_circBump_subset (n : ℕ) :
    tsupport (circBump n 0 1 : ℂ → ℝ) ⊆ cthickening ((2 : ℝ)⁻¹ ^ n) (sphere (0 : ℂ) 1) :=
  closure_minimal (fun y hy => by_contra fun h' => hy (circBump_eq_zero h')) isClosed_cthickening

/-- `χ − (∫χ) σₙ`, a mean-zero test function -/
def meanZeroApprox (χ : TestC) (n : ℕ) : TestC0 :=
  ⟨χ - (∫ x, χ x) • circBump n 0 1, by
    change ∫ x, (χ x - (∫ y, χ y) * circBump n 0 1 x) = 0
    rw [integral_sub (integrable_testC χ) ((integrable_testC _).const_mul _), integral_const_mul,
      integral_circBump, mul_one, sub_self]⟩

lemma meanZeroApprox_apply (g : DistC) (χ : TestC) (n : ℕ) :
    g (meanZeroApprox χ n).1 = g χ - (∫ x, χ x) * mollAvg g n 0 1 := by
  simp [meanZeroApprox, mollAvg_eq, map_sub, map_smul]

lemma tsupport_meanZeroApprox (χ : TestC) (n : ℕ) :
    tsupport ((meanZeroApprox χ n).1 : ℂ → ℝ) ⊆
      tsupport (χ : ℂ → ℝ) ∪ cthickening ((2 : ℝ)⁻¹ ^ n) (sphere (0 : ℂ) 1) := by
  have hcoe : ((meanZeroApprox χ n).1 : ℂ → ℝ) =
      (χ : ℂ → ℝ) - (fun _ : ℂ => ∫ x, χ x) • (circBump n 0 1 : ℂ → ℝ) := by
    funext x; simp [meanZeroApprox]
  rw [hcoe]
  refine (tsupport_sub _ _).trans (union_subset_union_right _ ?_)
  exact (tsupport_smul_subset_right (fun _ : ℂ => ∫ x, χ x) (circBump n 0 1 : ℂ → ℝ)).trans
    (tsupport_circBump_subset n)

/-- under `h_1(0) = 0`, `⟨h, χ⟩ = lim ⟨h, χ − (∫χ)σₙ⟩` for all `χ`, almost surely -/
lemma ae_tendsto_meanZeroApprox (hh : IsNormalizedWPGFF h P) :
    ∀ᵐ ω ∂P, ∀ χ : TestC, Tendsto (fun n => h ω (meanZeroApprox χ n).1) atTop (𝓝 (h ω χ)) := by
  filter_upwards [ae_tendsto_mollAvg hh.1 0 one_pos, hh.2] with ω ⟨a, ha⟩ h0 χ
  rw [circleAvg_eq_of_tendsto ha] at h0
  subst h0
  simp_rw [meanZeroApprox_apply]
  simpa using tendsto_const_nhds.sub (ha.const_mul (∫ x, χ x))

lemma exists_pow_cthickening_subset {O : Opens ℂ} (hO : sphere (0 : ℂ) 1 ⊆ O) :
    ∃ N : ℕ, ∀ n, N ≤ n → cthickening ((2 : ℝ)⁻¹ ^ n) (sphere (0 : ℂ) 1) ⊆ O := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_sphere (0 : ℂ) 1).exists_cthickening_subset_open O.isOpen hO
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun n hn => (cthickening_mono ?_ _).trans hsub⟩
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans hN.le

lemma measurable_eval (hh : IsWholePlaneGFF h P) (χ : TestC) : Measurable fun ω => h ω χ :=
  (measurable_evalDist χ).comp hh.measurable

/-- the finite-dimensional marginals of `h|_O` -/
def vecJ (h : Ω → DistC) (O : Opens ℂ) (J : Finset (TestOn O)) (ω : Ω) : J → ℝ :=
  fun j => restrictTo O (h ω) j

lemma measurable_vecJ (hh : IsWholePlaneGFF h P) (O : Opens ℂ) (J : Finset (TestOn O)) :
    Measurable (vecJ h O J) :=
  measurable_pi_iff.2 fun j => measurable_eval hh (extC O j)

lemma measurable_vecJ_fieldSigma (O : Opens ℂ) (J : Finset (TestOn O)) :
    Measurable[fieldSigma h O] (vecJ h O J) := by
  have h1 : Measurable[fieldSigma h O] fun ω => restrictTo O (h ω) := comap_measurable _
  have h2 : Measurable fun (g : DistOn O) (j : J) => g j :=
    measurable_pi_iff.2 fun j => (measurable_pi_apply (j : TestOn O)).comp (measurable_distEval O)
  exact h2.comp h1

lemma comap_eval_le (O : Opens ℂ) (φ : TestOn O) :
    MeasurableSpace.comap (fun ω => restrictTo O (h ω) φ) inferInstance ≤
      MeasurableSpace.comap (vecJ h O {φ}) inferInstance := by
  have : (fun ω => restrictTo O (h ω) φ) = (fun v : ({φ} : Finset (TestOn O)) → ℝ =>
      v ⟨φ, Finset.mem_singleton_self φ⟩) ∘ vecJ h O {φ} := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

lemma fieldSigma_eq_iSup (O : Opens ℂ) :
    fieldSigma h O = ⨆ J : Finset (TestOn O), MeasurableSpace.comap (vecJ h O J) inferInstance := by
  refine le_antisymm ?_ (iSup_le fun J => (measurable_vecJ_fieldSigma O J).comap_le)
  have : fieldSigma h O = MeasurableSpace.comap (fun ω (φ : TestOn O) => restrictTo O (h ω) φ)
      MeasurableSpace.pi := by
    rw [fieldSigma, DistOn.measurableSpace, MeasurableSpace.comap_comp]; rfl
  rw [this, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => ?_
  rw [MeasurableSpace.comap_comp]
  exact (comap_eval_le O φ).trans (le_iSup (fun J : Finset (TestOn O) =>
    MeasurableSpace.comap (vecJ h O J) inferInstance) {φ})

lemma comap_vecJ_mono (O : Opens ℂ) {J₁ J₂ : Finset (TestOn O)} (hJ : J₁ ⊆ J₂) :
    MeasurableSpace.comap (vecJ h O J₁) inferInstance ≤
      MeasurableSpace.comap (vecJ h O J₂) inferInstance := by
  have : vecJ h O J₁ = (fun (v : J₂ → ℝ) (j : J₁) => v ⟨j, hJ j.2⟩) ∘ vecJ h O J₂ := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (measurable_pi_iff.2 fun j => measurable_pi_apply _).comap_le

/-- **Orthogonal to the mean-zero pairings in `O ⊇ ∂𝔻` ⇒ independent of `σ(h|_O)`.** -/
theorem indep_fieldSigma_of_orth (hh : IsNormalizedWPGFF h P) (O : Opens ℂ)
    (hO : sphere (0 : ℂ) 1 ⊆ O) {S : Type*} [Fintype S] (W : S → Lp ℝ 2 P)
    (hW : ∀ s, W s ∈ gaussSpace (pairProc h) (memLp_pair hh.1))
    (horth : ∀ s (χ : TestC0), tsupport (χ.1 : ℂ → ℝ) ⊆ O →
      ⟪W s, (memLp_pair hh.1 χ).toLp _⟫ = 0)
    {Wm : Ω → S → ℝ} (hWm : Measurable Wm) (hae : ∀ s, (fun ω => Wm ω s) =ᵐ[P] W s) :
    Indep (fieldSigma h O) (MeasurableSpace.comap Wm inferInstance) P := by
  obtain ⟨N, hN⟩ := exists_pow_cthickening_subset hO
  rw [fieldSigma_eq_iSup]
  refine indep_iSup_of_directed_le (fun J => ?_) (fun J => (measurable_vecJ hh.1 O J).comap_le)
    hWm.comap_le ?_
  · set ι : ℕ → J → TestC0 := fun n j => meanZeroApprox (extC O j) (n + N) with hι
    have hsupp : ∀ n j, tsupport ((ι n j).1 : ℂ → ℝ) ⊆ O := fun n j =>
      (tsupport_meanZeroApprox _ _).trans (union_subset
        (by rw [coe_extC]; exact (j : TestOn O).tsupport_subset) (hN _ (by omega)))
    set Zn : ℕ → Ω → J → ℝ := fun n ω j => h ω (ι n j).1 with hZndef
    have hZn : ∀ n, Measurable (Zn n) := fun n =>
      measurable_pi_iff.2 fun j => measurable_eval hh.1 _
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (vecJ h O J ω)) := by
      filter_upwards [ae_tendsto_meanZeroApprox hh] with ω hω
      refine tendsto_pi_nhds.2 fun j => ?_
      exact (hω (extC O j)).comp (tendsto_add_atTop_nat N)
    have hind : ∀ n, Indep (MeasurableSpace.comap (Zn n) inferInstance)
        (MeasurableSpace.comap Wm inferInstance) P := by
      intro n
      have hi := indepFun_of_inner_eq_zero (gaussian_pairProc hh.1) (centered_pairProc hh.1)
        (memLp_pair hh.1) W hW (ι n) (fun s j => horth s _ (hsupp n j))
      have hae' : (fun ω s => (W s : Ω → ℝ) ω) =ᵐ[P] Wm := by
        have : ∀ᵐ ω ∂P, ∀ s, Wm ω s = (W s : Ω → ℝ) ω := ae_all_iff.2 hae
        filter_upwards [this] with ω hω
        funext s; exact (hω s).symm
      exact (IndepFun_iff_Indep _ _ _).1 (hi.congr hae' Filter.EventuallyEq.rfl).symm
    exact indep_comap_of_tendsto_ae (measurable_vecJ hh.1 O J) hZn hWm.comap_le hlim hind
  · intro J₁ J₂
    classical
    exact ⟨J₁ ∪ J₂, comap_vecJ_mono O Finset.subset_union_left,
      comap_vecJ_mono O Finset.subset_union_right⟩

end MarkovGerm
end LQGMetric
