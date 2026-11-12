/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.UnifSWGaussSup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.FibreGaussMaxMain
import LatticeProb.Bonanno.LQGDimension.LFPP.ExpectedSupLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWS-G (1): exponential moments of a countable Gaussian supremum (Sheffield–Wang Lemma 3.5)

Abstract form of S. Sheffield, M. Wang, *Field-measurability of the conformal welding of
quantum surfaces*, arXiv:1605.06171, Lemma 3.5 (p. 16, displays (3.20)–(3.22) and the final
display): for a centred Gaussian process `Z` indexed by a countable set, a reference index `i₀`
and a subset `A` of indices carrying parameters `p i ∈ ℝ^d` (sup norm, diameter `≤ a`) with the
Hölder variance modulus `Var(Z i - Z j) ≤ L² ‖p i - p j‖^β` on `A` and `Var(Z i - Z i₀) ≤ σ²`
on `A`, the supremum `M = sup_{i ∈ A} (Z i - Z i₀)` satisfies, for every `t ≥ 0`,

  `E e^{t M} ≤ exp(t · m + π²/8 · t² σ²)`,   `m = fgmChainConst d β · L · a^{β/2}`.

This is SW's `E e^{α sup(...)} ≤ e^{α m_ε + 4cα²ε²}`: SW bound `m_ε = E sup` by an a.s.
continuity argument (3.23) and use Houdré's variance bound + Borell–TIS (their Prop. 2.6, 2.8);
here `m` is bounded quantitatively by Dudley chaining in Hölder form (`fgmChain_bound`;
Adler–Taylor, *Random Fields and Geometry*, Thm 1.3.3) and the concentration step is the
Maurey–Pisier form of Borell–TIS (`MaxConc.lintegral_exp_max_le`; Adler–Taylor Thm 2.1.1;
Pisier 1986 Thm 2.2), whose constant `π²/8` replaces SW's `4 · 2 = 8` (Prop. 2.8 applied to
(3.22)). Finite marginals are realised through the Gram representation `fgmLaw_gram`; the
countable supremum is the monotone limit of finite maxima (monotone convergence).

The reference `i₀` need not lie in `A` (SWS-ASM compares the fixed source-radius semicircle with
the pushed target semicircles); recentring the chaining bound at a member of `A` uses
Sudakov–Fernique (`vecExpectedMax_le_sub`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Real

namespace QuantumZipper.RegUnif

open LQGDimension

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type}

/-- **SW Lemma 3.5, finite maxima.** -/
theorem swg_exp_max_finset_le {Z : ι → Ω → ℝ} (hZ : IsGaussianProcess Z P)
    (hc : ∀ i, ∫ ω, Z i ω ∂P = 0) {d : ℕ} (p : ι → Fin d → ℝ) {L a β σ t : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hσ0 : 0 ≤ σ) (ht : 0 ≤ t) (i₀ : ι)
    (F : Finset ι) (hp : ∀ i ∈ F, ∀ j ∈ F, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ F, ∀ j ∈ F, Var[fun ω => Z i ω - Z j ω; P] ≤ L ^ 2 * ‖p i - p j‖ ^ β)
    (hσ : ∀ i ∈ F, Var[fun ω => Z i ω - Z i₀ ω; P] ≤ σ ^ 2) :
    ∫⁻ ω, ⨆ i ∈ F, ENNReal.ofReal (Real.exp (t * (Z i ω - Z i₀ ω))) ∂P ≤
      ENNReal.ofReal (Real.exp (t * (fgmChainConst d β * L * a ^ (β / 2)) +
        π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨i₁, hi₁⟩
  · simp
  set G : Finset ι := insert i₀ F with hG
  obtain ⟨v, hvar, -, hlaw⟩ := fgmLaw_gram (Z := Z) hZ hc G id
  have hi₀G : i₀ ∈ G := Finset.mem_insert_self _ _
  have hFG : ∀ i ∈ F, i ∈ G := fun i hi => Finset.mem_insert_of_mem hi
  set w : ι → EuclideanSpace ℝ G := fun i => v i - v i₀ with hw
  have hwσ : ∀ i ∈ F, ‖w i‖ ≤ σ := by
    intro i hi
    have h := hvar i (hFG i hi) i₀ hi₀G
    have h2 : ‖w i‖ ^ 2 ≤ σ ^ 2 := by
      simp only [hw]; rw [h]; exact hσ i hi
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hσ0 two_ne_zero).1 h2
  have hv' : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖ ^ β :=
    fun i hi j hj => by rw [hvar i (hFG i hi) j (hFG j hj)]; exact hv i hi j hj
  have hchain := fgmChain_bound F p v hβ hβ1 hL hp hv' hi₁
  have hshift : vecExpectedMax F w 0 ≤ vecExpectedMax F (fun i => v i - v i₁) 0 := by
    have h := ESLimit.vecExpectedMax_le_sub F w i₁
    have e : (fun i => w i - w i₁) = fun i => v i - v i₁ := by
      funext i; simp only [hw]; abel
    rwa [e] at h
  have hgauss := fgm_gauss_exp_le F w ht hwσ (hshift.trans hchain)
  set Φ : (G → ℝ) → ℝ≥0∞ := fun y => ⨆ g : G, if (g : ι) ∈ F then
      ENNReal.ofReal (Real.exp (t * (y g - y ⟨i₀, hi₀G⟩))) else 0 with hΦdef
  have hΦ : Measurable Φ := by
    refine Measurable.iSup fun g => ?_
    by_cases hg : (g : ι) ∈ F
    · simp only [hg, ↓reduceIte]
      exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul ((measurable_pi_apply g).sub (measurable_pi_apply _))))
    · simp only [hg, ↓reduceIte]; exact measurable_const
  have hstep1 : ∫⁻ ω, ⨆ i ∈ F, ENNReal.ofReal (Real.exp (t * (Z i ω - Z i₀ ω))) ∂P ≤
      ∫⁻ ω, Φ (fun g : G => Z (id g) ω) ∂P := by
    refine lintegral_mono fun ω => iSup₂_le fun i hi => ?_
    refine le_iSup_of_le (⟨i, hFG i hi⟩ : G) ?_
    simp only [hi, ↓reduceIte, id]
    exact le_rfl
  rw [hlaw Φ hΦ] at hstep1
  refine hstep1.trans (le_trans ?_ hgauss)
  refine lintegral_mono fun x => iSup_le fun g => ?_
  by_cases hg : (g : ι) ∈ F
  · simp only [hg, ↓reduceIte]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ ht))
    have := le_ciSup (f := fun i : F => ⟪w i, x⟫ + (0 : ι → ℝ) i)
      (Set.finite_range _).bddAbove ⟨g, hg⟩
    simpa [hw, inner_sub_left] using this
  · simp only [hg, ↓reduceIte]; exact bot_le

/-- **SW Lemma 3.5 / (3.21)–(3.22), countable supremum.** For a centred Gaussian process on a
countable index type, a reference index `i₀` and a set `A` of indices with parameters of diameter
`≤ a`, Hölder variance modulus `L² ‖p i - p j‖^β` and `Var(Z i - Z i₀) ≤ σ²` on `A`:
`E sup_{i ∈ A} e^{t (Z i - Z i₀)} ≤ exp(t · fgmChainConst d β · L · a^{β/2} + π²/8 · t² σ²)`. -/
theorem swg_exp_sup_le [Countable ι] {Z : ι → Ω → ℝ} (hZ : IsGaussianProcess Z P)
    (hc : ∀ i, ∫ ω, Z i ω ∂P = 0) {d : ℕ} (p : ι → Fin d → ℝ) {L a β σ t : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hσ0 : 0 ≤ σ) (ht : 0 ≤ t) (i₀ : ι)
    (A : Set ι) (hp : ∀ i ∈ A, ∀ j ∈ A, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ A, ∀ j ∈ A, Var[fun ω => Z i ω - Z j ω; P] ≤ L ^ 2 * ‖p i - p j‖ ^ β)
    (hσ : ∀ i ∈ A, Var[fun ω => Z i ω - Z i₀ ω; P] ≤ σ ^ 2) :
    ∫⁻ ω, ⨆ i ∈ A, ENNReal.ofReal (Real.exp (t * (Z i ω - Z i₀ ω))) ∂P ≤
      ENNReal.ofReal (Real.exp (t * (fgmChainConst d β * L * a ^ (β / 2)) +
        π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  set Fn : ℕ → Finset ι := fun n => ((Finset.range n).image e).filter (· ∈ A) with hFn
  set f : ι → Ω → ℝ≥0∞ := fun i ω => ENNReal.ofReal (Real.exp (t * (Z i ω - Z i₀ ω))) with hf
  have hmono : Monotone Fn := fun m n hmn =>
    Finset.filter_subset_filter _ (Finset.image_subset_image (Finset.range_subset_range.2 hmn))
  have heq : ∀ ω, ⨆ i ∈ A, f i ω = ⨆ n, ⨆ i ∈ Fn n, f i ω := by
    intro ω
    apply le_antisymm
    · refine iSup₂_le fun i hi => ?_
      obtain ⟨n, rfl⟩ := he i
      refine le_iSup_of_le (n + 1) (le_iSup₂_of_le (e n) ?_ le_rfl)
      simp only [hFn, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      exact ⟨⟨n, by omega, rfl⟩, hi⟩
    · exact iSup_le fun n => iSup₂_le fun i hi =>
        le_iSup₂_of_le (f := fun i (_ : i ∈ A) => f i ω) i (Finset.mem_filter.1 hi).2 le_rfl
  have hfm : ∀ i, AEMeasurable (f i) P := fun i =>
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).comp_aemeasurable
      (((hZ.aemeasurable i).sub (hZ.aemeasurable i₀)).const_mul t)
  calc ∫⁻ ω, ⨆ i ∈ A, f i ω ∂P = ∫⁻ ω, ⨆ n, ⨆ i ∈ Fn n, f i ω ∂P :=
        lintegral_congr fun ω => heq ω
    _ = ⨆ n, ∫⁻ ω, ⨆ i ∈ Fn n, f i ω ∂P := by
        refine lintegral_iSup' (fun n => ?_) (ae_of_all _ fun ω m n hmn => ?_)
        · exact AEMeasurable.iSup fun i => AEMeasurable.iSup fun _ => hfm i
        · exact biSup_mono fun i hi => hmono hmn hi
    _ ≤ _ := iSup_le fun n => by
        have hA : ∀ i ∈ Fn n, i ∈ A := fun i hi => (Finset.mem_filter.1 hi).2
        exact swg_exp_max_finset_le hZ hc p hβ hβ1 hL hσ0 ht i₀ (Fn n)
          (fun i hi j hj => hp i (hA i hi) j (hA j hj))
          (fun i hi j hj => hv i (hA i hi) j (hA j hj)) (fun i hi => hσ i (hA i hi))

end QuantumZipper.RegUnif
