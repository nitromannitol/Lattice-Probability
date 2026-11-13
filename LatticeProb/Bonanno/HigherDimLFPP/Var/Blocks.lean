/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Var.Blocks at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Var.Ag
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique

/-!
# Comparison with independent blocks

Two generic finite-Gaussian statements behind (2.6) and Lemma 2.3 (HA1 (T2), (T6)):

* `gEM_le_sum_blocks`: if a PSD kernel `C` on a finite family is dominated, in canonical distance,
  by the independent sum of rescaled `gCov`-processes of block profiles `P k i ∈ Vg E' (p k)`, and
  the drift splits accordingly, then the expected maximum is at most `∑ₖ sₖ Bₖ`, where `Bₖ` bounds
  the penalized expected maxima at level `p k`.  Sudakov–Fernique with drift
  (`LQGDimension.sudakovFernique`), then "a maximum of a sum is at most the sum of the maxima".
  This is the skeleton of `LQGDimension.Subadd.main_bound` (`LQGDimension/Section2/Subadditive.lean`),
  with the coarse/fine decomposition abstracted into block maps.
* `vecEM_pi_eq`: over a product family `piFinset (fun _ => F*)`, the expected maximum of a
  separable sum of independent copies is the sum of the expected maxima (product equality in HA1
  (T6)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Var

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

/-- **Comparison with independent blocks.** -/
theorem gEM_le_sum_blocks {ι : Type} (F : Finset ι) (C : ι → ι → ℝ) (hC : PSDOn F C)
    (b : ι → ℝ) {E' : Type} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E'] {K : Type} [Fintype K] [DecidableEq K] (p : K → ℕ)
    (P : K → ι → ℝ → E') (hP : ∀ k i, P k i ∈ Vg E' (p k)) (s : K → ℝ) (hs : ∀ k, 0 ≤ s k)
    (hb : ∀ i ∈ F, b i = ∑ k, s k * -energy (P k i))
    (hdist : ∀ i ∈ F, ∀ j ∈ F, C i i + C j j - 2 * C i j ≤
      ∑ k, s k ^ 2 * (2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖P k i x - P k j x‖))
    (B : K → ℝ) (hB : ∀ k (G : Finset (Vg E' (p k))),
      gaussianExpectedMax G (fun f g => gCov (f : ℝ → E') g)
        (fun f => -energy (f : ℝ → E')) ≤ B k) :
    gaussianExpectedMax F C b ≤ ∑ k, s k * B k := by
  classical
  -- a Gram representation of `C` on `F`
  obtain ⟨v, hv⟩ := LQGDimension.exists_gram_of_psdOn F C hC
  -- a Gram representation of `gCov` on all block profiles
  set S : Finset (ℝ → E') := Finset.univ.biUnion (fun k => F.image (P k)) with hS
  have hScont : ∀ a ∈ S, Continuous a := by
    intro a ha
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hk
    exact Vg_continuous (hP k i)
  obtain ⟨T, hT⟩ := LQGDimension.exists_gram_of_psdOn S (fun f g => gCov f g)
    (gCov_psdOn_of_continuous S hScont)
  have hPS : ∀ k, ∀ i ∈ F, P k i ∈ S := fun k i hi =>
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ hi⟩
  -- the comparison vectors
  let W : ι → PiLp 2 (fun _ : K => EuclideanSpace ℝ S) :=
    fun i => WithLp.toLp 2 (fun k => s k • T (P k i))
  -- Step 1: pass to vectors
  have step1 : gaussianExpectedMax F C b = vecExpectedMax F v b := by
    rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact LQGDimension.gaussianExpectedMax_congr F b (fun i hi j hj => (hv i hi j hj).symm)
  -- Step 2: Sudakov–Fernique comparison with the block family
  have step2 : vecExpectedMax F v b ≤ vecExpectedMax F W b := by
    refine LQGDimension.sudakovFernique ι (EuclideanSpace ℝ F)
      (PiLp 2 (fun _ : K => EuclideanSpace ℝ S)) F v W b fun i hi j hj => ?_
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have h1 : ‖v i - v j‖ ^ 2 = C i i + C j j - 2 * C i j := by
      rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        hv i hi i hi, hv j hj j hj, hv i hi j hj]
      ring
    have h2 : ‖W i - W j‖ ^ 2 =
        ∑ k, s k ^ 2 * (2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖P k i x - P k j x‖) := by
      rw [← WithLp.toLp_sub, PiLp.norm_sq_eq_of_L2]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.sub_apply]
      rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        gCov_dist_sq T (Vg_continuous (hP k i)) (Vg_continuous (hP k j))
          (hT _ (hPS k i hi) _ (hPS k i hi)) (hT _ (hPS k j hj) _ (hPS k j hj))
          (hT _ (hPS k i hi) _ (hPS k j hj))]
    rw [h1, h2]
    exact hdist i hi j hj
  -- Step 3: a maximum of a sum is at most the sum of the maxima
  have step3 : vecExpectedMax F W b ≤
      ∑ k, vecExpectedMax F (fun i => (PiLp.single 2 k (s k • T (P k i)) :
        PiLp 2 (fun _ : K => EuclideanSpace ℝ S))) (fun i => s k * -energy (P k i)) := by
    have e1 : W = fun i => ∑ k, (PiLp.single 2 k (s k • T (P k i)) :
        PiLp 2 (fun _ : K => EuclideanSpace ℝ S)) :=
      funext fun i => LQGDimension.Subadd.toLp_eq_sum_single _
    rw [vecEM_congr_drift F W hb, e1]
    exact LQGDimension.Subadd.vecEM_sum_le LQGDimension.maxIntegrable Finset.univ F
      (fun k i => (PiLp.single 2 k (s k • T (P k i)) :
        PiLp 2 (fun _ : K => EuclideanSpace ℝ S))) (fun k i => s k * -energy (P k i))
  -- Step 4: each block is a rescaled problem at level `p k`
  have step4 : ∀ k, vecExpectedMax F (fun i => (PiLp.single 2 k (s k • T (P k i)) :
        PiLp 2 (fun _ : K => EuclideanSpace ℝ S))) (fun i => s k * -energy (P k i)) ≤
      s k * B k := by
    intro k
    rw [LQGDimension.Subadd.vecEM_congr_gram LQGDimension.gramBridge F
      (fun i => (PiLp.single 2 k (s k • T (P k i)) :
        PiLp 2 (fun _ : K => EuclideanSpace ℝ S)))
      (fun i => s k • T (P k i)) (fun i => s k * -energy (P k i))
      (fun i => s k * -energy (P k i))
      (fun i _ j _ => LQGDimension.Subadd.inner_single_single k _ _) (fun _ _ => rfl),
      LQGDimension.Subadd.vecEM_smul F (fun i => T (P k i)) (fun i => -energy (P k i)) (hs k)]
    refine mul_le_mul_of_nonneg_left ?_ (hs k)
    let φ : ι → Vg E' (p k) := fun i => ⟨P k i, hP k i⟩
    have hcomp := LQGDimension.Subadd.vecEM_comp_image F φ
      (fun g : Vg E' (p k) => T (g : ℝ → E')) (fun g => -energy (g : ℝ → E'))
    refine (le_of_eq hcomp).trans ?_
    rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
    refine le_trans (le_of_eq ?_) (hB k (F.image φ))
    apply LQGDimension.gaussianExpectedMax_congr
    intro g hg g' hg'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hg'
    exact hT _ (hPS k i hi) _ (hPS k j hj)
  rw [step1]
  exact step2.trans (step3.trans (Finset.sum_le_sum fun k _ => step4 k))

/-! ## Product families -/

/-- Over a product family, the maximum of a separable sum is the sum of the maxima. -/
lemma iSup_piFinset_sum {κ : Type*} {m : ℕ} (F : Finset κ) (hF : F.Nonempty)
    (h : Fin m → κ → ℝ) :
    (⨆ σ : (Fintype.piFinset fun _ : Fin m => F), ∑ j, h j ((σ : Fin m → κ) j)) =
      ∑ j, ⨆ a : F, h j a := by
  classical
  have hne : Nonempty F := hF.to_subtype
  have hP : (Fintype.piFinset fun _ : Fin m => F).Nonempty :=
    Fintype.piFinset_nonempty.2 fun _ => hF
  have hneP : Nonempty (Fintype.piFinset fun _ : Fin m => F) := hP.to_subtype
  apply le_antisymm
  · refine ciSup_le fun σ => Finset.sum_le_sum fun j _ => ?_
    have hσ : (σ : Fin m → κ) j ∈ F := Fintype.mem_piFinset.1 σ.2 j
    exact le_ciSup (f := fun a : F => h j a) (Finite.bddAbove_range _) ⟨_, hσ⟩
  · have hmax : ∀ j, ∃ a : F, h j a = ⨆ a : F, h j a := fun j =>
      exists_eq_ciSup_of_finite (f := fun a : F => h j a)
    choose a ha using hmax
    have hmem : (fun j => ((a j : F) : κ)) ∈ Fintype.piFinset fun _ : Fin m => F :=
      Fintype.mem_piFinset.2 fun j => (a j).2
    calc ∑ j, ⨆ a : F, h j a = ∑ j, h j (a j) := Finset.sum_congr rfl fun j _ => (ha j).symm
      _ ≤ ⨆ σ : (Fintype.piFinset fun _ : Fin m => F), ∑ j, h j ((σ : Fin m → κ) j) :=
        le_ciSup (f := fun σ : (Fintype.piFinset fun _ : Fin m => F) =>
          ∑ j, h j ((σ : Fin m → κ) j)) (Finite.bddAbove_range _) ⟨_, hmem⟩

/-- **Product equality** (HA1 (T6)): for independent copies over a product family,
`E max_{σ ∈ F^m} ∑ⱼ (⟪T σⱼ, xⱼ⟫ + β σⱼ) = m · E max_{a ∈ F} (⟪T a, x⟫ + β a)`. -/
theorem vecEM_pi_eq {κ H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] {m : ℕ} (F : Finset κ)
    (hF : F.Nonempty) (T : κ → H) (β : κ → ℝ) :
    vecExpectedMax (Fintype.piFinset fun _ : Fin m => F)
      (fun σ => (WithLp.toLp 2 (fun j => T (σ j)) : PiLp 2 (fun _ : Fin m => H)))
      (fun σ => ∑ j, β (σ j)) = m * vecExpectedMax F T β := by
  classical
  have hpt : ∀ x : PiLp 2 (fun _ : Fin m => H),
      (⨆ σ : (Fintype.piFinset fun _ : Fin m => F),
        ⟪(WithLp.toLp 2 (fun j => T ((σ : Fin m → κ) j)) : PiLp 2 (fun _ : Fin m => H)), x⟫ +
          ∑ j, β ((σ : Fin m → κ) j)) =
      ∑ j, ⨆ a : F, ⟪(PiLp.single 2 j (T a) : PiLp 2 (fun _ : Fin m => H)), x⟫ + β a := by
    intro x
    have e : ∀ σ : Fin m → κ,
        ⟪(WithLp.toLp 2 (fun j => T (σ j)) : PiLp 2 (fun _ : Fin m => H)), x⟫ +
          ∑ j, β (σ j) =
        ∑ j, (⟪(PiLp.single 2 j (T (σ j)) : PiLp 2 (fun _ : Fin m => H)), x⟫ + β (σ j)) := by
      intro σ
      rw [Finset.sum_add_distrib, LQGDimension.Subadd.toLp_eq_sum_single, sum_inner]
    simp_rw [e]
    exact iSup_piFinset_sum F hF
      (fun j a => ⟪(PiLp.single 2 j (T a) : PiLp 2 (fun _ : Fin m => H)), x⟫ + β a)
  have hint : ∀ j : Fin m, Integrable (fun x : PiLp 2 (fun _ : Fin m => H) =>
      ⨆ a : F, ⟪(PiLp.single 2 j (T a) : PiLp 2 (fun _ : Fin m => H)), x⟫ + β a)
      (stdGaussian (PiLp 2 (fun _ : Fin m => H))) := fun j =>
    LQGDimension.integrable_iSup_inner_add F
      (fun a => (PiLp.single 2 j (T a) : PiLp 2 (fun _ : Fin m => H))) β
  unfold vecExpectedMax
  simp_rw [hpt]
  rw [MeasureTheory.integral_finsetSum Finset.univ fun j _ => hint j]
  have hj : ∀ j : Fin m, ∫ x, (⨆ a : F, ⟪(PiLp.single 2 j (T a) :
      PiLp 2 (fun _ : Fin m => H)), x⟫ + β a) ∂(stdGaussian (PiLp 2 (fun _ : Fin m => H))) =
      vecExpectedMax F T β := by
    intro j
    have := LQGDimension.vecExpectedMax_eq_of_gram_eq F
      (fun a => (PiLp.single 2 j (T a) : PiLp 2 (fun _ : Fin m => H))) T β
      (fun a _ b _ => LQGDimension.Subadd.inner_single_single j _ _)
    exact this
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rfl

end HigherDimLFPP.Var
