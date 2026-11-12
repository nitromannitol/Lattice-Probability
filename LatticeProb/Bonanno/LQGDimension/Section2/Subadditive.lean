/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Section2.Subadditive at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Section2.SubadditiveAux

/-!
# Subadditivity of `a_n` (Lemma 2.1)

We prove `Blueprint.ASubadditiveE`: `aE (n + m) ≤ aE n + aE m`, following the paper.  For a
finite family `F ⊆ V (n+m)`, each `f` is decomposed as its coarse interpolant `g ∈ V n` plus
fine pieces `ũ_k ∈ V m` (`k < 16ⁿ`) rescaled from the coarse intervals.  The canonical `L¹`
distances satisfy `‖f - f'‖₁ ≤ ‖g - g'‖₁ + ∑ₖ 16^{-2n} ‖ũ_k - ũ'_k‖₁`, and the energy splits
exactly, `E(f) = E(g) + ∑ₖ 16⁻ⁿ E(ũ_k)`.  Sudakov–Fernique compares the family with the
independent sum of the coarse field and the `16ⁿ` rescaled fine fields; a maximum of a sum is at
most the sum of maxima.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension

namespace Subadd

/-! ## Finite Gaussian families -/

lemma gEM_congr {ι : Type*} (F : Finset ι) {C C' : ι → ι → ℝ} {b b' : ι → ℝ}
    (hC : ∀ i ∈ F, ∀ j ∈ F, C i j = C' i j) (hb : ∀ i ∈ F, b i = b' i) :
    gaussianExpectedMax F C b = gaussianExpectedMax F C' b' := by
  unfold gaussianExpectedMax
  have h1 : (Matrix.of fun i j : F => C i j) = Matrix.of fun i j : F => C' i j := by
    ext i j; exact hC i i.2 j j.2
  rw [h1]
  congr 1
  funext x
  congr 1
  funext i
  rw [hb i i.2]

lemma vecEM_congr_gram (hGB : Blueprint.GramBridge) {ι E E' : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E'] [BorelSpace E']
    (F : Finset ι) (v : ι → E) (w : ι → E') (b b' : ι → ℝ)
    (hvw : ∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = ⟪w i, w j⟫) (hb : ∀ i ∈ F, b i = b' i) :
    vecExpectedMax F v b = vecExpectedMax F w b' := by
  rw [← hGB ι E F v b, ← hGB ι E' F w b']
  exact gEM_congr F hvw hb

lemma iSup_finset_comp {ι κ : Type*} [DecidableEq κ] (F : Finset ι) (φ : ι → κ) (h : κ → ℝ) :
    (⨆ i : F, h (φ i)) = ⨆ j : F.image φ, h j := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.image_empty]
    have : IsEmpty (↥(∅ : Finset κ)) := ⟨fun x => Finset.notMem_empty _ x.2⟩
    have : IsEmpty (↥(∅ : Finset ι)) := ⟨fun x => Finset.notMem_empty _ x.2⟩
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]
  · have : Nonempty F := hne.to_subtype
    have : Nonempty (F.image φ) := (hne.image φ).to_subtype
    apply le_antisymm
    · exact ciSup_le fun i => le_ciSup (f := fun j : F.image φ => h j) (Finite.bddAbove_range _)
        (⟨φ i, Finset.mem_image_of_mem φ i.2⟩ : F.image φ)
    · refine ciSup_le fun j => ?_
      obtain ⟨i, hi, hij⟩ := Finset.mem_image.1 j.2
      calc h j = h (φ i) := by rw [hij]
        _ ≤ _ := le_ciSup (f := fun i : F => h (φ i)) (Finite.bddAbove_range _) (⟨i, hi⟩ : F)

lemma vecEM_comp_image {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [DecidableEq κ]
    (F : Finset ι) (φ : ι → κ) (v : κ → E) (b : κ → ℝ) :
    vecExpectedMax F (fun i => v (φ i)) (fun i => b (φ i)) = vecExpectedMax (F.image φ) v b := by
  unfold vecExpectedMax
  congr 1
  funext x
  exact iSup_finset_comp F φ (fun j => ⟪v j, x⟫ + b j)

lemma vecEM_smul {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    (F : Finset ι) (v : ι → E) (b : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    vecExpectedMax F (fun i => r • v i) (fun i => r * b i) = r * vecExpectedMax F v b := by
  unfold vecExpectedMax
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [Real.mul_iSup_of_nonneg hr]
  congr 1
  funext i
  rw [real_inner_smul_left]
  ring

lemma iSup_add_le_finset {ι : Type*} (F : Finset ι) (a b : ι → ℝ) :
    (⨆ i : F, (a i + b i)) ≤ (⨆ i : F, a i) + ⨆ i : F, b i := by
  rcases isEmpty_or_nonempty F with h | h
  · simp
  · exact ciSup_le fun i => add_le_add (le_ciSup (f := fun i : F => a i) (Finite.bddAbove_range _) i)
      (le_ciSup (f := fun i : F => b i) (Finite.bddAbove_range _) i)

lemma vecEM_add_le (hMI : Blueprint.MaxIntegrable) {ι E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : Finset ι) (v w : ι → E) (b c : ι → ℝ) :
    vecExpectedMax F (fun i => v i + w i) (fun i => b i + c i) ≤
      vecExpectedMax F v b + vecExpectedMax F w c := by
  have hle : ∀ x : E, (⨆ i : F, ⟪v i + w i, x⟫ + (b i + c i)) ≤
      (⨆ i : F, ⟪v i, x⟫ + b i) + ⨆ i : F, ⟪w i, x⟫ + c i := by
    intro x
    calc (⨆ i : F, ⟪v i + w i, x⟫ + (b i + c i))
        = ⨆ i : F, ((⟪v i, x⟫ + b i) + (⟪w i, x⟫ + c i)) := by
          congr 1; funext i; rw [inner_add_left]; ring
      _ ≤ _ := iSup_add_le_finset F (fun i => ⟪v i, x⟫ + b i) (fun i => ⟪w i, x⟫ + c i)
  have h1 := hMI ι E F (fun i => v i + w i) (fun i => b i + c i)
  have h2 := hMI ι E F v b
  have h3 := hMI ι E F w c
  unfold vecExpectedMax
  rw [← integral_add h2 h3]
  exact integral_mono h1 (h2.add h3) hle

lemma vecEM_sum_le (hMI : Blueprint.MaxIntegrable) {ι E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {κ : Type*} (s : Finset κ) (F : Finset ι) (v : κ → ι → E) (b : κ → ι → ℝ) :
    vecExpectedMax F (fun i => ∑ k ∈ s, v k i) (fun i => ∑ k ∈ s, b k i) ≤
      ∑ k ∈ s, vecExpectedMax F (v k) (b k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [vecExpectedMax, Real.iSup_const_zero]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (vecEM_add_le hMI F _ _ _ _).trans (add_le_add le_rfl ih)

/-! ## Orthogonal blocks -/

lemma toLp_eq_sum_single {K : Type*} [Fintype K] [DecidableEq K] {E : Type*}
    [NormedAddCommGroup E] (d : K → E) :
    (WithLp.toLp 2 d : PiLp 2 (fun _ : K => E)) = ∑ o, PiLp.single 2 o (d o) := by
  simp only [← PiLp.toLp_single, ← WithLp.toLp_sum, Finset.univ_sum_single]

lemma inner_single_single {K : Type*} [Fintype K] [DecidableEq K] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (o : K) (a b : E) :
    ⟪(PiLp.single 2 o a : PiLp 2 (fun _ : K => E)), PiLp.single 2 o b⟫ = ⟪a, b⟫ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single o]
  · simp [PiLp.single_eq_same]
  · intro j _ hj; simp [hj]
  · simp

/-! ## Gram representations of `zCov` -/

lemma exists_gram (hGR : Blueprint.GramRepresentation) (hPSD : Blueprint.ZCovPSD)
    (S : Finset (ℝ → ℝ)) (hS : ∀ a ∈ S, ∃ p, a ∈ V p) :
    ∃ T : (ℝ → ℝ) → EuclideanSpace ℝ S, ∀ a ∈ S, ∀ b ∈ S, ⟪T a, T b⟫ = zCov a b :=
  hGR (ℝ → ℝ) S zCov (hPSD S fun a ha => by
    obtain ⟨p, hp⟩ := hS a ha
    exact (V_continuous hp).intervalIntegrable 0 1)

lemma aE_nonneg (p : ℕ) : (0 : EReal) ≤ aE p := by
  unfold aE
  refine le_iSup_of_le ∅ ?_
  have : IsEmpty (↥(∅ : Finset (V p))) := ⟨fun x => Finset.notMem_empty _ x.2⟩
  simp [gaussianExpectedMax]

lemma vecEM_le_of_gram (hGB : Blueprint.GramBridge) {p : ℕ} {ι E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (F : Finset ι) (φ : ι → V p) (T : (ℝ → ℝ) → E)
    (hT : ∀ i ∈ F, ∀ j ∈ F, ⟪T (φ i), T (φ j)⟫ = zCov (φ i) (φ j)) (B : ℝ)
    (hB : ∀ G : Finset (V p),
      gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) ≤ B) :
    vecExpectedMax F (fun i => T (φ i)) (fun i => -energy (φ i)) ≤ B := by
  classical
  rw [vecEM_comp_image F φ (fun g : V p => T g) (fun g : V p => -energy g),
    ← hGB (V p) E (F.image φ) (fun g => T g) (fun g => -energy g)]
  refine le_trans (le_of_eq ?_) (hB (F.image φ))
  apply gEM_congr
  · intro g hg g' hg'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hg'
    exact hT i hi j hj
  · intro _ _; rfl

/-! ## The comparison family -/

/-- Components of the comparison vector: the coarse part, then the rescaled fine pieces. -/
def comp {E : Type*} [AddCommGroup E] [Module ℝ E] (n : ℕ) (T : (ℝ → ℝ) → E) (f : ℝ → ℝ) :
    Option (Fin (16 ^ n)) → E
  | none => T (coarse n f)
  | some k => (1 / (16 : ℝ) ^ n) • T (fine n f k)

/-- Components of the drift `-E(f) = -E(g) - ∑ₖ 16⁻ⁿ E(ũ_k)`. -/
def drift (n : ℕ) (f : ℝ → ℝ) : Option (Fin (16 ^ n)) → ℝ
  | none => -energy (coarse n f)
  | some k => (1 / (16 : ℝ) ^ n) * -energy (fine n f k)

lemma sum_drift {n m : ℕ} {f : ℝ → ℝ} (hf : f ∈ V (n + m)) :
    ∑ o, drift n f o = -energy f := by
  rw [Fintype.sum_option]
  simp only [drift]
  rw [Fin.sum_univ_eq_sum_range (fun k => 1 / (16 : ℝ) ^ n * -energy (fine n f k)) (16 ^ n),
    energy_decomp hf]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-! ## The main estimate -/

theorem main_bound (hSF : Blueprint.SudakovFernique) (hGB : Blueprint.GramBridge)
    (hGR : Blueprint.GramRepresentation) (hMI : Blueprint.MaxIntegrable)
    (hPSD : Blueprint.ZCovPSD) {n m : ℕ} (F : Finset (V (n + m))) (A B : ℝ)
    (hA : ∀ G : Finset (V n),
      gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) ≤ A)
    (hB : ∀ G : Finset (V m),
      gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) ≤ B) :
    gaussianExpectedMax F (fun f g => zCov f g) (fun f => -energy f) ≤ A + B := by
  classical
  have hN : (0 : ℝ) < 16 ^ n := by positivity
  -- a Gram representation of `zCov` on `F`
  obtain ⟨v, hv⟩ := exists_gram hGR hPSD (F.image Subtype.val) (by
    intro a ha
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.1 ha
    exact ⟨n + m, f.2⟩)
  have hvF : ∀ f ∈ F, f.1 ∈ F.image Subtype.val := fun f hf => Finset.mem_image_of_mem _ hf
  -- a Gram representation of `zCov` on the coarse parts and the rescaled fine pieces
  set S : Finset (ℝ → ℝ) := F.image (fun f => coarse n f.1) ∪
    (F ×ˢ Finset.range (16 ^ n)).image (fun q => fine n q.1.1 q.2) with hSdef
  obtain ⟨T, hT⟩ := exists_gram hGR hPSD S (by
    intro a ha
    rcases Finset.mem_union.1 ha with ha | ha
    · obtain ⟨f, _, rfl⟩ := Finset.mem_image.1 ha
      exact ⟨n, coarse_mem n f.2.1 f.2.2.1 f.2.2.2.1⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ha
      exact ⟨m, fine_mem q.1.2 (Finset.mem_range.1 (Finset.mem_product.1 hq).2)⟩)
  have hgS : ∀ f ∈ F, coarse n f.1 ∈ S := fun f hf =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hf)
  have huS : ∀ f ∈ F, ∀ k : Fin (16 ^ n), fine n f.1 k ∈ S := fun f hf k =>
    Finset.mem_union_right _ (Finset.mem_image.2
      ⟨(f, k), Finset.mem_product.2 ⟨hf, Finset.mem_range.2 k.2⟩, rfl⟩)
  -- Step 1: pass to vectors
  have step1 : gaussianExpectedMax F (fun f g => zCov f g) (fun f => -energy f) =
      vecExpectedMax F (fun f => v f.1) (fun f => -energy f.1) := by
    rw [← hGB (V (n + m)) (EuclideanSpace ℝ (F.image Subtype.val)) F (fun f => v f.1)
      (fun f => -energy f.1)]
    apply gEM_congr
    · intro f hf g hg; exact (hv f.1 (hvF f hf) g.1 (hvF g hg)).symm
    · intro _ _; rfl
  -- Step 2: Sudakov–Fernique comparison with the block family
  have step2 : vecExpectedMax F (fun f => v f.1) (fun f => -energy f.1) ≤
      vecExpectedMax F (fun f => (WithLp.toLp 2 (comp n T f.1) :
        PiLp 2 (fun _ : Option (Fin (16 ^ n)) => EuclideanSpace ℝ S))) (fun f => -energy f.1) := by
    refine hSF (V (n + m)) (EuclideanSpace ℝ (F.image Subtype.val))
      (PiLp 2 (fun _ : Option (Fin (16 ^ n)) => EuclideanSpace ℝ S)) F (fun f => v f.1)
      (fun f => WithLp.toLp 2 (comp n T f.1)) (fun f => -energy f.1) fun f hf g hg => ?_
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      zCov_dist_sq v (V_continuous f.2) (V_continuous g.2) (hv _ (hvF f hf) _ (hvF f hf))
        (hv _ (hvF g hg) _ (hvF g hg)) (hv _ (hvF f hf) _ (hvF g hg)),
      ← WithLp.toLp_sub, PiLp.norm_sq_eq_of_L2, Fintype.sum_option]
    simp only [Pi.sub_apply, comp]
    rw [zCov_dist_sq T (coarse_continuous f.2) (coarse_continuous g.2)
      (hT _ (hgS f hf) _ (hgS f hf)) (hT _ (hgS g hg) _ (hgS g hg))
      (hT _ (hgS f hf) _ (hgS g hg))]
    have hk : ∀ k : Fin (16 ^ n), ‖(1 / (16 : ℝ) ^ n) • T (fine n f.1 k) -
        (1 / (16 : ℝ) ^ n) • T (fine n g.1 k)‖ ^ 2 =
        (1 / (16 : ℝ) ^ n) ^ 2 *
          (2 * π * ∫ t in (0 : ℝ)..1, |fine n f.1 k t - fine n g.1 k t|) := by
      intro k
      rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / 16 ^ n),
        zCov_dist_sq T (V_continuous (fine_mem f.2 k.2)) (V_continuous (fine_mem g.2 k.2))
          (hT _ (huS f hf k) _ (huS f hf k)) (hT _ (huS g hg k) _ (huS g hg k))
          (hT _ (huS f hf k) _ (huS g hg k))]
    rw [Finset.sum_congr rfl (fun k _ => hk k),
      Fin.sum_univ_eq_sum_range (fun k => (1 / (16 : ℝ) ^ n) ^ 2 *
        (2 * π * ∫ t in (0 : ℝ)..1, |fine n f.1 k t - fine n g.1 k t|)) (16 ^ n)]
    have hl1 := l1_decomp (n := n) (m := m) f.2 g.2
    have := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 2 * π)
    refine this.trans (le_of_eq ?_)
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  -- Step 3: a maximum of a sum is at most the sum of the maxima
  have step3 : vecExpectedMax F (fun f => (WithLp.toLp 2 (comp n T f.1) :
        PiLp 2 (fun _ : Option (Fin (16 ^ n)) => EuclideanSpace ℝ S))) (fun f => -energy f.1) ≤
      ∑ o, vecExpectedMax F (fun f => (PiLp.single 2 o (comp n T f.1 o) :
        PiLp 2 (fun _ : Option (Fin (16 ^ n)) => EuclideanSpace ℝ S)))
          (fun f => drift n f.1 o) := by
    have e1 : (fun f : V (n + m) => (WithLp.toLp 2 (comp n T f.1) :
        PiLp 2 (fun _ : Option (Fin (16 ^ n)) => EuclideanSpace ℝ S))) =
        fun f => ∑ o, (PiLp.single 2 o (comp n T f.1 o) :
          PiLp 2 (fun _ : Option (Fin (16 ^ n)) => EuclideanSpace ℝ S)) := by
      funext f; exact toLp_eq_sum_single _
    have e2 : (fun f : V (n + m) => -energy f.1) = fun f => ∑ o, drift n f.1 o := by
      funext f; exact (sum_drift f.2).symm
    rw [e1, e2]
    exact vecEM_sum_le hMI Finset.univ F
      (fun o f => (PiLp.single 2 o (comp n T f.1 o) :
        PiLp 2 (fun _ : Option (Fin (16 ^ n)) => EuclideanSpace ℝ S)))
      (fun o f => drift n f.1 o)
  -- Step 4: identify each block with a problem at level `n` or (rescaled) `m`
  have step4 : ∀ o, vecExpectedMax F (fun f => (PiLp.single 2 o (comp n T f.1 o) :
        PiLp 2 (fun _ : Option (Fin (16 ^ n)) => EuclideanSpace ℝ S)))
          (fun f => drift n f.1 o) ≤ Option.elim o A (fun _ => 1 / (16 : ℝ) ^ n * B) := by
    intro o
    rw [vecEM_congr_gram hGB F (fun f => (PiLp.single 2 o (comp n T f.1 o) :
        PiLp 2 (fun _ : Option (Fin (16 ^ n)) => EuclideanSpace ℝ S)))
      (fun f => comp n T f.1 o) (fun f => drift n f.1 o) (fun f => drift n f.1 o)
      (fun f _ g _ => inner_single_single o _ _) (fun _ _ => rfl)]
    cases o with
    | none =>
      exact vecEM_le_of_gram hGB F
        (fun f => ⟨coarse n f.1, coarse_mem n f.2.1 f.2.2.1 f.2.2.2.1⟩)
        T (fun f hf g hg => hT _ (hgS f hf) _ (hgS g hg)) A hA
    | some k =>
      simp only [comp, drift, Option.elim_some]
      rw [vecEM_smul (r := 1 / (16 : ℝ) ^ n) F (fun f => T (fine n f.1 k))
        (fun f => -energy (fine n f.1 k)) (by positivity)]
      exact mul_le_mul_of_nonneg_left (vecEM_le_of_gram hGB F
        (fun f => ⟨fine n f.1 k, fine_mem f.2 k.2⟩) T
        (fun f hf g hg => hT _ (huS f hf k) _ (huS g hg k)) B hB) (by positivity)
  -- conclusion
  rw [step1]
  refine step2.trans (step3.trans ((Finset.sum_le_sum fun o _ => step4 o).trans (le_of_eq ?_)))
  rw [Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, mul_one_div_cancel hN.ne', one_mul]

end Subadd

/-- **Lemma 2.1 (subadditivity)**: `a_{n+m} ≤ a_n + a_m` in `EReal`. -/
theorem aSubadditiveE_of (hSF : Blueprint.SudakovFernique) (hGB : Blueprint.GramBridge)
    (hGR : Blueprint.GramRepresentation) (hMI : Blueprint.MaxIntegrable)
    (hPSD : Blueprint.ZCovPSD) : Blueprint.ASubadditiveE := by
  intro n m
  have hnb : aE n ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (Subadd.aE_nonneg n)
  have hmb : aE m ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot (Subadd.aE_nonneg m)
  by_cases hn : aE n = ⊤
  · rw [hn, EReal.top_add_of_ne_bot hmb]; exact le_top
  by_cases hm : aE m = ⊤
  · rw [hm, EReal.add_top_of_ne_bot hnb]; exact le_top
  have hbound : ∀ p : ℕ, aE p ≠ ⊤ → aE p ≠ ⊥ → ∀ G : Finset (V p),
      gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) ≤ (aE p).toReal := by
    intro p hp hp' G
    have h1 : ((gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) : ℝ) : EReal) ≤
        aE p :=
      le_iSup (fun G : Finset (V p) =>
        ((gaussianExpectedMax G (fun f g => zCov f g) (fun f => -energy f) : ℝ) : EReal)) G
    rw [← EReal.coe_toReal hp hp'] at h1
    exact EReal.coe_le_coe_iff.1 h1
  rw [← EReal.coe_toReal hn hnb, ← EReal.coe_toReal hm hmb, ← EReal.coe_add]
  refine iSup_le fun F => ?_
  exact EReal.coe_le_coe_iff.2 (Subadd.main_bound hSF hGB hGR hMI hPSD F _ _
    (hbound n hn hnb) (hbound m hm hmb))

end LQGDimension
