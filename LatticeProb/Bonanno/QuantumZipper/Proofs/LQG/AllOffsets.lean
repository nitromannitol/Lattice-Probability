/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AllOffsets at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Opens of namespaces with no copied declaration are removed (BdryVague, GaussTK). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsModulus

/-!
# M4-B4: the boundary measure along all offsets `a 2^{-k}` simultaneously; M4-T2

Blueprint `M4_BLUEPRINT.md`, nodes M4-B4 and M4-T2.

* `ae_hasBdryLimit`: for the free field (any additive-constant convention), almost surely
  `HasBdryLimit γ (X ω) (qBoundaryMeasure γ (X ω))`, i.e. the approximations `ν_{a 2^{-k}}`
  converge vaguely to `qBoundaryMeasure γ (X ω)` **uniformly in `a ∈ [1,2]`**.
  Proof (grid plus modulus): for `f` in the countable test family and a level-`n` dyadic offset
  `a`, `|ν_{aε}(f) − ν(f)| ≤ ∫ |f| d_{2ε} · chainT + ∑_{grid} |ν_{cε}(f) − ν(f)|`
  (`pathwise_bound`); the expectation of the right side is `≤ C θ^m + (2^m+1) C 2^{-βk}`
  uniformly in `n` (`lintegral_sup_level_le`); with `m = ⌊βk/2⌋` this is summable in `k`, and the
  continuity of the densities in the radius (every-circle regularity) passes from dyadic
  offsets to all of `[1,2]`.
* M4-T2: `qBoundaryMeasure_translate` and `qBoundaryMeasure_reflectH` (for good samples and
  every real `t` at once).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace AllOffsets

open BdryExist BdryVague GaussTK TwoRadius GoodSample

/-! ## C0. Countable test family along `goodFilter` -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## C1. Pathwise bound -/

/-- `L(ω) = ∫ g dν(Z ω)`. -/
def Lf (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (g : ℝ → ℝ) (ω : Ω) : ℝ :=
  ∫ t, g t ∂qBoundaryMeasure γ (zField X R ω)

theorem bA_eq_integral (hX : IsFreeGFFModConstH X P) (γ R : ℝ) {r : ℝ} (hr : 0 < r)
    (g : ℝ → ℝ) (ω : Ω) :
    bA γ X R g r ω = ∫ t, bdryDens γ (zField X R ω) r t * g t := by
  have hd : Measurable (fun t => bdryDens γ (zField X R ω) r t) := by
    have h : Measurable (fun t : ℝ => ((ω, t) : Ω × ℝ)) := measurable_const.prodMk measurable_id
    exact Measurable.comp (g := fun p : Ω × ℝ => bdryDens γ (zField X R p.1) r p.2)
      (f := fun t : ℝ => ((ω, t) : Ω × ℝ)) (measurable_bdryDens_zField hX γ R r) h
  rw [bA, bdryR, GoodSample.integral_withDensity_ofReal hd
    (fun t => GoodSample.bdryDens_nonneg γ _ hr t)]

theorem measurable_chainT_Ht (hX : IsFreeGFFModConstH X P) (γ R ε : ℝ) (m n : ℕ) :
    Measurable (fun p : Ω × ℝ => chainT m n (fun a => Ht γ X R ε p.2 a p.1)) := by
  have hz : ∀ r, Measurable (fun p : Ω × ℝ => zV X R r p.2 p.1) := fun r =>
    Measurable.comp (g := fun p : ℝ × Ω => zV X R r p.1 p.2) (f := Prod.swap)
      (measurable_zV hX R r) measurable_swap
  have hH : ∀ a, Measurable (fun p : Ω × ℝ => Ht γ X R ε p.2 a p.1) := by
    intro a
    show Measurable (fun p : Ω × ℝ => (a / 2) ^ (γ ^ 2 / 4) *
      exp (γ / 2 * (zV X R (a * ε) p.2 p.1 - zV X R (2 * ε) p.2 p.1)))
    exact measurable_const.mul ((((hz _).sub (hz _)).const_mul _).exp)
  unfold chainT incr
  exact Finset.measurable_sum _ fun j _ => measurable_const.add
    ((Finset.measurable_sum _ fun l _ => ((hH _).sub (hH _)).pow_const 4).div_const _)

theorem pathwise_bound (hX : IsFreeGFFModConstH X P) {γ R : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F)
    (L : ℝ) {ε : ℝ} (hε : 0 < ε) (m d : ℕ) {i : ℕ} (hi : i ≤ 2 ^ (m + d)) :
    ENNReal.ofReal |bA γ X R g (dpt (m + d) i * ε) ω - L| ≤
      (∫⁻ t, ENNReal.ofReal (|g t| * (bdryDens γ (zField X R ω) (2 * ε) t *
        chainT m (m + d) (fun a => Ht γ X R ε t a ω)))) +
      ∑ l ∈ Finset.range (2 ^ m + 1), ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - L| := by
  have hFZ := regular_zField (R := R) hF
  have ha : 0 < dpt (m + d) i := by linarith [dpt_ge_one (m + d) i]
  have ha' : 0 < dpt m (i / 2 ^ d) := by linarith [dpt_ge_one m (i / 2 ^ d)]
  have hint : ∀ r, 0 < r → Integrable (fun t => bdryDens γ (zField X R ω) r t * g t) :=
    fun r hr => ((continuous_bdryDens γ hFZ hr).mul hg).integrable_of_hasCompactSupport
      hgc.mul_left
  have hil : i / 2 ^ d ≤ 2 ^ m :=
    Nat.div_le_of_le_mul (by rw [pow_add] at hi; rw [mul_comm]; exact hi)
  have h1 := mul_pos ha hε
  have h2 := mul_pos ha' hε
  have hmod : ENNReal.ofReal |bA γ X R g (dpt (m + d) i * ε) ω -
      bA γ X R g (dpt m (i / 2 ^ d) * ε) ω| ≤
      ∫⁻ t, ENNReal.ofReal (|g t| * (bdryDens γ (zField X R ω) (2 * ε) t *
        chainT m (m + d) (fun a => Ht γ X R ε t a ω))) := by
    rw [bA_eq_integral hX γ R h1, bA_eq_integral hX γ R h2,
      ← integral_sub (hint _ h1) (hint _ h2)]
    have hi2 : Integrable (fun t => |bdryDens γ (zField X R ω) (dpt (m + d) i * ε) t * g t -
        bdryDens γ (zField X R ω) (dpt m (i / 2 ^ d) * ε) t * g t|) :=
      ((hint _ h1).sub (hint _ h2)).abs
    refine (ENNReal.ofReal_le_ofReal (abs_integral_le_integral_abs)).trans ?_
    rw [ofReal_integral_eq_lintegral_ofReal hi2 (ae_of_all _ fun _ => abs_nonneg _)]
    refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
    rw [bdryDens_eq_mul_Ht γ R hε ha t ω, bdryDens_eq_mul_Ht γ R hε ha' t ω, ← sub_mul,
      ← mul_sub, abs_mul, abs_mul,
      abs_of_nonneg (bdryDens_nonneg γ _ (by positivity : (0 : ℝ) < 2 * ε) t)]
    have hc : |Ht γ X R ε t (dpt (m + d) i) ω - Ht γ X R ε t (dpt m (i / 2 ^ d)) ω| ≤
        chainT m (m + d) (fun b => Ht γ X R ε t b ω) :=
      chain_bound (fun b => Ht γ X R ε t b ω) m d i hi
    have hd0 := bdryDens_nonneg γ (zField X R ω) (show (0 : ℝ) < 2 * ε by positivity) t
    calc bdryDens γ (zField X R ω) (2 * ε) t *
          |Ht γ X R ε t (dpt (m + d) i) ω - Ht γ X R ε t (dpt m (i / 2 ^ d)) ω| * |g t|
        ≤ bdryDens γ (zField X R ω) (2 * ε) t *
          chainT m (m + d) (fun b => Ht γ X R ε t b ω) * |g t| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hd0) (abs_nonneg _)
      _ = _ := by ring
  have hgrid : ENNReal.ofReal |bA γ X R g (dpt m (i / 2 ^ d) * ε) ω - L| ≤
      ∑ l ∈ Finset.range (2 ^ m + 1), ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - L| :=
    Finset.single_le_sum (f := fun l => ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - L|)
      (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))
  calc ENNReal.ofReal |bA γ X R g (dpt (m + d) i * ε) ω - L|
      ≤ ENNReal.ofReal (|bA γ X R g (dpt (m + d) i * ε) ω -
          bA γ X R g (dpt m (i / 2 ^ d) * ε) ω| +
          |bA γ X R g (dpt m (i / 2 ^ d) * ε) ω - L|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ ≤ _ := ENNReal.ofReal_add_le.trans (add_le_add hmod hgrid)

/-! ## C2. Expectation at a fixed level -/

theorem lintegral_sup_level_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgS : ∀ t ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), g t = 0)
    {Cg : ℝ} (hCg0 : 0 ≤ Cg) (hCg : ∀ k : ℕ, ∀ c ∈ Icc (1 : ℝ) 2,
      AEMeasurable (fun ω => bA γ X ((N : ℝ) + 3) g (c * radius k) ω -
        Lf γ X ((N : ℝ) + 3) g ω) P ∧
      ∫⁻ ω, ENNReal.ofReal |bA γ X ((N : ℝ) + 3) g (c * radius k) ω -
        Lf γ X ((N : ℝ) + 3) g ω| ∂P ≤
        ENNReal.ofReal (Cg * exp (-bdryRate γ * (k * log 2))))
    (k m d : ℕ) :
    ∫⁻ ω, ⨆ i : Fin (2 ^ (m + d) + 1), ENNReal.ofReal
        |bA γ X ((N : ℝ) + 3) g (dpt (m + d) i * radius k) ω - Lf γ X ((N : ℝ) + 3) g ω| ∂P ≤
      ENNReal.ofReal ((∫ t, |g t|) * (((N : ℝ) + 3) ^ (γ ^ 2 / 4) *
          ((8 + 4 * (2544 * exp 16)) * θm ^ m)) +
        (2 ^ m + 1) * (Cg * exp (-bdryRate γ * (k * log 2)))) := by
  set R : ℝ := (N : ℝ) + 3 with hR
  set ε := radius k with hεd
  have hε := radius_pos k
  have hε1 := radius_le_one k
  set K := R ^ (γ ^ 2 / 4) * ((8 + 4 * (2544 * exp 16)) * θm ^ m) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ R := by positivity
    have := θm_pos
    positivity
  set Mod : Ω → ℝ≥0∞ := fun ω => ∫⁻ t, ENNReal.ofReal (|g t| *
    (bdryDens γ (zField X R ω) (2 * ε) t * chainT m (m + d) (fun a => Ht γ X R ε t a ω)))
    with hMod
  set Gr : Ω → ℝ≥0∞ := fun ω => ∑ l ∈ Finset.range (2 ^ m + 1),
    ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - Lf γ X R g ω| with hGr
  have hpt : ∀ᵐ ω ∂P, (⨆ i : Fin (2 ^ (m + d) + 1), ENNReal.ofReal
      |bA γ X R g (dpt (m + d) i * ε) ω - Lf γ X R g ω|) ≤ Mod ω + Gr ω := by
    filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg
    obtain ⟨F, hF⟩ := hreg
    exact iSup_le fun i => pathwise_bound hX hg hgc hF _ hε m d (i := (i : ℕ)) (Nat.lt_succ_iff.1 i.2)
  refine (lintegral_mono_ae hpt).trans ?_
  have hFm : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (|g p.2| *
      (bdryDens γ (zField X R p.1) (2 * ε) p.2 *
        chainT m (m + d) (fun a => Ht γ X R ε p.2 a p.1)))) :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp (hg.measurable.comp measurable_snd)).mul
      ((measurable_bdryDens_zField hX γ R _).mul (measurable_chainT_Ht hX γ R ε m (m + d))))
  have hModm : Measurable Mod := hFm.lintegral_prod_right'
  rw [lintegral_add_left' hModm.aemeasurable]
  have hgi : Integrable (fun t => |g t|) := (hg.integrable_of_hasCompactSupport hgc).abs
  have hI0 : 0 ≤ ∫ t, |g t| := integral_nonneg fun _ => abs_nonneg _
  have hModb : ∫⁻ ω, Mod ω ∂P ≤ ENNReal.ofReal ((∫ t, |g t|) * K) := by
    simp only [hMod]
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    have hpt2 : ∀ t, ∫⁻ ω, ENNReal.ofReal (|g t| * (bdryDens γ (zField X R ω) (2 * ε) t *
        chainT m (m + d) (fun a => Ht γ X R ε t a ω))) ∂P ≤
        ENNReal.ofReal |g t| * ENNReal.ofReal K := by
      intro t
      simp_rw [ENNReal.ofReal_mul (abs_nonneg (g t))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      by_cases ht : t ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)
      · have htR : |t| + 2 * ε ≤ R := by
          have := abs_le.2 ⟨ht.1, ht.2⟩
          rw [hR]; linarith
        gcongr
        exact lintegral_dens_chainT_le hX hγ hγ2 hε htR m (m + d)
      · rw [hgS t ht, abs_zero, ENNReal.ofReal_zero, zero_mul, zero_mul]
    refine (lintegral_mono hpt2).trans (le_of_eq ?_)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ fun _ => abs_nonneg _),
      ← ENNReal.ofReal_mul hI0]
  have hGrb : ∫⁻ ω, Gr ω ∂P ≤
      ENNReal.ofReal ((2 ^ m + 1) * (Cg * exp (-bdryRate γ * (k * log 2)))) := by
    have hmem : ∀ l ∈ Finset.range (2 ^ m + 1), dpt m l ∈ Icc (1 : ℝ) 2 := fun l hl =>
      ⟨dpt_ge_one m l, dpt_le_two (by have := Finset.mem_range.1 hl; omega)⟩
    simp only [hGr]
    have hael : ∀ l ∈ Finset.range (2 ^ m + 1), AEMeasurable (fun ω =>
        ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - Lf γ X R g ω|) P := fun l hl =>
      (continuous_abs.measurable.comp_aemeasurable (hCg k _ (hmem l hl)).1).ennreal_ofReal
    rw [lintegral_finset_sum' _ hael]
    refine (Finset.sum_le_sum fun l hl => (hCg k _ (hmem l hl)).2).trans (le_of_eq ?_)
    have hC0 : 0 ≤ (2 : ℝ) ^ m + 1 := by positivity
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul hC0,
      show ((2 : ℝ) ^ m + 1) = ((2 ^ m + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  refine (add_le_add hModb hGrb).trans (le_of_eq ?_)
  have hCg0' : 0 ≤ (2 ^ m + 1) * (Cg * exp (-bdryRate γ * (k * log 2))) := by positivity
  rw [← ENNReal.ofReal_add (mul_nonneg hI0 hK0) hCg0']

/-! ## C3. Summation over the scales -/
/-- The supremum over all dyadic offsets at scale `k`. -/
def supG (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (g : ℝ → ℝ) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (i : Fin (2 ^ n + 1)),
    ENNReal.ofReal |bA γ X R g (dpt n i * radius k) ω - Lf γ X R g ω|

theorem dpt_double (n i : ℕ) : dpt n i = dpt (n + 1) (2 * i) := by
  unfold dpt; push_cast; rw [pow_succ]; field_simp

theorem level_mono (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (g : ℝ → ℝ) (k : ℕ) (ω : Ω) :
    Monotone (fun n : ℕ => ⨆ i : Fin (2 ^ n + 1),
      ENNReal.ofReal |bA γ X R g (dpt n i * radius k) ω - Lf γ X R g ω|) := by
  refine monotone_nat_of_le_succ fun n => iSup_le fun i => ?_
  have hi : 2 * (i : ℕ) < 2 ^ (n + 1) + 1 := by have := i.2; rw [pow_succ]; omega
  refine le_iSup_of_le (⟨2 * i, hi⟩ : Fin (2 ^ (n + 1) + 1)) (le_of_eq ?_)
  rw [dpt_double n i]

theorem lintegral_supG_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgS : ∀ t ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), g t = 0)
    {Cg : ℝ} (hCg0 : 0 ≤ Cg) (hCg : ∀ k : ℕ, ∀ c ∈ Icc (1 : ℝ) 2,
      AEMeasurable (fun ω => bA γ X ((N : ℝ) + 3) g (c * radius k) ω -
        Lf γ X ((N : ℝ) + 3) g ω) P ∧
      ∫⁻ ω, ENNReal.ofReal |bA γ X ((N : ℝ) + 3) g (c * radius k) ω -
        Lf γ X ((N : ℝ) + 3) g ω| ∂P ≤
        ENNReal.ofReal (Cg * exp (-bdryRate γ * (k * log 2))))
    (k m : ℕ) :
    ∫⁻ ω, supG γ X ((N : ℝ) + 3) g k ω ∂P ≤
      ENNReal.ofReal ((∫ t, |g t|) * (((N : ℝ) + 3) ^ (γ ^ 2 / 4) *
          ((8 + 4 * (2544 * exp 16)) * θm ^ m)) +
        (2 ^ m + 1) * (Cg * exp (-bdryRate γ * (k * log 2)))) := by
  have hmeas : ∀ n, AEMeasurable (fun ω => ⨆ i : Fin (2 ^ n + 1), ENNReal.ofReal
      |bA γ X ((N : ℝ) + 3) g (dpt n i * radius k) ω - Lf γ X ((N : ℝ) + 3) g ω|) P :=
    fun n => AEMeasurable.iSup fun i =>
      (continuous_abs.measurable.comp_aemeasurable (hCg k _
        ⟨dpt_ge_one n i, dpt_le_two (Nat.lt_succ_iff.1 i.2)⟩).1).ennreal_ofReal
  show ∫⁻ ω, ⨆ n : ℕ, (⨆ i : Fin (2 ^ n + 1), ENNReal.ofReal
      |bA γ X ((N : ℝ) + 3) g (dpt n i * radius k) ω - Lf γ X ((N : ℝ) + 3) g ω|) ∂P ≤ _
  rw [lintegral_iSup' hmeas (ae_of_all _ fun ω => level_mono γ X _ g k ω)]
  refine iSup_le fun n => ?_
  obtain ⟨d, hd⟩ : ∃ d, max n m = m + d := ⟨max n m - m, by omega⟩
  exact (lintegral_mono fun ω => level_mono γ X _ g k ω (show n ≤ m + d by omega)).trans
    (lintegral_sup_level_le hX hγ hγ2 hg hgc hgS hCg0 hCg k m d)

/-! ## C4. Almost sure uniform convergence for the normalized field -/

/-! ## C5. Back to the free field -/

/-! ## T2. Translation and reflection (M4-T2) -/

section T2

variable {x : FieldSample} {γ : ℝ}

end T2

end AllOffsets
end QuantumZipper
