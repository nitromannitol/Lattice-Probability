/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA3Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA3Product

/-!
# [18] Lemma A.3 for product data, the moment bound

[18] Lemma A.3, (A.6) for `X ≥ 0`, in the abstract form described
in `LemmaA3Product`: for data `(E, C, Z)` with the independence structure of the Markov decomposition, a pointwise
Cameron–Martin change of measure between the two harmonic parts `e, e'` with variance bound `M(e, e')`, and the
exponential moment `E exp(2 s θ q² M) ≤ K` (`s = p p₀/(p₀ − p)`, `θ = 1 − 1/p₀`):

`E|E[X | 𝒢] − E[X | σ(C)]|^p ≤ 2^{p−1} (t^p E[X^p] + E[X^{p₀}]^{p/p₀} (2^s e^{−sθqt/4} K)^{1−p/p₀})`.

* **`GMSAppA.lemmaA3_product`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

variable {Ω 𝓔 𝓒 𝓩 : Type*} {𝓖 m0 : MeasurableSpace Ω} [MeasurableSpace 𝓔] [MeasurableSpace 𝓒]
  [MeasurableSpace 𝓩] {P : Measure Ω} [IsProbabilityMeasure P]

/-- the coupling exponent `s = p p₀/(p₀ − p)` -/
def cplExp (p p₀ : ℝ) : ℝ := p * (p₀ / (p₀ - p))

/-- the constant `(2^s e^{−sθqt/4} K)^{1−p/p₀}` -/
def cplTail (p p₀ q t K : ℝ) : ℝ :=
  (2 ^ cplExp p p₀ * Real.exp (-(cplExp p p₀ * (1 - 1 / p₀) * (q * t / 4))) * K)

/-- **[18] Lemma A.3 for product data** (`X ≥ 0`). -/
theorem lemmaA3_product {E : Ω → 𝓔} {C : Ω → 𝓒} {Z : Ω → 𝓩} (h𝓖 : 𝓖 ≤ m0)
    (hE𝓖 : Measurable[𝓖] E) (hC𝓖 : Measurable[𝓖] C) (hZ : Measurable Z)
    (hind : Indep 𝓖 (MeasurableSpace.comap Z inferInstance) P)
    (hCEZ : IndepFun C (fun ω => (E ω, Z ω)) P) (hEZ : IndepFun E Z P)
    {Φ : 𝓔 × 𝓒 × 𝓩 → ℝ} (hΦ : Measurable Φ) (hΦ0 : ∀ x, 0 ≤ Φ x)
    {X : Ω → ℝ} (hX : X =ᵐ[P] fun ω => Φ (E ω, C ω, Z ω))
    {p p₀ q t K : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (hq1 : 1 ≤ q) (hqr : p₀ / (p₀ - 1) ≤ q)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {Mf : Ω × Ω → ℝ} (hMf : Measurable Mf)
    (hCM : ∀ᵐ x ∂(P.prod P), ∃ ρ : 𝓩 → ℝ, Measurable ρ ∧ (∀ z, 0 ≤ ρ z) ∧
      ∃ V : ℝ, 0 ≤ V ∧ V ≤ Mf x ∧
        (∀ s : ℝ, ∫⁻ z, ENNReal.ofReal (ρ z) ^ s ∂(P.map Z) =
          ENNReal.ofReal (Real.exp (s * (s - 1) * V / 2))) ∧
        ∀ c : 𝓒, ∫⁻ z, ENNReal.ofReal (Φ (E x.1, c, z)) ∂(P.map Z) =
          ∫⁻ z, ENNReal.ofReal (Φ (E x.2, c, z)) * ENNReal.ofReal (ρ z) ∂(P.map Z))
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.exp (2 * cplExp p p₀ * (1 - 1 / p₀) * q ^ 2 * Mf x))
      ∂(P.prod P) ≤ ENNReal.ofReal K)
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal (X ω) ^ p₀ ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal |P[X | 𝓖] ω - P[X | MeasurableSpace.comap C inferInstance] ω| ^ p ∂P ≤
      2 ^ (p - 1) * (ENNReal.ofReal t ^ p * ∫⁻ ω, ENNReal.ofReal (X ω) ^ p ∂P +
        (∫⁻ ω, ENNReal.ofReal (X ω) ^ p₀ ∂P) ^ (p / p₀) *
          ENNReal.ofReal (cplTail p p₀ q t K) ^ (1 - p / p₀)) := by
  have hp0 : 0 < p := by linarith
  have hp₀1 : 1 < p₀ := by linarith
  have hp₀ : 0 < p₀ := by linarith
  have hE : Measurable E := hE𝓖.mono h𝓖 le_rfl
  have hC : Measurable C := hC𝓖.mono h𝓖 le_rfl
  have hECZ : IndepFun (fun ω => (E ω, C ω)) Z P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind (hE𝓖.prodMk hC𝓖).comap_le
  set νZ := P.map Z
  have hνZ : IsProbabilityMeasure νZ := (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 ‹_›
  -- the integrand and its integrability
  set f : 𝓔 × 𝓒 × 𝓩 → ℝ≥0∞ := fun x => ENNReal.ofReal (Φ x) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp hΦ
  have hXΦ : (fun ω => ENNReal.ofReal (X ω)) =ᵐ[P] fun ω => f (E ω, C ω, Z ω) := by
    filter_upwards [hX] with ω hω; rw [hω]
  have hpowΦ : ∀ r : ℝ, ∫⁻ ω, ENNReal.ofReal (X ω) ^ r ∂P = ∫⁻ ω, f (E ω, C ω, Z ω) ^ r ∂P :=
    fun r => lintegral_congr_ae (hXΦ.mono fun ω hω => by simp only [hω])
  have hXfin : ∫⁻ ω, f (E ω, C ω, Z ω) ∂P ≠ ⊤ := by
    have h1 := lintegral_rpow_le_rpow_lintegral (P := P) (Z := fun ω => f (E ω, C ω, Z ω))
      (hfm.comp (hE.prodMk (hC.prodMk hZ))).aemeasurable one_pos hp₀1.le
    simp only [ENNReal.rpow_one] at h1
    refine ne_top_of_le_ne_top ?_ h1
    rw [← hpowΦ]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hXp₀
  have hi : Integrable (fun ω => Φ (E ω, C ω, Z ω)) P := by
    refine ⟨(hΦ.comp (hE.prodMk (hC.prodMk hZ))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => hΦ0 _)]
    exact lt_top_iff_ne_top.2 hXfin
  -- `A` and `Ã`
  set A : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, f (E ω, C ω, z) ∂νZ with hAdef
  set At : Ω × Ω → ℝ≥0∞ := fun x => ∫⁻ z, f (E x.2, C x.1, z) ∂νZ with hAtdef
  have hfZ : Measurable fun p : (Ω × Ω) × 𝓩 => f (E p.1.2, C p.1.1, p.2) :=
    hfm.comp ((hE.comp (measurable_snd.comp measurable_fst)).prodMk
      ((hC.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
  have hAtm : Measurable At := hfZ.lintegral_prod_right'
  -- the two conditional expectations
  have hcA : P[X | 𝓖] =ᵐ[P] fun ω => (A ω).toReal := by
    refine (condExp_congr_ae hX).trans ((condExp_eq_A h𝓖 hE𝓖 hC𝓖 hZ hind hΦ hi).trans ?_)
    refine ae_of_all _ fun ω => ?_
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => hΦ0 _)
      (hΦ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have hcB : P[X | MeasurableSpace.comap C inferInstance] =ᵐ[P]
      fun ω => (∫⁻ ω', At (ω, ω') ∂P).toReal := by
    refine (condExp_congr_ae hX).trans ((condExp_eq_B hE hC hZ hCEZ hEZ hΦ hi).trans ?_)
    refine ae_of_all _ fun ω => ?_
    have hgm : Measurable fun y : 𝓔 × 𝓩 => Φ (y.1, C ω, y.2) :=
      hΦ.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    show ∫ x, Φ (x.1, C ω, x.2) ∂((P.map E).prod νZ) = _
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => hΦ0 _) hgm.aestronglyMeasurable]
    congr 1
    have hgm' : Measurable fun y : 𝓔 × 𝓩 => ENNReal.ofReal (Φ (y.1, C ω, y.2)) :=
      ENNReal.measurable_ofReal.comp hgm
    rw [lintegral_prod _ hgm'.aemeasurable, lintegral_map hgm'.lintegral_prod_right' hE]
  -- finiteness
  have hAfin : ∀ᵐ ω ∂P, A ω ≠ ⊤ := by
    have : ∫⁻ ω, A ω ∂P ≠ ⊤ := by
      rw [hAdef, lintegral_lintegral_eq_of_indepFun hE hC hZ hECZ hfm]; exact hXfin
    have hAm : Measurable A := (hfm.comp ((hE.comp measurable_fst).prodMk
      ((hC.comp measurable_fst).prodMk measurable_snd))).lintegral_prod_right'
    exact (ae_lt_top hAm this).mono fun ω h => h.ne
  have hBfin : ∀ᵐ ω ∂P, ∫⁻ ω', At (ω, ω') ∂P ≠ ⊤ := by
    have : ∫⁻ ω, ∫⁻ ω', At (ω, ω') ∂P ∂P ≠ ⊤ := by
      rw [hAtdef, lintegral_lintegral_lintegral_eq_of_indepFun hE hC hZ hCEZ hEZ hfm]; exact hXfin
    exact (ae_lt_top hAtm.lintegral_prod_right' this).mono fun ω h => h.ne
  have hEE : Measurable fun x : Ω × Ω => (E x.1, E x.2) :=
    (hE.comp measurable_fst).prodMk (hE.comp measurable_snd)
  have hCM' := hCM
  -- the bounds `N`, `Θ`, `T`
  set N : Ω × Ω → ℝ≥0∞ := fun x => ∫⁻ z, f (E x.2, C x.1, z) ^ p₀ ∂νZ with hNdef
  have hNm : Measurable N := (hfZ.pow_const p₀).lintegral_prod_right'
  set Θ : Ω × Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (tiltTail p₀ q t (Mf x)) with hΘdef
  have hΘm : Measurable Θ := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold tiltTail
    exact (Real.measurable_exp.comp ((measurable_const.mul
      ((measurable_const.mul hMf).sub measurable_const)))).const_mul _
  set T : Ω × Ω → ℝ≥0∞ := fun x => N x ^ (1 / p₀) * Θ x with hTdef
  have hTm : Measurable T := (hNm.pow_const _).mul hΘm
  have htt : ∀ V W : ℝ, V ≤ W → tiltTail p₀ q t V ≤ tiltTail p₀ q t W := by
    intro V W hVW
    unfold tiltTail
    have hθ : 0 ≤ 1 - 1 / p₀ := by
      rw [sub_nonneg, div_le_one hp₀]; linarith
    gcongr
  have hsand : ∀ᵐ x ∂(P.prod P), A x.1 ≤ ENNReal.ofReal (1 + t) * At x + T x ∧
      At x ≤ A x.1 + ENNReal.ofReal t * At x + T x := by
    filter_upwards [hCM'] with x ⟨ρ, hρm, hρ0, V, hV0, hVM, hmomρ, hshift⟩
    set Ψ : 𝓩 → ℝ≥0∞ := fun z => f (E x.2, C x.1, z) with hΨdef
    have hΨm : Measurable Ψ := hfm.comp (measurable_const.prodMk (measurable_const.prodMk
      measurable_id))
    have hAx : A x.1 = ∫⁻ z, Ψ z * ENNReal.ofReal (ρ z) ∂νZ := hshift (C x.1)
    have hAtx : At x = ∫⁻ z, Ψ z ∂νZ := rfl
    have hup := lintegral_mul_ofReal_le_tilt (ν := νZ) hΨm (ρ := ρ) ht0
    have hlo := lintegral_le_tilt (ν := νZ) hΨm hρm ht0
    have hmP : ∫⁻ z, ENNReal.ofReal (ρ z) ^ q ∂νZ ≤ ENNReal.ofReal (Real.exp (q ^ 2 * V / 2)) := by
      rw [hmomρ q]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
    have hmN : ∫⁻ z, ENNReal.ofReal (ρ z) ^ (-q) ∂νZ ≤ ENNReal.ofReal (Real.exp (q ^ 2 * V)) := by
      rw [hmomρ (-q)]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
        nlinarith [mul_nonneg (sub_nonneg.2 hq1) hV0]))
    have hm2 : ∫⁻ z, ENNReal.ofReal (ρ z) ^ (2 * (1 * (p₀ / (p₀ - 1)))) ∂νZ ≤
        ENNReal.ofReal (Real.exp (2 * (p₀ / (p₀ - 1)) ^ 2 * V)) := by
      rw [hmomρ]
      have hr0 : 0 ≤ p₀ / (p₀ - 1) := div_nonneg hp₀.le (by linarith)
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
    have htails := tails_le_tilt (ν := νZ) hΨm hρm hp₀1 hq1 hqr ht0 ht1 hV0 hmP hmN hm2
    have hTx : ∫⁻ z, tUp Ψ ρ t z ∂νZ + ∫⁻ z, tLo Ψ ρ t z ∂νZ ≤ T x := by
      refine htails.trans ?_
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (htt V _ hVM))
    refine ⟨?_, ?_⟩
    · rw [hAx, hAtx]
      exact hup.trans (add_le_add le_rfl ((le_self_add).trans hTx))
    · rw [hAx, hAtx]
      refine hlo.trans (add_le_add le_rfl ((le_add_self).trans hTx))
  have hmain := coupled_longRange (P := P) (A := A) hAtm hTm hNm hΘm hAfin hBfin ht0
    (hsand.mono fun x h => h.1) (hsand.mono fun x h => h.2) hp hpp₀
    (ae_of_all _ fun x => le_rfl)
  -- the left-hand side
  have hLHS : ∫⁻ ω, ENNReal.ofReal |P[X | 𝓖] ω - P[X | MeasurableSpace.comap C inferInstance] ω| ^ p ∂P
      = ∫⁻ ω, ENNReal.ofReal |(A ω).toReal - (∫⁻ ω', At (ω, ω') ∂P).toReal| ^ p ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hcA, hcB] with ω h1 h2
    rw [h1, h2]
  rw [hLHS]
  refine hmain.trans ?_
  -- the moments
  have hm1 : ∫⁻ x, At x ^ p ∂(P.prod P) ≤ ∫⁻ ω, ENNReal.ofReal (X ω) ^ p ∂P := by
    calc ∫⁻ x, At x ^ p ∂(P.prod P) ≤ ∫⁻ x, ∫⁻ z, f (E x.2, C x.1, z) ^ p ∂νZ ∂(P.prod P) :=
          lintegral_mono fun x => rpow_lintegral_le_lintegral_rpow
            (hfm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aemeasurable hp
      _ = ∫⁻ ω, ∫⁻ ω', ∫⁻ z, f (E ω', C ω, z) ^ p ∂νZ ∂P ∂P :=
          lintegral_prod _ (hfZ.pow_const p).lintegral_prod_right'.aemeasurable
      _ = ∫⁻ ω, f (E ω, C ω, Z ω) ^ p ∂P :=
          lintegral_lintegral_lintegral_eq_of_indepFun hE hC hZ hCEZ hEZ (hfm.pow_const p)
      _ = ∫⁻ ω, ENNReal.ofReal (X ω) ^ p ∂P := (hpowΦ p).symm
  have hm2 : ∫⁻ x, N x ∂(P.prod P) = ∫⁻ ω, ENNReal.ofReal (X ω) ^ p₀ ∂P := by
    rw [lintegral_prod _ hNm.aemeasurable, hNdef]
    rw [lintegral_lintegral_lintegral_eq_of_indepFun hE hC hZ hCEZ hEZ (hfm.pow_const p₀)]
    exact (hpowΦ p₀).symm
  have hm3 : ∫⁻ x, Θ x ^ (p * (p₀ / (p₀ - p))) ∂(P.prod P) ≤ ENNReal.ofReal (cplTail p p₀ q t K) := by
    set s := p * (p₀ / (p₀ - p)) with hs
    have hs0 : 0 ≤ s := by positivity
    have hpt : ∀ x : Ω × Ω, Θ x ^ s = ENNReal.ofReal (2 ^ s *
        Real.exp (-(s * (1 - 1 / p₀) * (q * t / 4)))) *
        ENNReal.ofReal (Real.exp (2 * s * (1 - 1 / p₀) * q ^ 2 * Mf x)) := by
      intro x
      rw [hΘdef, ENNReal.ofReal_rpow_of_nonneg (tiltTail_nonneg _ _ _ _) hs0,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold tiltTail
      rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc (2 ^ s),
        ← Real.exp_add]
      congr 2
      ring
    simp_rw [hpt]
    have hmeas : Measurable fun x : Ω × Ω =>
        ENNReal.ofReal (Real.exp (2 * s * (1 - 1 / p₀) * q ^ 2 * Mf x)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hMf))
    rw [lintegral_const_mul _ hmeas]
    have hK : ∫⁻ x, ENNReal.ofReal (Real.exp (2 * s * (1 - 1 / p₀) * q ^ 2 * Mf x))
        ∂(P.prod P) ≤ ENNReal.ofReal K := hmom
    calc ENNReal.ofReal (2 ^ s * Real.exp (-(s * (1 - 1 / p₀) * (q * t / 4)))) *
          ∫⁻ x, ENNReal.ofReal (Real.exp (2 * s * (1 - 1 / p₀) * q ^ 2 * Mf x)) ∂(P.prod P)
        ≤ ENNReal.ofReal (2 ^ s * Real.exp (-(s * (1 - 1 / p₀) * (q * t / 4)))) *
          ENNReal.ofReal K := by gcongr
      _ = ENNReal.ofReal (cplTail p p₀ q t K) := by
          by_cases hK0 : 0 ≤ K
          · rw [← ENNReal.ofReal_mul (by positivity), cplTail, cplExp]
          · push Not at hK0
            rw [ENNReal.ofReal_of_nonpos hK0.le, mul_zero, cplTail,
              ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hK0.le)]
  have hθ1 : 0 ≤ 1 - p / p₀ := by rw [sub_nonneg, div_le_one hp₀]; linarith
  refine mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hm1)
    (mul_le_mul' (le_of_eq (by rw [hm2])) (ENNReal.rpow_le_rpow hm3 hθ1)))

end MatedCRTHarmonic.GMSAppA
