/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L23Cond at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable). -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L23

/-!
# DDDF (5.59), finite-dimensional part: resampling a Gaussian input of a Lipschitz functional

DDDF = arXiv:1904.08021, `tightness.tex` l. 1086–1091 (Step 3 of the proof of Theorem 20,
(5.59) = `eq:SndTerm`): "using Gaussian concentration as in the proof of Lemma 23,
`E((log L^K_n(ψ) − log L_n(ψ))²) = 2 E(Var(log L_n(ψ) | ψ_{0,n} − ψ_{0,K})) ≤ C K`",
where `L^K_n` uses an independent copy `ψ̃_{0,K}` of `ψ_{0,K}`.

Finite-dimensional form (`L23.lintegral_sq_sub_copy_le`): if `A, A'` are i.d. centered Gaussian
vectors with `Var A_i ≤ s`, `A ⟂ A'`, `(A, A') ⟂ B`, and `g(·, b)` is `K`-Lipschitz for the sup
metric, then `E (g(A', B) − g(A, B))² ≤ 2 K² s`. Proof as in DDDF: conditionally on `B = b`
(Fubini for the product law), `E (g(A', b) − g(A, b))² = 2 Var g(A, b)`
(`L23.integral_prod_sub_sq`, the independent-copy identity) and `Var g(A, b) ≤ K² s`
(Lemma 23's Gaussian concentration, `L23.memLp_variance_le_fintype`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DDDF
namespace L23

section copy

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- the independent-copy identity `E (G(X') − G(X))² = 2 Var G(X)` -/
lemma integral_prod_sub_sq {G : α → ℝ} (hG : MemLp G 2 μ) :
    Integrable (fun z : α × α => (G z.2 - G z.1) ^ 2) (μ.prod μ) ∧
      ∫ z, (G z.2 - G z.1) ^ 2 ∂(μ.prod μ) = 2 * Var[G; μ] := by
  set m := ∫ x, G x ∂μ
  have hc : MemLp (fun x => G x - m) 2 μ := hG.sub (memLp_const m)
  have h2 : Integrable (fun x => (G x - m) ^ 2) μ := hc.integrable_sq
  have h1 : Integrable (fun x => G x - m) μ := hc.integrable one_le_two
  have e : (fun z : α × α => (G z.2 - G z.1) ^ 2) = fun z =>
      ((G z.2 - m) ^ 2 + (G z.1 - m) ^ 2) - 2 * ((G z.1 - m) * (G z.2 - m)) := by
    funext z; ring
  have i1 : Integrable (fun z : α × α => (G z.2 - m) ^ 2) (μ.prod μ) := h2.comp_snd μ
  have i2 : Integrable (fun z : α × α => (G z.1 - m) ^ 2) (μ.prod μ) := h2.comp_fst μ
  have i3 : Integrable (fun z : α × α => (G z.1 - m) * (G z.2 - m)) (μ.prod μ) :=
    h1.mul_prod h1
  have i12 : Integrable (fun z : α × α => (G z.2 - m) ^ 2 + (G z.1 - m) ^ 2) (μ.prod μ) :=
    i1.add i2
  have i3' : Integrable (fun z : α × α => 2 * ((G z.1 - m) * (G z.2 - m))) (μ.prod μ) :=
    i3.const_mul 2
  rw [e]
  refine ⟨i12.sub i3', ?_⟩
  rw [integral_sub i12 i3', integral_add i1 i2, integral_const_mul,
    integral_fun_snd (f := fun x => (G x - m) ^ 2), integral_fun_fst (f := fun x => (G x - m) ^ 2),
    integral_prod_mul (f := fun x => G x - m) (g := fun x => G x - m)]
  have hm0 : ∫ x, (G x - m) ∂μ = 0 := by
    rw [integral_sub (hG.integrable one_le_two) (integrable_const m)]; simp [m]
  rw [hm0, variance_eq_integral hG.aestronglyMeasurable.aemeasurable]
  simp only [probReal_univ, one_smul, mul_zero, sub_zero]
  ring

end copy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **DDDF (5.59), finite-dimensional form**: `E (g(A', B) − g(A, B))² ≤ 2 K² s`. -/
theorem lintegral_sq_sub_copy_le {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {A A' : Ω → ι → ℝ} {B : Ω → ι' → ℝ} (hA : HasGaussianLaw A P)
    (h0 : ∀ i, ∫ ω, A ω i ∂P = 0) {s : ℝ} (hs : 0 ≤ s)
    (hvar : ∀ i, Var[fun ω => A ω i; P] ≤ s) (hAm : Measurable A) (hA'm : Measurable A')
    (hBm : Measurable B) (hid : IdentDistrib A A' P P) (hind1 : IndepFun A A' P)
    (hind2 : IndepFun (fun ω => (A ω, A' ω)) B P) {g : (ι → ℝ) → (ι' → ℝ) → ℝ}
    (hgc : Continuous (Function.uncurry g)) {K : ℝ≥0} (hg : ∀ b, LipschitzWith K fun a => g a b) :
    ∫⁻ ω, ENNReal.ofReal ((g (A' ω) (B ω) - g (A ω) (B ω)) ^ 2) ∂P ≤
      ENNReal.ofReal (2 * (K ^ 2 * s)) := by
  set μ := P.map A
  set ν := P.map B
  have hμ' : P.map A' = μ := hid.map_eq.symm
  have hAA' : P.map (fun ω => (A ω, A' ω)) = μ.prod μ := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hAm.aemeasurable hA'm.aemeasurable).1 hind1, hμ']
  have hlaw : P.map (fun ω => ((A ω, A' ω), B ω)) = (μ.prod μ).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hAm.prodMk hA'm).aemeasurable
      hBm.aemeasurable).1 hind2, hAA']
  set F : ((ι → ℝ) × (ι → ℝ)) × (ι' → ℝ) → ℝ≥0∞ :=
    fun w => ENNReal.ofReal ((g w.1.2 w.2 - g w.1.1 w.2) ^ 2)
  have hc2 : Continuous fun w : ((ι → ℝ) × (ι → ℝ)) × (ι' → ℝ) => g w.1.2 w.2 :=
    hgc.comp (by fun_prop : Continuous fun w : ((ι → ℝ) × (ι → ℝ)) × (ι' → ℝ) => (w.1.2, w.2))
  have hc1 : Continuous fun w : ((ι → ℝ) × (ι → ℝ)) × (ι' → ℝ) => g w.1.1 w.2 :=
    hgc.comp (by fun_prop : Continuous fun w : ((ι → ℝ) × (ι → ℝ)) × (ι' → ℝ) => (w.1.1, w.2))
  have hF : Measurable F :=
    (ENNReal.continuous_ofReal.comp ((hc2.sub hc1).pow 2)).measurable
  -- conditionally on `B = b`
  have inner : ∀ b, ∫⁻ z, F (z, b) ∂(μ.prod μ) ≤ ENNReal.ofReal (2 * (K ^ 2 * s)) := by
    intro b
    set G : (ι → ℝ) → ℝ := fun a => g a b
    have hGc : Continuous G := hgc.comp (by fun_prop : Continuous fun a : ι → ℝ => (a, b))
    obtain ⟨hL2, hV⟩ := memLp_variance_le_fintype hA h0 hs hvar (hg b)
    have hGm : AEStronglyMeasurable G μ := hGc.aestronglyMeasurable
    have hL2μ : MemLp G 2 μ := (memLp_map_measure_iff hGm hAm.aemeasurable).2 hL2
    have hVμ : Var[G; μ] ≤ (K : ℝ) ^ 2 * s := by
      rw [variance_map hGc.aemeasurable hAm.aemeasurable]; exact hV
    obtain ⟨hint, hval⟩ := integral_prod_sub_sq hL2μ
    calc ∫⁻ z, F (z, b) ∂(μ.prod μ)
        = ENNReal.ofReal (∫ z, (G z.2 - G z.1) ^ 2 ∂(μ.prod μ)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (2 * (K ^ 2 * s)) := by
          rw [hval]; exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ∫⁻ ω, ENNReal.ofReal ((g (A' ω) (B ω) - g (A ω) (B ω)) ^ 2) ∂P
      = ∫⁻ ω, F ((A ω, A' ω), B ω) ∂P := rfl
    _ = ∫⁻ w, F w ∂(P.map fun ω => ((A ω, A' ω), B ω)) :=
        (lintegral_map hF ((hAm.prodMk hA'm).prodMk hBm)).symm
    _ = ∫⁻ b, ∫⁻ z, F (z, b) ∂(μ.prod μ) ∂ν := by
        rw [hlaw, lintegral_prod_symm _ hF.aemeasurable]
    _ ≤ ∫⁻ _, ENNReal.ofReal (2 * (K ^ 2 * s)) ∂ν := lintegral_mono inner
    _ = ENNReal.ofReal (2 * (K ^ 2 * s)) := by simp

end L23
end DDDF
end LQGMetric
