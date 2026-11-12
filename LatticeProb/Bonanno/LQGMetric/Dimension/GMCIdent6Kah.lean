/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent6Kah at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Exp

/-!
# One-sided Kahane comparison with a log-correlated reference family (P2-GMCID6, step (a))

For a centred Gaussian vector `X` indexed by the level-`j` dyadic cells whose covariance is
bounded **above** by `−β log max(2^{-j}, ‖cpt i − cpt k‖) + c₁`, and a `β`-log-correlated
reference family `Z` (`DGMC.LogCorr Z P₀ β c`), for `q ≤ 0` or `q ≥ 1`:

  `E (∑ᵢ 4^{-j} e^{Xᵢ − Var Xᵢ/2})^q ≤ e^{q(q−1)(c₁+c)/2} E gM_j(Z_j)^q`

(`kahane_logRef`). This is Kahane's inequality with an added constant covariance
(`Kahane.kahane_rpow_le_add_const`; Berestycki–Powell arXiv:2404.16642, `GMCproperties.tex`
l. 1211–1218, (encadrKahane)); only the upper covariance bound on `X` is used, since `y ↦ y^q` is
convex for `q ∉ (0,1)` and Kahane's inequality is monotone in the covariance (as in
`DZZ.negU_integral_gM_rpow_le`, which assumes two-sided bounds). The integrability of the
left-hand side (`integrable_sum_exp_rpow`) is the argument of `DGMC.integrable_oM_rpow`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent6

open DGMC

variable {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {P : Measure Ω}
  {P₀ : Measure Ω₀}

/-- moments `q ∉ (0,1)` of a finite lognormal sum are integrable -/
lemma integrable_sum_exp_rpow {ι : Type*} [Fintype ι] [Nonempty ι] [IsFiniteMeasure P]
    {X : Ω → ι → ℝ} (hXmeas : ∀ i, Measurable fun ω => X ω i)
    (hXint : ∀ i (t : ℝ), Integrable (fun ω => Real.exp (t * X ω i)) P)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) (v : ι → ℝ) {q : ℝ} (hq : q ≤ 0 ∨ 1 ≤ q) :
    Integrable (fun ω => (∑ i, p i * Real.exp (X ω i - v i)) ^ q) P := by
  have hmeas : Measurable fun ω => ∑ i, p i * Real.exp (X ω i - v i) :=
    Finset.measurable_sum _ fun i _ => ((hXmeas i).sub_const _).exp.const_mul _
  have ha : ∀ i, Integrable (fun ω => (p i * Real.exp (X ω i - v i)) ^ q) P := fun i => by
    have e : (fun ω => (p i * Real.exp (X ω i - v i)) ^ q) =
        fun ω => (p i ^ q * Real.exp (-(q * v i))) * Real.exp (q * X ω i) := by
      funext ω
      rw [Real.mul_rpow (hp i).le (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
      congr 2; ring
    rw [e]; exact (hXint i q).const_mul _
  have h0 : ∀ i ω, 0 ≤ p i * Real.exp (X ω i - v i) := fun i ω => by
    have := hp i; positivity
  rcases hq with hq | hq
  · obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    refine Integrable.mono' (ha i₀) (hmeas.pow_const q).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have hpos : 0 < p i₀ * Real.exp (X ω i₀ - v i₀) := mul_pos (hp i₀) (Real.exp_pos _)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => h0 i ω) _)]
    exact Real.rpow_le_rpow_of_nonpos hpos
      (Finset.single_le_sum (fun i _ => h0 i ω) (Finset.mem_univ i₀)) hq
  · refine Integrable.mono' ((integrable_finsetSum Finset.univ fun i _ => ha i).const_mul
      (((Finset.univ : Finset ι).card : ℝ) ^ (q - 1))) (hmeas.pow_const q).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => h0 i ω) _)]
    exact Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ hq fun i _ => h0 i ω

/-- **one-sided Kahane comparison with a log-correlated reference** -/
theorem kahane_logRef {j : ℕ} {X : Ω → ↥(grid j) → ℝ} (hX : HasGaussianLaw X P)
    (hXm : ∀ i, ∫ ω, X ω i ∂P = 0) (hXmeas : ∀ i, Measurable fun ω => X ω i)
    (hXint : ∀ i (t : ℝ), Integrable (fun ω => Real.exp (t * X ω i)) P)
    {β c₁ c : ℝ} (hc₁ : 0 ≤ c₁)
    (hcov : ∀ i k, cov[fun ω => X ω i, fun ω => X ω k; P] ≤
      -(β * Real.log (max ((2 : ℝ)⁻¹ ^ j) ‖cpt j i - cpt j k‖)) + c₁)
    {Z : ℕ → ℂ → Ω₀ → ℝ} (hZ : LogCorr Z P₀ β c) {q : ℝ} (hq : q ≤ 0 ∨ 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i, (4 : ℝ)⁻¹ ^ j *
        Real.exp (X ω i - Var[fun ω => X ω i; P] / 2)) ^ q) ∂P ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (c₁ + c) / 2) *
        ∫ ω, gM (Z j) P₀ j (grid j) ω ^ q ∂P₀) := by
  have hP := hX.isProbabilityMeasure
  have hne : Nonempty ↥(grid j) := DGMC.grid_nonempty j
  have h0 : (0 : ℂ) ∈ unitSq := by simp [unitSq]
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hZ.cov j 0 0 h0 h0)
  have hYv : HasGaussianLaw (fun ω (i : ↥(grid j)) => Z j (cpt j i) ω) P₀ :=
    hasGaussianLaw_fintype (hZ.gauss j) (fun i : ↥(grid j) => cpt j i)
  have hcov' : ∀ a b : ↥(grid j), cov[fun ω => X ω a, fun ω => X ω b; P] ≤
      cov[fun ω => Z j (cpt j a) ω, fun ω => Z j (cpt j b) ω; P₀] +
        ((⟨c₁ + c, by linarith⟩ : ℝ≥0) : ℝ) := by
    intro a b
    show _ ≤ _ + (c₁ + c)
    have h2 := abs_le.1 (hZ.cov j _ _ (cpt_mem_unitSq a.2) (cpt_mem_unitSq b.2))
    linarith [hcov a b, h2.1]
  have hKa := Kahane.kahane_rpow_le_add_const hq
    (p := fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) (fun _ => by positivity) hX hYv
    hXm (fun i => hZ.mean j _) _ hcov'
  have hY : (fun ω => (∑ i : ↥(grid j), (fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j) i *
      Real.exp ((fun ω (i : ↥(grid j)) => Z j (cpt j i) ω) ω i -
        Var[fun ω => (fun ω (i : ↥(grid j)) => Z j (cpt j i) ω) ω i; P₀] / 2)) ^ q) =
      fun ω => gM (Z j) P₀ j (grid j) ω ^ q := by
    funext ω
    rw [gM, ← Finset.sum_coe_sort (grid j)]
  rw [hY] at hKa
  have hint := integrable_sum_exp_rpow hXmeas hXint (p := fun _ : ↥(grid j) => (4 : ℝ)⁻¹ ^ j)
    (fun _ => by positivity) (fun i => Var[fun ω => X ω i; P] / 2) hq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω =>
    Real.rpow_nonneg (Finset.sum_nonneg fun i _ => by positivity) _)]
  exact ENNReal.ofReal_le_ofReal hKa

end GMCIdent6
end LQGMetric
