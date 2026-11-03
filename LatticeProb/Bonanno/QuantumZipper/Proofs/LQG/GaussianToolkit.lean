/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.GaussianToolkit at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.KernelIdentities
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# M4-R2: Gaussian toolkit for the normalized free field

All quantities used are differences `X(fc(a,r)) − X(fc(b,ρ))` of folded-circle pairings
(`fcPairVal`), which are balanced pairs; in particular `Z(fc(a,r)) = fcPairVal X (a,r,0,R)` for
`Z = addConst X (−X(fc(0,R)))` (`addConst_fc_eq_fcPairVal`).

* (a) `isGaussianProcess_fcPair`, `integral_fcPairVal`, `covariance_fcPairVal`;
  for `Z`: `isGaussianProcess_Z`, `integral_Z_fc`, `covariance_Z_fc` (covariance `K + 2 log R`).
* (b) `indepFun_fcPair`: zero cross-covariances imply independence.
* (c) `fcPairCov_incr_Zsame`, `fcPairCov_incr_Zfar`, `fcPairCov_incr_incr_far`,
  `indepFun_incr_bullet1`; `fcPairCov_band_Z`, `fcPairCov_band_band`, `indepFun_band`;
  `fcPairCov_inner_Z`, `fcPairCov_inner_inner`, `indepFun_inner`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Real ComplexConjugate

namespace QuantumZipper

namespace GaussTK

/-- Index `(a, r, b, ρ)` of the folded-circle pair `(fc(a,r), fc(b,ρ))`. -/
abbrev FcIdx := ℂ × ℝ × ℂ × ℝ

/-- Admissible index: centres in `Hbar`, positive radii. -/
def FcIdx.Good (p : FcIdx) : Prop := p.1 ∈ Hbar ∧ 0 < p.2.1 ∧ p.2.2.1 ∈ Hbar ∧ 0 < p.2.2.2

/-- The pair difference `X(fc(a,r)) − X(fc(b,ρ))`. -/
def fcPairVal {Ω : Type*} (X : Ω → FieldSample) (p : FcIdx) (ω : Ω) : ℝ :=
  X ω (foldedCircle p.1 p.2.1) - X ω (foldedCircle p.2.2.1 p.2.2.2)

/-- The covariance `kernelCov2 neumannH` of two folded-circle pairs. -/
def fcPairCov (p q : FcIdx) : ℝ :=
  kernelCov2 neumannH (foldedCircle p.1 p.2.1, foldedCircle p.2.2.1 p.2.2.2)
    (foldedCircle q.1 q.2.1, foldedCircle q.2.2.1 q.2.2.2)

theorem ofReal_mem_Hbar (t : ℝ) : (t : ℂ) ∈ Hbar := by simp [Hbar]

theorem zero_mem_Hbar : (0 : ℂ) ∈ Hbar := by simp [Hbar]

/-- Real-centred index is good. -/
theorem good_real {s r t ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    FcIdx.Good ((s : ℂ), r, (t : ℂ), ρ) :=
  ⟨ofReal_mem_Hbar s, hr, ofReal_mem_Hbar t, hρ⟩

/-- `Z`-index `(a, r, 0, R)` is good. -/
theorem good_Z {a : ℂ} {r R : ℝ} (ha : a ∈ Hbar) (hr : 0 < r) (hR : 0 < R) :
    FcIdx.Good (a, r, 0, R) :=
  ⟨ha, hr, zero_mem_Hbar, hR⟩

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The balanced admissible pair attached to a good index. -/
def toPair (p : {p : FcIdx // p.Good}) : {q : Measure ℂ × Measure ℂ //
    IsAdmissibleH q.1 ∧ IsAdmissibleH q.2 ∧ q.1 Set.univ = q.2 Set.univ} :=
  ⟨(foldedCircle p.1.1 p.1.2.1, foldedCircle p.1.2.2.1 p.1.2.2.2),
    isAdmissibleH_foldedCircle p.2.1 p.2.2.1, isAdmissibleH_foldedCircle p.2.2.2.1 p.2.2.2.2,
    by simp [measure_univ]⟩

/-- (a) Folded-circle pair differences form a Gaussian process. -/
theorem isGaussianProcess_fcPair (hX : IsFreeGFFModConstH X P) :
    IsGaussianProcess (fun (p : {p : FcIdx // p.Good}) (ω : Ω) => fcPairVal X p.1 ω) P :=
  hX.gaussian.comp_right toPair

theorem measurable_fcPairVal (hX : IsFreeGFFModConstH X P) (p : FcIdx) :
    Measurable (fcPairVal X p) :=
  (hX.measurable_coord _).sub (hX.measurable_coord _)

theorem integral_fcPairVal (hX : IsFreeGFFModConstH X P) {p : FcIdx} (hp : p.Good) :
    ∫ ω, fcPairVal X p ω ∂P = 0 :=
  hX.centered _ _ (isAdmissibleH_foldedCircle hp.1 hp.2.1)
    (isAdmissibleH_foldedCircle hp.2.2.1 hp.2.2.2) (by simp [measure_univ])

theorem covariance_fcPairVal (hX : IsFreeGFFModConstH X P) {p q : FcIdx} (hp : p.Good)
    (hq : q.Good) : cov[fcPairVal X p, fcPairVal X q; P] = fcPairCov p q :=
  hX.covariance_eq (foldedCircle p.1 p.2.1, foldedCircle p.2.2.1 p.2.2.2)
    (foldedCircle q.1 q.2.1, foldedCircle q.2.2.1 q.2.2.2) (isAdmissibleH_foldedCircle hp.1 hp.2.1)
    (isAdmissibleH_foldedCircle hp.2.2.1 hp.2.2.2) (by simp [measure_univ])
    (isAdmissibleH_foldedCircle hq.1 hq.2.1)
    (isAdmissibleH_foldedCircle hq.2.2.1 hq.2.2.2) (by simp [measure_univ])

/-- (b) Zero cross-covariances imply independence of two families of pair differences. -/
theorem indepFun_fcPair (hX : IsFreeGFFModConstH X P) {S T : Type*}
    (f : S → {p : FcIdx // p.Good}) (g : T → {p : FcIdx // p.Good})
    (h : ∀ s t, fcPairCov (f s).1 (g t).1 = 0) :
    IndepFun (fun ω s => fcPairVal X (f s).1 ω) (fun ω t => fcPairVal X (g t).1 ω) P := by
  have hG := (isGaussianProcess_fcPair hX).comp_right (Sum.elim f g)
  have hG' : IsGaussianProcess (Sum.elim (fun s => fcPairVal X (f s).1)
      (fun t => fcPairVal X (g t).1)) P := by
    have e : Sum.elim (fun s => fcPairVal X (f s).1) (fun t => fcPairVal X (g t).1) =
        (fun (p : {p : FcIdx // p.Good}) (ω : Ω) => fcPairVal X p.1 ω) ∘ Sum.elim f g := by
      funext i; cases i <;> rfl
    rw [e]; exact hG
  exact hG'.indepFun_of_covariance_eq_zero
    (fun s => (measurable_fcPairVal hX _).aemeasurable)
    (fun t => (measurable_fcPairVal hX _).aemeasurable)
    (fun s t => by rw [covariance_fcPairVal hX (f s).2 (g t).2]; exact h s t)

/-! ### The normalized field `Z = addConst X (−X(fc(0,R)))` -/

theorem addConst_fc_eq_fcPairVal (R : ℝ) (a : ℂ) (r : ℝ) (ω : Ω) :
    addConst (X ω) (-X ω (foldedCircle 0 R)) (foldedCircle a r) = fcPairVal X (a, r, 0, R) ω := by
  simp only [addConst, fcPairVal, measure_univ, ENNReal.toReal_one, mul_one]
  ring

end Prob

/-- (a) Covariance of `Z` inside `B(0,R)`, at the level of kernels. -/
theorem fcPairCov_Z {a b : ℂ} {r ρ R : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (har : ‖a‖ + r ≤ R)
    (hbρ : ‖b‖ + ρ ≤ R) :
    fcPairCov (a, r, 0, R) (b, ρ, 0, R) =
      kernelCov neumannH (foldedCircle a r) (foldedCircle b ρ) + 2 * Real.log R := by
  have hR : 0 < R := by linarith [norm_nonneg a]
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_bigCircle_right hr har, kernelCov_fc_bigCircle_left hρ hbρ,
    kernelCov_fc_bigCircle_left hR (by simp)]
  ring

theorem covariance_Z_fc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {a b : ℂ} {r ρ R : ℝ} (ha : a ∈ Hbar) (hb : b ∈ Hbar)
    (hr : 0 < r) (hρ : 0 < ρ) (har : ‖a‖ + r ≤ R) (hbρ : ‖b‖ + ρ ≤ R) :
    cov[fun ω => addConst (X ω) (-X ω (foldedCircle 0 R)) (foldedCircle a r),
      fun ω => addConst (X ω) (-X ω (foldedCircle 0 R)) (foldedCircle b ρ); P] =
      kernelCov neumannH (foldedCircle a r) (foldedCircle b ρ) + 2 * Real.log R := by
  have hR : 0 < R := by linarith [norm_nonneg a]
  simp_rw [addConst_fc_eq_fcPairVal]
  rw [covariance_fcPairVal hX (good_Z ha hr hR) (good_Z hb hρ hR)]
  exact fcPairCov_Z hr hρ har hbρ

/-! ### (c) Consequences of R1 on the boundary -/

theorem norm_ofReal' (t : ℝ) : ‖(t : ℂ)‖ = |t| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `Δ_t = Z_ε(t) − Z_{ε'}(t)` is uncorrelated with `Z_{ε'}(t)`. -/
theorem fcPairCov_incr_Zsame {t ε ε' R : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hR : |t| + ε' ≤ R) :
    fcPairCov ((t : ℂ), ε, (t : ℂ), ε') ((t : ℂ), ε', 0, R) = 0 := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter hε hε', kernelCov_fc_real_sameCenter hε' hε',
    kernelCov_fc_bigCircle_right hε (by rw [norm_ofReal']; linarith),
    kernelCov_fc_bigCircle_right hε' (by rw [norm_ofReal']; linarith), max_eq_right hεε',
    max_self]
  ring

/-- `Δ_t` is uncorrelated with `Z_r(u)` when `|t − u| ≥ ε' + r`. -/
theorem fcPairCov_incr_Zfar {t u ε ε' r R : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') (hr : 0 < r)
    (hR : |t| + ε' ≤ R) (hu : |u| + r ≤ R) (htu : ε' + r ≤ |t - u|) :
    fcPairCov ((t : ℂ), ε, (t : ℂ), ε') ((u : ℂ), r, 0, R) = 0 := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_separated hε hr (by linarith),
    kernelCov_fc_real_separated hε' hr htu,
    kernelCov_fc_bigCircle_right hε (by rw [norm_ofReal']; linarith),
    kernelCov_fc_bigCircle_right hε' (by rw [norm_ofReal']; linarith)]
  ring

/-- `Δ_t` is uncorrelated with `Δ_u` when `|t − u| ≥ ε' + δ'`. -/
theorem fcPairCov_incr_incr_far {t u ε ε' δ δ' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ)
    (hδδ' : δ ≤ δ') (htu : ε' + δ' ≤ |t - u|) :
    fcPairCov ((t : ℂ), ε, (t : ℂ), ε') ((u : ℂ), δ, (u : ℂ), δ') = 0 := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_separated hε hδ (by linarith),
    kernelCov_fc_real_separated hε hδ' (by linarith),
    kernelCov_fc_real_separated hε' hδ (by linarith),
    kernelCov_fc_real_separated hε' hδ' htu]
  ring

/-- Band increments `Z_{aε}(t) − Z_{2ε}(t)` are uncorrelated with `Z_{2ε}(t)`. -/
theorem fcPairCov_band_Z {t ε a R : ℝ} (hε : 0 < ε) (ha : 0 < a) (ha2 : a ≤ 2)
    (hR : |t| + 2 * ε ≤ R) :
    fcPairCov ((t : ℂ), a * ε, (t : ℂ), 2 * ε) ((t : ℂ), 2 * ε, 0, R) = 0 :=
  fcPairCov_incr_Zsame (mul_pos ha hε) (mul_le_mul_of_nonneg_right ha2 hε.le) hR

/-- Covariance of band increments: `2 log (2 / max a b)`, independent of `(ε, t)`. -/
theorem fcPairCov_band_band {t ε a b : ℝ} (hε : 0 < ε) (ha : 0 < a) (ha2 : a ≤ 2) (hb : 0 < b)
    (hb2 : b ≤ 2) :
    fcPairCov ((t : ℂ), a * ε, (t : ℂ), 2 * ε) ((t : ℂ), b * ε, (t : ℂ), 2 * ε) =
      2 * Real.log (2 / max a b) := by
  have h2 : (0 : ℝ) < 2 * ε := by positivity
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter (mul_pos ha hε) (mul_pos hb hε),
    kernelCov_fc_real_sameCenter (mul_pos ha hε) h2,
    kernelCov_fc_real_sameCenter h2 (mul_pos hb hε), kernelCov_fc_real_sameCenter h2 h2, max_self,
    max_eq_right (mul_le_mul_of_nonneg_right ha2 hε.le),
    max_eq_left (mul_le_mul_of_nonneg_right hb2 hε.le), ← max_mul_of_nonneg _ _ hε.le,
    Real.log_mul (lt_of_lt_of_le ha (le_max_left a b)).ne' hε.ne',
    Real.log_mul (by norm_num) hε.ne',
    Real.log_div (by norm_num) (lt_of_lt_of_le ha (le_max_left a b)).ne']
  ring

/-- The inner field index `(t + δu, δr ; t, δ)`. -/
def innerIdx (t δ u r : ℝ) : FcIdx := (((t + δ * u : ℝ) : ℂ), δ * r, (t : ℂ), δ)

/-- Inner-field increments are uncorrelated with `Z_δ(t)`. -/
theorem fcPairCov_inner_Z {t δ u r R : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hur : |u| + r ≤ 1)
    (hR : |t| + δ ≤ R) :
    fcPairCov (innerIdx t δ u r) ((t : ℂ), δ, 0, R) = 0 := by
  have hδr : 0 < δ * r := mul_pos hδ hr
  have hin : |t + δ * u - t| + δ * r ≤ δ := by
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hδ]
    nlinarith
  have hin' : ‖(((t + δ * u : ℝ)) : ℂ)‖ + δ * r ≤ R := by
    rw [norm_ofReal']
    have := abs_add_le t (δ * u)
    rw [abs_mul, abs_of_pos hδ] at this
    nlinarith
  simp only [fcPairCov, kernelCov2, innerIdx]
  rw [kernelCov_fc_real_nested' hδr hin, kernelCov_fc_real_sameCenter hδ hδ, max_self,
    kernelCov_fc_bigCircle_right hδr hin',
    kernelCov_fc_bigCircle_right hδ (by rw [norm_ofReal']; linarith)]
  ring

section Indep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- (c), first bullet: `Δ_t` is independent of `(Z_{ε'}(t), Z_r(u), Δ_u)`. -/
theorem indepFun_incr_bullet1 (hX : IsFreeGFFModConstH X P) {t u ε ε' r δ δ' R : ℝ}
    (hε : 0 < ε) (hεε' : ε ≤ ε') (hr : 0 < r) (hδ : 0 < δ) (hδδ' : δ ≤ δ')
    (hR : |t| + ε' ≤ R) (hu : |u| + r ≤ R) (htu : ε' + max r δ' ≤ |t - u|) :
    IndepFun (fun ω (_ : Unit) => fcPairVal X ((t : ℂ), ε, (t : ℂ), ε') ω)
      (fun ω (i : Fin 3) => fcPairVal X
        (![((t : ℂ), ε', 0, R), ((u : ℂ), r, 0, R), ((u : ℂ), δ, (u : ℂ), δ')] i) ω) P := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  have hR0 : 0 < R := by linarith [abs_nonneg t]
  have hg : ∀ i : Fin 3, FcIdx.Good
      (![((t : ℂ), ε', 0, R), ((u : ℂ), r, 0, R), ((u : ℂ), δ, (u : ℂ), δ')] i) := by
    intro i
    fin_cases i
    · exact good_Z (ofReal_mem_Hbar t) hε' hR0
    · exact good_Z (ofReal_mem_Hbar u) hr hR0
    · exact good_real hδ (hδ.trans_le hδδ')
  refine indepFun_fcPair hX (fun _ => ⟨_, good_real hε hε'⟩) (fun i => ⟨_, hg i⟩) ?_
  intro _ i
  fin_cases i
  · exact fcPairCov_incr_Zsame hε hεε' hR
  · exact fcPairCov_incr_Zfar hε hεε' hr hR hu (by linarith [le_max_left r δ'])
  · exact fcPairCov_incr_incr_far hε hεε' hδ hδδ' (by linarith [le_max_right r δ'])

/-- (c), second bullet: the band process `a ↦ Z_{aε}(t) − Z_{2ε}(t)`, `a ∈ [1,2]`, is
independent of `Z_{2ε}(t)`. -/
theorem indepFun_band (hX : IsFreeGFFModConstH X P) {t ε R : ℝ} (hε : 0 < ε)
    (hR : |t| + 2 * ε ≤ R) :
    IndepFun (fun ω (a : Set.Icc (1 : ℝ) 2) =>
        fcPairVal X ((t : ℂ), a.1 * ε, (t : ℂ), 2 * ε) ω)
      (fun ω (_ : Unit) => fcPairVal X ((t : ℂ), 2 * ε, 0, R) ω) P := by
  have hR0 : 0 < R := by linarith [abs_nonneg t]
  refine indepFun_fcPair hX
    (fun a => ⟨_, good_real (mul_pos (by linarith [a.2.1]) hε) (by positivity : (0:ℝ) < 2 * ε)⟩)
    (fun _ => ⟨_, good_Z (ofReal_mem_Hbar t) (by positivity) hR0⟩) ?_
  intro a _
  exact fcPairCov_band_Z hε (by linarith [a.2.1]) a.2.2 hR

/-- (c), third bullet: the inner field `(u, r) ↦ Z(fc(t+δu, δr)) − Z_δ(t)`, `|u| + r ≤ 1`,
is independent of `Z_δ(t)`. -/
theorem indepFun_inner (hX : IsFreeGFFModConstH X P) {t δ R : ℝ} (hδ : 0 < δ)
    (hR : |t| + δ ≤ R) :
    IndepFun (fun ω (q : {q : ℝ × ℝ // 0 < q.2 ∧ |q.1| + q.2 ≤ 1}) =>
        fcPairVal X (innerIdx t δ q.1.1 q.1.2) ω)
      (fun ω (_ : Unit) => fcPairVal X ((t : ℂ), δ, 0, R) ω) P := by
  have hR0 : 0 < R := by linarith [abs_nonneg t]
  refine indepFun_fcPair hX
    (fun q => ⟨_, good_real (mul_pos hδ q.2.1) hδ⟩)
    (fun _ => ⟨_, good_Z (ofReal_mem_Hbar t) hδ hR0⟩) ?_
  intro q _
  exact fcPairCov_inner_Z hδ q.2.1 q.2.2 hR

end Indep

end GaussTK

end QuantumZipper
