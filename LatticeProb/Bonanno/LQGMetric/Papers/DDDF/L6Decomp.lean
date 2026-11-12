/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6Decomp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePushCoupling
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePhi
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne

/-!
# DDDF Lemma 6: the decomposition `φ̃_δ ∘ F − φ_δ = φ_L + φ_H` and the independence of `φ_H`

DDDF (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 545–556, proof Step 1
l. 561–575), after Dubédat–Falconet (arXiv:1809.02607, `LiouvilleMetricStarScale.tex`
l. 396–410). Under the coupling `W̃ = coupledNoise h W W'` (DDDF l. 541–543,
`LQGMetric.Field.WhiteNoisePushCoupling`),

  `φ̃_δ(F(x)) = √π [W(T k_{δ,F(x)}) + W'(k_{δ,F(x)} 1_{((0,∞)×V)ᶜ})]`,

where `k_{δ,z}` is the kernel of `φ_δ(z)` and `T` the pushforward operator. The kernel
`T k_{δ,F(x)}` lives on times `t ∈ [δ²|F'(y)|⁻², |F'(y)|⁻²]`; DDDF split it at `t = δ²`:

* `φ_H^{(δ)}(x) = √π W(T k_{δ,F(x)} 1_{t < δ²})` — DDDF's `−φ₃^{(δ)}` (l. 571–573), noise on times
  `[δ²|F'|⁻², δ²)`;
* `φ_L^{(δ)}(x) = √π [W(T k_{δ,F(x)} 1_{t ≥ δ²} − k_{δ,x}) + W'(k_{δ,F(x)} 1_{((0,∞)×V)ᶜ})]` —
  DDDF's `−(φ₁^{(δ)} + φ₂^{(δ)})` (l. 563–570).

Results: `l6_decomp_ae` (the identity (eq:Decompo), a.s. for each `x`) and `l6_indep`
("`φ_H^{(δ)}` is independent of `(φ_δ, φ_L^{(δ)})`", l. 553; DDDF l. 576: "`φ₃` is independent of
`φ_δ`, `φ₁`, `φ₂`"): `φ_H` uses only the noise `W` on times `< δ²`, while `φ_δ` and the `W`-part
of `φ_L` use only times `≥ δ²`, and `W'` is independent of `W`.

`indep_sup_of_indep` is copied from QuantumZipper (`Proofs/Zipper/UnzipInvariance.lean`,
`indep_sup_of_indep`) to avoid importing that heavy module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

/-- Independent join (QuantumZipper `indep_sup_of_indep`, copied): if `m₁, m₂ ≤ m_B` are
independent and `m_X` is independent of `m_B`, then `m₁ ⊔ m_X` is independent of `m₂`. -/
theorem indep_sup_of_indep {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m₁ m₂ mX mB : MeasurableSpace Ω} (h₁ : m₁ ≤ mB) (h₂ : m₂ ≤ mB)
    (hmB : mB ≤ mΩ) (hmX : mX ≤ mΩ) (h12 : Indep m₁ m₂ P) (hXB : Indep mX mB P) :
    Indep (m₁ ⊔ mX) m₂ P := by
  refine IndepSets.indep (sup_le (h₁.trans hmB) hmX) (h₂.trans hmB)
    (QuantumZipper.GermZeroOne.isPiSystem_rectSets m₁ mX)
    (@MeasurableSpace.isPiSystem_measurableSet Ω m₂)
    (QuantumZipper.GermZeroOne.sup_eq_generateFrom_rectSets m₁ mX)
    (@MeasurableSpace.generateFrom_measurableSet Ω m₂).symm ?_
  rw [IndepSets_iff]
  rintro _ D ⟨A, C, hA, hC, rfl⟩ hD
  have e1 : P (C ∩ (A ∩ D)) = P C * P (A ∩ D) :=
    (Indep_iff _ _ _).1 hXB C (A ∩ D) hC ((h₁ A hA).inter (h₂ D hD))
  have e2 : P (A ∩ D) = P A * P D := (Indep_iff _ _ _).1 h12 A D hA hD
  have e3 : P (C ∩ A) = P C * P A := (Indep_iff _ _ _).1 hXB C A hC (h₁ A hA)
  calc P (A ∩ C ∩ D) = P (C ∩ (A ∩ D)) := by
        congr 1; ext ω; simp only [mem_inter_iff]; tauto
    _ = P C * (P A * P D) := by rw [e1, e2]
    _ = P (A ∩ C) * P D := by rw [inter_comm A C, e3, mul_assoc]

/-- The times `t ≥ δ²` (space-time, time first). -/
def timeHigh (δ : ℝ) : Set (ℝ × ℂ) := Ici (δ ^ 2) ×ˢ univ

lemma measurableSet_timeHigh (δ : ℝ) : MeasurableSet (timeHigh δ) :=
  measurableSet_Ici.prod MeasurableSet.univ

lemma supportedIn_mono {A B : Set (ℝ × ℂ)} (hAB : A ⊆ B) {f : WNSpace} (hf : SupportedIn A f) :
    SupportedIn B f :=
  ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 hAB) hf

lemma supportedIn_cutL2 {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) (g : WNSpace) :
    SupportedIn A (cutL2 hA g) := by
  refine (ae_restrict_iff' hA.compl).2 ?_
  filter_upwards [coeFn_cutL2 hA g] with p hp hpA
  rw [hp, indicator_of_notMem hpA]

lemma supportedIn_sub {A : Set (ℝ × ℂ)} {f g : WNSpace} (hf : SupportedIn A f)
    (hg : SupportedIn A g) : SupportedIn A (f - g) := by
  filter_upwards [hf, hg, ae_restrict_of_ae (Lp.coeFn_sub f g)] with p h1 h2 h3
  rw [h3, Pi.sub_apply, h1, h2, sub_zero]

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- The kernel of `φ_H^{(δ)}(x)`: `T k_{δ,F(x)}` on times `t < δ²`. -/
def hKer (F : ℂ → ℂ) (U : Set ℂ) (δ : ℝ) (x : ℂ) : WNSpace :=
  cutL2 (measurableSet_timeHigh δ).compl (pushL2 F U (phiKernelL2 δ 1 (F x)))

/-- The `W`-kernel of `φ_L^{(δ)}(x)`: `T k_{δ,F(x)}` on times `t ≥ δ²`, minus `k_{δ,x}`. -/
def lKer (F : ℂ → ℂ) (U : Set ℂ) (δ : ℝ) (x : ℂ) : WNSpace :=
  cutL2 (measurableSet_timeHigh δ) (pushL2 F U (phiKernelL2 δ 1 (F x))) - phiKernelL2 δ 1 x

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `φ_H^{(δ)}(x) = √π W(T k_{δ,F(x)} 1_{t<δ²})` (DDDF's `−φ₃^{(δ)}`, l. 571–573). -/
def phiH (F : ℂ → ℂ) (U : Set ℂ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (x : ℂ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (hKer F U δ x) ω

/-- `φ_L^{(δ)}(x)` (DDDF's `−(φ₁^{(δ)} + φ₂^{(δ)})`, l. 563–570). -/
def phiL (h : ConfHyp F U) (W W' : WNSpace → Ω → ℝ) (δ : ℝ) (x : ℂ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * (W (lKer F U δ x) ω +
    W' (cutL2 h.measurableSet_pushTarget.compl (phiKernelL2 δ 1 (F x))) ω)

lemma cutL2_add_compl {A : Set (ℝ × ℂ)} (hA : MeasurableSet A) (g : WNSpace) :
    cutL2 hA g + cutL2 hA.compl g = g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (cutL2 hA g) (cutL2 hA.compl g), coeFn_cutL2 hA g,
    coeFn_cutL2 hA.compl g] with p h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  by_cases hp : p ∈ A <;> simp [hp]

/-- **DDDF Lemma 6, decomposition (eq:Decompo)**: under the coupling,
`φ̃_δ(F(x)) − φ_δ(x) = φ_L^{(δ)}(x) + φ_H^{(δ)}(x)` almost surely, for each `x`. -/
theorem l6_decomp_ae (h : ConfHyp F U) {W W' : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (δ : ℝ) (x : ℂ) :
    (fun ω => phi (coupledNoise h W W') δ 1 (F x) ω - phi W δ 1 x ω) =ᵐ[P]
      fun ω => phiL h W W' δ x ω + phiH F U W δ x ω := by
  have hA := measurableSet_timeHigh δ
  have e := (cutL2_add_compl hA (pushL2 F U (phiKernelL2 δ 1 (F x)))).symm
  have h1 := hW.add_ae (cutL2 hA (pushL2 F U (phiKernelL2 δ 1 (F x))))
    (cutL2 hA.compl (pushL2 F U (phiKernelL2 δ 1 (F x))))
  rw [← e] at h1
  have h2 := hW.add_ae (cutL2 hA (pushL2 F U (phiKernelL2 δ 1 (F x))))
    ((-1 : ℝ) • phiKernelL2 δ 1 x)
  have h3 := hW.smul_ae (-1) (phiKernelL2 δ 1 x)
  have hl : lKer F U δ x = cutL2 hA (pushL2 F U (phiKernelL2 δ 1 (F x))) +
      (-1 : ℝ) • phiKernelL2 δ 1 x := by
    rw [lKer, neg_one_smul, sub_eq_add_neg]
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  simp only [phi, coupledNoise, phiL, phiH, hKer]
  rw [hl, e2, e3, e1]
  ring

/-- **DDDF Lemma 6, independence** (l. 553, 576): the field `φ_H^{(δ)}` is independent of the
pair `(φ_δ, φ_L^{(δ)})`. -/
theorem l6_indep (h : ConfHyp F U) {W W' : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P W')
    (hind : IndepFun (fun ω f => W f ω) (fun ω f => W' f ω) P) {δ : ℝ} (hδ : 0 < δ) :
    IndepFun (fun ω x => phiH F U W δ x ω) (fun ω x => (phi W δ 1 x ω, phiL h W W' δ x ω)) P := by
  have := hW.isProbabilityMeasure
  have hA := measurableSet_timeHigh δ
  have hkA : ∀ x, SupportedIn (timeHigh δ) (phiKernelL2 δ 1 x) := fun x =>
    supportedIn_mono
      (fun p hp => mem_prod.2 ⟨mem_Ici.2 (mem_Icc.1 (mem_prod.1 hp).1).1, mem_univ _⟩)
      (supportedIn_phiKernelL2' hδ x)
  have hWm : Measurable (fun ω f => W f ω) := measurable_pi_iff.2 hW.measurable
  have hres : ∀ B : Set (ℝ × ℂ), Measurable (fun (y : WNSpace → ℝ) (f : {f // SupportedIn B f}) =>
      y f) := fun B => measurable_pi_iff.2 fun f => measurable_pi_apply _
  have h12 := (IndepFun_iff_Indep _ _ _).1
    (hW.indepFun_of_disjoint (A := timeHigh δ) (B := (timeHigh δ)ᶜ) disjoint_compl_right)
  have hJ := indep_sup_of_indep ((hres _).comp (comap_measurable (fun ω f => W f ω))).comap_le
    ((hres _).comp (comap_measurable (fun ω f => W f ω))).comap_le hWm.comap_le
    (measurable_pi_iff.2 fun f => hW'.measurable f).comap_le h12
    ((IndepFun_iff_Indep _ _ _).1 hind).symm
  rw [← MeasurableSpace.comap_prodMk] at hJ
  have hpair := ((IndepFun_iff_Indep _ _ _).2 hJ).symm
  refine hpair.comp
    (φ := fun (y : {f // SupportedIn (timeHigh δ)ᶜ f} → ℝ) x =>
      Real.sqrt Real.pi * y ⟨hKer F U δ x, supportedIn_cutL2 hA.compl _⟩)
    (ψ := fun (yz : ({f // SupportedIn (timeHigh δ) f} → ℝ) × (WNSpace → ℝ)) x =>
      (Real.sqrt Real.pi * yz.1 ⟨phiKernelL2 δ 1 x, hkA x⟩,
        Real.sqrt Real.pi * (yz.1 ⟨lKer F U δ x, supportedIn_sub (supportedIn_cutL2 hA _) (hkA x)⟩
          + yz.2 (cutL2 h.measurableSet_pushTarget.compl (phiKernelL2 δ 1 (F x))))))
    ?_ ?_
  · exact measurable_pi_iff.2 fun x => (measurable_pi_apply _).const_mul _
  · refine measurable_pi_iff.2 fun x => Measurable.prodMk ?_ ?_
    · exact ((measurable_pi_apply _).comp measurable_fst).const_mul _
    · refine Measurable.const_mul (Measurable.add ?_ ?_) _
      · exact (measurable_pi_apply _).comp measurable_fst
      · exact (measurable_pi_apply _).comp measurable_snd

end DDDF
end LQGMetric
