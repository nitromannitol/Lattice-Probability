/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3F
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# GM Lemma 4.20, the `E`-piece (D81b, packet B3)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.20 (l. 2349–2351: "`E_r(z)`
is determined by `h|_{B_{λ₄r}(z)}` … contained in `𝓑^•_{s_{k+1}}`"), Thm 4.2 (2) (l. 1559:
`E_r(z) ∈ σ((h − h_{λ₅r}(z))|_{A_{λ₁r,λ₄r}(z)})`). Decision `decisions/DEC-81.md` (D81b): the
circle average `h_{λ₅r}(z)` is a function of `h` near `∂B_{λ₅r}(z)`, so `E_r(z)` is determined by
`h|_W` for the open `W = B_{λ₅r + λ₄ε𝕣}(z) ⊆ B_{(2λ₄+λ₅)ε𝕣}(z) ⊆ 𝓑^•_{s_{k+1}}` on `F_k`.

* `gm_fieldSigma_circleAvg_le`: `σ((h − h_ρ(z))|_A) ≤ σ(h|_W)` for open `W ⊇ A ∪ ∂B_ρ(z)`
  (`measurable_circleAvg_fieldSigma`, `fieldSigma_mono`; the pairing computation as
  `DFGPS.L219.measurable_restrictTo_addConst`);
* `gm_E_piece_Fk`: `{(z,r) ∈ 𝒵_k} ∩ {h ∈ E_r(z)} ∩ F_k` is a.s. an event of `𝓕_{k+1}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

/-- **the normalised field is local** (D81b): for open `A ⊆ W` with `∂B_ρ(z) ⊆ W`,
`σ((h − h_ρ(z))|_A) ≤ σ(h|_W)` -/
theorem gm_fieldSigma_circleAvg_le {Ω : Type} (h : Ω → DistC) {A W : TopologicalSpace.Opens ℂ}
    {ρ : ℝ} {z : ℂ} (hAW : A ≤ W) (hsph : sphere z |ρ| ⊆ W) :
    fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) ρ z)) A ≤ fieldSigma h W := by
  letI : MeasurableSpace Ω := fieldSigma h W
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_sphere z |ρ|).exists_thickening_subset_open W.isOpen hsph
  have hc : Measurable fun ω => circleAvg (h ω) ρ z :=
    (measurable_circleAvg_fieldSigma h ρ z hδ).mono
      (fieldSigma_mono h (V := nbhdO δ (sphere z |ρ|)) (W := W) hδW) le_rfl
  have hA : Measurable fun ω => restrictTo A (h ω) :=
    (comap_measurable (fun ω => restrictTo A (h ω))).mono (fieldSigma_mono h hAW) le_rfl
  have hm : Measurable fun ω => restrictTo A (addConst (h ω) (-circleAvg (h ω) ρ z)) := by
    refine measurable_distOn_iff.2 fun φ => ?_
    have e : ∀ ω, restrictTo A (addConst (h ω) (-circleAvg (h ω) ρ z)) φ = restrictTo A (h ω) φ +
        (∫ y, (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := A) (Ω₂ := ⊤) φ) y) *
          (-circleAvg (h ω) ρ z) :=
      fun ω => GFFInv.addConst_apply _ _ _
    simp_rw [e]
    exact ((measurable_distOn_apply φ).comp hA).add (hc.neg.const_mul _)
  exact hm.comap_le

variable {γ : ℝ} {D : DistC → ContMetric} {c' : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **the `E`-piece of GM Lemma 4.20** (l. 2349–2351, with D81b): if `E_r(z)` is a.s. in
`σ((h − h_{λ₅r}(z))|_{A_{λ₁r,λ₄r}(z)})` (Thm 4.2 (2)) and `0 ≤ r ≤ ε𝕣`, then
`{(z,r) ∈ 𝒵_k} ∩ {h ∈ E_r(z)} ∩ F_k` is a.s. an event of `𝓕_{k+1}` -/
theorem gm_E_piece_Fk [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c') (hh : IsWholePlaneGFF h P) (R : RegPar) (𝕫 𝕨 : ℂ)
    (η : Ω → C(unitInterval, ℂ)) {𝕣 ε β : ℝ} {k : ℕ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε)
    (h𝕣 : 0 < 𝕣) (hlam : 0 < R.lam 3) (hlam5 : 0 ≤ R.lam 4) (z : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hre : r ≤ ε * 𝕣) {Es : Set DistC}
    (hE : AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (R.lam 4 * r) z))
      (annulus z (R.lam 0 * r) (R.lam 3 * r))) (h ⁻¹' Es)) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1))
      ({ω | (z, r) ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0)
          (R.lam 3) ε R.ν 𝕣 (p4Rads R 𝕣 ε)} ∩ h ⁻¹' Es ∩ gmFk D h R 𝕫 𝕨 𝕣 ε β k) := by
  have he : 0 < ε * 𝕣 := mul_pos hε h𝕣
  have ha : 0 < R.lam 3 * ε * 𝕣 := by rw [mul_assoc]; positivity
  set V := ball z (R.lam 4 * r + R.lam 3 * (ε * 𝕣)) with hVdef
  have hAW : annulus z (R.lam 0 * r) (R.lam 3 * r) ≤ toOpens V isOpen_ball := by
    intro w hw
    have hw2 : ‖w - z‖ < R.lam 3 * r := hw.2
    show dist w z < _
    rw [dist_eq_norm]
    have : R.lam 3 * r ≤ R.lam 3 * (ε * 𝕣) := mul_le_mul_of_nonneg_left hre hlam.le
    have : 0 ≤ R.lam 4 * r := mul_nonneg hlam5 hr
    linarith
  have hsph : sphere z |R.lam 4 * r| ⊆ toOpens V isOpen_ball := by
    intro w hw
    show dist w z < _
    rw [mem_sphere.1 hw, abs_of_nonneg (mul_nonneg hlam5 hr)]
    have : 0 < R.lam 3 * (ε * 𝕣) := mul_pos hlam he
    linarith
  obtain ⟨F, hF, hEF⟩ := hE
  have hF' := gm_fieldSigma_circleAvg_le h hAW hsph _ hF
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have hloc := gm_aeEventIn_localSigma_of_field h
    (A := fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω))
    (fun ω => gm_filledBall_isClosed _ _ _)
    (by filter_upwards [hlen] with ω hω; exact gm_filledBall_isBounded_of_lenSet hω 𝕫 _)
    isOpen_ball hF'
  obtain ⟨G₁, hG₁, hEG₁⟩ := hloc
  have hloc' : AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1))
      ({ω | V ⊆ filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1) ω)} ∩ F) :=
    ⟨G₁, (le_sup_left : gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1)) ≤ _) _ hG₁, hEG₁⟩
  have hCd := gm_cand_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε ha k z r (β := β)
  have hFk := gm_gmFk_aeEventIn h38 hγ hγ2 hD hh R 𝕫 𝕨 η hℓ𝕣 hε ha k (β := β)
  obtain ⟨G, hG, hEG⟩ := gm_aeEventIn_inter (gm_aeEventIn_inter hCd hloc') hFk
  refine ⟨G, hG, EventuallyEq.trans ?_ hEG⟩
  filter_upwards [hEF] with ω hω
  have hiff := Iff.of_eq hω
  apply propext
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
  constructor
  · rintro ⟨⟨hc, hes⟩, hf⟩
    refine ⟨⟨hc, ?_, hiff.1 hes⟩, hf⟩
    have hrad : R.lam 4 * r + R.lam 3 * (ε * 𝕣) ≤ (2 * R.lam 3 + R.lam 4) * (ε * 𝕣) := by
      have : R.lam 4 * r ≤ R.lam 4 * (ε * 𝕣) := mul_le_mul_of_nonneg_left hre hlam5
      have : 0 ≤ R.lam 3 * (ε * 𝕣) := (mul_pos hlam he).le
      nlinarith
    exact (ball_subset_ball hrad).trans ((gm_gmF0C_ball hf.1.1 hc).trans
      (gm_filledBall_mono _ _ (gm_s4S_le_s4T hε (k + 1) ω)))
  · rintro ⟨⟨hc, -, hf'⟩, hf⟩
    exact ⟨⟨hc, hiff.2 hf'⟩, hf⟩

end LQGMetric.GM
