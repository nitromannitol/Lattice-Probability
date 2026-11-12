/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11Loc4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Loc3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3TrInv1
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Locality of `μ_{ĥ^tr}` (P2-DGLOC, part 4): the events `E_S` are local (DG:1268, 1302–1305)

DG, arXiv:1807.01072, DG:1268: "`E_S^ε` is a.s. determined by `ĥ^tr|_{S(1)}`" and DG:1302–1305
(the events are a.s. determined by the white noise on `(s-neighbourhood of S) × (0, s²]`).

* `measure_eq_iSup_limUnder_of_vague`: for a vague limit `ν` on `O` and an open bounded `B ⊆ O`,
  `ν(B) = sup_n lim_k ∫ φ_{B,n} dμ_k` (QZ's cut-offs `openBump`; as `S3TrInv3.muOfMod_eq_triMass`);
* `dgLGDRat_congr`: `D^ε(·,·;U)` only uses the masses of the rational balls in `Ū`;
* **`goodSq_muTr_loc`** (unit frame): for `sqOne ⊆ K`, the event `E = {goodSq (muTr W)}` is a.s.
  equal to an event of `σ(W|_{(0,1) × B_{1/10}(sqOne)})`: the ball masses in `sqOne` are a.s.
  limits of the local approximations `(2^{-k})^{γ²/2} e^{γ ĥ^tr_{2^{-k}}} dz` on `int sqOne`
  (DG:984, `ae_isVagueLimitOn_muOfMod_loc` with the local versions `exists_trCircVer_loc`);
* **`goodSq_muTr_loc_scaled`**: the same for `W' = W ∘ U_{s,c}` (`s = 2^{-j}`), with the region
  `(0, s²) × (s · B_{1/10}(U) + c)` of the original noise (`supportedIn_wnScale`).

Own elementary glue (DV-D105l-2 reading of "a.s. determined by").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent SupTail QuantumZipper

/-- ball masses of a vague limit through the cut-offs `openBump` -/
theorem measure_eq_iSup_limUnder_of_vague {O B : Set ℂ} {μk : ℕ → Measure ℂ} {ν : Measure ℂ}
    (hv : IsVagueLimitOn O μk ν) (hB : IsOpen B) (hBb : Bornology.IsBounded B) (hBO : B ⊆ O)
    (hBc : Bᶜ.Nonempty) :
    ν B = ⨆ n : ℕ, ENNReal.ofReal
      (limUnder atTop fun k => ∫ z, LQGMeas.openBump B n z ∂(μk k)) := by
  have hsupp : ∀ n, tsupport (LQGMeas.openBump B n) ⊆ O := fun n =>
    (LQGMeas.tsupport_openBump_subset B n).trans hBO
  have hlim : ∀ n, limUnder atTop (fun k => ∫ z, LQGMeas.openBump B n z ∂(μk k)) =
      ∫ z, LQGMeas.openBump B n z ∂ν := fun n =>
    (hv.2.2 _ (LQGMeas.continuous_openBump B n) (LQGMeas.hasCompactSupport_openBump hBb n)
      (hsupp n)).limUnder_eq
  have hint : ∀ n, Integrable (LQGMeas.openBump B n) ν := fun n =>
    GoodSample.integrable_of_tsupport hv.2.1 (LQGMeas.continuous_openBump B n)
      (LQGMeas.hasCompactSupport_openBump hBb n) (hsupp n)
  simp_rw [hlim, fun n => ofReal_integral_eq_lintegral_ofReal (hint n)
    (ae_of_all _ (LQGMeas.openBump_nonneg B n))]
  rw [← lintegral_iSup (fun n => (LQGMeas.continuous_openBump B n).measurable.ennreal_ofReal)
    (fun m n hmn z => ENNReal.ofReal_le_ofReal (LQGMeas.openBump_mono B z hmn))]
  simp_rw [LQGMeas.iSup_openBump hB hBc]
  rw [lintegral_indicator_one hB.measurableSet]

/-- `D^ε(z,w;U)` only depends on the masses of the rational balls in `Ū` -/
lemma dgLGDRat_congr {m m' : ℚ × ℚ → ℚ → ℝ≥0∞} {ε : ℝ} {U : Set ℂ}
    (h : ∀ (c : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt c) q ⊆ closure U → m c q = m' c q) (z w : ℂ) :
    dgLGDRat m ε U z w = dgLGDRat m' ε U z w := by
  have hA : ∀ N, dgRatAdm m ε U z w N ↔ dgRatAdm m' ε U z w N := by
    intro N
    unfold dgRatAdm
    constructor
    · rintro ⟨c, q, hP, hi⟩
      exact ⟨c, q, hP, fun i => ⟨(hi i).1, by rw [← h _ _ (hi i).1.1 (hi i).1.2]; exact (hi i).2⟩⟩
    · rintro ⟨c, q, hP, hi⟩
      exact ⟨c, q, hP, fun i => ⟨(hi i).1, by rw [h _ _ (hi i).1.1 (hi i).1.2]; exact (hi i).2⟩⟩
  unfold dgLGDRat
  simp_rw [hA]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **locality of `E_S` for `μ_{ĥ^tr}`, unit frame** (DG:1268): if `sqOne s₀ b₀ x₀ ⊆ K`, the event
`goodSq (muTr W) …` is a.s. equal to an event of the white noise on `(0,1) × B_{1/10}(sqOne)` -/
theorem goodSq_muTr_loc (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ}
    {b : ℝ} (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    {s₀ : ℝ} {b₀ : ℂ} {x₀ : ℤ × ℤ} (hsq : sqOne s₀ b₀ x₀ ⊆ ferniqueBox y b) (ε M : ℝ) :
    ∃ A', MeasurableSet[wnSigma W (trLocReg (sqOne s₀ b₀ x₀))] A' ∧
      {ω | goodSq (muTr hW γ hb hK ω) ε s₀ b₀ M x₀} =ᵐ[P] A' := by
  set Q := sqOne s₀ b₀ x₀
  set O := interior Q
  have hQc : IsCompact Q := isCompact_Icc.reProdIm isCompact_Icc
  have hOb : Bornology.IsBounded O := hQc.isBounded.subset interior_subset
  have hOK : O ⊆ ferniqueBox y b := interior_subset.trans hsq
  have hOS : O ⊆ openSquare := hOK.trans (ferniqueBox_subset hK)
  choose V hVm hV using fun k => exists_trCircVer_loc hW (P := P) hOb k
  have hσ : wnSigma W (trLocReg O) ≤ (wnSigma W (trLocReg Q)) :=
    wnSigma_mono (prod_mono subset_rfl (thickening_subset_of_subset _ interior_subset))
  have hVσ : ∀ k, Measurable[@Prod.instMeasurableSpace ℂ Ω _ (wnSigma W (trLocReg Q))] fun p : ℂ × Ω => V k p.1 p.2 :=
    fun k => (hVm k).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono hσ)) le_rfl
  have hVf : ∀ k, Measurable fun p : ℂ × Ω => V k p.1 p.2 := fun k =>
    (hVσ k).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (wnSigma_le hW _))) le_rfl
  have hvag := ae_isVagueLimitOn_muOfMod_loc hW hγ hγ2 (isCompact_ferniqueBox y b)
    (ferniqueBox_subset hK) isOpen_interior hOK (trMod_spec hW hb hK) hVf hV
  -- the local functional of the rational ball masses
  set dens : ℕ → ℂ → Ω → ℝ := fun k z ω =>
    ((2 : ℝ)⁻¹ ^ k) ^ (γ ^ 2 / 2) * Real.exp (γ * V k z ω)
  set I : ℚ × ℚ → ℚ → ℕ → ℕ → Ω → ℝ := fun c q n k ω =>
    ∫ z, dens k z ω * LQGMeas.openBump (ball (ratPt c) q) n z ∂(volume.restrict O)
  classical
  set m' : Ω → ℚ × ℚ → ℚ → ℝ≥0∞ := fun ω c q =>
    if 0 < q ∧ ball (ratPt c) q ⊆ closure Q then
      ⨆ n : ℕ, ENNReal.ofReal (limUnder atTop fun k => I c q n k ω) else 0
  have hIm : ∀ c q n k, Measurable[(wnSigma W (trLocReg Q))] (I c q n k) := by
    intro c q n k
    let _ : MeasurableSpace Ω := (wnSigma W (trLocReg Q))
    have h : StronglyMeasurable (Function.uncurry fun z ω =>
        dens k z ω * LQGMeas.openBump (ball (ratPt c) q) n z) :=
      (((Real.measurable_exp.comp ((hVσ k).const_mul γ)).const_mul _).mul
        ((LQGMeas.continuous_openBump _ n).measurable.comp measurable_fst)).stronglyMeasurable
    exact (h.integral_prod_left (μ := volume.restrict O)).measurable
  have hm' : Measurable[(wnSigma W (trLocReg Q))] m' := by
    let _ : MeasurableSpace Ω := (wnSigma W (trLocReg Q))
    refine measurable_pi_iff.2 fun c => measurable_pi_iff.2 fun q => ?_
    by_cases hcq : 0 < q ∧ ball (ratPt c) q ⊆ closure Q
    · simp only [m', hcq, and_self, ite_true]
      exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
        (StronglyMeasurable.limUnder fun k => (hIm c q n k).stronglyMeasurable).measurable
    · simp only [m', hcq, ite_false]
      exact measurable_const
  refine ⟨m' ⁻¹' goodSqRat ε s₀ b₀ M x₀, hm' (measurableSet_goodSqRat ε s₀ b₀ M x₀), ?_⟩
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hvag] with ω hω
  simp only [mem_ofPred_eq, mem_preimage, goodSq_iff_rat, goodSqRat]
  have hc : ∀ (c : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt c) q ⊆ closure Q →
      ballMassQ (muTr hW γ hb hK ω) c q = m' ω c q := by
    intro c q hq hBQ
    set B := ball (ratPt c) q
    have hBO : B ⊆ O := interior_maximal (hBQ.trans hQc.isClosed.closure_eq.subset) isOpen_ball
    have hBc : Bᶜ.Nonempty := ⟨0, fun h => by have := hOS (hBO h); simp [openSquare] at this⟩
    show muOfMod W γ (ferniqueBox y b) (trMod hW hb hK) ω B = m' ω c q
    have e1 : muOfMod W γ (ferniqueBox y b) (trMod hW hb hK) ω B =
        (muOfMod W γ (ferniqueBox y b) (trMod hW hb hK) ω).restrict O B := by
      rw [Measure.restrict_apply isOpen_ball.measurableSet, inter_eq_left.2 hBO]
    have e2 : m' ω c q = ⨆ n : ℕ, ENNReal.ofReal (limUnder atTop fun k => I c q n k ω) :=
      ite_eq_left_iff.2 fun h => absurd ⟨hq, hBQ⟩ h
    rw [e1, e2, measure_eq_iSup_limUnder_of_vague hω isOpen_ball isBounded_ball hBO hBc]
    congr 1; funext n; congr 2; funext k
    have hdm : Measurable fun z => dens k z ω :=
      (Real.measurable_exp.comp (((hVf k).comp (measurable_id.prodMk measurable_const)).const_mul
        γ)).const_mul _
    exact GMCIdent4.integral_withDensity_ofReal (d := fun z => dens k z ω) hdm
      (fun z => by simp only [dens]; positivity) _
  constructor
  · intro h u hu v hv
    rw [← dgLGDRat_congr hc]; exact h u hu v hv
  · intro h u hu v hv
    rw [dgLGDRat_congr hc]; exact h u hu v hv

end DG
end LQGMetric
