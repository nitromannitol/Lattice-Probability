/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L19R3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19R2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Loc5

/-!
# DG Lemma 3.19 at `μ = μ_ĥ`: locality of the unit-frame event `E_𝕊` (P2-DG105r)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1643 ("the reason for the
second condition is to make it so that `E_S^ε` is determined by `ĥ^tr|_{S(3/4)}`") and DG:1656
(the percolation argument of Lemma 3.11). The event `l319Ev (μ_{ĥ^tr}) t M` (S3L19R2) only uses
the masses of rational balls in `B̄(u, 13/280)`; those are a.s. local functionals of the white
noise on `(0,1) × B_{1/10}(B̄(u,13/280))`. The proof is P2-DGLOC's `goodSq_muTr_loc` (S3L11Loc4),
copied with the closed square `sqOne` replaced by the compact set `B̄(u, 13/280)` and the event
`goodSqRat` by `l319EvRat`; the transfer to the rescaled noise is that of `dgLocTr_proved`
(S3L11Loc5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent SupTail QuantumZipper

/-- `D^ε(A,B;U)` only depends on the masses of the rational balls in `Ū` -/
lemma dgLGDSetRat_congr {m m' : ℚ × ℚ → ℚ → ℝ≥0∞} {ε : ℝ} {U : Set ℂ}
    (h : ∀ (c : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt c) q ⊆ closure U → m c q = m' c q)
    (A B : Set ℂ) : dgLGDSetRat m ε U A B = dgLGDSetRat m' ε U A B := by
  have hA : ∀ N, dgRatAdmSet m ε U A B N ↔ dgRatAdmSet m' ε U A B N := by
    intro N
    unfold dgRatAdmSet
    constructor
    · rintro ⟨c, q, hP, hi⟩
      exact ⟨c, q, hP, fun i => ⟨(hi i).1, by rw [← h _ _ (hi i).1.1 (hi i).1.2]; exact (hi i).2⟩⟩
    · rintro ⟨c, q, hP, hi⟩
      exact ⟨c, q, hP, fun i => ⟨(hi i).1, by rw [h _ _ (hi i).1.1 (hi i).1.2]; exact (hi i).2⟩⟩
  unfold dgLGDSetRat
  simp_rw [hA]

/-- `E_𝕊` only depends on the masses of the rational balls in `B̄(u, 13/280)` -/
lemma l319EvRat_congr {m m' : ℚ × ℚ → ℚ → ℝ≥0∞} (t M : ℝ)
    (h : ∀ (c : ℚ × ℚ) (q : ℚ), 0 < q → ball (ratPt c) q ⊆ closure (closedBall l319U l319r) →
      m c q = m' c q) : m ∈ l319EvRat t M ↔ m' ∈ l319EvRat t M := by
  have hg : ∀ i j : ℤ, ‖(⟨i * l319g, j * l319g⟩ : ℂ) - l319U‖ ≤ 1 / 28 + 3 / 560 + l319g →
      m ((i : ℚ) / 400, (j : ℚ) / 400) (1 / 400) = m' ((i : ℚ) / 400, (j : ℚ) / 400) (1 / 400) := by
    intro i j hij
    refine h _ _ (by norm_num) ?_
    rw [closure_closedBall, ratPt_l319]
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_closedBall, dist_eq_norm]
    have := norm_sub_le_norm_sub_add_norm_sub x (⟨i * l319g, j * l319g⟩ : ℂ) l319U
    push_cast at hx
    norm_num at hij hx ⊢; linarith
  simp only [l319EvRat, mem_inter_iff, mem_preimage, mem_setOf_eq, dgLGDSetRat_congr h,
    l319HeavyRat]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i j hij => hg i j hij ▸ h1 i j hij, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun i j hij => (hg i j hij).symm ▸ h1 i j hij, h2⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **locality of `E_𝕊` for `μ_{ĥ^tr}`, unit frame** (DG:1643): the event `l319Ev (muTr W) t M`
is a.s. equal to an event of the white noise on `(0,1) × B_{1/10}(B̄(u,13/280))` (proof of
`goodSq_muTr_loc`, S3L11Loc4) -/
theorem l319Ev_muTr_loc (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ}
    {b : ℝ} (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    (hsq : closedBall l319U l319r ⊆ ferniqueBox y b) (t M : ℝ) :
    ∃ A', MeasurableSet[wnSigma W (trLocReg (closedBall l319U l319r))] A' ∧
      {ω | l319Ev (muTr hW γ hb hK ω) t M} =ᵐ[P] A' := by
  set Q := closedBall l319U l319r
  set O := interior Q
  have hQc : IsCompact Q := isCompact_closedBall _ _
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
  refine ⟨m' ⁻¹' l319EvRat t M, hm' (measurableSet_l319EvRat t M), ?_⟩
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hvag] with ω hω
  simp only [mem_ofPred_eq, mem_preimage, l319Ev_iff]
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
  exact l319EvRat_congr t M hc

/-- the white-noise region of the unit-frame event of the cell with offset `c` at scale `2^{-j}`:
times `(0, s²)`, space `s · B_{1/10}(B̄(u,13/280)) + c` (DG:1643, 1656) -/
def l319LocReg (j : ℕ) (c : ℂ) : Set (ℝ × ℂ) :=
  Ioo 0 (((2 : ℝ)⁻¹ ^ j) ^ 2) ×ˢ
    (affineC ((2 : ℝ)⁻¹ ^ j) c '' Metric.thickening (1 / 10) (closedBall l319U l319r))

/-- **locality of `E_𝕊` for the rescaled noise** (DG:1643, 1656): for `W' = W ∘ U_{2^{-j},c}`,
the event `l319Ev (muTr W') t M` is a.s. equal to an event of `W` on `l319LocReg j c` -/
theorem l319Ev_loc (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {y : ℂ}
    {b : ℝ} (hb : 0 < b) (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare)
    (hsq : closedBall l319U l319r ⊆ ferniqueBox y b) (j : ℕ) (c : ℂ) (t M : ℝ) :
    ∃ A', MeasurableSet[wnSigma W (l319LocReg j c)] A' ∧
      {ω | l319Ev (muTr (dgN5_wnScaleDy hW j c).1 γ hb hK ω) t M} =ᵐ[P] A' := by
  obtain ⟨A', hA', hE⟩ := l319Ev_muTr_loc (dgN5_wnScaleDy hW j c).1 hγ hγ2 hb hK hsq t M
  refine ⟨A', wnSigma_comp_le (W := W) (wnScaleDy j c) (fun g hg => ?_) A' hA', hE⟩
  exact supportedIn_wnScale _ c isOpen_thickening.measurableSet hg

end DG
end LQGMetric
