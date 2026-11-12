/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412iStop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412gTrace

/-!
# GM L4.15 Step 4: events of `σ(𝓑^•_σ, h|)` on `{σ ≤ s}`, a.s. form (D98 (b), packet P-stop)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Lemma 4.15, Step 4, l. 2189–2191: "The radius `σ_k` is a stopping time for
`{(𝓑^•_s, h|_{𝓑^•_s})}_{s ≥ 0}`, so the event inside the conditional probability in (4.40′)
belongs to `σ(𝓑^•_{s_{k+1}}, h|_{𝓑^•_{s_{k+1}}})`." The stopping-time property of `σ_k` is CONF
(arXiv:1905.00381, `confluence-final.tex`) l. 1302.

`p412g_stop_inter` (P412gTrace) needs `{σ ≤ s}` to be *surely* an event of `σ(𝓑^•_{σ∧s}, h|)`;
Axiom II (locality) holds only a.s., so for `σ = confSigma` only a.s.-statements are available.
This file gives the a.s. form, with the stopping-time input stated piecewise (`gmPieceSig`, the
method of `gm_localSigma_le_aeSigma`):

* **`p412i_hullSigma_le_trace`**: one hull level of `σ(A, h|_A)` lies in the trace on `C` of the
  piecewise-local σ-algebra of `B`, if `A ⊆ B` on `C` and `C`, `{A ∩ U ≠ ∅} ∩ C` are piecewise local;
* **`p412i_aeEventIn_inter`**: then `E ∩ C` is a.s. an event of `σ(B, h|_B)` for `E ∈ σ(A, h|_A)`;
* **`p412i_aeEventIn_of_pieces`**: a piecewise-local event is a.s. an event of `σ(B, h|_B)`;
* **`p412i_stop_inter_ae`**: the filled-ball form: `σ ∈ [0,∞]` random, `s ≤ T` random reals,
  `E ∈ filledBallSigmaAt σ` ⇒ `E ∩ {σ ≤ s}` is a.s. an event of `σ(𝓑^•_T, h|_{𝓑^•_T})`, given
  (b2-C′) `{σ ≤ s}` and (b2-H′) `{𝓑^•_σ ∩ U ≠ ∅} ∩ {σ ≤ s}` piecewise local for `𝓑^•_T`;
* **`p412i_stop_inter_aeSigma`**: the same in `gmAESigma` (complete space, D70).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set Filter
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

variable {Ω : Type} [MeasurableSpace Ω]

/-- one hull level of `σ(A, h|_A)` lies in the trace on `C` of the piecewise-local σ-algebra
of `B`, when `A ⊆ B` on `C` -/
theorem p412i_hullSigma_le_trace (h : Ω → DistC) {P : Measure Ω} {A B : Ω → Set ℂ}
    {C : Set Ω} (hA : ∀ ω, IsClosed (A ω)) (hAB : ∀ ω ∈ C, A ω ⊆ B ω) (n : ℕ) (S' : Set ℂ)
    (hC : MeasurableSet[gmPieceSig h B n S' P] C)
    (hhit : ∀ U : Set ℂ, IsOpen U →
      MeasurableSet[gmPieceSig h B n S' P] ({ω | (A ω ∩ U).Nonempty} ∩ C)) :
    hullSigma h A n ≤ p412gTraceSig (gmPieceSig h B n S' P) C hC := by
  have hset : setSigma A ≤ p412gTraceSig (gmPieceSig h B n S' P) C hC :=
    generateFrom_le (by rintro _ ⟨U, hU, rfl⟩; exact hhit U hU)
  refine sup_le hset (generateFrom_le ?_)
  rintro _ ⟨S, F, hF, rfl⟩
  have hSC : MeasurableSet[gmPieceSig h B n S' P] ({ω | dyadicHull n (A ω) = S} ∩ C) :=
    hset _ (measurableSet_hull_eq hA n S)
  show MeasurableSet[gmPieceSig h B n S' P] ({ω | dyadicHull n (A ω) = S} ∩ F ∩ C)
  have e : {ω | dyadicHull n (A ω) = S} ∩ F ∩ C = ({ω | dyadicHull n (A ω) = S} ∩ C) ∩ F := by
    ext ω; simp only [mem_inter_iff]; tauto
  rw [e]
  by_cases hSS : S ⊆ S'
  · have hF' : MeasurableSet[gmPieceSig h B n S' P] F :=
      ⟨F, fieldSigma_mono h (V := toOpens (interior S) isOpen_interior)
        (W := toOpens (interior S') isOpen_interior) (interior_mono hSS) _ hF,
        Eventually.of_forall fun _ _ => Iff.rfl⟩
    exact @MeasurableSet.inter Ω (gmPieceSig h B n S' P) _ _ hSC hF'
  · refine ⟨∅, @MeasurableSet.empty Ω (fieldSigma _ _), Eventually.of_forall fun ω hS => ?_⟩
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨h1, h2⟩ _
    exact hSS (h1 ▸ hS ▸ gm_dyadicHull_mono n (hAB ω h2))

/-- a piecewise-local event (for `B`, at every level and hull) is a.s. an event of
`σ(B, h|_B)` -/
theorem p412i_aeEventIn_of_pieces (h : Ω → DistC) {P : Measure Ω} {B : Ω → Set ℂ}
    (hB : ∀ ω, IsClosed (B ω)) (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (B ω)) {E : Set Ω}
    (hE : ∀ (n : ℕ) (s : Finset (ℤ × ℤ)), MeasurableSet[gmPieceSig h B n (hullFin n s) P] E) :
    AEEventIn P (localSigma h B) E :=
  aeEventIn_localSigma h hB fun n => aeEventIn_hullSigma_of_pieces h B hb n fun s => hE n s

/-- **`E ∩ C` is a.s. an event of `σ(B, h|_B)`** for `E ∈ σ(A, h|_A)`, when `A ⊆ B` on `C` and
`C`, `{A ∩ U ≠ ∅} ∩ C` are piecewise local for `B` (a.s. form of `p412g_inter_aeSigma`) -/
theorem p412i_aeEventIn_inter (h : Ω → DistC) {P : Measure Ω} {A B : Ω → Set ℂ}
    (hA : ∀ ω, IsClosed (A ω)) (hB : ∀ ω, IsClosed (B ω))
    (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (B ω)) {C : Set Ω} (hAB : ∀ ω ∈ C, A ω ⊆ B ω)
    (hC : ∀ (n : ℕ) (s : Finset (ℤ × ℤ)), MeasurableSet[gmPieceSig h B n (hullFin n s) P] C)
    (hhit : ∀ (n : ℕ) (s : Finset (ℤ × ℤ)) (U : Set ℂ), IsOpen U →
      MeasurableSet[gmPieceSig h B n (hullFin n s) P] ({ω | (A ω ∩ U).Nonempty} ∩ C))
    {E : Set Ω} (hE : MeasurableSet[localSigma h A] E) :
    AEEventIn P (localSigma h B) (E ∩ C) :=
  p412i_aeEventIn_of_pieces h hB hb fun n s =>
    p412i_hullSigma_le_trace h hA hAB n _ (hC n s) (hhit n s) E
      (MeasurableSpace.measurableSet_iInf.1 hE n)

/-- `𝓑^•_σ` is closed for `σ ∈ [0,∞]` -/
theorem p412i_filledBallE_isClosed (d : ContMetric) (z₀ : ℂ) (σ : ℝ≥0∞) :
    IsClosed (filledBallE d z₀ σ) := by
  unfold filledBallE
  split_ifs
  · exact isClosed_univ
  · exact gm_filledBall_isClosed _ _ _

/-- on `{σ ≤ s}`, `𝓑^•_σ ⊆ 𝓑^•_T` for `s ≤ T` -/
theorem p412i_filledBallE_subset (d : ContMetric) (z₀ : ℂ) {σ : ℝ≥0∞} {s T : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ T) (hσ : σ ≤ ENNReal.ofReal s) : filledBallE d z₀ σ ⊆ filledBall d z₀ T := by
  rw [p412g_filledBallE_eq d z₀ hs hσ]
  exact gm_filledBall_mono _ _ ((min_le_right _ _).trans hsT)

/-- **GM l. 2189–2191, a.s. form (D98 (b))**: for a random radius `σ ∈ [0,∞]` and random reals
`0 ≤ s ≤ T`, an event of `σ(𝓑^•_σ, h|)` intersected with `{σ ≤ s}` is a.s. an event of
`σ(𝓑^•_T, h|_{𝓑^•_T})`, given the piecewise stopping-time inputs (b2-C′) `hC` and (b2-H′)
`hhit` -/
theorem p412i_stop_inter_ae (D : DistC → ContMetric) (h : Ω → DistC) {P : Measure Ω} (z₀ : ℂ)
    (σ : Ω → ℝ≥0∞) {s T : Ω → ℝ} (hs : ∀ ω, 0 ≤ s ω) (hsT : ∀ ω, s ω ≤ T ω)
    (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (filledBall (D (h ω)) z₀ (T ω)))
    (hC : ∀ (n : ℕ) (fs : Finset (ℤ × ℤ)),
      MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) z₀ (T ω)) n (hullFin n fs) P]
        {ω | σ ω ≤ ENNReal.ofReal (s ω)})
    (hhit : ∀ (n : ℕ) (fs : Finset (ℤ × ℤ)) (U : Set ℂ), IsOpen U →
      MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) z₀ (T ω)) n (hullFin n fs) P]
        ({ω | (filledBallE (D (h ω)) z₀ (σ ω) ∩ U).Nonempty} ∩
          {ω | σ ω ≤ ENNReal.ofReal (s ω)}))
    {E : Set Ω} (hE : MeasurableSet[filledBallSigmaAt D h z₀ σ] E) :
    AEEventIn P (localSigma h (fun ω => filledBall (D (h ω)) z₀ (T ω)))
      (E ∩ {ω | σ ω ≤ ENNReal.ofReal (s ω)}) :=
  p412i_aeEventIn_inter h (fun _ => p412i_filledBallE_isClosed _ _ _)
    (fun _ => gm_filledBall_isClosed _ _ _) hb
    (fun ω hω => p412i_filledBallE_subset _ _ (hs ω) (hsT ω) hω) hC hhit hE

omit [MeasurableSpace Ω] in
/-- an a.s. event of `G ≤ mΩ` on a complete space is an event of `gmAESigma G` -/
theorem p412i_aeSigma_of_aeEventIn {mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} [P.IsComplete]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) {E : Set Ω} (hE : @AEEventIn Ω mΩ P G E) :
    MeasurableSet[@gmAESigma Ω mΩ G P] E := by
  obtain ⟨F, hF, hEF⟩ := hE
  have hFm : MeasurableSet[mΩ] F := hG _ hF
  have hEm : MeasurableSet[mΩ] E :=
    (hFm.nullMeasurableSet.congr hEF.symm).measurable_of_complete
  refine MeasurableSpace.measurableSet_inf.2 ⟨hEm, F, hF, ?_⟩
  rwa [inter_univ]

/-- **`p412i_stop_inter_ae` in the completed σ-algebra** `gmAESigma σ(𝓑^•_T, h|)` (D70) -/
theorem p412i_stop_inter_aeSigma (D : DistC → ContMetric) (h : Ω → DistC) {P : Measure Ω}
    [P.IsComplete] (z₀ : ℂ) (σ : Ω → ℝ≥0∞) {s T : Ω → ℝ} (hs : ∀ ω, 0 ≤ s ω)
    (hsT : ∀ ω, s ω ≤ T ω)
    (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (filledBall (D (h ω)) z₀ (T ω)))
    (hTm : localSigma h (fun ω => filledBall (D (h ω)) z₀ (T ω)) ≤ ‹MeasurableSpace Ω›)
    (hC : ∀ (n : ℕ) (fs : Finset (ℤ × ℤ)),
      MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) z₀ (T ω)) n (hullFin n fs) P]
        {ω | σ ω ≤ ENNReal.ofReal (s ω)})
    (hhit : ∀ (n : ℕ) (fs : Finset (ℤ × ℤ)) (U : Set ℂ), IsOpen U →
      MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) z₀ (T ω)) n (hullFin n fs) P]
        ({ω | (filledBallE (D (h ω)) z₀ (σ ω) ∩ U).Nonempty} ∩
          {ω | σ ω ≤ ENNReal.ofReal (s ω)}))
    {E : Set Ω} (hE : MeasurableSet[filledBallSigmaAt D h z₀ σ] E) :
    MeasurableSet[gmAESigma (localSigma h (fun ω => filledBall (D (h ω)) z₀ (T ω))) P]
      (E ∩ {ω | σ ω ≤ ENNReal.ofReal (s ω)}) :=
  p412i_aeSigma_of_aeEventIn _ hTm (p412i_stop_inter_ae D h z₀ σ hs hsT hb hC hhit hE)

/-- the event `{σ ≤ s}` (and its complement `{σ > s}`) is an event of `gmAESigma σ(𝓑^•_T, h|)`
under (b2-C′) -/
theorem p412i_stopEvent_aeSigma (D : DistC → ContMetric) (h : Ω → DistC) {P : Measure Ω}
    [P.IsComplete] (z₀ : ℂ) (σ : Ω → ℝ≥0∞) {s T : Ω → ℝ}
    (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (filledBall (D (h ω)) z₀ (T ω)))
    (hTm : localSigma h (fun ω => filledBall (D (h ω)) z₀ (T ω)) ≤ ‹MeasurableSpace Ω›)
    (hC : ∀ (n : ℕ) (fs : Finset (ℤ × ℤ)),
      MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) z₀ (T ω)) n (hullFin n fs) P]
        {ω | σ ω ≤ ENNReal.ofReal (s ω)}) :
    MeasurableSet[gmAESigma (localSigma h (fun ω => filledBall (D (h ω)) z₀ (T ω))) P]
      {ω | σ ω ≤ ENNReal.ofReal (s ω)} :=
  p412i_aeSigma_of_aeEventIn _ hTm
    (p412i_aeEventIn_of_pieces h (fun _ => gm_filledBall_isClosed _ _ _) hb hC)

end LQGMetric.GM
