/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39KC2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5j
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K7b
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K8L3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K5d

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, the last mile in the D132 form (packet P-132C)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1543–1566, 1586 (the iteration and the locality of `n_k`, `x_k`, the events at step `k`);
decision D132 (decisions/DEC-132.md §2 N5, §5 P-132C).

This is `S3T39KC1` (P2-T39KC) with the input `hB` of `t39k5_fields_at` replaced, as in D132 N5,
by the two deterministic properties of J3's arcs `t39jArcs m i`:
* `harcs`: `t39jArcs m i Γ ⊆ Γ` for closed `Γ` (`t39j_arcs_subset`, `IsClosed.closure_eq`);
* `harcsM`: `effrosSigma ⊗ Borel`-measurability of membership (`t39k5_arcs_mem_meas`).
The proofs of `t39kc_fields_meas`, `t39k5FieldsJ3_of`, `confThm3_9RestAll_of_meas` (S3T39KC1)
are copied with this one change (KC1 passes `hB` to the pre-D132 `t39k5_fields_at`).

Moreover (P2-T39INT, S3T39K5j) the class of `hCtr`, `hGood` is restricted to `(interior K).Nonempty`
(`t39k5_fields_atI`), supplied by `t39k8_hCtrI`, `t39k8_hGoodI` (P2-T39K8L, S3T39K8L3).

* **`t39kc2_fields_meas`**, **`t39kc2_fieldsJ3_of`**: fields 4–6 / `T39K5FieldsJ3` from `hCtr`,
  `hGood` (interior class) only;
* **`confThm3_9RestAll_of_ctrGood`**: `CONFW.CONFThm3_9RestAll` from DFGPS Lemma 3.8 and `hCtr`,
  `hGood` (no `hB`);
* **`confThm3_9RestAll_holds`**: `CONFW.CONFThm3_9RestAll` from DFGPS Lemma 3.8 alone.
-/

noncomputable section

open MeasureTheory Set Metric Filter TopologicalSpace

namespace LQGMetric.CONF

open Blueprint LocalEvent GM

/-- D132 N5 input `harcs` for J3's arcs -/
theorem t39kc2_harcs (m : ℕ) : ∀ (i : Fin m) (Γ : Set ℂ), IsClosed Γ → t39jArcs m i Γ ⊆ Γ :=
  fun i Γ hΓ => (t39j_arcs_subset m i Γ).trans hΓ.closure_eq.subset

/-- D132 N5 input `harcsM` for J3's arcs -/
theorem t39kc2_harcsM (m : ℕ) (i : Fin m) :
    MeasurableSet[@Prod.instMeasurableSpace (Set ℂ) ℂ effrosSigma inferInstance]
      {p : Set ℂ × ℂ | p.2 ∈ t39jArcs m i p.1} :=
  t39k5_arcs_mem_meas m i

section Step
variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [P.IsComplete] {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
  {h : Ω → DistC} {z₀ : ℂ} {R : ℝ} {τ : Ω → ℝ} {m : ℕ}

/-- **fields 4–6 at step `k`** for J3's arcs, given `Measurable s_k` and `Inv(j)`, `j ≤ k`
(S3T39KC1 `t39kc_fields_meas`, D132 form) -/
theorem t39kc2_fields_meas (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η)
    (hh : IsWholePlaneGFF h P) (hR : 0 < R) (hτ : IsFilledBallStoppingTime D h z₀ τ)
    (hτI : ∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ R ω) (tauR D h z₀ (2 * R) ω))
    (hCtr : ∃ Ψ : ℝ → Set ℂ × Set ℂ → ℂ,
      (∀ r, @Measurable _ _ (@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma) _ (Ψ r)) ∧
      ∀ (K J : Set ℂ) (r : ℝ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K → t39jCtr K J r = Ψ r (K, J))
    (hGood : ∃ A : ℕ → Set (Set ℂ × Set ℂ),
      (∀ q, MeasurableSet[@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma] (A q)) ∧
      ∀ (K J : Set ℂ) (q : ℕ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K →
        (t39jGoodAct K J q R ↔ (K, J) ∈ A q))
    (k : ℕ)
    (hinv : ∀ j ≤ k, IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀
      (t39j7S γ D c p P h z₀ R (t39jA t39jArcChoice D h z₀ τ m) τ j ω)))
    (hsm : Measurable (t39j7S γ D c p P h z₀ R (t39jA t39jArcChoice D h z₀ τ m) τ k)) :
    T39K7Fields γ D c p P h z₀ R (t39jA t39jArcChoice D h z₀ τ m) τ k := by
  set I₀ := t39jA t39jArcChoice D h z₀ τ m with hI₀
  set s := t39j7S γ D c p P h z₀ R I₀ τ with hsdef
  have hpos : ∀ᵐ ω ∂P, 0 < τ ω :=
    hτI.mono fun ω hω => (t39h_tauR_pos D h z₀ hR ω).trans_le hω.1
  have hge := t39j7_ge_tau (I₀ := I₀) h38 hγ hγ2 hD H35 hη hh hR hτ hpos
  have hsnn := t39j7_hsnn (γ := γ) (c := c) (p := p) (R := R) (I₀ := I₀) hτ hpos
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have hgood : ∀ᵐ ω ∂P, 0 < τ ω ∧ τ ω ≤ s k ω ∧
      Bornology.IsBounded (filledBall (D (h ω)) z₀ (s k ω)) ∧
      JordanMap.IsJordanCurve (frontier (filledBall (D (h ω)) z₀ (s k ω))) := by
    filter_upwards [hpos, hge, hlen] with ω h0 hk hl
    exact ⟨h0, hk k, gm_filledBall_isBounded_of_lenSet hl z₀ _,
      gm_filledBall_frontier_isJordanCurve' (h0.trans_le (hk k)) (isLength_of_mem_lenSet hl)
        (isBounded_ballM_of_bc (bcpt_of_mem_lenSet hl) z₀ _)⟩
  have hss := t39k7_hss (I₀ := I₀) h38 hγ hγ2 hD H35 hη hh hR hτ hpos
  have hτhit : ∀ V : Set ℂ, IsOpen V → ∀ j ≤ k,
      AEEventIn P (filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s j ω)))
        {ω | (filledBall (D (h ω)) z₀ (τ ω) ∩ V).Nonempty} := by
    intro V hV j
    induction j with
    | zero => intro _; exact t39k5_fb_hit D h z₀ (hsnn 0) hV
    | succ j ih =>
      intro hj
      obtain ⟨A, hA, hEA⟩ := ih (Nat.le_of_succ_le hj)
      obtain ⟨B, hB', hAB⟩ := t39k_hmono_of_le D h z₀ hlen (s j) (s (j + 1))
        (hinv j (Nat.le_of_succ_le hj)) (hss j) A hA
      exact ⟨B, hB', hEA.trans hAB⟩
  have hle : filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (s k ω)) ≤ mΩ := by
    rw [t39h_fbs0_eq D h z₀ (hsnn k)]
    exact (localSigma0_le_localSigma h _).trans ((iInf_le _ 0).trans
      (gm_hullSigma_filledBall_le (P := P) hh (hD.measurable.comp hh.measurable) hsm z₀ 0))
  exact t39k5_fields_atI h38 hγ hγ2 hD hh z₀ R (t39jArcs m) τ I₀ (fun _ _ => rfl) s k
    (hsnn k) hgood (fun V hV => hτhit V hV k le_rfl) hle
    (t39kc2_harcs m) (t39kc2_harcsM m) hCtr hGood

end Step

/-- **the J6d target `T39K5FieldsJ3`** from the deterministic inputs `hCtr`, `hGood`
(S3T39KC1 `t39k5FieldsJ3_of`, D132 form) -/
theorem t39kc2_fieldsJ3_of (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : CONFParams}
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η)
    (hCtr : ∃ Ψ : ℝ → Set ℂ × Set ℂ → ℂ,
      (∀ r, @Measurable _ _ (@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma) _ (Ψ r)) ∧
      ∀ (K J : Set ℂ) (r : ℝ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K → t39jCtr K J r = Ψ r (K, J))
    (hGood : ∀ R : ℝ, 0 < R → ∃ A : ℕ → Set (Set ℂ × Set ℂ),
      (∀ q, MeasurableSet[@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma] (A q)) ∧
      ∀ (K J : Set ℂ) (q : ℕ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K →
        (t39jGoodAct K J q R ↔ (K, J) ∈ A q)) :
    T39K5FieldsJ3 γ D c p := by
  intro Ω _ P _ _ h hh z₀ R hR τ hτ hτI m
  set I₀ := t39jA t39jArcChoice D h z₀ τ m with hI₀
  have key : ∀ k, (∀ j ≤ k, IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀
      (t39j7S γ D c p P h z₀ R I₀ τ j ω))) →
      Measurable (t39j7S γ D c p P h z₀ R I₀ τ k) ∧
        T39K7Fields γ D c p P h z₀ R I₀ τ k := by
    intro k
    induction k with
    | zero =>
      intro hinv
      have hsm : Measurable (t39j7S γ D c p P h z₀ R I₀ τ 0) :=
        t39j7_measurable_stop hh hD.measurable hτ
      exact ⟨hsm, t39kc2_fields_meas h38 hγ hγ2 hD H35 hη hh hR hτ hτI hCtr (hGood R hR) 0
        hinv hsm⟩
    | succ k ih =>
      intro hinv
      obtain ⟨hsk, hFk⟩ := ih fun j hj => hinv j (Nat.le_succ_of_le hj)
      have hpos : ∀ᵐ ω ∂P, 0 < τ ω :=
        hτI.mono fun ω hω => (t39h_tauR_pos D h z₀ hR ω).trans_le hω.1
      have hsnn := t39j7_hsnn (γ := γ) (c := c) (p := p) (R := R) (I₀ := I₀) hτ hpos
      obtain ⟨g, hg, hng⟩ := hFk.1
      have hle : filledBallSigmaAt0 D h z₀
          (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω)) ≤ ‹MeasurableSpace Ω› := by
        rw [t39h_fbs0_eq D h z₀ (hsnn k)]
        exact (localSigma0_le_localSigma h _).trans ((iInf_le _ 0).trans
          (gm_hullSigma_filledBall_le (P := P) hh (hD.measurable.comp hh.measurable) hsk z₀ 0))
      have hsm := t39j8_measurable_succ hD hh p z₀ hR I₀ τ k hsk
        ((hg.mono hle le_rfl).congr_ae hng.symm)
      exact ⟨hsm, t39kc2_fields_meas h38 hγ hγ2 hD H35 hη hh hR hτ hτI hCtr (hGood R hR)
        (k + 1) hinv hsm⟩
  exact fun k hinv => (key k hinv).2

/-- **`CONFW.CONFThm3_9RestAll`** from DFGPS Lemma 3.8 and the deterministic inputs `hCtr`,
`hGood` (D132: no `hB`) -/
theorem confThm3_9RestAll_of_ctrGood (h38 : DFGPSLem3_8)
    (hCtr : ∃ Ψ : ℝ → Set ℂ × Set ℂ → ℂ,
      (∀ r, @Measurable _ _ (@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma) _ (Ψ r)) ∧
      ∀ (K J : Set ℂ) (r : ℝ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K → t39jCtr K J r = Ψ r (K, J))
    (hGood : ∀ R : ℝ, 0 < R → ∃ A : ℕ → Set (Set ℂ × Set ℂ),
      (∀ q, MeasurableSet[@Prod.instMeasurableSpace _ _ effrosSigma effrosSigma] (A q)) ∧
      ∀ (K J : Set ℂ) (q : ℕ), IsClosed K → Bornology.IsBounded K → (interior K).Nonempty →
        JordanMap.IsJordanCurve (frontier K) → J ⊆ frontier K →
        (t39jGoodAct K J q R ↔ (K, J) ∈ A q)) :
    CONFW.CONFThm3_9RestAll :=
  confThm3_9RestAll_of_K7 h38 fun γ hγ hγ2 D c hD _p hp _ H35 =>
    t39kc2_fieldsJ3_of h38 hγ hγ2 hD H35 hp.2.2.2.2.2 hCtr hGood

/-- **the CONF Theorem 3.9 leaf `CONFW.CONFThm3_9RestAll`** from DFGPS Lemma 3.8 alone:
`hCtr`, `hGood` are P2-T39K8L's `t39k8_hCtrI`, `t39k8_hGoodI` (S3T39K8L3) -/
theorem confThm3_9RestAll_holds (h38 : DFGPSLem3_8) : CONFW.CONFThm3_9RestAll :=
  confThm3_9RestAll_of_ctrGood h38 t39k8_hCtrI fun R _ => t39k8_hGoodI R

end LQGMetric.CONF
