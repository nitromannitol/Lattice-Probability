/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J9
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J3e
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K2
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39K6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, packet J6e-2 (DEC-130B §5): the induction `IsLocalSetDet0 P h 𝓑^•_{s_k}`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1292–1302 (σ^ε is a stopping time when its base is one, read modulo constants, C:1154),
C:1431–1432 (L2.1 applied with `h` modulo constants), C:1543–1566 (the iteration); DEC-130B §3
(route L2′), DV-D130B-1.

* `t39k7_fbs0`: `filledBallSigmaAt0` at a real radius is `localSigma0` of the filled ball;
* `t39k7_hss`: `s_k ≤ s_{k+1}` a.s.;
* **`t39k7_isLocalSetDet0_succ`** (L2′): `Inv(k) ∧ field 4 at k ⇒ Inv(k+1)`, for each `ψ` via SCALE
  (`t39k6_iter_normIn`, S3T39K6), TRANSFER (`t39k6_isLocalSetDet0_normIn_of_ae_eq`), the arc
  scaling `t39k6_gArc_smul`, AE-CONGR/EVENTS→FUN (`t39k6_aeEventIn_localSigma0_of_ae_eq`,
  `t39k6_exists_measurable_nat_of_ae`), L0/L1/L3 at `normIn h ψ`
  (`t39k_ae0_of_isLocalSetDet0`, `t39k_confSigma_ae0`, `t39k_ae_of_ae0`) and
  `t39k2_isLocalSetDet0_of_cov`;
* `t39k7_ae0_succ` (field 1 chain at `h`: L0, L1);
* **`t39k7_rest`**: `T39J6Rest` by induction on `k` with invariant `Inv(k)`, fields 4–6 from the
  J6d target `T39K7Fields`;
* **`confThm3_9RestJ6_of`**: `CONFThm3_9RestJ6` with J3's arcs `t39jA t39jArcChoice`
  (S3T39J3e) from the J6d target `T39K5FieldsJ3`; `confThm3_9RestCL_of_K7`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Function
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Blueprint GM

section Iter
variable {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω}

/-- fields 4–6 of `T39J6Rest` at step `k` (the J6d target) -/
def T39K7Fields (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) (P : Measure Ω)
    (h : Ω → DistC) (z₀ : ℂ) (R : ℝ) {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ)
    (τ : Ω → ℝ) (k : ℕ) : Prop :=
  (∃ g : Ω → ℕ, Measurable[filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω))] g ∧
    (fun ω => t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω) =ᵐ[P] g) ∧
  (∀ i, ∃ g : Ω → ℂ, Measurable[filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω))] g ∧
    t39jX D h z₀ R I₀ (t39j7S γ D c p P h z₀ R I₀ τ)
      (fun k => t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k)) k i =ᵐ[P] g) ∧
  (∀ i, AEEventIn P (filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω)))
    (t39jAct D h z₀ R I₀ (t39j7S γ D c p P h z₀ R I₀ τ)
      (fun k => t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k)) k i))

omit m0 in
/-- `filledBallSigmaAt0` at a real radius is `localSigma0` of the filled ball -/
theorem t39k7_fbs0 {Ω : Type} (D : DistC → ContMetric) (g : Ω → DistC) (z₀ : ℂ) (x : Ω → ℝ) :
    filledBallSigmaAt0 D g z₀ (fun ω => ENNReal.ofReal (x ω)) =
      localSigma0 g (fun ω => filledBall (D (g ω)) z₀ (x ω)) := by
  unfold filledBallSigmaAt0
  simp_rw [t39k1_filledBallE_ofReal]

variable [IsProbabilityMeasure P] {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
  {h : Ω → DistC} {z₀ : ℂ} {R : ℝ} {ι : Type} [Fintype ι] {I₀ : ι → Ω → Set ℂ} {τ : Ω → ℝ}

/-- `s_k ≤ s_{k+1}` a.s. -/
theorem t39k7_hss (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c)
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) (hh : IsWholePlaneGFF h P) (hR : 0 < R)
    (hτ : IsFilledBallStoppingTime D h z₀ τ) (hpos : ∀ᵐ ω ∂P, 0 < τ ω) :
    ∀ k, ∀ᵐ ω ∂P, t39j7S γ D c p P h z₀ R I₀ τ k ω ≤ t39j7S γ D c p P h z₀ R I₀ τ (k + 1) ω :=
  fun k => by
  filter_upwards [t39j7_hsucc (I₀ := I₀) (τ := τ) (z₀ := z₀) h38 hγ hγ2 hD H35 hη hh hR k]
    with ω hω
  have h1 := t39j7_le_confSigma (xiGamma γ) c D P h p z₀ R
    ((2 : ℝ)⁻¹ ^ t39gExp (t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω))
    (t39j7S γ D c p P h z₀ R I₀ τ k ω) ω
  rw [← hω] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (t39j7_hsnn hτ hpos (k + 1) ω)).1 h1

/-- **the field-1 chain at `h`** (L0 then L1): `s_{k+1}` is an a.s. stopping time modulo
constants -/
theorem t39k7_ae0_succ (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η)
    (hh : IsWholePlaneGFF h P) (hR : 0 < R) (hτ : IsFilledBallStoppingTime D h z₀ τ)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) (k : ℕ)
    (hloc : IsLocalSetDet0 P h
      (fun ω => filledBall (D (h ω)) z₀ (t39j7S γ D c p P h z₀ R I₀ τ k ω)))
    (hnm : ∃ g : Ω → ℕ, Measurable[filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω))] g ∧
      (fun ω => t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω) =ᵐ[P] g) :
    IsFilledBallStoppingTimeAE0 P D h z₀ (t39j7S γ D c p P h z₀ R I₀ τ (k + 1)) := by
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  have h0 := t39k_ae0_of_isLocalSetDet0 D h z₀ hlen _ hloc
    (Eventually.of_forall (t39j7_hsnn (γ := γ) (c := c) (p := p) (R := R) (I₀ := I₀) hτ hpos k))
  obtain ⟨g₀, hg₀, hNg⟩ := hnm
  exact t39k_confSigma_ae0 h38 hγ hγ2 hD H35 hη hh z₀ hR h0
    (ε := fun ω => (2 : ℝ)⁻¹ ^ t39gExp (t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω))
    (fun ω => ⟨_, rfl⟩)
    ⟨fun ω => (2 : ℝ)⁻¹ ^ t39gExp (g₀ ω), (measurable_of_countable (fun n : ℕ => (2 : ℝ)⁻¹ ^ t39gExp n)).comp hg₀,
      hNg.mono fun ω hω => by simp only [hω]⟩

/-- **L2′ (DEC-130B §3)**: `𝓑^•_{s_{k+1}}` is a local set modulo constants when `𝓑^•_{s_k}` is
and `n_k` is a.s. `𝓕_k`-measurable (field 4 at `k`) -/
theorem t39k7_isLocalSetDet0_succ (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η)
    (hh : IsWholePlaneGFF h P) (hR : 0 < R) (hτ : IsFilledBallStoppingTime D h z₀ τ)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω) (k : ℕ)
    (hloc : IsLocalSetDet0 P h
      (fun ω => filledBall (D (h ω)) z₀ (t39j7S γ D c p P h z₀ R I₀ τ k ω)))
    (hnm : ∃ g : Ω → ℕ, Measurable[filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω))] g ∧
      (fun ω => t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω) =ᵐ[P] g) :
    IsLocalSetDet0 P h
      (fun ω => filledBall (D (h ω)) z₀ (t39j7S γ D c p P h z₀ R I₀ τ (k + 1) ω)) := by
  have hge := t39j7_ge_tau (I₀ := I₀) h38 hγ hγ2 hD H35 hη hh hR hτ hpos
  have hsnn := t39j7_hsnn (γ := γ) (c := c) (p := p) (R := R) (I₀ := I₀) hτ hpos
  refine t39k2_isLocalSetDet0_of_cov h38 hγ hγ2 hD hh z₀ _ (fun ψ hψ => ?_)
    (by filter_upwards [hpos, hge] with ω h0 hk using h0.trans_le (hk (k + 1)))
  set lm : Ω → ℝ := fun ω => Real.exp (-(xiGamma γ * h ω ψ)) with hlm
  set s' := t39j7S γ D c p P (normIn h ψ) z₀ R I₀ (fun ω => lm ω * τ ω) with hs'
  have hlm0 : ∀ ω, 0 < lm ω := fun ω => Real.exp_pos _
  have hW : ∀ᵐ ω ∂P, ∀ u v, (D (normIn h ψ ω)).1 (u, v) = lm ω * (D (h ω)).1 (u, v) := by
    filter_upwards [hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh)] with ω hω u v
    rw [normIn, hω, mul_neg]
  have hsc : ∀ᵐ ω ∂P, ∀ j, s' j ω = lm ω * t39j7S γ D c p P h z₀ R I₀ τ j ω := t39k6_iter_normIn hD p hh ψ z₀ hR I₀ τ
  have hball : ∀ j, ∀ᵐ ω ∂P, filledBall (D (normIn h ψ ω)) z₀ (s' j ω) =
      filledBall (D (h ω)) z₀ (t39j7S γ D c p P h z₀ R I₀ τ j ω) := fun j => by
    filter_upwards [hW, hsc] with ω hw hsω
    rw [hsω j]
    exact p412n_filledBall_smul (hlm0 ω) hw z₀ _
  have hh' : IsWholePlaneGFF (normIn h ψ) P := isWholePlaneGFF_normIn hh ψ
  have hlen' := ae_mem_lenSet h38 hγ hγ2 hD P (normIn h ψ) hh'
  have hloc' : IsLocalSetDet0 P (normIn h ψ)
      (fun ω => filledBall (D (normIn h ψ ω)) z₀ (s' k ω)) :=
    t39k6_isLocalSetDet0_normIn_of_ae_eq ψ hloc ((hball k).mono fun ω hω => hω.symm)
  have hs'0 : ∀ᵐ ω ∂P, 0 ≤ s' k ω := hsc.mono fun ω hω => by
    rw [hω k]; exact mul_nonneg (hlm0 ω).le (hsnn k ω)
  have hAE0 := t39k_ae0_of_isLocalSetDet0 D (normIn h ψ) z₀ hlen' (s' k) hloc' hs'0
  -- `n'_k = n_k` a.s. (the arcs are scale invariant)
  obtain ⟨g₀, hg₀, hNg⟩ := hnm
  have hN : ∀ᵐ ω ∂P, t39j7N D (normIn h ψ) z₀ I₀ (s' k) ω =
      t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω := by
    filter_upwards [hW, hsc] with ω hw hsω
    classical
    unfold t39j7N
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    rw [hsω k, t39k6_gArc_smul (hlm0 ω) hw]
  -- the `𝓕'_k`-version of `n'_k` (AE-CONGR, EVENTS→FUN)
  obtain ⟨g', hg', hgg'⟩ := t39k6_exists_measurable_nat_of_ae
    (m := filledBallSigmaAt0 D h z₀ (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω)))
    (m' := filledBallSigmaAt0 D (normIn h ψ) z₀ (fun ω => ENNReal.ofReal (s' k ω))) (P := P)
    g₀ hg₀ (fun n => by
      have hA := hg₀ (measurableSet_singleton n)
      rw [t39k7_fbs0] at hA ⊢
      rw [t39k6_localSigma0_normIn]
      exact t39k6_aeEventIn_localSigma0_of_ae_eq h (fun ω => gm_filledBall_isClosed _ z₀ _)
        ((hball k).mono fun ω hω => hω.symm) hA)
  have hL1 := t39k_confSigma_ae0 h38 hγ hγ2 hD H35 hη hh' z₀ hR hAE0
    (ε := fun ω => (2 : ℝ)⁻¹ ^ t39gExp (t39j7N D (normIn h ψ) z₀ I₀ (s' k) ω))
    (fun ω => ⟨_, rfl⟩)
    ⟨fun ω => (2 : ℝ)⁻¹ ^ t39gExp (g' ω), (measurable_of_countable (fun n : ℕ => (2 : ℝ)⁻¹ ^ t39gExp n)).comp hg', by
      filter_upwards [hN, hNg, hgg'] with ω h1 h2 h3
      simp only [h1, h2, h3]⟩
  refine ⟨s' (k + 1), t39k_ae_of_ae0 hL1, ?_, hball (k + 1)⟩
  filter_upwards [hsc, hpos, hge] with ω hω h0 hk
  rw [hω]
  exact mul_pos (hlm0 ω) (h0.trans_le (hk _))

/-- **`T39J6Rest` by induction on `k`** with the invariant `IsLocalSetDet0 P h 𝓑^•_{s_k}`
(DEC-130B §3), from SCALE (J6e-1) and fields 4–6 (J6d) -/
theorem t39k7_rest (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η)
    (hh : IsWholePlaneGFF h P) (hR : 0 < R) (hτ : IsFilledBallStoppingTime D h z₀ τ)
    (hpos : ∀ᵐ ω ∂P, 0 < τ ω)
    (hloc0 : IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)))
    (HF : ∀ k, (∀ j ≤ k, IsLocalSetDet0 P h
      (fun ω => filledBall (D (h ω)) z₀ (t39j7S γ D c p P h z₀ R I₀ τ j ω))) →
      T39K7Fields γ D c p P h z₀ R I₀ τ k) :
    T39J6Rest γ D c p P h z₀ R I₀ τ := by
  have hinv : ∀ k, ∀ j ≤ k, IsLocalSetDet0 P h
      (fun ω => filledBall (D (h ω)) z₀ (t39j7S γ D c p P h z₀ R I₀ τ j ω)) := by
    intro k
    induction k with
    | zero => intro j hj; rw [Nat.le_zero.1 hj]; exact hloc0
    | succ k ih =>
      intro j hj
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact ih j (Nat.lt_succ_iff.1 hj)
      · exact t39k7_isLocalSetDet0_succ h38 hγ hγ2 hD H35 hη hh hR hτ hpos k
          (ih k le_rfl) (HF k ih).1
  have hF := fun k => HF k (hinv k)
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  exact ⟨fun k => t39k_ae_of_ae0
      (t39k7_ae0_succ h38 hγ hγ2 hD H35 hη hh hR hτ hpos k (hinv k k le_rfl) (hF k).1),
    fun k => hinv (k + 1) (k + 1) le_rfl,
    t39k_hmono_seq D h z₀ hlen _ (fun k => hinv k k le_rfl)
      (t39k7_hss h38 hγ hγ2 hD H35 hη hh hR hτ hpos),
    fun k => (hF k).1, fun k i => (hF k).2.1 i, fun k i => (hF k).2.2 i⟩

end Iter

/-- **the J6d target** (fields 4–6 of `T39J6Rest`, DEC-130B §5) for J3's arcs
`t39jA t39jArcChoice`, at every step `k` from the invariant `IsLocalSetDet0 P h 𝓑^•_{s_j}`,
`j ≤ k` -/
def T39K5FieldsJ3 (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTime D h z₀ τ →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ R ω) (tauR D h z₀ (2 * R) ω)) →
      ∀ m k, (∀ j ≤ k, IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀
          (t39j7S γ D c p P h z₀ R (t39jA t39jArcChoice D h z₀ τ m) τ j ω))) →
        T39K7Fields γ D c p P h z₀ R (t39jA t39jArcChoice D h z₀ τ m) τ k

/-- **`CONFThm3_9RestJ6`** with J3's arcs `t39jA t39jArcChoice` (separation, inclusion,
connectivity, disjointness: `t39jA_sep`, `t39jA_subset`, `t39jA_conn`, `t39jA_disj`) from the
J6d target (fields 4–6) -/
theorem confThm3_9RestJ6_of (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : CONFParams}
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) (HF : T39K5FieldsJ3 γ D c p) :
    CONFThm3_9RestJ6 γ D c p := by
  intro Ω _ P _ _ h hh z₀ R hR τ hτ hloc0 hτI
  have hgood := t39h_tau_ae h38 hγ hγ2 hD P h hh z₀ hR τ hτI
  have hg : ∀ᵐ ω ∂P, 0 < τ ω ∧ (D (h ω)).IsLength ∧
      Bornology.IsBounded (ballM (D (h ω)) z₀ (τ ω)) := by
    filter_upwards [hgood, hD.length P h (Tight.isGFFPlusCont_of_wp hh)] with ω h1 h2
    exact ⟨h1.1, h2, h1.2.2.2 _⟩
  have hpos : ∀ᵐ ω ∂P, 0 < τ ω := hg.mono fun ω hω => hω.1
  refine ⟨t39jA t39jArcChoice D h z₀ τ, t39jA_sep _ D h z₀ τ hg, fun m =>
    ⟨t39jA_subset _ D h z₀ τ m, ?_, ?_⟩⟩
  · filter_upwards [hg] with ω hω
    exact ⟨fun i hne => t39jA_conn _ hω m i hne, t39jA_disj _ hω m⟩
  · exact t39k7_rest h38 hγ hγ2 hD H35 hη hh hR hτ hpos hloc0
      (HF P h hh z₀ R hR τ hτ hτI m)

/-- **`CONFThm3_9RestCL`** from the J6d target (`confThm3_9RestCL_of_J6`) -/
theorem confThm3_9RestCL_of_K7 (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : CONFParams}
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) (HF : T39K5FieldsJ3 γ D c p) (χ : ℝ) :
    CONFThm3_9RestCL γ D c p χ :=
  confThm3_9RestCL_of_J6 h38 hγ hγ2 hD H35 hη
    (confThm3_9RestJ6_of h38 hγ hγ2 hD H35 hη HF) χ

end CONF
end LQGMetric
