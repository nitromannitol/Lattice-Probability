/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39J9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J8

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9, packet J6 (part 4): `T39JRestData` from the open part `T39J6Rest`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1543–1590; DEC-120 §5. For the iteration `t39j7S` (S3T39J7):

* `T39J6Rest`: the fields of `T39JRestData` which remain open — a.s. stopping times `s_{k+1}`,
  `IsLocalSetDet0` for `𝓑^•_{s_{k+1}}`, the a.s. inclusions `𝓕_k ⊆ 𝓕_{k+1}`, the a.s.
  `𝓕_k`-measurability of `n_k`, `x_{k,i}`, `Act k i`;
* the `k = 0` locality field `IsLocalSetDet0 P h 𝓑^•_τ` is an explicit hypothesis: it does not
  follow from `IsFilledBallStoppingTime D h z₀ τ` (a raw stopping time may depend on the additive
  constant of `h`; handoff/P2-CONFJ6.md), so `CONFThm3_9RestC` needs it as a hypothesis on `τ`
  (`CONFThm3_9RestCL`, `confThm3_9RestCL_of_J6`);
* **`t39j9_restData_of`**: `T39JRestData` from `T39J6Rest`, CONF Lemma 3.5 (`CONFLem3_5At`, for the
  a.s. finiteness of `σ^ε`), the arc properties, and P2-CONFJ1's `t39j_hAct`, `t39j_hxf`,
  `t39j_hstar_of`. Proved here: `s_0 = τ`, the a.s. recursion, `n_k`, `s_k ≥ 0`, `Measurable (s k)`
  (induction: `t39j7_measurable_stop`, `t39j8_measurable_succ`, `n_k` measurable from its
  `𝓕_k`-version on the complete space), `IsFilledBallStoppingTimeAE` for `s_0 = τ`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Function
open scoped ENNReal

namespace LQGMetric
namespace CONF

open Blueprint GM

variable {Ω : Type} [m0 : MeasurableSpace Ω]

/-- **the open part of packet J6**: the stopping-time, locality and `𝓕_k`-measurability fields of
`T39JRestData` (DEC-120 §5) for the iteration `t39j7S` -/
def T39J6Rest (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) (P : Measure Ω)
    (h : Ω → DistC) (z₀ : ℂ) (R : ℝ) {ι : Type} [Fintype ι] (I₀ : ι → Ω → Set ℂ)
    (τ : Ω → ℝ) : Prop :=
  (∀ k, IsFilledBallStoppingTimeAE P D h z₀ (t39j7S γ D c p P h z₀ R I₀ τ (k + 1))) ∧
  (∀ k, IsLocalSetDet0 P h
    (fun ω => filledBall (D (h ω)) z₀ (t39j7S γ D c p P h z₀ R I₀ τ (k + 1) ω))) ∧
  (∀ k, ∀ A : Set Ω, MeasurableSet[filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω))] A →
    AEEventIn P (filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ (k + 1) ω))) A) ∧
  (∀ k, ∃ g : Ω → ℕ, Measurable[filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω))] g ∧
    (fun ω => t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k) ω) =ᵐ[P] g) ∧
  (∀ k i, ∃ g : Ω → ℂ, Measurable[filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω))] g ∧
    t39jX D h z₀ R I₀ (t39j7S γ D c p P h z₀ R I₀ τ)
      (fun k => t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k)) k i =ᵐ[P] g) ∧
  (∀ k i, AEEventIn P (filledBallSigmaAt0 D h z₀
      (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω)))
    (t39jAct D h z₀ R I₀ (t39j7S γ D c p P h z₀ R I₀ τ)
      (fun k => t39j7N D h z₀ I₀ (t39j7S γ D c p P h z₀ R I₀ τ k)) k i))

/-- **`T39JRestData` from the open part `T39J6Rest`** (packets J2 and J6) -/
theorem t39j9_restData_of (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {a : ℝ} (ha : 0 < a) :
    ∃ N₁ : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      [P.IsComplete]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (p : CONFParams), CONFLem3_5At γ D c p →
      0 < p.η → ∀ (χ : ℝ) (z₀ : ℂ) (R : ℝ), 0 < R → ∀ {ι : Type} [Fintype ι]
      (I₀ : ι → Ω → Set ℂ) (τ : Ω → ℝ), IsFilledBallStoppingTime D h z₀ τ →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ R ω) (tauR D h z₀ (2 * R) ω)) →
      (∀ i ω, I₀ i ω ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω))) →
      (∀ᵐ ω ∂P, (∀ i, (I₀ i ω).Nonempty → IsPreconnected (I₀ i ω)) ∧
        Pairwise (Disjoint on fun i => I₀ i ω)) →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      T39J6Rest γ D c p P h z₀ R I₀ τ →
      T39JRestData γ D c p χ a N₁ P h z₀ R I₀ τ := by
  obtain ⟨N₁, hN⟩ := t39j_hstar_of h38 hγ hγ2 hD ha
  refine ⟨N₁, ?_⟩
  intro Ω _ P _ _ h hh p H35 hη χ z₀ R hR ι _ I₀ τ hτ hτI hI₀ hI₀c hloc0 hrest
  obtain ⟨hst', hloc', hmono, hnm, hxm, hActm⟩ := hrest
  have hloc : ∀ k, IsLocalSetDet0 P h
      (fun ω => filledBall (D (h ω)) z₀ (t39j7S γ D c p P h z₀ R I₀ τ k ω))
    | 0 => hloc0
    | k + 1 => hloc' k
  have hpos : ∀ᵐ ω ∂P, 0 < τ ω := hτI.mono fun ω hω => (t39h_tauR_pos D h z₀ hR ω).trans_le hω.1
  have hge := t39j7_ge_tau (I₀ := I₀) h38 hγ hγ2 hD H35 hη hh hR hτ hpos
  have hsnn := t39j7_hsnn (γ := γ) (c := c) (p := p) (R := R) (I₀ := I₀) hτ hpos
  -- `s_k` measurable, by induction (complete space)
  have hsm : ∀ k, Measurable (t39j7S γ D c p P h z₀ R I₀ τ k) := by
    intro k
    induction k with
    | zero => exact t39j7_measurable_stop hh hD.measurable hτ
    | succ k ih =>
      refine t39j8_measurable_succ hD hh p z₀ hR I₀ τ k ih ?_
      obtain ⟨g, hg, hng⟩ := hnm k
      have hle : filledBallSigmaAt0 D h z₀
          (fun ω => ENNReal.ofReal (t39j7S γ D c p P h z₀ R I₀ τ k ω)) ≤ ‹MeasurableSpace Ω› := by
        rw [t39h_fbs0_eq D h z₀ (hsnn k)]
        exact (localSigma0_le_localSigma h _).trans ((iInf_le _ 0).trans
          (gm_hullSigma_filledBall_le (P := P) hh (hD.measurable.comp hh.measurable) ih z₀ 0))
      exact (hg.mono hle le_rfl).congr_ae hng.symm
  have hst : ∀ k, IsFilledBallStoppingTimeAE P D h z₀ (t39j7S γ D c p P h z₀ R I₀ τ k)
    | 0 => hτ.ae P
    | k + 1 => hst' k
  set s := t39j7S γ D c p P h z₀ R I₀ τ with hsdef
  set n := fun k => t39j7N D h z₀ I₀ (s k) with hndef
  refine ⟨s, n, t39jX D h z₀ R I₀ s n, t39jAct D h z₀ R I₀ s n, hI₀, t39j7_hs0,
    t39j7_hsucc h38 hγ hγ2 hD H35 hη hh hR, t39j7_hn, hsnn, hsm, hst, hloc,
    hmono, hnm, hxm, ?_, hActm, t39j_hAct D h z₀ R I₀ s n, ?_⟩
  · refine t39j_hxf I₀ n fun k => ?_
    filter_upwards [hpos, hge, ae_mem_lenSet h38 hγ hγ2 hD P h hh] with ω h0 hk hlen
    exact ⟨h0.trans_le (hk k), isBounded_ballM_of_bc (LocalEvent.bcpt_of_mem_lenSet hlen) z₀ _⟩
  · refine hN P h hh p χ z₀ R hR I₀ τ s n (fun k ω => t39j7_hn k ω) hI₀ hI₀c ?_
    filter_upwards [hpos, hge, hτI] with ω h0 hk hI
    exact ⟨h0, hI.1, hk⟩

/-- **the arcs and the open part**: J3 (arc families with separation, inclusion, connectivity,
disjointness) and J6 (`T39J6Rest`) for every complete space, `τ` and `m` -/
def CONFThm3_9RestJ6 (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTime D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ R ω) (tauR D h z₀ (2 * R) ω)) →
      ∃ A : (m : ℕ) → Fin m → Ω → Set ℂ,
        (∀ᵐ ω ∂P, ∀ F : Finset ℂ, (F : Set ℂ) ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
          ∀ᶠ m in atTop, (∀ x ∈ F, ∃ i, x ∈ A m i ω) ∧
            ∀ i, ∀ x ∈ F, ∀ y ∈ F, x ∈ A m i ω → y ∈ A m i ω → x = y) ∧
        ∀ m, (∀ i ω, A m i ω ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω))) ∧
          (∀ᵐ ω ∂P, (∀ i, (A m i ω).Nonempty → IsPreconnected (A m i ω)) ∧
            Pairwise (Disjoint on fun i => A m i ω)) ∧
          T39J6Rest γ D c p P h z₀ R (A m) τ

/-- `CONFThm3_9RestC` (S3T39J5) with the additional hypothesis that `𝓑^•_τ` is a local set
modulo additive constants (the `k = 0` case of the field `hloc`) -/
def CONFThm3_9RestCL (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) (χ : ℝ) :
    Prop :=
  ∀ a ∈ Ioo (0 : ℝ) 1, ∃ N₁ : ℕ,
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTime D h z₀ τ →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      (∀ᵐ ω ∂P, τ ω ∈ Icc (tauR D h z₀ R ω) (tauR D h z₀ (2 * R) ω)) →
      ∃ A : (m : ℕ) → Fin m → Ω → Set ℂ,
        (∀ᵐ ω ∂P, ∀ F : Finset ℂ, (F : Set ℂ) ⊆ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
          ∀ᶠ m in atTop, (∀ x ∈ F, ∃ i, x ∈ A m i ω) ∧
            ∀ i, ∀ x ∈ F, ∀ y ∈ F, x ∈ A m i ω → y ∈ A m i ω → x = y) ∧
        ∀ m, T39JRestData γ D c p χ a N₁ P h z₀ R (A m) τ

/-- **`CONFThm3_9RestCL` from the arcs (J3) and `T39J6Rest`**, for parameters satisfying CONF
Lemma 3.5 (needed for the a.s. finiteness of `σ^ε`) -/
theorem confThm3_9RestCL_of_J6 (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : CONFParams}
    (H35 : CONFLem3_5At γ D c p) (hη : 0 < p.η) (H : CONFThm3_9RestJ6 γ D c p) (χ : ℝ) :
    CONFThm3_9RestCL γ D c p χ := by
  intro a ha
  obtain ⟨N₁, hN⟩ := t39j9_restData_of h38 hγ hγ2 hD ha.1
  refine ⟨N₁, ?_⟩
  intro Ω _ P _ _ h hh z₀ R hR τ hτ hloc0 hτI
  obtain ⟨A, hsep, hA⟩ := H P h hh z₀ R hR τ hτ hloc0 hτI
  refine ⟨A, hsep, fun m => ?_⟩
  obtain ⟨hsub, hcd, hrest⟩ := hA m
  exact hN P h hh p H35 hη χ z₀ R hR (A m) τ hτ hτI hsub hcd hloc0 hrest

end CONF
end LQGMetric
