/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.Assembly at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Events
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Lipschitz
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.Rates
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.WPCase34
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities

/-!
# [18] Proposition 4.10 on the frozen coupling: the per-root chain

Source: [18], proof of Proposition 4.10; DMS14 Lemma A.10.

**The two named inputs** (the estimates stated below):

* `ZeroConeCase0At D ρ` — [18] (4.40) for the 0-quantum cone `h₀` with its area-parametrized space-filling SLE
  `η₀` at the ambient radius `ρ`: `∃ q, α₀ > 0, A₀, C₀`, for every dyadic mesh `ε = 2^{-k}` (`k ≥ 1`) and every
  open `D ⊆ B_ρ(0)` with a continuous test `0 ≤ g ≤ M` on `D`, the event `E^ε_0(ρ) ∩ {∫_D g u^ε_* ≤ A₀ ∫_D g +
  ε^{α₀} M}` (`GlobalGood`, windows `≤ ε^q` on `B_ρ(0)`) fails with probability `≤ C₀ ε^{α₀}`. In [18] this is
  "Case 0" (Lemma 2.7 + Propositions 4.5 and 4.8, which [18] proves for the whole-plane GFF *and* the 0-cone,
  `[18]`). 
* `Lemma43Measurable D` — [18] Lemma 4.3 in measurable form: for every open `V ⊆ 𝔻`, `failSet` (a set of
  `(h|_V, η_L)`) is null-measurable for the laws of the γ-cone and of the 0-cone local data. 

**The chain** at one root `z₀` (`‖z₀‖ + r₁ ≤ 1`), for a test pair `(D, g)` in the recentred coordinates:

1. γ-cone: failure of the geometric good event for the recentred pair `(D − z₀, g(· + z₀))` puts the cone's local
   data on `V_c = B_{r₀}(−z₀)` in `failSet` (bridge, `mem_failSet_of_globalFail`);
2. law: the γ-cone field on `B_{r₁}(0)` with the IG data has the law of the translated Case 2 field
   `h₀(· + z₀) − γ log|·|` with the IG data re-rooted at `z₀` (`GMSCase.map_shiftedCase2_eq_cone`;
   [18]'s Cases 3–4 replaced by a pure translation, which removes the random mesh of [18] (4.41));
3. recentring: the translated Case 2 data in `failSet` for the recentred pair give the Case 2 data
   `h₀ − γ log|· − z₀|` on `V₀ = B_{r₀}(0)` in `failSet` for `(D, g)` (`mem_failSet_translate`).

`cone_le_case2` packages 1–3; `zeroCone_failSet_le` is the bridge at the 0-cone end; `case2_smallRoot_failSet_le`
applies the Cases 1–2 (A.10 rooting, Hölder, small-root conditioning) to `failSet`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
/-- **[18] Lemma 4.3, measurable form** (named input from [18] Lemma 4.3). -/
def Lemma43Measurable (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Prop :=
  ∀ (V : Opens ℂ), (V : Set ℂ) ⊆ ball (0 : ℂ) 1 →
    ∀ (ε : ℝ) (Dm : Set ℂ) (g : ℂ → ℝ) (A tol : ℝ) (R : Set ℂ) (r : ℝ),
      NullMeasurableSet (failSet γ V ε Dm g A tol R r)
          (P.map fun ω => (restrictTo V (coneField (X ω) (coneRadial γ γ (fun t => B t ω)
            (fun t => B' t ω))), ηL ω)) ∧
        NullMeasurableSet (failSet γ V ε Dm g A tol R r)
          (P.map fun ω => (restrictTo V (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
            (fun t => B₀' t ω))), ηL ω))

/-- **[18] (4.40) for the 0-quantum cone at radius `ρ`** (named input from Propositions 4.8 and 4.5). -/
def ZeroConeCase0At (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (ρ : ℝ) :
    Prop :=
  ∃ q α₀ A₀ C₀ : ℝ, 0 < q ∧ 0 < α₀ ∧ 0 ≤ A₀ ∧ 0 ≤ C₀ ∧
    ∀ k : ℕ, 1 ≤ k → ∀ (Dm : Set ℂ) (g : ℂ → ℝ) (M : ℝ), IsOpen Dm → Dm ⊆ ball (0 : ℂ) ρ →
      ContinuousOn g Dm → (∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
        P {ω | ¬ GlobalGood (η₀ ω) (CellFamily.mesh k) Dm g A₀ (CellFamily.mesh k ^ α₀ * M) (ball (0 : ℂ) ρ)
          (CellFamily.mesh k ^ q)} ≤ ENNReal.ofReal (C₀ * CellFamily.mesh k ^ α₀)

/-! ### The bridge hypotheses on the bundle -/

/-- Almost surely the γ-cone area exists, parametrizes `η = ηL ∘ φ`, and gives a bridge on every bounded open set. -/
theorem ae_bridge_cone (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) μ ∧
      ∃ φ : ℝ ≃o ℝ, (⇑(η ω) : ℝ → ℂ) = (ηL ω) ∘ φ ∧
        ∀ V : Opens ℂ, Bornology.IsBounded (V : Set ℂ) → BridgeHyp μ (ηL ω) φ V := by
  filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone D hγ, D.areaParam, D.spaceFilling]
    with ω hex hpar hsf
  obtain ⟨μ, hμ⟩ := hex
  obtain ⟨⟨φ, -, hφ⟩, harea⟩ := hpar
  have hηφ : (⇑(η ω) : ℝ → ℂ) = (ηL ω) ∘ φ := funext hφ
  refine ⟨μ, hμ, φ, hηφ, fun V hVb => ?_⟩
  refine ⟨(ηL ω).continuous, fun s t hst => ?_, hasFirstVisits_of_surjective hsf.1 hsf.2.1,
    hsf.2.1, V.isOpen, hVb⟩
  rw [← hηφ]
  exact harea μ hμ s t hst

/-- The same for the 0-cone and `η₀`. -/
theorem ae_bridge_zeroCone (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℂ, CellScaling.IsVagueLimitC (CellScaling.lqgAreaApprox γ
        (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))) μ ∧
      ∃ φ : ℝ ≃o ℝ, (⇑(η₀ ω) : ℝ → ℂ) = (ηL ω) ∘ φ ∧
        ∀ V : Opens ℂ, Bornology.IsBounded (V : Set ℂ) → BridgeHyp μ (ηL ω) φ V := by
  filter_upwards [MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ, D.areaParam₀, D.spaceFilling]
    with ω hex hpar hsf
  obtain ⟨μ, hμ⟩ := hex
  obtain ⟨⟨φ, -, hφ⟩, harea⟩ := hpar
  have hηφ : (⇑(η₀ ω) : ℝ → ℂ) = (ηL ω) ∘ φ := funext hφ
  refine ⟨μ, hμ, φ, hηφ, fun V hVb => ?_⟩
  refine ⟨(ηL ω).continuous, fun s t hst => ?_, hasFirstVisits_of_surjective hsf.1 hsf.2.1,
    hsf.2.1, V.isOpen, hVb⟩
  rw [← hηφ]
  exact harea μ hμ s t hst

/-! ### The 0-cone end -/

/-- **The 0-cone end**: the local failure event of the 0-cone is contained (a.s.) in the failure of the geometric
good event of `η₀`. -/
theorem zeroCone_failSet_le (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {V : Opens ℂ} (hVb : Bornology.IsBounded (V : Set ℂ)) {ε : ℝ} (hε : 0 < ε)
    {Dm R : Set ℂ} {g : ℂ → ℝ} {A tol r : ℝ} (hr : 0 ≤ r) (hDR : Dm ⊆ R)
    (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V) (hD : MeasurableSet Dm) :
    P {ω | (restrictTo V (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))),
        ηL ω) ∈ failSet γ V ε Dm g A tol R r} ≤
      P {ω | ¬ GlobalGood (η₀ ω) ε Dm g A tol R r} := by
  refine measure_mono_ae ?_
  filter_upwards [ae_bridge_zeroCone D hγ] with ω hω hmem
  obtain ⟨μ, hμ, φ, hηφ, hbr⟩ := hω
  have := globalFail_of_mem_failSet hμ (hbr V hVb) hε hr hDR hRV hD hmem
  change ¬ GlobalGood (η₀ ω) ε Dm g A tol R r
  rwa [hηφ]

/-! ### Images under translations -/

theorem image_add_image_sub (S : Set ℂ) (z₀ : ℂ) :
    (fun z => z + z₀) '' ((fun z => z - z₀) '' S) = S := by
  rw [image_image]
  simp

theorem measurableSet_image_sub {S : Set ℂ} (hS : MeasurableSet S) (z₀ : ℂ) :
    MeasurableSet ((fun z => z - z₀) '' S) := by
  rw [image_sub_eq_preimage_add]
  exact hS.preimage (measurable_id.add_const z₀)

/-! ### One root: the γ-cone event and the Case 2 event -/

/-- The γ-cone local data with the IG data. -/
theorem aemeasurable_coneData (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) :
    AEMeasurable (fun ω => (restrictTo V
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))),
        GMSCase1.wpAux hIG₀ U ηL ω)) P :=
  ((measurable_restrictTo _).comp_aemeasurable (GMSCase.aemeasurable_coneField D hγ)).prodMk
    (GMSCase1.aemeasurable_wpAux D hγ)

theorem measurable_shiftedField (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : Opens ℂ) (z₀ : ℂ) :
    Measurable fun ω => restrictTo V (GMSCase.shiftedCase2Field γ (GMSCase1.wpField X₀ ω) z₀) := by
  have hp : Measurable fun ω => ((GMSCase1.wpField X₀ ω, z₀) : DistC × ℂ) :=
    (GMSCase1.measurable_wpField D).prodMk measurable_const
  have e : Measurable ((restrictTo V) ∘ (fun q : DistC × ℂ => GMSCase.shiftedCase2Field γ q.1 q.2) ∘
      fun ω => ((GMSCase1.wpField X₀ ω, z₀) : DistC × ℂ)) :=
    (measurable_restrictTo _).comp ((GMSCase.measurable_shiftedCase2Field γ).comp hp)
  exact e

theorem aemeasurable_rerootAux (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] (z₀ : ℂ) :
    AEMeasurable (fun ω =>
      GMSCase.igTransformS (2 * Real.pi * igChi γ) 1 z₀ (GMSCase1.wpAux hIG₀ U ηL ω)) P := by
  have hq : AEMeasurable (fun ω => ((z₀, GMSCase1.wpAux hIG₀ U ηL ω) : ℂ × GMSCase1.AuxData)) P :=
    aemeasurable_const.prodMk (GMSCase1.aemeasurable_wpAux D hγ)
  have e : AEMeasurable ((fun q : ℂ × GMSCase1.AuxData =>
      GMSCase.igTransformS (2 * Real.pi * igChi γ) 1 q.1 q.2) ∘
        fun ω => ((z₀, GMSCase1.wpAux hIG₀ U ηL ω) : ℂ × GMSCase1.AuxData)) P :=
    (GMSCase.measurable_igTransformS (2 * Real.pi * igChi γ) 1).comp_aemeasurable hq
  exact e

/-- **The restricted law** (the `GMSCase.map_shiftedCase2_eq_cone`, restricted to `V ⊆ B_{r₁}(0)` and to the
curve coordinate). -/
theorem map_cone_eq_shifted (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] {r₁ : ℝ} (hr₁ : 0 < r₁) {z₀ : ℂ}
    (hz₀ : ‖z₀‖ + r₁ ≤ 1) {V : Opens ℂ} (hV : V ≤ ballO (0 : ℂ) r₁) :
    P.map (fun ω => (restrictTo V
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), ηL ω)) =
    P.map (fun ω => (restrictTo V (GMSCase.shiftedCase2Field γ (GMSCase1.wpField X₀ ω) z₀),
      MatedCRT.affineReroot z₀ 1 0 (ηL ω))) := by
  let Φ : DistOn (ballO (0 : ℂ) r₁) × GMSCase1.AuxData → DistOn V × C(ℝ, ℂ) := fun x =>
    (MoTPort.IG.GFFAbsCont.resOn V (ballO (0 : ℂ) r₁) x.1, x.2.2)
  have hΦ : Measurable Φ :=
    ((MoTPort.IG.GFFAbsCont.measurable_resOn V _).comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)
  have hPc := aemeasurable_coneData D hγ (ballO (0 : ℂ) r₁)
  have hPs : AEMeasurable (fun ω => (restrictTo (ballO (0 : ℂ) r₁)
      (GMSCase.shiftedCase2Field γ (GMSCase1.wpField X₀ ω) z₀),
        GMSCase.igTransformS (2 * Real.pi * igChi γ) 1 z₀ (GMSCase1.wpAux hIG₀ U ηL ω))) P :=
    (measurable_shiftedField D _ z₀).aemeasurable.prodMk (aemeasurable_rerootAux D hγ z₀)
  have hΦc : (fun ω => (restrictTo V
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), ηL ω)) =
      Φ ∘ (fun ω => (restrictTo (ballO (0 : ℂ) r₁)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))),
          GMSCase1.wpAux hIG₀ U ηL ω)) := by
    funext ω
    simp only [Function.comp_apply, Φ, MoTPort.IG.GFFAbsCont.resOn_restrictTo hV]
    rfl
  have hΦs : (fun ω => (restrictTo V (GMSCase.shiftedCase2Field γ (GMSCase1.wpField X₀ ω) z₀),
      MatedCRT.affineReroot z₀ 1 0 (ηL ω))) =
      Φ ∘ (fun ω => (restrictTo (ballO (0 : ℂ) r₁)
        (GMSCase.shiftedCase2Field γ (GMSCase1.wpField X₀ ω) z₀),
          GMSCase.igTransformS (2 * Real.pi * igChi γ) 1 z₀ (GMSCase1.wpAux hIG₀ U ηL ω))) := by
    funext ω
    simp only [Function.comp_apply, Φ, MoTPort.IG.GFFAbsCont.resOn_restrictTo hV]
    rfl
  rw [hΦc, hΦs, ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hPc,
    ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hPs,
    GMSCase.map_shiftedCase2_eq_cone D hγ hr₁ hz₀]

theorem ball_neg_subset {z₀ : ℂ} {r₀ r₁ : ℝ} (hr₀₁ : r₀ + ‖z₀‖ ≤ r₁) :
    ball (-z₀) r₀ ⊆ ball (0 : ℂ) r₁ := by
  intro y hy
  rw [mem_ball, dist_eq_norm, sub_neg_eq_add] at hy
  rw [mem_ball, dist_zero_right]
  calc ‖y‖ = ‖(y + z₀) - z₀‖ := by ring_nf
    _ ≤ ‖y + z₀‖ + ‖z₀‖ := norm_sub_le _ _
    _ < r₀ + ‖z₀‖ := by linarith
    _ ≤ r₁ := hr₀₁

theorem mem_ball_neg_iff (z₀ : ℂ) (r₀ : ℝ) (y : ℂ) :
    y ∈ ballO (-z₀) r₀ ↔ y + z₀ ∈ ballO (0 : ℂ) r₀ := by
  change dist y (-z₀) < r₀ ↔ dist (y + z₀) 0 < r₀
  rw [dist_zero_right, dist_eq_norm, sub_neg_eq_add]

/-- **The per-root chain** (γ-cone → translated Case 2 field → Case 2 field). For a root `z₀` with
`‖z₀‖ + r₁ ≤ 1` and `r₀ + ‖z₀‖ ≤ r₁`, failure of the γ-cone's good event for the recentred pair
`((D − z₀), g(· + z₀))` has at most the probability that the Case 2 data `(h₀ − γ log|· − z₀|)|_{B_{r₀}(0)}` with
`ηL` lie in `failSet` for `(D, g)`. -/
theorem cone_le_case2 (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] (hL : Lemma43Measurable D)
    {r₀ r₁ : ℝ} (hr₁ : 0 < r₁) {z₀ : ℂ} (hz₀ : ‖z₀‖ + r₁ ≤ 1)
    (hr₀₁ : r₀ + ‖z₀‖ ≤ r₁) {ε : ℝ} (hε : 0 < ε) {Dm R : Set ℂ} {g : ℂ → ℝ} {A tol r : ℝ}
    (hr : 0 ≤ r) (hDR : Dm ⊆ R) (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ ball (0 : ℂ) r₀)
    (hD : MeasurableSet Dm) :
    P {ω | ¬ GlobalGood (η ω) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
        ((fun z => z - z₀) '' R) r} ≤
      P {ω | (restrictTo (ballO (0 : ℂ) r₀) (GMSCase1.wpField X₀ ω +
          CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z₀‖)), ηL ω) ∈
        failSet γ (ballO (0 : ℂ) r₀) ε Dm g A tol R r} := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hVcball : (ballO (-z₀) r₀ : Set ℂ) ⊆ ball (0 : ℂ) r₁ := ball_neg_subset hr₀₁
  have hVc1 : (ballO (-z₀) r₀ : Set ℂ) ⊆ ball (0 : ℂ) 1 :=
    hVcball.trans (ball_subset_ball (by linarith [norm_nonneg z₀]))
  have hUV := mem_ball_neg_iff z₀ r₀
  -- step 1: the γ-cone side, through the bridge
  have hstep1 : P {ω | ¬ GlobalGood (η ω) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
      ((fun z => z - z₀) '' R) r} ≤
      P {ω | (restrictTo (ballO (-z₀) r₀)
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), ηL ω) ∈
          failSet γ (ballO (-z₀) r₀) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
            ((fun z => z - z₀) '' R) r} := by
    refine measure_mono_ae ?_
    filter_upwards [ae_bridge_cone D hγ] with ω hω hfail
    obtain ⟨μ, hμ, φ, hηφ, hbr⟩ := hω
    have hfail' : ¬ GlobalGood ((ηL ω) ∘ φ) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
        ((fun z => z - z₀) '' R) r := by
      rw [← hηφ]; exact hfail
    refine mem_failSet_of_globalFail hμ (hbr (ballO (-z₀) r₀) isBounded_ball) hε hr (image_mono hDR) ?_
      (measurableSet_image_sub hD z₀) hfail'
    rintro _ ⟨w, hw, rfl⟩ x hx
    have hx' : x + z₀ ∈ closedBall w (4 * r) := by
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      rwa [show x + z₀ - w = x - (w - z₀) by ring]
    exact (hUV x).2 (hRV w hw hx')
  -- step 2: the restricted law
  have hπc : AEMeasurable (fun ω => (restrictTo (ballO (-z₀) r₀)
      (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))), ηL ω)) P :=
    ((measurable_restrictTo _).comp_aemeasurable (GMSCase.aemeasurable_coneField D hγ)).prodMk
      D.measurable_curves.1.aemeasurable
  have hπs : AEMeasurable (fun ω => (restrictTo (ballO (-z₀) r₀)
      (GMSCase.shiftedCase2Field γ (GMSCase1.wpField X₀ ω) z₀),
        MatedCRT.affineReroot z₀ 1 0 (ηL ω))) P := by
    have hc : Measurable fun ω => MatedCRT.affineReroot z₀ 1 0 (ηL ω) := by
      have hp : Measurable fun ω => ((z₀, ηL ω) : ℂ × C(ℝ, ℂ)) :=
        measurable_const.prodMk D.measurable_curves.1
      have e : Measurable ((fun p : ℂ × C(ℝ, ℂ) => GMSCase.caseCurve 1 p.1 p.2) ∘
          fun ω => ((z₀, ηL ω) : ℂ × C(ℝ, ℂ))) :=
        (GMSCase.measurable_caseCurve 1).comp hp
      exact e
    exact (measurable_shiftedField D _ z₀).aemeasurable.prodMk hc.aemeasurable
  have hmaps := map_cone_eq_shifted D hγ hr₁ hz₀ (V := ballO (-z₀) r₀) hVcball
  have hnull := (hL (ballO (-z₀) r₀) hVc1 ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
    ((fun z => z - z₀) '' R) r).1
  have hstep2 := (Measure.map_apply₀ hπc hnull).symm.trans
    ((congrArg (fun m : Measure (DistOn (ballO (-z₀) r₀) × C(ℝ, ℂ)) => m _) hmaps).trans
      (Measure.map_apply₀ hπs (hmaps ▸ hnull)))
  -- step 3: recentring
  refine hstep1.trans (hstep2.le.trans (measure_mono_ae ?_))
  filter_upwards [D.spaceFilling] with ω hsf hmem
  have hfv : HasFirstVisits (ηL ω) := hasFirstVisits_of_surjective hsf.1 hsf.2.1
  have hmem' : (restrictTo (ballO (-z₀) r₀) (affineComp 1 z₀ (GMSCase1.wpField X₀ ω +
      CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z₀‖))), MatedCRT.affineReroot z₀ 1 0 (ηL ω)) ∈
      failSet γ (ballO (-z₀) r₀) ε ((fun z => z - z₀) '' Dm) (fun u => g (u + z₀)) A tol
        ((fun z => z - z₀) '' R) r := by
    rw [GMSCase.affineComp_one_case2_eq]
    exact hmem
  have := mem_failSet_translate hUV hfv hmem'
  rw [image_add_image_sub, image_add_image_sub] at this
  simpa only [sub_add_cancel] using this

/-! ### Cases 1–2 (the rooted cases) on `failSet` -/
/-- **Cases 0 (0-cone) → 1 → 2 on `failSet`**: the A.10 rooting, Hölder and small-root conditioning, applied to
The local failure event (made Borel by `toMeasurable`, using `Lemma43Measurable`). -/
theorem case2_smallRoot_failSet_le (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (hL : Lemma43Measurable D) {V₀ : Opens ℂ}
    (hV₀ : (V₀ : Set ℂ) ⊆ ball (0 : ℂ) 1) {ε : ℝ} {Dm R : Set ℂ} {g : ℂ → ℝ} {A tol r : ℝ}
    {p q : ℝ} (hpq : p.HolderConjugate q) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {δ : ℝ≥0∞}
    (hbad : P {ω | (restrictTo V₀ (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
        (fun t => B₀' t ω))), ηL ω) ∈ failSet γ V₀ ε Dm g A tol R r} ≤ δ) :
    (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ]
        {v : Ω × ℂ | (restrictTo V₀ (GMSCase1.wpField X₀ v.1 +
          CellScaling.ofFunC (fun w => -γ * Real.log ‖w - v.2‖)), ηL v.1) ∈
            failSet γ V₀ ε Dm g A tol R r} ≤
      GMSCase1.case1Moment D hγ p ^ (1 / p) * δ ^ (1 / q) / ENNReal.ofReal (κ ^ 2) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  set F := failSet γ V₀ ε Dm g A tol R r with hF
  set G₀ : Set (DistOn V₀ × GMSCase1.AuxData) := {x | (x.1, x.2.2) ∈ F} with hG₀
  set π₀ : Ω → DistOn V₀ × GMSCase1.AuxData := fun ω =>
    GMSCase1.restrictData V₀ (GMSCase1.zeroConeData γ X₀ hIG₀ B₀ B₀' U ηL ω) with hπ₀
  have hπ₀m : AEMeasurable π₀ P :=
    (GMSCase1.measurable_restrictData V₀).comp_aemeasurable
      ((GMS4.aemeasurable_prop48ZeroConeField D).prodMk (GMSCase1.aemeasurable_wpAux D hγ))
  set G := toMeasurable (P.map π₀) G₀ with hG
  have hGm : MeasurableSet G := measurableSet_toMeasurable _ _
  have proj_m : Measurable fun x : DistOn V₀ × GMSCase1.AuxData => (x.1, x.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hlaw : (P.map π₀).map (fun x : DistOn V₀ × GMSCase1.AuxData => (x.1, x.2.2)) =
      P.map fun ω => (restrictTo V₀ (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω)
        (fun t => B₀' t ω))), ηL ω) := by
    rw [AEMeasurable.map_map_of_aemeasurable proj_m.aemeasurable hπ₀m]
    rfl
  have hG₀null : NullMeasurableSet G₀ (P.map π₀) := by
    have h := (hL V₀ hV₀ ε Dm g A tol R r).2
    rw [← hlaw] at h
    exact h.preimage (proj_m.quasiMeasurePreserving _)
  have hV₀le : V₀ ≤ Blueprint.ballO (0 : ℂ) 1 := hV₀
  have hbad' : P ((fun ω => GMSCase1.restrictData V₀ (GMSCase1.wpData X₀ hIG₀ U ηL ω)) ⁻¹' G) ≤ δ := by
    rw [← GMSCase1.measure_restrictData_zeroConeData_preimage D hγ V₀ hV₀le hGm,
      ← Measure.map_apply_of_aemeasurable hπ₀m hGm, hG, measure_toMeasurable,
      Measure.map_apply₀ hπ₀m hG₀null]
    exact hbad
  refine le_trans (measure_mono_ae ?_) (GMSCase1.case2_smallRoot_local_event_le D hγ V₀ hV₀ hGm hpq hbad'
    hκ0 hκ1)
  have hac : (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ] ≪ Canon.rootedLaw P :=
    cond_absolutelyContinuous
  filter_upwards [hac.ae_le (GMSCase1.ae_case2Field_eq D)] with v hv hmem
  change GMSCase1.restrictData V₀ (GMSCase1.case2WPData γ X₀ hIG₀ U ηL v) ∈ G
  apply subset_toMeasurable
  change (restrictTo V₀ (Canon.case2Field γ (GMSCase1.wpField X₀ v.1) v.2),
    (GMSCase1.wpAux hIG₀ U ηL v.1).2) ∈ F
  rw [hv]
  exact hmem

end Coupling

end MatedCRTHarmonic.GMS4FO
