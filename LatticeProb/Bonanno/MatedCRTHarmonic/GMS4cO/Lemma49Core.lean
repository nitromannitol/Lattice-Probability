/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.Lemma49Core at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Freeze
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Rescale
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.FieldRecentre

/-!
# The core of [18] Lemma 4.9 for the 0-quantum cone

Source: [18], the proof of Lemma 4.9.

The proof of [18] conditions on the two circle averages `a = (h_r(z), h^IG_r(z))`, `r = ε^{q−4ζ}`, recentres by
`w ↦ z + r w`, and compares with the `ε`-uniform moments of [18] Theorem 4.4. Formally:

1. (`Rescale`) on `{diam η([τ_z − ε, τ_z + ε]) ≤ ε^q}` the source quantity at `(z, ε)` equals the masked quantity of
   the rescaled curve `η̂ = r⁻¹(η(τ_z + λ ·) − z)` at mesh `ε/λ`, `λ = e^{γ a₁} r^{γQ}` (the γ-LQG coordinate change
   (2.6));
2. ([18] (4.22), Lemma 4.3 — the *named input* `ZeroConeRescaledLocality` below) that masked quantity is almost
   surely `G(ε/λ, L)` for one jointly measurable `G`, where `L = (ĥ|_W, E_V(η̂_L))` is the local data of the
   recentred pair: the recentred field `ĥ = h(z + r ·) − h_r(z)` on `W ⊆ 𝔻` and the rational-point excursion data in
   `V` of the recentred Lebesgue-time curve `η̂_L = affineReroot z r 0 η_L`; the same `G` reads the unrecentred
   quantity of the 0-cone from `(h|_W, E_V(η_L))`;
3. (`FieldRecentre`, `IGRecentre`; [18] Lemma A.2 with Radon–Nikodym derivative `≡ 1`) `a ⟂ L` and
   `law(L) = law(h|_W, E_V(η_L))`;
4. (`Freeze`) hence `∫_{a ∈ A} Y ≤ sup_s E[obs_s(η)^p] · P(a ∈ A)` for every measurable `A`.

`ZeroConeRescaledLocality D obs W V` is exactly the content of (4.22) used in the source proof ("Let `X̂_{a₁,a₂}` be
The random variable which is determined by `(ĥ, ĥ^IG)` in the same manner that `u^{ε̂}_*(0) 1_{B^{ε̂}_0 ⊂ 𝔻}` is
determined by `(h, h^IG)|_𝔻` (c.f. Lemma 4.3)"): Lemma 4.3 at every centre and scale, written in the
recentred coordinates. It is **not proved here**; its producer is the measurable Lemma 4.3. Every other step is proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.L43O

attribute [local instance] Classical.propDecidable

/-- The time scale `λ = e^{γ a} r^{γQ}` of the γ-LQG coordinate change: `μ_{h(z + r·) − a} = λ⁻¹ (ψ⁻¹)_* μ_h`. -/
def timeScale (γ a r : ℝ) : ℝ := Real.exp (γ * a) * r ^ (γ * CellScaling.lqgQ γ)

theorem timeScale_pos (γ a : ℝ) {r : ℝ} (hr : 0 < r) : 0 < timeScale γ a r :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hr _)

theorem measurable_timeScale (γ r : ℝ) : Measurable fun a : ℝ => timeScale γ a r :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul_const _

/-- `affineReroot z₀ s φ` is Borel on continuous curves. -/
theorem measurable_affineReroot (z₀ : ℂ) (s φ : ℝ) :
    Measurable (affineReroot z₀ s φ : C(ℝ, ℂ) → C(ℝ, ℂ)) := by
  refine (GMS4c.measurableEmbedding_ratRestrict.measurable_comp_iff).1 ?_
  refine measurable_pi_iff.mpr fun t => ?_
  have hT : Measurable fun c : C(ℝ, ℂ) => firstHit c z₀ + s ^ 2 * (t : ℝ) :=
    (GMS4b.measurable_hitTime.comp (measurable_id.prodMk measurable_const)).add_const _
  have hev : Measurable fun c : C(ℝ, ℂ) => c (firstHit c z₀ + s ^ 2 * (t : ℝ)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk hT)
  change Measurable fun c : C(ℝ, ℂ) =>
    (((s : ℂ) * Complex.exp (φ * Complex.I))⁻¹) * (c (firstHit c z₀ + s ^ 2 * (t : ℝ)) - z₀)
  exact (hev.sub_const z₀).const_mul _

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **[18] (4.22) / Lemma 4.3 at every centre and scale, in recentred coordinates (named input).**
For an observable `obs s c` of a curve `c` at mesh `s` (in the application the masked `DA^s(0)` or `u^s_*(0)` with
`B^s_0 ⊆ B̄_θ(0)`), there is one jointly measurable `G` such that almost surely, for every mesh `s > 0`,
* the 0-cone's `obs s η₀ = G(s, (h₀|_W, E_V(η_L)))`;
* for every centre and radius with `B̄_r(z) ⊆ 𝔻`, the rescaled curve
  `η̂ = r⁻¹(η₀(τ_z + λ ·) − z)`, `λ = e^{γ h₀,r(z)} r^{γQ}`, has
  `obs s η̂ = G(s, ((h₀(z + r ·) − h₀,r(z))|_W, E_V(affineReroot z r 0 η_L)))`.
Source: [18] (Lemma 4.3), :2196–2201 ((4.22)), :2260–2266 (its use in the proof of Lemma 4.9). -/
def ZeroConeRescaledLocality
    (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (obs : ℝ → (ℝ → ℂ) → ℝ≥0∞) (W V : TopologicalSpace.Opens ℂ) : Prop :=
  ∃ G : ℝ × (DistOn W × (ℚ × ℚ → ℝ → ℂ)) → ℝ≥0∞, Measurable G ∧
    (∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      obs s (η₀ ω) = G (s, (restrictTo W (zeroConeField γ X₀ B₀ B₀' ω), excursionData V (ηL ω)))) ∧
    ∀ (z : ℂ) (r : ℝ), 0 < r → closedBall z r ⊆ ball (0 : ℂ) 1 → ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      obs s (rescaledCurve (η₀ ω) z r
          (timeScale γ (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) r)) =
        G (s, (restrictTo W (IGLaw.affField r 0 z (zeroConeField γ X₀ B₀ B₀' ω)),
          excursionData V (affineReroot z r 0 (ηL ω))))

/-- The marginal law of the second coordinate of a product with a probability measure. -/
theorem map_snd_of_map_eq_prod {Ω' α β : Type*} [MeasurableSpace Ω'] [MeasurableSpace α]
    [MeasurableSpace β] {Q : Measure Ω'} [IsProbabilityMeasure Q] {f : Ω' → α} {g : Ω' → β}
    (hf : AEMeasurable f Q) (hg : AEMeasurable g Q) {ν : Measure β} [SFinite ν]
    (h : Q.map (fun ω => (f ω, g ω)) = (Q.map f).prod ν) : Q.map g = ν := by
  have hfp : IsProbabilityMeasure (Q.map f) := inferInstance
  have := congrArg (fun μ : Measure (α × β) => μ.map Prod.snd) h
  rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (hf.prodMk hg),
    Measure.map_snd_prod, measure_univ, one_smul] at this
  exact this

/-- **The core of [18] Lemma 4.9 for the 0-cone.** Let `Y ≤ obs(ε/λ, η̂)^p` almost surely and suppose every
`ε`-slice of the 0-cone observable has `p`-th moment at most `C`. Given the named Lemma 4.3 input, for every
measurable set `A` of circle-average values,
`∫_{(h₀,r(z), h^IG_r(z)) ∈ A} Y ≤ C · P((h₀,r(z), h^IG_r(z)) ∈ A)`. -/
theorem lemma49_core
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {W V : TopologicalSpace.Opens ℂ}
    (hW : (W : Set ℂ) ⊆ ball (0 : ℂ) 1) (hVb : Bornology.IsBounded (V : Set ℂ)) {δ : ℝ}
    (hδ : 0 < δ)
    (hVδ : ((GMS4c.thickOpen V δ : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {obs : ℝ → (ℝ → ℂ) → ℝ≥0∞} (hloc : ZeroConeRescaledLocality D obs W V) {p : ℝ}
    {C : ℝ≥0∞} (hC : ∀ s : ℝ, 0 < s → ∫⁻ ω, obs s (η₀ ω) ^ p ∂P ≤ C)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : closedBall z r ⊆ ball (0 : ℂ) 1) {ε : ℝ} (hε : 0 < ε)
    {Y : Ω → ℝ≥0∞}
    (hY : ∀ᵐ ω ∂P, Y ω ≤ obs (ε / timeScale γ (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) r)
      (rescaledCurve (η₀ ω) z r (timeScale γ (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) r)) ^ p)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    ∫⁻ ω in (fun ω => (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z,
        circleAvg (hIG₀ ω) r z)) ⁻¹' A, Y ω ∂P ≤
      C * P ((fun ω => (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z,
        circleAvg (hIG₀ ω) r z)) ⁻¹' A) := by
  have := D.isProbabilityMeasure
  obtain ⟨G, hGm, hbase, hresc⟩ := hloc
  set h₀ : Ω → Field := zeroConeField γ X₀ B₀ B₀' with hh₀def
  have hh₀ : AEMeasurable h₀ P := GMS4.aemeasurable_prop48ZeroConeField D
  have hhIG : Measurable hIG₀ := D.igField.1.1.measurable
  have hηL : Measurable ηL := D.measurable_curves.1
  have hVW : (V : Set ℂ) ⊆ (GMS4c.thickOpen V δ : Set ℂ) := self_subset_thickening hδ _
  have hVc : ((V : Set ℂ)ᶜ).Nonempty := compl_nonempty_of_subset_ball (hVW.trans hVδ)
  -- the coordinates
  set a1 : Ω → ℝ := fun ω => circleAvg (h₀ ω) r z with ha1def
  set a2 : Ω → ℝ := fun ω => circleAvg (hIG₀ ω) r z with ha2def
  set L1 : Ω → DistOn W := fun ω => restrictTo W (IGLaw.affField r 0 z (h₀ ω)) with hL1def
  set L2 : Ω → ℚ × ℚ → ℝ → ℂ := fun ω => excursionData V (affineReroot z r 0 (ηL ω)) with hL2def
  set B1 : Ω → DistOn W := fun ω => restrictTo W (h₀ ω) with hB1def
  set B2 : Ω → ℚ × ℚ → ℝ → ℂ := fun ω => excursionData V (ηL ω) with hB2def
  have hf1 : Measurable fun x : Field => (circleAvg x r z, restrictTo W (IGLaw.affField r 0 z x)) :=
    (measurable_circleAvg_left r z).prodMk
      ((measurable_restrictTo W).comp (IGLaw.measurable_affField r 0 z))
  have hf2 : Measurable fun y : (Field × ℝ) × C(ℝ, ℂ) =>
      (circleAvg y.1.1 r z, excursionData V (affineReroot z r 0 y.2)) :=
    ((measurable_circleAvg_left r z).comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_excursionData V hVc).comp ((measurable_affineReroot z r 0).comp measurable_snd))
  have ha1 : AEMeasurable a1 P := (measurable_circleAvg_left r z).comp_aemeasurable hh₀
  have ha2 : AEMeasurable a2 P := ((measurable_circleAvg_left r z).comp hhIG).aemeasurable
  have hL1 : AEMeasurable L1 P :=
    ((measurable_restrictTo W).comp (IGLaw.measurable_affField r 0 z)).comp_aemeasurable hh₀
  have hL2 : AEMeasurable L2 P :=
    ((measurable_excursionData V hVc).comp ((measurable_affineReroot z r 0).comp hηL)).aemeasurable
  have hB1 : AEMeasurable B1 P := (measurable_restrictTo W).comp_aemeasurable hh₀
  have hB2 : AEMeasurable B2 P := ((measurable_excursionData V hVc).comp hηL).aemeasurable
  -- the two sides of the recentring
  have hF := map_circleAvg_restrict_affField_zeroCone D hγ hW hr hzr
  have hI := map_circleAvg_excursionData_affineReroot D V hVb hδ hVδ hr
    (hzr.trans ball_subset_closedBall)
  have hlaw1 : P.map L1 = P.map B1 := map_snd_of_map_eq_prod ha1 hL1 hF
  have hlaw2 : P.map L2 = P.map B2 := map_snd_of_map_eq_prod ha2 hL2 hI
  have h1 : IndepFun a1 L1 P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map ha1 hL1, hlaw1]
    exact hF
  have h2 : IndepFun a2 L2 P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map ha2 hL2, hlaw2]
    exact hI
  -- the cross independence: the cone field is independent of the IG data and its curve
  obtain ⟨Φ, hΦ, -, hroot, -, -⟩ := D.igMap
  have hIGdata : IndepFun h₀ (fun ω => (hIG₀ ω, U ω)) P :=
    GMS4.prop48_zeroCone_indepFun_IGdata D hγ
  have hcurve : IndepFun h₀ (fun ω => ((hIG₀ ω, U ω), ηL ω)) P := by
    have hg : Measurable fun x : Field × ℝ => (x, Φ (IGLaw.igCircleAvgInput x)) :=
      measurable_id.prodMk (hΦ.comp IGLaw.measurable_igCircleAvgInput)
    refine (hIGdata.comp measurable_id hg).congr (ae_of_all _ fun _ => rfl) ?_
    filter_upwards [hroot] with ω hω
    simp only [Function.comp]
    rw [hω]
    rfl
  have hcross : IndepFun (fun ω => (a1 ω, L1 ω)) (fun ω => (a2 ω, L2 ω)) P :=
    hcurve.comp hf1 hf2
  have hcrossB : IndepFun B1 B2 P :=
    hcurve.comp (measurable_restrictTo W)
      ((measurable_excursionData V hVc).comp measurable_snd)
  have hind : IndepFun (fun ω => (a1 ω, a2 ω)) (fun ω => (L1 ω, L2 ω)) P :=
    indepFun_prod_prod ha1 ha2 hL1 hL2 hcross h1 h2
  have hlawL : P.map (fun ω => (L1 ω, L2 ω)) = P.map (fun ω => (B1 ω, B2 ω)) := by
    have hL12 : IndepFun L1 L2 P := hcross.comp measurable_snd measurable_snd
    rw [(indepFun_iff_map_prod_eq_prod_map_map hL1 hL2).1 hL12,
      (indepFun_iff_map_prod_eq_prod_map_map hB1 hB2).1 hcrossB, hlaw1, hlaw2]
  -- freezing
  set Gp : (ℝ × ℝ) × (DistOn W × (ℚ × ℚ → ℝ → ℂ)) → ℝ≥0∞ :=
    fun x => G (ε / timeScale γ x.1.1 r, x.2) ^ p with hGpdef
  have hGpm : Measurable Gp := by
    refine (hGm.comp (Measurable.prodMk ?_ measurable_snd)).pow_const p
    exact measurable_const.div ((measurable_timeScale γ r).comp (measurable_fst.comp measurable_fst))
  have hM : ∀ x : ℝ × ℝ, ∫⁻ ω, Gp (x, (L1 ω, L2 ω)) ∂P ≤ C := by
    intro x
    set s := ε / timeScale γ x.1 r with hsdef
    have hs : 0 < s := div_pos hε (timeScale_pos γ _ hr)
    have hGs : Measurable fun ℓ : DistOn W × (ℚ × ℚ → ℝ → ℂ) => G (s, ℓ) ^ p :=
      (hGm.comp measurable_prodMk_left).pow_const p
    calc ∫⁻ ω, Gp (x, (L1 ω, L2 ω)) ∂P
        = ∫⁻ ℓ, G (s, ℓ) ^ p ∂(P.map fun ω => (L1 ω, L2 ω)) :=
          (lintegral_map' hGs.aemeasurable (hL1.prodMk hL2)).symm
      _ = ∫⁻ ℓ, G (s, ℓ) ^ p ∂(P.map fun ω => (B1 ω, B2 ω)) := by rw [hlawL]
      _ = ∫⁻ ω, G (s, (B1 ω, B2 ω)) ^ p ∂P := lintegral_map' hGs.aemeasurable (hB1.prodMk hB2)
      _ = ∫⁻ ω, obs s (η₀ ω) ^ p ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hbase] with ω hω
          rw [hω s hs]
      _ ≤ C := hC s hs
  have hYle : ∀ᵐ ω ∂P, Y ω ≤ Gp ((a1 ω, a2 ω), (L1 ω, L2 ω)) := by
    filter_upwards [hY, hresc z r hr hzr] with ω hYω hrω
    refine hYω.trans (le_of_eq ?_)
    rw [hrω _ (div_pos hε (timeScale_pos γ _ hr))]
  exact setLIntegral_le_of_le_comp_indep (ha1.prodMk ha2) (hL1.prodMk hL2) hind hGpm hM hYle hA

end Bundle

end MatedCRTHarmonic.L43O
