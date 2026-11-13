/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.Lemma49 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Core
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ZeroConeScalingCells

/-!
# [18] Lemma 4.9, conditional moments (4.24)–(4.25), for the 0-quantum cone

Source: [18] :

> **Lemma 4.9.** Suppose `h` is a whole-plane GFF with `h_1(0) = 0` and define the events `F^ε(z)` as above. There
> exists `ε_* = ε_*(ρ, γ) ∈ (0,1)` such that for each `p ≥ 1`,
> `E[1_{F^ε(z)} DA^ε(z)^p | h_{ε^{q−4ζ}}(z), h^IG_{ε^{q−4ζ}}(z)] ≲ 1` for all `z ∈ B_ρ(0)`, `ε ∈ (0, ε_*]` (4.24),
> and for each `p ∈ (1, 4/γ²)`, the same with `u^ε_*(z)` (4.25), with deterministic implicit constant depending only
> on `p`, `ρ`, `γ`.

**Model.** The statement is proved for the bundle's 0-quantum cone `h₀ = coneField X₀ (coneRadial γ 0 B₀ B₀')` with
its area-time curve `η₀` (frozen `areaParam₀`) and the IG field `hIG₀ + U`, which is a model of Proposition 4.1 in
[18] (: "`h` equal to either the circle-average embedding of a 0-quantum cone or a whole-plane GFF"). On
`𝔻` the 0-cone and the normalized whole-plane GFF agree in law ([18]; the
`GMS4.prop48_zeroCone_disk_law_eq_wholePlaneGFF`), so the source's whole-plane hypothesis enters only through
`h₀|_𝔻`. The curve `η₀` is the actual area-parametrized SLE of the bundle, so no whole-plane area-time curve has to
be constructed for this model.

**Form of the conditional bound.** `E[Y | a] ≤ C` almost surely is stated through set integrals: for every
measurable set `A ⊆ ℝ²` of circle-average values, `∫_{a ∈ A} Y ≤ C · P(a ∈ A)`
(`L43O.condExp_le_of_setIntegral_le` converts it to a `condExp` bound). The bound is proved for the larger observable
`1{diam η₀([τ_z − ε, τ_z + ε]) ≤ ε^q} · X`, hence for `1_{F^ε(z)} X` with any version of the remaining two conditions
of `F^ε(z)` (degree cap; circle averages, with or without the IG phase `U`). The constant `C` depends only on
`p` (and the coupling); it is uniform in `ρ`, `z` and `ε`, because the `ε`-uniform moments of [18] Theorem 4.4
hold at every mesh. `ε_*` depends on `ρ`, `q`, `ζ` only through `ε_*^{q−4ζ} < 1 − ρ` and `8 ε_*^{4ζ} ≤ 1`.

**Conditioning variables.** The pair `(h₀,r(z), hIG₀,r(z))` of the source (the normalized IG field, [18]),
with the phase `U` integrated out. Conditioning additionally on `U` would require the rotation invariance of the
observable given the phase (IGCO's `exists_igMap_package`); see the local interfaces.

**Named input.** `ZeroConeRescaledLocality` ([18] (4.22) = Lemma 4.3 at every centre and scale, in recentred
coordinates; producer: the measurable Lemma 4.3). Every other step is proved here.

Main results: `L43O.lemma49_zeroCone_uStar` ((4.25)), `L43O.lemma49_zeroCone_DA` ((4.24)),
`L43O.lemma49_zeroCone_uStar_condExp` (the `condExp` form), `L43O.lemma49_zeroCone_maskedUStar` (the masked
observable).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.L43O

attribute [local instance] Classical.propDecidable

/-! ## The scale choice -/

/-- The circle-average radius `ε^{q−4ζ}` of [18] (4.22). -/
def averageRadius (q ζ ε : ℝ) : ℝ := ε ^ (q - 4 * ζ)

/-- `ε_*` of [18] Lemma 4.9: `ε_*^{q−4ζ} ≤ (1−ρ)/2` and `ε_*^{4ζ} ≤ 1/8`. -/
def epsStar (ρ q ζ : ℝ) : ℝ :=
  min (1 / 2) (min (((1 - ρ) / 2) ^ (q - 4 * ζ)⁻¹) ((1 / 8 : ℝ) ^ (4 * ζ)⁻¹))

theorem epsStar_mem {ρ q ζ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    epsStar ρ q ζ ∈ Ioo (0 : ℝ) 1 := by
  have h1 : 0 < ((1 - ρ) / 2) ^ (q - 4 * ζ)⁻¹ := Real.rpow_pos_of_pos (by linarith [hρ.2]) _
  have h2 : 0 < (1 / 8 : ℝ) ^ (4 * ζ)⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨lt_min (by norm_num) (lt_min h1 h2), ?_⟩
  exact (min_le_left _ _).trans_lt (by norm_num)

/-- For `ε ≤ ε_*`, the radius `r = ε^{q−4ζ}` satisfies `r ≤ (1−ρ)/2`. -/
theorem averageRadius_le {ρ q ζ ε : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hζq : 4 * ζ < q) (hε : 0 < ε)
    (hεs : ε ≤ epsStar ρ q ζ) : averageRadius q ζ ε ≤ (1 - ρ) / 2 := by
  have hqz : 0 < q - 4 * ζ := by linarith
  have hb : 0 ≤ (1 - ρ) / 2 := by linarith [hρ.2]
  have hle : ε ≤ ((1 - ρ) / 2) ^ (q - 4 * ζ)⁻¹ :=
    hεs.trans ((min_le_right _ _).trans (min_le_left _ _))
  calc averageRadius q ζ ε = ε ^ (q - 4 * ζ) := rfl
    _ ≤ (((1 - ρ) / 2) ^ (q - 4 * ζ)⁻¹) ^ (q - 4 * ζ) :=
        Real.rpow_le_rpow hε.le hle hqz.le
    _ = (1 - ρ) / 2 := Real.rpow_inv_rpow hb hqz.ne'

/-- For `ε ≤ ε_*`, `8 ε^{4ζ} ≤ 1`. -/
theorem eight_mul_rpow_le {ρ q ζ ε : ℝ} (hζ : 0 < ζ) (hε : 0 < ε) (hεs : ε ≤ epsStar ρ q ζ) :
    8 * ε ^ (4 * ζ) ≤ 1 := by
  have h4 : 0 < 4 * ζ := by linarith
  have hle : ε ≤ (1 / 8 : ℝ) ^ (4 * ζ)⁻¹ :=
    hεs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have : ε ^ (4 * ζ) ≤ 1 / 8 :=
    calc ε ^ (4 * ζ) ≤ ((1 / 8 : ℝ) ^ (4 * ζ)⁻¹) ^ (4 * ζ) := Real.rpow_le_rpow hε.le hle h4.le
      _ = 1 / 8 := Real.rpow_inv_rpow (by norm_num) h4.ne'
  linarith

/-- For `ε ≤ ε_*` and `|z| < ρ`, `B̄_r(z) ⊆ 𝔻` and `4 ε^q ≤ r / 2`. -/
theorem scale_admissible {ρ q ζ ε : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hζ : 0 < ζ) (hζq : 4 * ζ < q)
    (hε : 0 < ε) (hεs : ε ≤ epsStar ρ q ζ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) :
    0 < averageRadius q ζ ε ∧ closedBall z (averageRadius q ζ ε) ⊆ ball (0 : ℂ) 1 ∧
      4 * ε ^ q ≤ 1 / 2 * averageRadius q ζ ε := by
  have hr : 0 < averageRadius q ζ ε := Real.rpow_pos_of_pos hε _
  refine ⟨hr, ?_, ?_⟩
  · intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball] at hz ⊢
    have hle := averageRadius_le hρ hζq hε hεs
    calc dist x 0 ≤ dist x z + dist z 0 := dist_triangle _ _ _
      _ < 1 := by linarith [hρ.2]
  · have hsplit : ε ^ q = averageRadius q ζ ε * ε ^ (4 * ζ) := by
      rw [averageRadius, ← Real.rpow_add hε]
      ring_nf
    have h8 := eight_mul_rpow_le (ρ := ρ) (q := q) hζ hε hεs
    rw [hsplit]
    nlinarith

/-! ## The bundle statements -/

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The conditioning pair `(h₀,r(z), hIG₀,r(z))` of [18] (4.24)–(4.25). -/
def circlePair (γ : ℝ) (X₀ hIG₀ : Ω → Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ) (r : ℝ) (z : ℂ)
    (ω : Ω) : ℝ × ℝ :=
  (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z, circleAvg (hIG₀ ω) r z)

/-- The diameter condition `diam η([τ_z − ε, τ_z + ε]) ≤ ε^q`, the first condition of `F^ε(z)`. -/
def diamEvent (η₀ : Ω → C(ℝ, ℂ)) (ε q : ℝ) (z : ℂ) : Set Ω :=
  {ω | GMS4b.windowDiam ε (η₀ ω) z ≤ ε ^ q}

/-- The local regions: `W = 𝔻` for the field and `V = B_{3/4}(0)` for the excursions, with `θ = 1/2`. -/
abbrev fieldRegion : TopologicalSpace.Opens ℂ := ballO 0 1

abbrev excursionRegion : TopologicalSpace.Opens ℂ := ballO 0 (3 / 4)

theorem thickOpen_excursionRegion_subset :
    ((GMS4c.thickOpen excursionRegion (1 / 8) : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆
      ball (0 : ℂ) 1 := by
  change thickening (1 / 8) (ball (0 : ℂ) (3 / 4)) ⊆ ball 0 1
  rw [_root_.thickening_ball (by norm_num) (by norm_num)]
  exact ball_subset_ball (by norm_num)

theorem isBounded_excursionRegion : Bornology.IsBounded ((excursionRegion : Set ℂ)) :=
  isBounded_ball

/-- The 0-cone curve hits every point at its first hitting time, almost surely. -/
theorem ae_hitTime_spec (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, η₀ ω (GMS4b.hitTime (η₀ ω) z) = z := by
  filter_upwards [D.areaParam₀, D.spaceFilling] with ω harea hspace z
  obtain ⟨φ, -, hη⟩ := harea.1
  have hφ : Tendsto φ (cocompact ℝ) (cocompact ℝ) :=
    φ.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hηfun : (η₀ ω : ℝ → ℂ) = (ηL ω) ∘ φ := funext hη
  have htrans : Tendsto (η₀ ω) (cocompact ℝ) (cocompact ℂ) := by
    rw [hηfun]
    exact hspace.2.1.comp hφ
  have hz : z ∈ range (η₀ ω) := by
    obtain ⟨t, ht⟩ := hspace.1 z
    exact ⟨φ.symm t, by rw [hη, φ.apply_symm_apply, ht]⟩
  exact GMS4b.hitTime_spec (η₀ ω).continuous htrans hz

/-- **Domination by the rescaled masked observable.** On `F¹ = {diam ≤ ε^q}`, `X^ε(z) = X^{ε/λ}(0)` of the rescaled
curve, and the latter is masked by `B^{ε/λ}_0 ⊆ B̄_{1/2}(0)`; off `F¹` the left side vanishes. -/
theorem ae_indicator_le_rescaled
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {Xo : ℝ → (ℝ → ℂ) → ℂ → ℝ≥0∞} {obs : ℝ → (ℝ → ℂ) → ℝ≥0∞}
    (hX : ∀ (c : ℝ → ℂ) (z : ℂ) (r l ε q : ℝ), c (GMS4b.hitTime c z) = z → 0 < r → 0 < l →
      GMS4b.windowDiam ε c z ≤ ε ^ q → 4 * ε ^ q ≤ 1 / 2 * r →
      Xo ε c z = obs (ε / l) (rescaledCurve c z r l))
    {p : ℝ} (hp : 0 < p) {z : ℂ} {r ε q : ℝ} (hr : 0 < r) (hθ : 4 * ε ^ q ≤ 1 / 2 * r) :
    ∀ᵐ ω ∂P, (diamEvent η₀ ε q z).indicator (fun ω => Xo ε (η₀ ω) z) ω ^ p ≤
      obs (ε / timeScale γ (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) r)
        (rescaledCurve (η₀ ω) z r
          (timeScale γ (circleAvg (zeroConeField γ X₀ B₀ B₀' ω) r z) r)) ^ p := by
  filter_upwards [ae_hitTime_spec D] with ω hω
  by_cases hF : ω ∈ diamEvent η₀ ε q z
  · rw [Set.indicator_of_mem hF]
    exact le_of_eq (by rw [hX _ z r _ ε q (hω z) hr (timeScale_pos γ _ hr) hF hθ])
  · rw [Set.indicator_of_notMem hF, ENNReal.zero_rpow_of_pos hp]
    exact bot_le

/-- **[18] (4.25) for the 0-quantum cone** (conditional on the named Lemma 4.3 input). There is
`ε_* = ε_*(ρ, q, ζ) ∈ (0,1)` such that for each `p ∈ [1, 4/γ²)` there is `C < ∞` with, for every `z ∈ B_ρ(0)`,
`ε ∈ (0, ε_*]` and measurable `A ⊆ ℝ²`,
`∫_{(h₀,r(z), hIG₀,r(z)) ∈ A} (1{diam ≤ ε^q} u^ε_*(z))^p ≤ C · P((h₀,r(z), hIG₀,r(z)) ∈ A)`, `r = ε^{q−4ζ}`. -/
theorem lemma49_zeroCone_uStar
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hloc : ZeroConeRescaledLocality D (maskedLocUStar (1 / 2)) fieldRegion excursionRegion)
    {ρ q ζ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hζ : 0 < ζ) (hζq : 4 * ζ < q) :
    epsStar ρ q ζ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ p : ℝ, 1 ≤ p → p < 4 / γ ^ 2 → ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ z ∈ ball (0 : ℂ) ρ, ∀ ε ∈ Ioc (0 : ℝ) (epsStar ρ q ζ),
          ∀ A : Set (ℝ × ℝ), MeasurableSet A →
            ∫⁻ ω in circlePair γ X₀ hIG₀ B₀ B₀' (averageRadius q ζ ε) z ⁻¹' A,
              (diamEvent η₀ ε q z).indicator (fun ω => GMS4b.uStar ε (η₀ ω) z) ω ^ p ∂P ≤
            C * P (circlePair γ X₀ hIG₀ B₀ B₀' (averageRadius q ζ ε) z ⁻¹' A) := by
  refine ⟨epsStar_mem hρ, fun p hp1 hpK => ?_⟩
  obtain ⟨C, hCtop, hC⟩ := CellScaling.ZeroConeScaling.uStarMoments_uniform D hγ p hp1 hpK
  refine ⟨C, hCtop, fun z hz ε hε A hA => ?_⟩
  obtain ⟨hr, hzr, hθ⟩ := scale_admissible hρ hζ hζq hε.1 hε.2 hz
  have hC' : ∀ s : ℝ, 0 < s → ∫⁻ ω, maskedLocUStar (1 / 2) s (η₀ ω) ^ p ∂P ≤ C := by
    intro s hs
    refine (lintegral_mono fun ω => ?_).trans (hC s hs)
    exact ENNReal.rpow_le_rpow (maskedLocUStar_le _ _ _) (by linarith)
  have hY := ae_indicator_le_rescaled (Xo := fun ε c z => GMS4b.uStar ε c z)
    (obs := maskedLocUStar (1 / 2)) D (fun c z r l ε q hcz hr hl hd hθ =>
      uStar_eq_maskedLocUStar_rescaled hcz hr hl hd hθ) (p := p) (z := z) (r := averageRadius q ζ ε) (ε := ε) (q := q) (by linarith) hr hθ
    (P := P) (X₀ := X₀) (B₀ := B₀) (B₀' := B₀')
  exact lemma49_core D hγ (W := fieldRegion) (V := excursionRegion) (fun x hx => hx)
    isBounded_excursionRegion (δ := 1 / 8) (by norm_num) thickOpen_excursionRegion_subset hloc
    hC' hr hzr hε.1 hY hA

/-- **[18] (4.24) for the 0-quantum cone** (conditional on the named Lemma 4.3 input): the same for
`DA^ε(z)` and every `p ≥ 1`. -/
theorem lemma49_zeroCone_DA
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hloc : ZeroConeRescaledLocality D (maskedLocDA (1 / 2)) fieldRegion excursionRegion)
    {ρ q ζ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hζ : 0 < ζ) (hζq : 4 * ζ < q) :
    epsStar ρ q ζ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ z ∈ ball (0 : ℂ) ρ, ∀ ε ∈ Ioc (0 : ℝ) (epsStar ρ q ζ),
          ∀ A : Set (ℝ × ℝ), MeasurableSet A →
            ∫⁻ ω in circlePair γ X₀ hIG₀ B₀ B₀' (averageRadius q ζ ε) z ⁻¹' A,
              (diamEvent η₀ ε q z).indicator (fun ω => GMS4b.areaRatio ε (η₀ ω) z) ω ^ p ∂P ≤
            C * P (circlePair γ X₀ hIG₀ B₀ B₀' (averageRadius q ζ ε) z ⁻¹' A) := by
  refine ⟨epsStar_mem hρ, fun p hp1 => ?_⟩
  have hmom := (CellScaling.ZeroConeScaling.cellMoments_uniform D hγ).1 p hp1
  refine ⟨∫⁻ ω, GMS4b.locDA 1 (η₀ ω) 0 ^ p ∂P, (hmom 1 one_pos).2, fun z hz ε hε A hA => ?_⟩
  obtain ⟨hr, hzr, hθ⟩ := scale_admissible hρ hζ hζq hε.1 hε.2 hz
  have hC' : ∀ s : ℝ, 0 < s →
      ∫⁻ ω, maskedLocDA (1 / 2) s (η₀ ω) ^ p ∂P ≤ ∫⁻ ω, GMS4b.locDA 1 (η₀ ω) 0 ^ p ∂P := by
    intro s hs
    refine (lintegral_mono fun ω => ?_).trans (le_of_eq (hmom s hs).1)
    exact ENNReal.rpow_le_rpow (maskedLocDA_le _ _ _) (by linarith)
  have hY := ae_indicator_le_rescaled (Xo := fun ε c z => GMS4b.areaRatio ε c z)
    (obs := maskedLocDA (1 / 2)) D (fun c z r l ε q hcz hr hl hd hθ =>
      areaRatio_eq_maskedLocDA_rescaled hcz hr hl hd hθ) (p := p) (z := z) (r := averageRadius q ζ ε) (ε := ε) (q := q) (by linarith) hr hθ
    (P := P) (X₀ := X₀) (B₀ := B₀) (B₀' := B₀')
  exact lemma49_core D hγ (W := fieldRegion) (V := excursionRegion) (fun x hx => hx)
    isBounded_excursionRegion (δ := 1 / 8) (by norm_num) thickOpen_excursionRegion_subset hloc
    hC' hr hzr hε.1 hY hA

end Bundle

end MatedCRTHarmonic.L43O
