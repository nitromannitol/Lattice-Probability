/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBUniform at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBRateCellFamily
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBMain
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsASource

/-!
# [18] Lemma 3.11 at every real mesh with a rate uniform in the radius

[18] Theorem 1.5 chooses the rate `α = α(γ)` before the radius `ρ`. The
first result (`lemma311Real_of_coupling`) had `∃ α` after `ρ`, because the annulus-disconnection / Lemma 3.8 chain
states its rates existentially. Here the chain is re-run with explicit rates (`EpsBRateAnnulus38`, `EpsBRateCellFamily`):

| step | rate |
|---|---|
| [18] Lemma 2.7 (`lemma27_real`, every radius) | `a₂₇ = α(q, γ)/2`, `q = 1/(2+γ)²` |
| [18] Proposition 4.10, source order (`epsA_prop410Source`) | `α₄.₁₀` (before `ρ`) |
| Proposition 2.10 on the band family (`bandFamily_prop210Bad_le`) | `a₂.₁₀ = α₄.₁₀/2` |
| One representative scale (`annulus38Rate_of_L27_G4`) | `min a₂₇ a₂.₁₀` |
| Representative-scale grid (`l38Rate_of_annulus38Rate`) — [18] Lemma 3.8, `α₈ = α(γ)` | `min a₂₇ a₂.₁₀ / 2` |
| itinerary (`itinRate_of_l38Rate`) | `aᵢ = min a₂₇ α₈` |
| Annulus-disconnection estimate (`sgcRate_of_itinRate`; grid exponent `χ = min a₂₇ aᵢ / 6 < α₈/3`) | `min a₂₇ aᵢ / 4` |
| [18] Lemma 3.11 (`lemma311Rate_of_sgc`), band → real mesh | unchanged |

So the final rate `chainRate a₂₇ a₂.₁₀` depends only on `γ` and the coupling (through `α₄.₁₀`), not on `ρ`.
The radius enters only the constants, the exponent `β` (via Lemma 3.8's `β₈` and the waypoint input) and `p` (via the
itinerary scale `s₀`). The diagonal argument (`uniform_fixedRate_of_bandSeq`) keeps the rate fixed and makes only
`(β, p, C)` independent of the band sequence.

* **`lemma311RealUniform_of_coupling`** — `∃ α > 0, ∀ ρ ∈ (0, 1), ∃ β p > 0, ∃ C, ∀ ε ∈ (0, 1),
  P (Lemma311GoodReal bm η ε ρ β p)ᶜ ≤ C ε^α`, for every frozen coupling.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.EpsB

open MatedCRTHarmonic

/-! ### The diagonal argument at a fixed rate -/

/-- **From every band sequence to every real mesh, at a fixed rate `α`.** As `uniform_rate_of_bandSeq`, but the rate
`α` is given and kept: if along every band sequence `b (θ k) β p ≤ C θₖ^α` for some `β, p > 0` and `C`, then
`b ε β p ≤ C ε^α` at every real `ε ∈ (0, 1)` with `β, p, C` independent of `ε`. -/
theorem uniform_fixedRate_of_bandSeq (b : ℝ → ℝ → ℝ → ℝ≥0∞) (hb1 : ∀ ε β p, b ε β p ≤ 1)
    (hmono : ∀ ε β p β' p', 0 < ε → ε < 1 → β' ≤ β → p' ≤ p → b ε β' p' ≤ b ε β p) {α : ℝ} (hα : 0 ≤ α)
    (h : ∀ θ, IsBandSeq θ → ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ k, b (θ k) β p ≤ ENNReal.ofReal (C * θ k ^ α)) :
    ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → b ε β p ≤ ENNReal.ofReal (C * ε ^ α) := by
  let τ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let Good : ℝ → ℕ → ℝ → Prop := fun ε n C => b ε (τ n) (τ n) ≤ ENNReal.ofReal (C * ε ^ α)
  have hn : ∀ ε n n' C, 0 < ε → ε < 1 → n ≤ n' → Good ε n C → Good ε n' C := by
    intro ε n n' C h0 h1 hnn' hg
    have hτ : τ n' ≤ τ n := inv_succ_anti hnn'
    exact (hmono ε (τ n) (τ n) (τ n') (τ n') h0 h1 hτ hτ).trans hg
  have hC : ∀ ε n C C', 0 < ε → ε < 1 → C ≤ C' → Good ε n C → Good ε n C' := by
    intro ε n C C' h0 _ hCC' hg
    exact hg.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg h0.le _)))
  have hbig : ∀ (n : ℕ) (δ : ℝ), 0 < δ → ∃ C, ∀ ε, δ ≤ ε → ε < 1 → Good ε n C := by
    intro n δ hδ
    refine ⟨(δ ^ α)⁻¹, fun ε hδε _ => (hb1 _ _ _).trans ?_⟩
    have hδpos : 0 < δ ^ α := Real.rpow_pos_of_pos hδ _
    have hle : δ ^ α ≤ ε ^ α := Real.rpow_le_rpow hδ.le hδε hα
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [inv_mul_eq_div, le_div_iff₀ hδpos, one_mul]
    exact hle
  have hθ : ∀ θ, IsBandSeq θ → ∃ n C, ∀ k, Good (θ k) n C := by
    intro θ hθb
    obtain ⟨β, hβ, p, hp, C, hbound⟩ := h θ hθb
    obtain ⟨n, hn'⟩ := exists_inv_succ_le (lt_min hβ hp)
    exact ⟨n, C, fun k => (hmono (θ k) β p (τ n) (τ n) (hθb.pos k) (hθb k).2.2
      (hn'.trans (min_le_left _ _)) (hn'.trans (min_le_right _ _))).trans (hbound k)⟩
  obtain ⟨n, C, hall⟩ := uniform_of_bandSeq Good hn hC hbig hθ
  exact ⟨τ n, inv_succ_pos n, τ n, inv_succ_pos n, C, hall⟩

/-! ### The explicit rate of the chain -/

/-- The rate of the explicit chain: `min a₂₇ aᵢ / 4` with `aᵢ = min a₂₇ (min a₂₇ a₂.₁₀ / 2)`. -/
def chainRate (a27 a210 : ℝ) : ℝ := min a27 (min a27 (min a27 a210 / 2)) / 4

theorem chainRate_pos {a27 a210 : ℝ} (ha27 : 0 < a27) (ha210 : 0 < a210) : 0 < chainRate a27 a210 := by
  unfold chainRate
  have h1 : 0 < min a27 a210 / 2 := half_pos (lt_min ha27 ha210)
  have h2 : 0 < min a27 (min a27 a210 / 2) := lt_min ha27 h1
  have h3 : 0 < min a27 (min a27 (min a27 a210 / 2)) := lt_min ha27 h2
  positivity

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- Lemma 2.7's diameter event on the band family, with its rate visible (the body of `bandFamily_lemma27Bad`). -/
theorem bandFamily_diameterGood_bad (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {θ : ℕ → ℝ} (hθb : IsBandSeq θ) {q ρ ρ'' α C : ℝ} (hq : 0 ≤ q) (hα : 0 < α) (hC : 0 ≤ C)
    (hρ : ρ < ρ'')
    (hL : ∀ ε ∈ Ioo (0 : ℝ) 1, P {ω | ¬ SegDiamGood (η ω) ε q ρ''} ≤ ENNReal.ofReal (C * ε ^ α)) (k : ℕ) :
    (bandFamily D θ hθb.pos).P (CellFamily.DiameterGood (bandFamily D θ hθb.pos) k q ρ)ᶜ ≤
      ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
  have hsub : (CellFamily.DiameterGood (bandFamily D θ hθb.pos) k q ρ)ᶜ ⊆
      (Subtype.val : BandSpace D θ hθb.pos → Ω) ⁻¹' {ω | ¬ SegDiamGood (η ω) (θ k) q ρ''} := by
    intro ω hω hgood
    apply hω
    intro x hx
    obtain ⟨w, hw1, hw2⟩ := hx
    refine bandFamily_diam_le_of_segDiamGood D θ hθb.pos hθb hq ω hgood x ⟨w, hw1, ?_⟩
    rw [mem_closedBall, dist_zero_right] at hw2
    rw [mem_ball, dist_zero_right]
    linarith
  calc (bandFamily D θ hθb.pos).P (CellFamily.DiameterGood (bandFamily D θ hθb.pos) k q ρ)ᶜ
      ≤ (bandFamily D θ hθb.pos).P ((Subtype.val : BandSpace D θ hθb.pos → Ω) ⁻¹'
          {ω | ¬ SegDiamGood (η ω) (θ k) q ρ''}) := measure_mono hsub
    _ ≤ P {ω | ¬ SegDiamGood (η ω) (θ k) q ρ''} :=
        (bandFamily_measurePreserving D θ hθb.pos).measure_preimage_le _
    _ ≤ ENNReal.ofReal (C * θ k ^ α) := hL (θ k) ⟨hθb.pos k, (hθb k).2.2⟩
    _ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (rpow_le_mesh_rpow hθb k hα.le) hC)

/-- **[18] Lemma 3.11 along a band sequence at the actual meshes `θₖ`, with the explicit rate
`chainRate a27 (α410/2)`**, from [18] Lemma 2.7 at real meshes at `ρ'` (rate `a27`) and Proposition 4.10 at real
meshes at `(ρ', 100)` (rate `α410`, exponent `β410`), `ρ < ρ' < 1`, `q = 1/(2+γ)²`. -/
theorem lemma311_bandSeq_rate (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo 0 2) {θ : ℕ → ℝ} (hθb : IsBandSeq θ) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hρ' : ρ' < 1) {a27 C27 α410 β410 A Cfail : ℝ} (ha27 : 0 < a27) (hC27 : 0 ≤ C27)
    (hL : ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ SegDiamGood (η ω) ε (1 / (2 + γ) ^ 2) ρ'} ≤ ENNReal.ofReal (C27 * ε ^ a27))
    (hα410 : 0 < α410) (hβ410 : 0 < β410) (hA : 0 ≤ A) (hCfail : 0 ≤ Cfail)
    (h410 : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible ε ρ' 100 β410 V f →
      P (BundleSec4.Prop410Bad η ε V f A (ε ^ α410)) ≤ ENNReal.ofReal (Cfail * ε ^ α410)) :
    ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ k, P (Lemma311GoodReal bm η (θ k) ρ β p)ᶜ ≤ ENNReal.ofReal (C * θ k ^ chainRate a27 (α410 / 2)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hden : 0 < (2 + γ) ^ 2 := by
    have : 0 < 2 + γ := by linarith [hγ.1]
    positivity
  have hq0 : 0 < q := by positivity
  have hq2 : q < 2 / (2 + γ) ^ 2 := by
    rw [hqdef]
    exact div_lt_div_of_pos_right (by norm_num) hden
  have hq1 : q < 1 := by
    have hfrac : 2 / (2 + γ) ^ 2 < 1 := (div_lt_iff₀ hden).mpr (by nlinarith [sq_nonneg γ, hγ.1])
    linarith
  set ρ₂ : ℝ := (ρ + ρ') / 2 with hρ₂def
  have hρ₂ : 0 < ρ₂ := by linarith
  have hρρ₂ : ρ < ρ₂ := by linarith
  have hρ₂ρ' : ρ₂ < ρ' := by linarith
  have ha210 : 0 < α410 / 2 := half_pos hα410
  set F := bandFamily D θ hθb.pos with hFdef
  have hconn := bandFamily_graphConnected D θ hθb.pos
  have hloop := bandFamily_graphLoopless D θ hθb.pos
  have hpeano := bandFamily_peanosphereG0 D θ hθb.pos
  have h27G3 := bandFamily_cellDiamBound_bad D θ hθb.pos hθb hq0.le ha27 hC27 hL
  have hDiam := bandFamily_diameterGood_bad D hθb hq0.le ha27 hC27 hρ₂ρ' hL
  have h210 : ∀ k (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible (CellFamily.mesh k) ρ' 100 β410 V f →
      F.P (GMS4.Prop210Bad F k V f (2 * A) (CellFamily.mesh k ^ (α410 / 2))) ≤
        ENNReal.ofReal ((Cfail + 2) * CellFamily.mesh k ^ (α410 / 2)) := fun k V f hadm =>
    bandFamily_prop210Bad_le D θ hθb.pos hθb hadm.2.2.2.2.2.2.1.measurableSet hα410 hCfail
      (h410 (θ k) ⟨hθb.pos k, (hθb k).2.2⟩ V f (prop210Admissible_mono (hθb.pos k) (hθb k).2.1 hadm))
  have hW : Annulus38Rate F ρ₂ (min a27 (α410 / 2)) :=
    annulus38Rate_of_L27_G4 F hρ₂ hρ₂ρ' hρ' hq0 hq1 hβ410 ha210 ha27 hA hC27 (by linarith) hpeano h27G3 h210
  have hmin : 0 < min a27 (α410 / 2) := lt_min ha27 ha210
  have h38 : L38Rate F ρ₂ (min a27 (α410 / 2) / 2) := l38Rate_of_annulus38Rate F ρ₂ hmin hW
  have hItin : ItinRate F ρ₂ (min a27 (min a27 (α410 / 2) / 2)) :=
    itinRate_of_l38Rate F q ρ₂ ha27 hDiam (half_pos hmin) h38 hconn hloop hq0
      (CellFamily.waypointStrongMarkovInputFixed2_holds F q ρ₂)
  obtain ⟨χ, β, p, C, hχ, hβ, hβmin, hp, h26⟩ :=
    sgcRate_of_itinRate F γ ρ₂ q hγ ⟨hρ₂, hρ₂ρ'.trans hρ'⟩ ⟨hq0, hq2⟩ ha27 hDiam
      (lt_min ha27 (half_pos hmin)) hItin (CellFamily.finiteGridCount_holds ρ₂) hconn
      (CellFamily.templateSeparation_of_peanosphereG0 F hpeano)
  have hrate := chainRate_pos ha27 ha210
  obtain ⟨C', hC'⟩ := lemma311Rate_of_sgc F hconn hβ (lt_of_lt_of_le hβmin (min_le_left _ _))
    (lt_of_lt_of_le hβmin (min_le_right _ _)) hrate hp hρρ₂ h26
  refine ⟨β / 2, by positivity, p, hp, max C' 0 * 2 ^ chainRate a27 (α410 / 2) + 2 ^ chainRate a27 (α410 / 2),
    fun k => ?_⟩
  refine ofReal_mesh_le_band hθb hrate.le k prob_le_one fun hk => ?_
  refine (measure_le_of_bandFamily D hθb.pos (Lemma311GoodReal bm η (θ k) ρ (β / 2) p)ᶜ
    (T15A.Lemma311Good F k ρ β p)ᶜ (fun ω hω hgood => hω ?_)).trans (hC' k)
  exact ⟨(bandSpace_good D θ hθb.pos ω).locFin k, bandEmbedding D θ hθb.pos ω k,
    fun x => bandEmbedding_cell D θ hθb.pos ω k x,
    lemma311Holds_of_floor_le hgood (mesh_rpow_le_band_rpow_half hθb hk hβ.le)⟩

/-- **[18] Lemma 3.11 at every real mesh with a rate uniform in the radius**, for the embedded mated-CRT map of every
frozen mating-of-trees coupling (standard Borel, `γ ∈ (0, 2)`): there is `α > 0` (depending only on `γ` and the
coupling) such that for every `ρ ∈ (0, 1)` there are `β, p > 0` and `C` with `P[(3.35) fails at mesh ε] ≤ C ε^α` for
every `ε ∈ (0, 1)`. The rate is `chainRate (α(q,γ)/2) (α₄.₁₀/2)`, `q = 1/(2+γ)²`, with the source-order
exponent `α₄.₁₀` of Proposition 4.10. -/
theorem lemma311RealUniform_of_coupling (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ β : ℝ, 0 < β ∧ ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ,
      ∀ ε : ℝ, 0 < ε → ε < 1 → P (Lemma311GoodReal bm η ε ρ β p)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  set q : ℝ := 1 / (2 + γ) ^ 2 with hqdef
  have hden : 0 < (2 + γ) ^ 2 := by
    have : 0 < 2 + γ := by linarith [hγ.1]
    positivity
  have hq0 : 0 < q := by positivity
  have hq2 : q < 2 / (2 + γ) ^ 2 := by
    rw [hqdef]
    exact div_lt_div_of_pos_right (by norm_num) hden
  have hexp : 0 < GMSLemma27.lemma27Exponent q γ := GMSLemma27.lemma27Exponent_pos hγ.1 hq0 hq2
  set a27 : ℝ := GMSLemma27.lemma27Exponent q γ / 2 with ha27def
  have ha27 : 0 < a27 := by positivity
  have ha27lt : a27 < GMSLemma27.lemma27Exponent q γ := by linarith
  obtain ⟨α410, hα410, β410, hβ410, hsrc⟩ := GMSMain.epsA_prop410Source D hstd hγ
  refine ⟨chainRate a27 (α410 / 2), chainRate_pos ha27 (half_pos hα410), fun ρ hρ hρ1 => ?_⟩
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'def
  have hρρ' : ρ < ρ' := by linarith
  have hρ' : ρ' < 1 := by linarith
  obtain ⟨A, hA, hCh⟩ := hsrc ρ' (by linarith) hρ'
  obtain ⟨Cfail, hCfail, h410⟩ := hCh 100 (by norm_num)
  obtain ⟨C27, hC27, hL⟩ := lemma27_real D hstd hγ hq0 hq2 (by linarith : 0 < ρ') hρ' ha27lt
  refine uniform_fixedRate_of_bandSeq (fun ε β p => P (Lemma311GoodReal bm η ε ρ β p)ᶜ)
    (fun _ _ _ => prob_le_one) ?_ (chainRate_pos ha27 (half_pos hα410)).le
    (fun θ hθb => lemma311_bandSeq_rate D hγ hθb hρ hρρ' hρ' ha27 hC27 hL hα410 hβ410 hA.le hCfail h410)
  intro ε β p β' p' h0 h1 hβ hp
  exact measure_mono (compl_subset_compl.mpr (lemma311GoodReal_mono h0 h1.le hβ hp))

end Coupling

end MatedCRTHarmonic.GMSMain.EpsB
