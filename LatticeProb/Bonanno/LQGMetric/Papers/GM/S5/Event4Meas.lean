/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event4Meas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event3Loc

/-!
# GM Lemma 5.9: the measurability of `E_r`, condition by condition (task P2-M2M7)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.9
(`lem-geo-event-msrble`, l. 3293–3302). `L5_9meas` (`Event3Loc`) asks that `E_r` be null-measurable
for the law of the whole-plane GFF. `E_r` (`eventE`, GM l. 3240–3266) is the intersection of the
event of Lemma 5.8 (`linkEvent`, conditions (1)–(3)) and conditions (4)–(10):

* `eventE_eq`: `E_r = linkEvent ∩ C₄ ∩ ⋯ ∩ C₁₀` (`eventC4`, …, `eventC10`);
* `measurableSet_eventC10`: condition (10) is Borel (`𝓖_r` is finite, `bumpFam_finite_m2m2`, and
  `g ↦ (g, φ)_∇` is measurable);
* `L59MeasOf F`: the null-measurability of `F` for the law of every whole-plane GFF, under the
  hypotheses of `L5_9`; `l5_9meas_of_parts`: `L5_9meas` from `L59MeasOf` for `linkEvent` and
  conditions (4)–(9), hence `gm_L5_9_of_parts : L5_9`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the null-measurability of an event `F` of the field (depending on the data of `E_r`) for the
law of every whole-plane GFF, under the hypotheses of `L5_9` -/
def L59MeasOf (F : (DistC → ContMetric) → (DistC → ContMetric) → EData → (ℂ → ℂ → Set ℂ) →
    (Set ℂ → TestC) → (Set ℂ → TestC) → ℝ → Set DistC) : Prop :=
  ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs ≤ Cs →
  ∀ (S : EData), S.ξ = xiGamma γ → S.c = c → S.cs = cs → S.Cs = Cs → S.Ranges →
  ∀ (r : ℝ), 0 < r → ∀ (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC),
    IsTubeFam S U r → IsBumpChoice S U fb gb r →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → NullMeasurableSet (F D D' S U fb gb r) (P.map h)

/-- conditions (1)–(3) of `E_r`: the event of Lemma 5.8 -/
def eventL (D D' : DistC → ContMetric) (S : EData) (U : ℂ → ℂ → Set ℂ) (_fb _gb : Set ℂ → TestC)
    (r : ℝ) : Set DistC :=
  linkEvent D D' S.cs S.Cs S.c₁ S.η S.δ S.ρ S.b S.ε₀ r U

/-- condition (4) of `E_r` -/
def eventC4 (D _D' : DistC → ContMetric) (S : EData) (_U : ℂ → ℂ → Set ℂ) (_fb _gb : Set ℂ → TestC)
    (r : ℝ) : Set DistC :=
  {g | ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), ‖x - y‖ < S.δ * r →
      (D g).internal (annulus 0 r (4 * r)) ((3 / 2 : ℂ) * x) ((3 / 2 : ℂ) * y) ≤
        ENNReal.ofReal (S.Δ * scaleFac S.ξ S.c g r 0) ∧
      ENNReal.ofReal (S.Δ * scaleFac S.ξ S.c g r 0) ≤
        setDist (D g) (sphere 0 (2 * r)) (sphere 0 (3 * r))}

/-- condition (5) of `E_r` -/
def eventC5 (D _D' : DistC → ContMetric) (S : EData) (U : ℂ → ℂ → Set ℂ) (_fb _gb : Set ℂ → TestC)
    (r : ℝ) : Set DistC :=
  {g | ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
      internalDiam (D g) (U x y) (U x y) ≤ ENNReal.ofReal (S.A * scaleFac S.ξ S.c g r 0)}

/-- condition (6) of `E_r` -/
def eventC6 (D _D' : DistC → ContMetric) (S : EData) (U : ℂ → ℂ → Set ℂ) (_fb _gb : Set ℂ → TestC)
    (r : ℝ) : Set DistC :=
  {g | ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
      ∀ (P : ℝ → ℂ) (s t : ℝ), s ≤ t → ContinuousOn P (Icc s t) →
        P '' Icc s t ⊆ thickening (2 * S.ζ * r) (frontier (U x y)) →
        S.ε₀ * r / 100 ≤ diam (P '' Icc s t) →
        ENNReal.ofReal (100 * S.A * scaleFac S.ξ S.c g r 0) ≤ (D g).len P s t}

/-- condition (7) of `E_r` -/
def eventC7 (D _D' : DistC → ContMetric) (S : EData) (_U : ℂ → ℂ → Set ℂ) (_fb _gb : Set ℂ → TestC)
    (r : ℝ) : Set DistC :=
  {g | ∀ z₁ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ), ∀ z₂ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ),
      S.ζ * r ≤ ‖z₁ - z₂‖ →
        ENNReal.ofReal (S.a * scaleFac S.ξ S.c g r 0) ≤
          (D g).internal (annulus 0 (r / 4) (4 * r)) z₁ z₂}

/-- condition (8) of `E_r` -/
def eventC8 (D _D' : DistC → ContMetric) (S : EData) (_U : ℂ → ℂ → Set ℂ) (_fb _gb : Set ℂ → TestC)
    (r : ℝ) : Set DistC :=
  {g | ∀ x ∈ sphere (0 : ℂ) (2 * r),
      (D g).internal (annulus 0 r (4 * r)) ((3 / 2 : ℂ) * x) (((3 / 2 - S.θ : ℝ) : ℂ) * x) ≤
        ENNReal.ofReal (Real.exp (-S.ξ * S.Kf) * scaleFac S.ξ S.c g r 0)}

/-- condition (9) of `E_r` -/
def eventC9 (D _D' : DistC → ContMetric) (S : EData) (_U : ℂ → ℂ → Set ℂ) (_fb _gb : Set ℂ → TestC)
    (r : ℝ) : Set DistC :=
  {g | ∀ x ∈ sphere (0 : ℂ) (2 * r),
      internalDiam (D g) (lineTube S.θ r x) (lineTube S.θ r x) ≤
        ENNReal.ofReal (S.M * scaleFac S.ξ S.c g r 0)}

/-- condition (10) of `E_r` -/
def eventC10 (_D _D' : DistC → ContMetric) (S : EData) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC)
    (r : ℝ) : Set DistC :=
  {g | ∀ φ ∈ bumpFam S U fb gb r, |dirInner g φ| + gradEnergy φ / 2 ≤ S.Λ₀}

/-- `E_r` is the intersection of its conditions -/
theorem eventE_eq (D D' : DistC → ContMetric) (S : EData) (U : ℂ → ℂ → Set ℂ)
    (fb gb : Set ℂ → TestC) (r : ℝ) :
    eventE D D' S U fb gb r = eventL D D' S U fb gb r ∩ (eventC4 D D' S U fb gb r ∩
      (eventC5 D D' S U fb gb r ∩ (eventC6 D D' S U fb gb r ∩ (eventC7 D D' S U fb gb r ∩
        (eventC8 D D' S U fb gb r ∩ (eventC9 D D' S U fb gb r ∩
          eventC10 D D' S U fb gb r)))))) :=
  rfl

/-- **condition (10) is Borel**: `𝓖_r` is finite and `g ↦ (g, φ)_∇` is measurable -/
theorem measurableSet_eventC10 {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r)
    {U : ℂ → ℂ → Set ℂ} (hU : IsTubeFam S U r) (D D' : DistC → ContMetric)
    (fb gb : Set ℂ → TestC) : MeasurableSet (eventC10 D D' S U fb gb r) := by
  have e : eventC10 D D' S U fb gb r =
      ⋂ φ ∈ bumpFam S U fb gb r, {g : DistC | |dirInner g φ| + gradEnergy φ / 2 ≤ S.Λ₀} := by
    ext g; simp only [eventC10, mem_iInter]; rfl
  rw [e]
  exact MeasurableSet.biInter (bumpFam_finite_m2m2 hS hr hU fb gb).countable fun φ _ =>
    measurableSet_le ((continuous_abs.measurable.comp (measurable_evalDist (cmTest φ))).add_const _)
      measurable_const

/-- **`L5_9meas` from the measurability of the conditions (1)–(9)** -/
theorem l5_9meas_of_parts (hL : L59MeasOf eventL) (h4 : L59MeasOf eventC4)
    (h5 : L59MeasOf eventC5) (h6 : L59MeasOf eventC6) (h7 : L59MeasOf eventC7)
    (h8 : L59MeasOf eventC8) (h9 : L59MeasOf eventC9) : L5_9meas := by
  intro γ D D' c cs Cs hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB Ω _ P _ h hh
  rw [eventE_eq]
  exact (hL hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB P h hh).inter
    ((h4 hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB P h hh).inter
    ((h5 hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB P h hh).inter
    ((h6 hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB P h hh).inter
    ((h7 hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB P h hh).inter
    ((h8 hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB P h hh).inter
    ((h9 hPS hR hcs hCs S hξ hc hscs hsCs hS r hr U fb gb hU hB P h hh).inter
      (measurableSet_eventC10 hS hr hU D D' fb gb).nullMeasurableSet))))))

/-- **GM Lemma 5.9** from the measurability of the conditions (1)–(9) of `E_r` -/
theorem gm_L5_9_of_parts (h38 : DFGPSLem3_8) (hL : L59MeasOf eventL) (h4 : L59MeasOf eventC4)
    (h5 : L59MeasOf eventC5) (h6 : L59MeasOf eventC6) (h7 : L59MeasOf eventC7)
    (h8 : L59MeasOf eventC8) (h9 : L59MeasOf eventC9) : L5_9 :=
  gm_L5_9_of_meas h38 (l5_9meas_of_parts hL h4 h5 h6 h7 h8 h9)

end LQGMetric.GM
