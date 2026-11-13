/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.LocalCurve at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Localized

/-!
# Localized observables read in Lebesgue time

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18]
(cited `[18]:N`), §4.2: the localized quantities
`DA^ε(z)`, `deg^ε_in(z)`, `deg^ε_out(z)`, `u^ε_*(z)` of (4.4)–(4.19) and Lemma 4.3 ("for each open `V`,
`DA^ε(z) 1(B̄^ε_z ⊂ V)` is a.s. determined by `h|_V` and `h^IG|_V`").

In [18] the curve `η` is the space-filling SLE parametrized by the LQG area `μ_h` of the field. The local
quantities at `z` only see `η` near its first visit to `z`, and only through *relative* area times. We therefore
read them from a Lebesgue-time curve `c` (the space-filling SLE `η_L`) and a measure `ν` (the LQG area,
restricted to an observation set `V`), with no global area-time curve:

* `sweep ν c σ u` is the signed `ν`-mass of `c([σ, σ + u])` (`u ≥ 0`) or `−ν(c([σ + u, σ]))` (`u < 0`);
* `relTime ν c σ s` is the first relative Lebesgue time at which the swept mass reaches `s`, clamped to the
  range of `sweep` (so that times beyond the swept mass stay at the last point of the support);
* `locCurve ν c z s = c(τ_z + relTime ν c τ_z s)`, `τ_z = GMS4b.hitTime c z`: the curve near its first visit to
  `z`, in `ν`-area time relative to that visit;
* `locU ν c ε z = GMS4b.locUStar ε (locCurve ν c z) 0` and `locWinDiam ν c ε z`: the localized `u^ε_*(z)` and
  window diameter (4.6);
* `LocalGood ν c ε D f A tol R r`: the window diameters are at most `r` on `R` and
  `∫⁻_D f u^ε_* ≤ A ∫⁻_D f + tol` (the event `G^ε_f` of (4.39)–(4.40) with the regularity event `E^ε_0`);
  `GlobalGood η …` is the same event for an area-parametrized curve `η` and the geometric `GMS4b.uStar`.

Everything here is deterministic. `GMS4FO/Bridge.lean` proves that `LocalGood (μ.restrict V) c` and
`GlobalGood (c ∘ φ)` agree when `c ∘ φ` is parametrized by `μ`-area and the degree balls lie in `V`;
`GMS4FO/Translate.lean` proves the exact translation covariance.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic

/-! ## Definitions -/

/-- The signed `ν`-mass swept by `c` between the root time `σ` and `σ + u`. -/
def sweep (ν : Measure ℂ) (c : ℝ → ℂ) (σ u : ℝ) : ℝ :=
  if 0 ≤ u then (ν (c '' Icc σ (σ + u))).toReal else -(ν (c '' Icc (σ + u) σ)).toReal

/-- The total mass swept after the root. -/
def sweepTop (ν : Measure ℂ) (c : ℝ → ℂ) (σ : ℝ) : ℝ := sSup (sweep ν c σ '' Ici 0)

/-- The total (negative) mass swept before the root. -/
def sweepBot (ν : Measure ℂ) (c : ℝ → ℂ) (σ : ℝ) : ℝ := sInf (sweep ν c σ '' Iic 0)

/-- The last relative time before which nothing is swept. -/
def sweepStart (ν : Measure ℂ) (c : ℝ → ℂ) (σ : ℝ) : ℝ :=
  sSup {u | sweep ν c σ u ≤ sweepBot ν c σ}

/-- The relative Lebesgue time at which the swept mass first reaches `s` (clamped to the swept range). -/
def relTime (ν : Measure ℂ) (c : ℝ → ℂ) (σ s : ℝ) : ℝ :=
  sInf {u | sweepStart ν c σ ≤ u ∧ min s (sweepTop ν c σ) ≤ sweep ν c σ u}

/-- The curve `c` near its first visit to `z`, in `ν`-area time relative to that visit. -/
def locCurve (ν : Measure ℂ) (c : ℝ → ℂ) (z : ℂ) (s : ℝ) : ℂ :=
  c (GMS4b.hitTime c z + relTime ν c (GMS4b.hitTime c z) s)

/-- The localized `u^ε_*(z)` (4.19) read from `(ν, c)`. -/
def locU (ν : Measure ℂ) (c : ℝ → ℂ) (ε : ℝ) (z : ℂ) : ℝ≥0∞ :=
  GMS4b.locUStar ε (locCurve ν c z) 0

/-- The localized window diameter `diam η([τ_z − ε, τ_z + ε])` read from `(ν, c)`. -/
def locWinDiam (ν : Measure ℂ) (c : ℝ → ℂ) (ε : ℝ) (z : ℂ) : ℝ :=
  diam (GMS4b.locWindow ε (locCurve ν c z) 0)

/-- The good event `E^ε_0 ∩ {∫_D f u^ε_* ≤ A ∫_D f + tol}` of (4.39)–(4.40), read from `(ν, c)`. -/
def LocalGood (ν : Measure ℂ) (c : ℝ → ℂ) (ε : ℝ) (D : Set ℂ) (f : ℂ → ℝ) (A tol : ℝ)
    (R : Set ℂ) (r : ℝ) : Prop :=
  (∀ z ∈ R, locWinDiam ν c ε z ≤ r) ∧
    (∫⁻ z in D, ENNReal.ofReal (f z) * locU ν c ε z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal tol

/-- The same event for an area-parametrized curve `η` and the geometric `u^ε_* = GMS4b.uStar`. -/
def GlobalGood (η : ℝ → ℂ) (ε : ℝ) (D : Set ℂ) (f : ℂ → ℝ) (A tol : ℝ) (R : Set ℂ) (r : ℝ) :
    Prop :=
  (∀ z ∈ R, GMS4b.windowDiam ε η z ≤ r) ∧
    (∫⁻ z in D, ENNReal.ofReal (f z) * GMS4b.uStar ε η z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal tol

/-! ## Elementary facts -/

theorem sweep_of_nonneg (ν : Measure ℂ) (c : ℝ → ℂ) (σ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    sweep ν c σ u = (ν (c '' Icc σ (σ + u))).toReal := by
  simp [sweep, hu]

theorem sweep_of_neg (ν : Measure ℂ) (c : ℝ → ℂ) (σ : ℝ) {u : ℝ} (hu : u < 0) :
    sweep ν c σ u = -(ν (c '' Icc (σ + u) σ)).toReal := by
  simp [sweep, not_le.2 hu]

/-- `GlobalGood` is monotone in the threshold and the tolerance. -/
theorem GlobalGood.mono {η : ℝ → ℂ} {ε : ℝ} {D : Set ℂ} {f : ℂ → ℝ} {A A' tol tol' : ℝ}
    {R : Set ℂ} {r : ℝ} (h : GlobalGood η ε D f A tol R r) (hA : A ≤ A') (htol : tol ≤ tol') :
    GlobalGood η ε D f A' tol' R r :=
  ⟨h.1, h.2.trans (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hA) le_rfl)
    (ENNReal.ofReal_le_ofReal htol))⟩

/-- `LocalGood` is monotone in the threshold and the tolerance. -/
theorem LocalGood.mono {ν : Measure ℂ} {c : ℝ → ℂ} {ε : ℝ} {D : Set ℂ} {f : ℂ → ℝ}
    {A A' tol tol' : ℝ} {R : Set ℂ} {r : ℝ} (h : LocalGood ν c ε D f A tol R r) (hA : A ≤ A')
    (htol : tol ≤ tol') : LocalGood ν c ε D f A' tol' R r :=
  ⟨h.1, h.2.trans (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hA) le_rfl)
    (ENNReal.ofReal_le_ofReal htol))⟩

end MatedCRTHarmonic.GMS4FO
