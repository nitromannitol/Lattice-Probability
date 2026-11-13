/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MatedCRT.BrownianG0SideStrict at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0NearZero
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DLevels

/-!
# Strict side condition for a correlated Brownian path

For a fixed mesh and coordinate, equality in the side condition would give two minimizers on a
compact interval. Brownian uniqueness identifies them at the shared endpoint, and immediate
oscillation rules out that endpoint as a minimizer.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRTHarmonic.MatedCRT

private theorem shiftedPath_eval {i : Fin 2} {p t : ℝ} {ω : Path2} (ht : 0 ≤ t) :
    MatedCRTHarmonic.MoTPort.BMLocalMin.path (shiftedCoordinate i p) ω t =
      lrCoord i (p + t) ω - lrCoord i p ω := by
  simp [MatedCRTHarmonic.MoTPort.BMLocalMin.path, shiftedCoordinate, Real.toNNReal_of_nonneg ht]

private theorem shifted_isMinOn_of_isMinOn {i : Fin 2} {ω : Path2} {p a b x : ℝ}
    (hpa : p ≤ a) (hx : x ∈ Icc a b)
    (hmin : IsMinOn (lrCoord i · ω) (Icc a b) x) :
    IsMinOn (MatedCRTHarmonic.MoTPort.BMLocalMin.path (shiftedCoordinate i p) ω)
      (Icc (a - p) (b - p)) (x - p) := by
  rw [isMinOn_iff] at hmin ⊢
  intro u hu
  have hu' : u + p ∈ Icc a b := by
    constructor <;> linarith [hu.1, hu.2]
  have hval := hmin (u + p) hu'
  have hx0 : 0 ≤ x - p := by linarith [hx.1]
  have hu0 : 0 ≤ u := by linarith [hu.1]
  rw [shiftedPath_eval hx0, shiftedPath_eval hu0]
  have hxp : p + (x - p) = x := by ring
  have hup : p + u = u + p := add_comm _ _
  rw [hxp, hup]
  linarith

private theorem ae_sideStrict_pair {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (ε : ℝ) (hε : 0 < ε)
    (x y : ℤ) (hxy : x + 1 < y) :
    ∀ᵐ ω ∂μ,
      SideCond ε (lrCoord i · ω) x y →
      max (intervalInf (lrCoord i · ω) (ε * ((x : ℝ) - 1)) (ε * x))
          (intervalInf (lrCoord i · ω) (ε * ((y : ℝ) - 1)) (ε * y)) <
        intervalInf (lrCoord i · ω) (ε * x) (ε * ((y : ℝ) - 1)) := by
  let a : ℝ := ε * ((x : ℝ) - 1)
  let b : ℝ := ε * x
  let c : ℝ := ε * ((y : ℝ) - 1)
  let d : ℝ := ε * y
  have hab : a < b := by dsimp [a, b]; nlinarith
  have hbc : b < c := by
    have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
    dsimp [b, c]
    nlinarith
  have hcd : c < d := by dsimp [c, d]; nlinarith
  letI : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hUnique₁ := MatedCRTHarmonic.MoTPort.BMLocalMin.ae_isMinOn_unique
    (shiftedCoordinate_isBrownianReal hμ i a) (a := 0) (b := c - a) le_rfl
  have hUnique₂ := MatedCRTHarmonic.MoTPort.BMLocalMin.ae_isMinOn_unique
    (shiftedCoordinate_isBrownianReal hμ i b) (a := 0) (b := d - b) le_rfl
  have hNeg₁ := BrownianG0NearZero.ae_negative_near_zero
    (shiftedCoordinate_isBrownianReal hμ i b)
    (fun t => (measurable_lrCoord (i, b + (t : ℝ))).sub
      (measurable_lrCoord (i, b)))
  have hNeg₂ := BrownianG0NearZero.ae_negative_near_zero
    (shiftedCoordinate_isBrownianReal hμ i c)
    (fun t => (measurable_lrCoord (i, c + (t : ℝ))).sub
      (measurable_lrCoord (i, c)))
  filter_upwards [hUnique₁, hUnique₂, hNeg₁, hNeg₂] with ω hU₁ hU₂ hN₁ hN₂
  intro hside
  let X : ℝ → ℝ := fun t => lrCoord i t ω
  let m₁ := intervalInf X a b
  let m₂ := intervalInf X c d
  let m₀ := intervalInf X b c
  have hX : Continuous X := by
    dsimp [X]
    by_cases hi : i = 0
    · subst i
      simp only [lrCoord, ↓reduceIte]
      exact continuous_fst.comp ω.continuous
    · simp only [lrCoord, hi, ↓reduceIte]
      exact continuous_snd.comp ω.continuous
  have hm₁m₀ : max m₁ m₂ ≤ m₀ := by
    simpa [SideCond, X, m₁, m₂, m₀, a, b, c, d] using hside
  by_contra hstrict
  have hnot : ¬ max m₁ m₂ < m₀ := by
    intro hlt
    apply hstrict
    simpa only [X, m₁, m₂, m₀, a, b, c, d] using hlt
  have hm₁ : m₁ ≤ m₀ := (le_max_left m₁ m₂).trans hm₁m₀
  have hm₂ : m₂ ≤ m₀ := (le_max_right m₁ m₂).trans hm₁m₀
  by_cases heq₁ : m₁ = m₀
  · -- Equality of the left outer and middle minima.
    obtain ⟨s, hs, hXs⟩ :=
      (RouteM.DAux.intervalInf_spec hX hab.le).1
    obtain ⟨t, ht, hXt⟩ :=
      (RouteM.DAux.intervalInf_spec hX hbc.le).1
    have hXs₁ : X s = m₁ := by simpa only [m₁] using hXs
    have hXt₀ : X t = m₀ := by simpa only [m₀] using hXt
    have hminS : IsMinOn X (Icc a c) s := by
      rw [isMinOn_iff]
      intro z hz
      rcases le_total z b with hzb | hbz
      · have hz' : z ∈ Icc a b := ⟨hz.1, hzb⟩
        have hlower : m₁ ≤ X z := by
          simpa only [m₁] using (RouteM.DAux.intervalInf_spec hX hab.le).2 z hz'
        calc
          X s = m₁ := hXs₁
          _ ≤ X z := hlower
      · have hz' : z ∈ Icc b c := ⟨hbz, hz.2⟩
        have hlower : m₀ ≤ X z := by
          simpa only [m₀] using (RouteM.DAux.intervalInf_spec hX hbc.le).2 z hz'
        calc
          X s = m₁ := hXs₁
          _ = m₀ := heq₁
          _ ≤ X z := hlower
    have hminT : IsMinOn X (Icc a c) t := by
      rw [isMinOn_iff]
      intro z hz
      rcases le_total z b with hzb | hbz
      · have hz' : z ∈ Icc a b := ⟨hz.1, hzb⟩
        have hlower : m₁ ≤ X z := by
          simpa only [m₁] using (RouteM.DAux.intervalInf_spec hX hab.le).2 z hz'
        calc
          X t = m₀ := hXt₀
          _ = m₁ := heq₁.symm
          _ ≤ X z := hlower
      · have hz' : z ∈ Icc b c := ⟨hbz, hz.2⟩
        have hlower : m₀ ≤ X z := by
          simpa only [m₀] using (RouteM.DAux.intervalInf_spec hX hbc.le).2 z hz'
        calc
          X t = m₀ := hXt₀
          _ ≤ X z := hlower
    have hs' : s ∈ Icc a c := ⟨hs.1, hs.2.trans hbc.le⟩
    have ht' : t ∈ Icc a c := ⟨le_trans hab.le ht.1, ht.2⟩
    have hss := shifted_isMinOn_of_isMinOn (p := a) (a := a) (b := c)
      (x := s) le_rfl hs' hminS
    have htt := shifted_isMinOn_of_isMinOn (p := a) (a := a) (b := c)
      (x := t) le_rfl ht' hminT
    have hsShift : s - a ∈ Icc (0 : ℝ) (c - a) := by
      constructor <;> linarith [hs'.1, hs'.2]
    have htShift : t - a ∈ Icc (0 : ℝ) (c - a) := by
      constructor <;> linarith [ht'.1, ht'.2]
    have hss' : IsMinOn (MatedCRTHarmonic.MoTPort.BMLocalMin.path (shiftedCoordinate i a) ω)
        (Icc (0 : ℝ) (c - a)) (s - a) := by
      convert hss using 1 <;> ring
    have htt' : IsMinOn (MatedCRTHarmonic.MoTPort.BMLocalMin.path (shiftedCoordinate i a) ω)
        (Icc (0 : ℝ) (c - a)) (t - a) := by
      convert htt using 1 <;> ring
    have hst : s - a = t - a := hU₁ (s - a) hsShift (t - a) htShift hss' htt'
    have hsEq : s = b := by
      have hsle : s ≤ b := hs.2
      have htle : b ≤ t := ht.1
      linarith
    have hminB : IsMinOn X (Icc a c) b := by
      rw [isMinOn_iff]
      intro z hz
      have h := (isMinOn_iff.mp hminS) z hz
      simpa [hsEq] using h
    let τ : ℝ≥0 := ⟨c - b, by linarith⟩
    have hτ : 0 < τ := by exact_mod_cast (sub_pos.mpr hbc)
    obtain ⟨r, hrpos, hrl, hnegative⟩ := hN₁ τ hτ
    have hrpos' : 0 < (r : ℝ) := by exact_mod_cast hrpos
    have hrlR : (r : ℝ) < (τ : ℝ) := by exact_mod_cast hrl
    have hrl' : (r : ℝ) < c - b := by
      change (r : ℝ) < c - b at hrlR
      exact hrlR
    have hrmem : b + (r : ℝ) ∈ Icc a c := by
      constructor <;> linarith
    have hvalue := (isMinOn_iff.mp hminB) (b + (r : ℝ)) hrmem
    have heval : shiftedCoordinate i b r ω = X (b + (r : ℝ)) - X b := by
      rfl
    rw [heval] at hnegative
    dsimp [X] at hvalue hnegative
    linarith
  · -- Equality of the right outer and middle minima.
    have hm₂eq : m₂ = m₀ := by
      by_contra hne
      have hm₁lt : m₁ < m₀ := lt_of_le_of_ne hm₁ heq₁
      have hm₂lt : m₂ < m₀ := lt_of_le_of_ne hm₂ hne
      have hmaxlt : max m₁ m₂ < m₀ := max_lt_iff.mpr ⟨hm₁lt, hm₂lt⟩
      exact hnot hmaxlt
    obtain ⟨s, hs, hXs⟩ :=
      (RouteM.DAux.intervalInf_spec hX hbc.le).1
    obtain ⟨t, ht, hXt⟩ :=
      (RouteM.DAux.intervalInf_spec hX hcd.le).1
    have hXs₀ : X s = m₀ := by simpa only [m₀] using hXs
    have hXt₂ : X t = m₂ := by simpa only [m₂] using hXt
    have hminS : IsMinOn X (Icc b d) s := by
      rw [isMinOn_iff]
      intro z hz
      rcases le_total z c with hzc | hcz
      · have hz' : z ∈ Icc b c := ⟨hz.1, hzc⟩
        have hlower : m₀ ≤ X z := by
          simpa only [m₀] using (RouteM.DAux.intervalInf_spec hX hbc.le).2 z hz'
        calc
          X s = m₀ := hXs₀
          _ ≤ X z := hlower
      · have hz' : z ∈ Icc c d := ⟨hcz, hz.2⟩
        have hlower : m₂ ≤ X z := by
          simpa only [m₂] using (RouteM.DAux.intervalInf_spec hX hcd.le).2 z hz'
        calc
          X s = m₀ := hXs₀
          _ = m₂ := hm₂eq.symm
          _ ≤ X z := hlower
    have hminT : IsMinOn X (Icc b d) t := by
      rw [isMinOn_iff]
      intro z hz
      rcases le_total z c with hzc | hcz
      · have hz' : z ∈ Icc b c := ⟨hz.1, hzc⟩
        have hlower : m₀ ≤ X z := by
          simpa only [m₀] using (RouteM.DAux.intervalInf_spec hX hbc.le).2 z hz'
        calc
          X t = m₂ := hXt₂
          _ = m₀ := hm₂eq
          _ ≤ X z := hlower
      · have hz' : z ∈ Icc c d := ⟨hcz, hz.2⟩
        have hlower : m₂ ≤ X z := by
          simpa only [m₂] using (RouteM.DAux.intervalInf_spec hX hcd.le).2 z hz'
        calc
          X t = m₂ := hXt₂
          _ ≤ X z := hlower
    have hs' : s ∈ Icc b d := ⟨hs.1, hs.2.trans hcd.le⟩
    have ht' : t ∈ Icc b d := ⟨le_trans hbc.le ht.1, ht.2⟩
    have hss := shifted_isMinOn_of_isMinOn (p := b) (a := b) (b := d)
      (x := s) le_rfl hs' hminS
    have htt := shifted_isMinOn_of_isMinOn (p := b) (a := b) (b := d)
      (x := t) le_rfl ht' hminT
    have hsShift : s - b ∈ Icc (0 : ℝ) (d - b) := by
      constructor <;> linarith [hs'.1, hs'.2]
    have htShift : t - b ∈ Icc (0 : ℝ) (d - b) := by
      constructor <;> linarith [ht'.1, ht'.2]
    have hss' : IsMinOn (MatedCRTHarmonic.MoTPort.BMLocalMin.path (shiftedCoordinate i b) ω)
        (Icc (0 : ℝ) (d - b)) (s - b) := by
      convert hss using 1 <;> ring
    have htt' : IsMinOn (MatedCRTHarmonic.MoTPort.BMLocalMin.path (shiftedCoordinate i b) ω)
        (Icc (0 : ℝ) (d - b)) (t - b) := by
      convert htt using 1 <;> ring
    have hst : s - b = t - b := hU₂ (s - b) hsShift (t - b) htShift hss' htt'
    have htEq : t = c := by
      have htle : t ≥ c := ht.1
      have hsle : s ≤ c := hs.2
      linarith
    have hminC : IsMinOn X (Icc b d) c := by
      simpa [htEq] using hminT
    let τ : ℝ≥0 := ⟨d - c, by linarith⟩
    have hτ : 0 < τ := by exact_mod_cast (sub_pos.mpr hcd)
    obtain ⟨r, hrpos, hrl, hnegative⟩ := hN₂ τ hτ
    have hrpos' : 0 < (r : ℝ) := by exact_mod_cast hrpos
    have hrlR : (r : ℝ) < (τ : ℝ) := by exact_mod_cast hrl
    have hrl' : (r : ℝ) < d - c := by
      change (r : ℝ) < d - c at hrlR
      exact hrlR
    have hrmem : c + (r : ℝ) ∈ Icc b d := by
      constructor <;> linarith
    have hvalue := (isMinOn_iff.mp hminC) (c + (r : ℝ)) hrmem
    have heval : shiftedCoordinate i c r ω = X (c + (r : ℝ)) - X c := by
      rfl
    rw [heval] at hnegative
    dsimp [X] at hvalue hnegative
    linarith

/-- For every fixed positive mesh, the Brownian coordinates satisfy the strict form of (1.1)
for every non-consecutive pair. -/
theorem ae_sideStrict {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, RouteM.SideStrict ε ω := by
  letI : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  intro ε hε
  refine ae_all_iff.2 fun b => ae_all_iff.2 fun x => ae_all_iff.2 fun y => ?_
  by_cases hxy : x + 1 < y
  · have hi : (if b then (1 : Fin 2) else 0) = (if b then 1 else 0) := rfl
    have hpair := ae_sideStrict_pair hμ (if b then (1 : Fin 2) else 0) ε hε x y hxy
    filter_upwards [hpair] with ω hω
    intro _ hside
    let i : Fin 2 := if b then 1 else 0
    have hcoord : (fun t => if b then (ω t).2 else (ω t).1) =
        fun t => lrCoord i t ω := by
      funext t
      cases b <;> simp [i, lrCoord]
    have hside' : SideCond ε (fun t => lrCoord i t ω) x y := by
      simpa [hcoord] using hside
    have hresult := hω hside'
    simpa [hcoord] using hresult
  · filter_upwards [ae_of_all μ fun _ => True.intro] with ω _
    intro _ hside
    exact False.elim (hxy (by omega))

end MatedCRTHarmonic.MatedCRT

end
