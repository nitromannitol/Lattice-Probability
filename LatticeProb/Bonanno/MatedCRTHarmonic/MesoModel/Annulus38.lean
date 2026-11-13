/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.Annulus38 at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma38Inputs
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Theorem14
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Probability
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.BadEventCore
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.BadEventInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.BPointConnected
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MesoscopicControlWith
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Recurrent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianLaw
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.LocalFiniteness
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsConnectedSet
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Mesoscopic
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Harm
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Graph
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.MeasureTheory.OuterMeasure.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.Chain
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Bound
import LatticeProb.Bonanno.MatedCRTHarmonic.CellularFacts.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.AnnularEvent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCoord
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTTwoSidedMin

/-!
# One-scale interfaces for annular estimates and recurrence

This module records the corrected Lemma 3.8 target, derives G3's connected-along-lines premise
from the Peanosphere Corollary B′, proves its one-scale walk estimate, assembles the finite scale
grid from a named one-scale outer-measure output, and adapts the conditional [18] Theorem 1.4 to
the unit-mesh recurrence interface.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic

/-- The representative scale at grid index `j`: start at the lower cutoff and increase by `5/4`,
clamping at `1/10`. -/
def annulus38ScaleRepresentative (k : ℕ) (β : ℝ) (j : ℕ) : ℝ :=
  min (CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ j) (1 / 10)

/-- The one-scale G3 output, extended to the interval covered by its grid representative. Its failure
probability is the single outer-measure input assembled by the G4 Proposition 2.10 and Lemma 2.7
cell-diameter producers, after applying `annulus38_lemma38_oneScale` and G3's inner-radius monotonicity.
The event is deliberately a complement event, so no measurability assumption is involved. -/
def Annulus38OneScaleGood (F : CellFamily.RandomCellFamily) (k : ℕ) (z : ℂ)
    (r β A₈ : ℝ) (j : ℕ) : Set F.Ω :=
  {ω | ∀ s ∈ Set.Icc (annulus38ScaleRepresentative k β j)
      (min (5 * annulus38ScaleRepresentative k β j / 4) (1 / 10)),
    ∀ x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * s * r)),
      ENNReal.ofReal (1 - A₈ / Real.sqrt (Real.log s⁻¹)) ≤
        (F.G k ω).walkLaw x {ω' | CellFamily.HitsBefore (F.H k ω).cell z s r
          ((F.G k ω).vertexPath ω')}}

/-- Outer-measure producer interface for one representative scale. This is the single named
probabilistic hypothesis consumed by the grid assembly; G4's exact `Prop210Bad` output and Lemma 2.7's
cell-diameter output are the lower-level producers used to establish it. -/
def Annulus38OneScaleBadBound (F : CellFamily.RandomCellFamily) (ρ : ℝ) : Prop :=
  ∃ α β A₈ C : ℝ, 0 < α ∧ 0 < β ∧ β ≤ 1 ∧ 0 ≤ C ∧
    ∀ k (z : ℂ) (r : ℝ) (j : ℕ), CellFamily.mesh k ^ β ≤ r → r ≤ ρ →
      ball z r ⊆ ball (0 : ℂ) ρ →
      F.P (Annulus38OneScaleGood F k z r β A₈ j)ᶜ ≤
        ENNReal.ofReal (C * CellFamily.mesh k ^ α)

private theorem annulus38_gridPow_reaches_unit (k : ℕ) :
    (2 : ℝ) ^ k ≤ (5 / 4 : ℝ) ^ (4 * k) := by
  have hbase : 2 ≤ (5 / 4 : ℝ) ^ 4 := by norm_num
  calc
    (2 : ℝ) ^ k ≤ ((5 / 4 : ℝ) ^ 4) ^ k := pow_le_pow_left₀ (by norm_num) hbase _
    _ = (5 / 4 : ℝ) ^ (4 * k) := by rw [← pow_mul]

private theorem annulus38_mesh_le_one (k : ℕ) : CellFamily.mesh k ≤ 1 := by
  rw [show CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ by simp [CellFamily.mesh, zpow_neg]]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

private theorem annulus38_mesh_le_rpow_of_beta_le_one (k : ℕ) {β : ℝ}
    (_hβ0 : 0 < β) (hβ1 : β ≤ 1) : CellFamily.mesh k ≤ CellFamily.mesh k ^ β := by
  have h := Real.rpow_le_rpow_of_exponent_ge
    (zpow_pos (by norm_num : (0 : ℝ) < 2) _) (annulus38_mesh_le_one k) hβ1
  simpa [CellFamily.mesh, Real.rpow_one] using h

private theorem annulus38_rawScale_crosses {β : ℝ} (k : ℕ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    1 / 10 ≤ CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ (4 * k) := by
  have hmesh : CellFamily.mesh k ≤ CellFamily.mesh k ^ β :=
    annulus38_mesh_le_rpow_of_beta_le_one k hβ0 hβ1
  have hmesh' : (2 : ℝ) ^ (-(k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ := by
    simp [zpow_neg]
  have hmeshEq : CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ := by
    exact hmesh'
  have hp := annulus38_gridPow_reaches_unit k
  have hpowPos : 0 < (2 : ℝ) ^ k := by positivity
  have hmul : 1 ≤ ((2 : ℝ) ^ k)⁻¹ * (5 / 4 : ℝ) ^ (4 * k) := by
    calc
      1 = ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ k := by field_simp
      _ ≤ ((2 : ℝ) ^ k)⁻¹ * (5 / 4 : ℝ) ^ (4 * k) :=
        mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hpowPos.le)
  have hprod : CellFamily.mesh k * (5 / 4 : ℝ) ^ (4 * k) ≤
      CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ (4 * k) :=
    mul_le_mul_of_nonneg_right hmesh (pow_nonneg (by norm_num) _)
  have hprod' : 1 ≤ CellFamily.mesh k * (5 / 4 : ℝ) ^ (4 * k) := by
    calc
      1 ≤ ((2 : ℝ) ^ k)⁻¹ * (5 / 4 : ℝ) ^ (4 * k) := hmul
      _ = CellFamily.mesh k * (5 / 4 : ℝ) ^ (4 * k) := by rw [← hmeshEq]
  calc
    1 / 10 ≤ 1 := by norm_num
    _ ≤ CellFamily.mesh k * (5 / 4 : ℝ) ^ (4 * k) := hprod'
    _ ≤ CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ (4 * k) := hprod

private theorem annulus38_scaleGrid_covers {β : ℝ} (k : ℕ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hlow : CellFamily.mesh k ^ β ≤ 1 / 10) {s : ℝ}
    (hslo : CellFamily.mesh k ^ β ≤ s) (hshi : s ≤ 1 / 10) :
    ∃ j ≤ 4 * k, annulus38ScaleRepresentative k β j ≤ s ∧
      s ≤ min (5 * annulus38ScaleRepresentative k β j / 4) (1 / 10) := by
  let raw : ℕ → ℝ := fun j => CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ j
  have hcross : s ≤ raw (4 * k) := by
    have hs := annulus38_rawScale_crosses k hβ0 hβ1
    dsimp [raw]
    calc
      s ≤ 1 / 10 := hshi
      _ ≤ CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ (4 * k) := hs
  have hHas : ∃ n, s ≤ raw n := ⟨4 * k, hcross⟩
  let n := Nat.find hHas
  have hn : s ≤ raw n := Nat.find_spec hHas
  have hnle : n ≤ 4 * k := Nat.find_min' hHas hcross
  by_cases hn0 : n = 0
  · subst n
    refine ⟨0, by omega, ?_, ?_⟩
    · dsimp [annulus38ScaleRepresentative, raw]
      rw [pow_zero, mul_one]
      exact le_trans (min_le_left _ _) hslo
    · have hfind0 : Nat.find hHas = 0 := hn0
      have hn' : s ≤ CellFamily.mesh k ^ β := by
        rw [hfind0] at hn
        simpa [raw] using hn
      have hrep : annulus38ScaleRepresentative k β 0 = CellFamily.mesh k ^ β := by
        change min (CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ 0) (1 / 10) = _
        rw [pow_zero, mul_one, min_eq_left hlow]
      have hsEq : s = CellFamily.mesh k ^ β := le_antisymm hn' hslo
      rw [hrep]
      rw [hsEq]
      apply le_min
      · have hlowpos : 0 < CellFamily.mesh k ^ β := Real.rpow_pos_of_pos
          (zpow_pos (by norm_num : (0 : ℝ) < 2) _) β
        nlinarith
      · exact hlow
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    let j := n - 1
    have hjn : j + 1 = n := by omega
    have hprev : ¬ s ≤ raw j := Nat.find_min hHas (by omega)
    have hprevlt : raw j < s := lt_of_not_ge hprev
    have hrawSucc : raw n = raw j * (5 / 4 : ℝ) := by
      dsimp [raw]
      rw [← hjn, pow_succ]
      ring
    have hrep : annulus38ScaleRepresentative k β j = raw j := by
      dsimp [annulus38ScaleRepresentative]
      rw [min_eq_left (le_of_lt (lt_of_lt_of_le hprevlt hshi))]
    refine ⟨j, by omega, ?_, ?_⟩
    · rw [hrep]
      exact le_of_lt hprevlt
    · have hscaleEq : 5 * raw j / 4 = raw j * (5 / 4 : ℝ) := by ring
      apply le_min
      · rw [hrep, hscaleEq]
        rw [hrawSucc] at hn
        exact hn
      · exact hshi

private theorem annulus38_gridCard_mul_mesh_rpow {α : ℝ} (hα : 0 < α) (k : ℕ) :
    (4 * (k : ℝ) + 1) * CellFamily.mesh k ^ α ≤
      (1 + 4 / ((2 : ℝ) ^ (α / 2) - 1)) * CellFamily.mesh k ^ (α / 2) := by
  let b : ℝ := (2 : ℝ) ^ (-α / 2)
  let q : ℝ := (2 : ℝ) ^ (α / 2)
  have hq1 : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hqpos : 0 < q := by linarith
  have hbpos : 0 < b := by positivity
  have hbq : b * q = 1 := by
    dsimp [b, q]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hexp : -α / 2 + α / 2 = 0 := by ring
    rw [hexp]
    simp
  have hbpow : b ^ k = (q ^ k)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← mul_pow, hbq, one_pow]
  have hBern : ∀ n : ℕ, 1 + (n : ℝ) * (q - 1) ≤ q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hd : 0 ≤ q - 1 := le_of_lt (sub_pos.mpr hq1)
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hqEq : q = 1 + (q - 1) := by ring
        have hstep : 1 + ((n + 1 : ℕ) : ℝ) * (q - 1) ≤
            (1 + (n : ℝ) * (q - 1)) * q := by
          rw [hqEq]
          push_cast
          nlinarith [mul_nonneg hn (sq_nonneg (q - 1))]
        calc
          1 + ((n + 1 : ℕ) : ℝ) * (q - 1) ≤
              (1 + (n : ℝ) * (q - 1)) * q := hstep
          _ ≤ q ^ n * q := mul_le_mul_of_nonneg_right ih hqpos.le
          _ = q ^ (n + 1) := by rw [pow_succ]
  have hratio : (k : ℝ) / q ^ k ≤ 1 / (q - 1) := by
    apply (div_le_div_iff₀ (pow_pos hqpos k) (sub_pos.mpr hq1)).2
    have h := hBern k
    nlinarith
  have hkbound : (k : ℝ) * b ^ k ≤ 1 / (q - 1) := by
    calc
      (k : ℝ) * b ^ k = (k : ℝ) / q ^ k := by rw [hbpow, ← div_eq_mul_inv]
      _ ≤ 1 / (q - 1) := hratio
  have hbkle : b ^ k ≤ 1 := by
    rw [hbpow]
    have hqk : 1 ≤ q ^ k := by
      have h := hBern k
      have hd : 0 ≤ (k : ℝ) * (q - 1) := mul_nonneg (Nat.cast_nonneg k)
        (le_of_lt (sub_pos.mpr hq1))
      linarith
    exact inv_le_one_of_one_le₀ hqk
  have hcount : (4 * (k : ℝ) + 1) * b ^ k ≤ 4 / (q - 1) + 1 := by
    calc
      (4 * (k : ℝ) + 1) * b ^ k = 4 * ((k : ℝ) * b ^ k) + b ^ k := by ring
      _ ≤ 4 * (1 / (q - 1)) + 1 := add_le_add
        (mul_le_mul_of_nonneg_left hkbound (by norm_num)) hbkle
      _ = 4 / (q - 1) + 1 := by ring
  have hmeshHalf : CellFamily.mesh k ^ (α / 2) = b ^ k := by
    rw [MatedCRTHarmonic.GMSLemma27.mesh_rpow_eq]
    congr 1
    dsimp [b]
    congr 1
    ring
  have hmeshPow : CellFamily.mesh k ^ α = (CellFamily.mesh k ^ (α / 2)) ^ 2 := by
    calc
      CellFamily.mesh k ^ α = CellFamily.mesh k ^ (α / 2 + α / 2) := by congr 1 <;> ring
      _ = CellFamily.mesh k ^ (α / 2) * CellFamily.mesh k ^ (α / 2) :=
        Real.rpow_add (zpow_pos (by norm_num : (0 : ℝ) < 2) _) _ _
      _ = (CellFamily.mesh k ^ (α / 2)) ^ 2 := by ring
  calc
    (4 * (k : ℝ) + 1) * CellFamily.mesh k ^ α =
        ((4 * (k : ℝ) + 1) * b ^ k) * b ^ k := by rw [hmeshPow, hmeshHalf]; ring
    _ ≤ (4 / (q - 1) + 1) * b ^ k :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg hbpos.le _)
    _ = (1 + 4 / ((2 : ℝ) ^ (α / 2) - 1)) * CellFamily.mesh k ^ (α / 2) := by
      rw [hmeshHalf]
      dsimp [q]
      ring

/-- Direct bad-event output of the finite-grid argument, for the bundle interface. This keeps
the proof entirely in outer measure and therefore needs no measurability premise. -/
theorem annulus38_lemma38AnnulusHitBad_of_oneScaleBadBound
    (F : CellFamily.RandomCellFamily) (ρ : ℝ)
    (hinput : Annulus38OneScaleBadBound F ρ) : CellFamily.Lemma38AnnulusHitBad F ρ := by
  rcases hinput with ⟨α, β, A₈, C, hα, hβ, hβ1, hC, hscale⟩
  let C₈ : ℝ := C * (1 + 4 / ((2 : ℝ) ^ (α / 2) - 1))
  have hα₈ : 0 < α / 2 := by linarith
  have hq : 1 < (2 : ℝ) ^ (α / 2) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hC₈ : 0 ≤ C₈ := by
    dsimp [C₈]
    positivity
  refine ⟨α / 2, hα₈, β, hβ, A₈, C₈, fun k z r hkr hr hball => ?_⟩
  let target : Set F.Ω := CellFamily.Lemma38EnvironmentGood F k z r β A₈
  by_cases hlow : CellFamily.mesh k ^ β ≤ 1 / 10
  · let I : Finset ℕ := Finset.range (4 * k + 1)
    let bad : ℕ → Set F.Ω := fun j => (Annulus38OneScaleGood F k z r β A₈ j)ᶜ
    let allBad : Set F.Ω := ⋃ j ∈ I, bad j
    have hbadGrid : F.P allBad ≤
        (I.card : ℝ≥0∞) * ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
      apply GMS4.finite_union_measure_le_card_mul
      intro j hj
      exact hscale k z r j hkr hr hball
    have hgridGood : allBadᶜ ⊆ target := by
      intro ω hω
      change ∀ s ∈ Set.Icc (CellFamily.mesh k ^ β) (1 / 10),
        ∀ x ∈ verticesMeeting (F.H k ω).cell (ball z (4 * s * r)),
          ENNReal.ofReal (1 - A₈ / Real.sqrt (Real.log s⁻¹)) ≤
            (F.G k ω).walkLaw x {ω' | CellFamily.HitsBefore (F.H k ω).cell z s r
              ((F.G k ω).vertexPath ω')}
      intro s hs x hx
      obtain ⟨j, hj, hjlow, hjhigh⟩ := annulus38_scaleGrid_covers k hβ hβ1 hlow hs.1 hs.2
      have hjI : j ∈ I := by
        simp [I]
        omega
      have hnotBad : ω ∉ bad j := by
        intro hmem
        have hnotUnion : ¬ ω ∈ ⋃ i ∈ I, bad i := by
          simpa only [allBad, Set.mem_compl_iff] using hω
        apply hnotUnion
        exact Set.mem_iUnion₂.mpr ⟨j, hjI, hmem⟩
      have hblock : ω ∈ Annulus38OneScaleGood F k z r β A₈ j := by
        simpa [bad] using hnotBad
      exact hblock s ⟨hjlow, hjhigh⟩ x hx
    have hbadTarget : F.P targetᶜ ≤
        ENNReal.ofReal (C₈ * CellFamily.mesh k ^ (α / 2)) := by
      have hcardReal : (I.card : ℝ) = 4 * (k : ℝ) + 1 := by
        simp [I]
      have hreal : (I.card : ℝ) * (C * CellFamily.mesh k ^ α) ≤
          C₈ * CellFamily.mesh k ^ (α / 2) := by
        rw [hcardReal]
        calc
          (4 * (k : ℝ) + 1) * (C * CellFamily.mesh k ^ α) =
              C * ((4 * (k : ℝ) + 1) * CellFamily.mesh k ^ α) := by ring
          _ ≤ C * ((1 + 4 / ((2 : ℝ) ^ (α / 2) - 1)) *
              CellFamily.mesh k ^ (α / 2)) :=
            mul_le_mul_of_nonneg_left (annulus38_gridCard_mul_mesh_rpow hα k) hC
          _ = C₈ * CellFamily.mesh k ^ (α / 2) := by dsimp [C₈]; ring
      have htargetSub : targetᶜ ⊆ allBad := by
        intro ω hω
        by_contra hnot
        exact hω (hgridGood hnot)
      calc
        F.P targetᶜ ≤ F.P allBad := measure_mono htargetSub
        _ ≤ (I.card : ℝ≥0∞) * ENNReal.ofReal (C * CellFamily.mesh k ^ α) := hbadGrid
        _ = ENNReal.ofReal ((I.card : ℝ) * (C * CellFamily.mesh k ^ α)) := by
          rw [show (I.card : ℝ≥0∞) = ENNReal.ofReal (I.card : ℝ) by simp,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        _ ≤ ENNReal.ofReal (C₈ * CellFamily.mesh k ^ (α / 2)) :=
          ENNReal.ofReal_le_ofReal hreal
    simpa [target] using hbadTarget
  · have hempty : Set.Icc (CellFamily.mesh k ^ β) (1 / 10) = ∅ := by
      ext s
      constructor
      · intro hs
        exact False.elim ((not_le_of_gt (lt_of_not_ge hlow)) (le_trans hs.1 hs.2))
      · intro hs
        exact False.elim hs
    have htarget : target = Set.univ := by
      ext ω
      simp only [target, CellFamily.Lemma38EnvironmentGood, Set.mem_setOf_eq,
        Set.mem_univ, iff_true]
      intro s hs
      have hs' : s ∈ (∅ : Set ℝ) := by rw [← hempty]; exact hs
      exact False.elim (Set.notMem_empty s hs')
    change F.P targetᶜ ≤ _
    rw [htarget]
    simp

private theorem annulus38_connected_of_adjIff {V : Type*} (G G' : SimpleGraph V)
    (hadj : ∀ x y, G.Adj x y ↔ G'.Adj x y) (hG' : G'.Connected) : G.Connected := by
  obtain ⟨root, hroot⟩ := G'.connected_iff_exists_forall_reachable.mp hG'
  apply G.connected_iff_exists_forall_reachable.mpr
  refine ⟨root, fun x => ?_⟩
  have hreach := hroot x
  have hrt := (G'.reachable_iff_reflTransGen root x).mp hreach
  have hrt' := Relation.ReflTransGen.mono (fun a b hab => (hadj a b).mpr hab) root x hrt
  exact (G.reachable_iff_reflTransGen root x).mpr hrt'

/-- The cells in a Peanosphere bundle satisfy G3's connected-along-lines premise. This is
Corollary B′ applied to each axis-parallel segment and transported across the cell and adjacency
identifications in `PeanosphereG0`. -/
theorem annulus38_connectedAlongLines_of_peanosphereG0
    (F : CellFamily.RandomCellFamily) (k : ℕ) (ω : F.Ω)
    (path : MatedCRT.Path2) (η : ℝ → ℂ)
    (h : MatedCRT.IsLocallyFinite (CellFamily.mesh k) path)
    (H' : CellularEmbedding (MatedCRT.graph (CellFamily.mesh k) path h) 0)
    (P : RouteM.Peanosphere path η)
    (hadj : ∀ x y, (F.G k ω).adj.Adj x y ↔ (MatedCRT.graph (CellFamily.mesh k) path h).adj.Adj x y)
    (hcell : ∀ x, (F.H k ω).cell x = H'.cell x)
    (heval : ∀ x, H'.cell x = η '' Set.Icc
      (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x)) :
    GMS3.ConnectedAlongLines (F.H k ω) := by
  intro a b hab
  have hcell' : H'.cell = fun x : ℤ =>
      η '' Set.Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) := by
    funext x
    exact heval x
  have hgraph (x y : ℤ) : (F.G k ω).adj.Adj x y ↔
      (MatedCRT.graph (CellFamily.mesh k) path h).adj.Adj x y := hadj x y
  have hconn := RouteM.connected_verticesMeeting_of_peanosphere_holds P H' hcell'
    (S := segment ℝ a b)
    ((convex_segment a b).isConnected ⟨a, left_mem_segment ℝ a b⟩)
  have hvertices : verticesMeeting (F.H k ω).cell (segment ℝ a b) =
      verticesMeeting H'.cell (segment ℝ a b) := by
    apply Set.ext
    intro x
    change ((F.H k ω).cell x ∩ segment ℝ a b).Nonempty ↔
      (H'.cell x ∩ segment ℝ a b).Nonempty
    rw [hcell x]
  have hconn' :
      ((F.G k ω).adj.induce (verticesMeeting (F.H k ω).cell (segment ℝ a b))).Connected := by
    rw [hvertices]
    exact annulus38_connected_of_adjIff
      ((F.G k ω).adj.induce (verticesMeeting H'.cell (segment ℝ a b)))
      ((MatedCRT.graph (CellFamily.mesh k) path h).adj.induce
        (verticesMeeting H'.cell (segment ℝ a b)))
      (by
        intro x y
        rw [SimpleGraph.induce_adj, SimpleGraph.induce_adj]
        exact hgraph x.1 y.1) hconn
  exact hconn'

end MatedCRTHarmonic.MesoModel
