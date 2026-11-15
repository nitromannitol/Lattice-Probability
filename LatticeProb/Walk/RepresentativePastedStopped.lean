import LatticeProb.Walk.RepresentativeStoppedPrefix
import LatticeProb.Bonanno.BouRabeeGwynne.WalkCanonicalStopping

/-! # Representative exit curves and pasted walk excursions -/

set_option autoImplicit false
noncomputable section

open Set Metric BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- A pasted selector curve close to a continuous curve controls the stopped
polygonal curve for a nearby embedding, through the same finite walk prefix. -/
theorem edist_stoppedPolygonalCurve_le_of_pastedWalkCurve
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (p q : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → Euc d → Option J) (n : ℕ) (ω : ℕ → V)
    (hfinite : (FiniteConductanceNetwork.actualWalkStage q B initial
      (fun i v => select i (q v)) n ω).1 ≠ ⊤)
    {m : ℕ}
    (hmM : m ≤ (FiniteConductanceNetwork.actualWalkStage q B initial
      (fun i v => select i (q v)) n ω).1.untopD 0)
    {U : Set (Euc d)} (hU : IsOpen U)
    (hτ : FiniteConductanceNetwork.exitTime (p ⁻¹' U) ω = (m : WithTop ℕ))
    {a e mesh δ η : ℝ} (ha : 0 ≤ a) (he : 0 < e) (hmesh : 0 ≤ mesh)
    (hbuffer : a + e + mesh < δ)
    (hpq : ∀ v, dist (p v) (q v) ≤ a)
    (hedge : ∀ k < m, dist (p (ω (k + 1))) (p (ω k)) ≤ mesh)
    (P : TimePartition n) (g : C(unitInterval, Euc d))
    (hclose : ∀ t, dist (pastedWalkCurve P
      (FiniteConductanceNetwork.actualWalkExcursionSequence q B initial select ω) t) (g t) ≤ e)
    (hgexit : ∃ t, g t ∉ thickening δ U)
    (hgood : g ∉ unitCurveExitOscillationBad (innerDomain U (a + e))
      (thickening δ U) η) :
    edist (stoppedPolygonalCurve p (p ⁻¹' U) ω) (unitCurveExitProjection U g) ≤
      ENNReal.ofReal (a + e + η) := by
  let Q := (ClockedWalkExcursion.prefixTimeData
    (FiniteConductanceNetwork.actualWalkExcursionSequence q B initial select ω)).knots P
  have hcurve := FiniteConductanceNetwork.pastedWalkCurve_actual_eq_comp_canonical
    q B initial select n ω hfinite P
  have hclose' : ∀ t, dist ((polygonalCurve q ω
      ((FiniteConductanceNetwork.actualWalkStage q B initial
        (fun i v => select i (q v)) n ω).1.untopD 0)).comp (P.weakClock Q) t) (g t) ≤ e := by
    intro t
    rw [← hcurve]
    exact hclose t
  exact edist_stoppedPolygonalCurve_le_of_nearby_embedding p q ω hmM hU hτ
    ha he hmesh hbuffer hpq hedge (P.weakClock Q) (P.weakClock_monotone Q)
    (P.weakClock_zero Q) (P.weakClock_one Q) g hclose' hgexit hgood

end LatticeProb
end
