/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.AreaFastClockIdentificationOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClockFastSpeedOccupation

/-!
# The missing half of the occupation comparison: the area clock *equals* the chain clock

`Process/AreaClockFastSpeedOccupation.tsum_below_mul_le_setLIntegral` proves only

`∑_{ξ < η} q(Y_ξ) · T^w_ξ  ≤  ∫₀^{τ^w_η} q(X_s) ds`,

which at `q = areaClockDensity` is the inequality `τ^{areaRate}_η ≤ areaClock(τ^w_η)`.  Step
(b) of the bracket atom `CoordinateLocallySquareIntegrable` needs the **equality**: the
clock `h` of the manuscript's time change `X^{area}_t = Y_{h(t)}` has to be identified with
the canonical inverse `inverseAreaClock` of the *occupation* clock, and only the occupation
form is manifestly a functional of the fast path on `[0,u]` (hence adapted, hence gives
stopping times).

The reverse inequality costs exactly one extra fact, already in the tree: the times covered
by **no** holding window are Lebesgue-null.  That is Lemma 3.7, first paragraph, in the
per-clock form `PathProperties.volume_notInOpenInterval_lt`, which needs no summability
hypothesis — only `Realized η` and `τ_η ≠ ⊤`, i.e. exactly the hypotheses already carried by
the `≤` half.

The three steps are:

* `setLIntegral_window` — on the window `[τ_ξ, τ_ξ̂)` the path is constantly `Y_ξ`
  (`Consistent.X_eq_of_inInterval`) and the window has length `T_ξ`
  (`PathProperties.tau_succ`), so the occupation integral over it is **exactly**
  `q(Y_ξ) · T_ξ`;
* `volume_Icc_diff_iUnion_window` — a time `0 < s < τ_η` interior to some holding interval
  lies in the window of that interval's index, because `τ_ξ < s < τ_η` forces `ξ < η`
  (contrapositive of `tau_mono`); so the uncovered part of `[0, τ_η]` sits inside the null
  set of Lemma 3.7 together with the two endpoints;
* `setLIntegral_Icc_tau_eq_tsum_below` — the windows are pairwise disjoint
  (`Consistent.inInterval_unique`) and cover `[0, τ_η]` up to a null set, so the integral is
  the sum of the window integrals.

The concrete corollary `setLIntegral_areaClockDensity_tau_eq_tau_areaRate` is the
**time-change identity at the chain times**: the occupation clock of the density
`cellArea / m` along the *fast* walk with speed `m = π/w`, read at the fast chain time
`τ^w_η`, is the *area* chain time `τ^{areaRate}_η`.  The pointwise reweighting is the already
checked `holding_areaRate_eq`.

Nothing here is probabilistic, and no speed measure is assumed summable; `w` is an arbitrary
positive rate.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.AreaFastClockIdentification

open StatementIngredients AreaClocks
open ReflectedWalk ReflectedWalk.IndexSet
open ReflectedGMS.AreaClockFastSpeedOccupation

universe u

section Deterministic

variable {V : Type u}

/-- **The occupation integral over one window is exactly `q(Y_ξ)·T_ξ`.**  The `≤` direction
is the estimate inside `tsum_below_mul_le_setLIntegral`; the path is *constant* on the
window, so the estimate is an identity. -/
theorem setLIntegral_window (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (Eh : (ℕ →₀ ℕ) → ℝ) (hc : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (q : V → ℝ≥0∞) {η : ℕ →₀ ℕ} (hη : Realized Gs Y η)
    (hfin : tau Gs Y w Eh η ≠ ⊤) (a : ℕ →₀ ℕ) :
    (∫⁻ s in window Gs Y w Eh η a, (X Gs Y w Eh (Real.toNNReal s)).elim 0 q)
      = (below Gs Y η).indicator
          (fun b => q (Yxi Gs Y b) * holding Gs Y w Eh b) a := by
  by_cases ha : a ∈ below Gs Y η
  · have hta : tau Gs Y w Eh a ≠ ⊤ := tau_ne_top_of_mem_below Gs Y w Eh ha hfin
    have hvol : volume (window Gs Y w Eh η a) = holding Gs Y w Eh a := by
      rw [window_of_mem Gs Y w Eh ha, Real.volume_Ico,
        PathProperties.tau_succ Gs Y w Eh hc hGm hcov ha.1,
        ENNReal.toReal_add hta (holding_ne_top Gs Y w Eh a), add_sub_cancel_left]
      exact ENNReal.ofReal_toReal (holding_ne_top Gs Y w Eh a)
    have hcongr : (∫⁻ s in window Gs Y w Eh η a, (X Gs Y w Eh (Real.toNNReal s)).elim 0 q)
        = ∫⁻ _s in window Gs Y w Eh η a, q (Yxi Gs Y a) := by
      refine lintegral_congr_ae ?_
      filter_upwards [self_mem_ae_restrict (measurableSet_window Gs Y w Eh η a)] with s hs
      rw [hc.X_eq_of_inInterval Gs Y w Eh hGm hcov
        (inInterval_of_mem_window Gs Y w Eh hc hGm hcov hη hfin hs)]
      rfl
    rw [hcongr, setLIntegral_const, hvol, Set.indicator_of_mem ha]
  · rw [window_of_notMem Gs Y w Eh ha, Set.indicator_of_notMem ha,
      Measure.restrict_empty, lintegral_zero_measure]

/-- **The uncovered part of `[0, τ_η]` is Lebesgue-null.**  Apart from the two endpoints, a
time not lying in any window lies in no *open* holding interval, and those times are null by
Lemma 3.7 (`PathProperties.volume_notInOpenInterval_lt`, which needs no summability). -/
theorem volume_Icc_diff_iUnion_window (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (Eh : (ℕ →₀ ℕ) → ℝ) (hc : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {η : ℕ →₀ ℕ} (hη : Realized Gs Y η)
    (hfin : tau Gs Y w Eh η ≠ ⊤) :
    volume (Set.Icc (0 : ℝ) (tau Gs Y w Eh η).toReal \
      ⋃ a, window Gs Y w Eh η a) = 0 := by
  have hnull := PathProperties.volume_notInOpenInterval_lt Gs Y w Eh hc hGm hcov hη hfin
  refine measure_mono_null (t := {s : ℝ | 0 < s ∧ s < (tau Gs Y w Eh η).toReal ∧
      ¬ PathProperties.InOpenInterval Gs Y w Eh (ENNReal.ofReal s)} ∪
      ({(0 : ℝ)} ∪ {(tau Gs Y w Eh η).toReal})) ?_
    (measure_union_null hnull
      (measure_union_null (measure_singleton (0 : ℝ))
        (measure_singleton (tau Gs Y w Eh η).toReal)))
  rintro s ⟨hsI, hsU⟩
  by_cases h0 : s = 0
  · exact Or.inr (Or.inl h0)
  by_cases hT : s = (tau Gs Y w Eh η).toReal
  · exact Or.inr (Or.inr hT)
  have hspos : 0 < s := lt_of_le_of_ne hsI.1 (Ne.symm h0)
  have hslt : s < (tau Gs Y w Eh η).toReal := lt_of_le_of_ne hsI.2 hT
  refine Or.inl ⟨hspos, hslt, ?_⟩
  rintro ⟨a, haR, hlt1, hlt2⟩
  have hsη : ENNReal.ofReal s < tau Gs Y w Eh η :=
    (ENNReal.ofReal_lt_iff_lt_toReal hspos.le hfin).2 hslt
  have hab : toLex a < toLex η := by
    by_contra hcon
    have hle : tau Gs Y w Eh η ≤ tau Gs Y w Eh a := tau_mono Gs Y w Eh (not_lt.1 hcon)
    exact absurd (lt_of_le_of_lt hle hlt1) (not_lt.2 hsη.le)
  have hain : a ∈ below Gs Y η := ⟨haR, hab⟩
  have hts : tau Gs Y w Eh (succ Gs Y a) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (tau_succ_le_of_mem_below Gs Y w Eh hc hGm hcov hη hain)
  have hlt2' : ENNReal.ofReal s < tau Gs Y w Eh (succ Gs Y a) := by
    rw [PathProperties.tau_succ Gs Y w Eh hc hGm hcov haR]
    exact hlt2
  have hmem : s ∈ window Gs Y w Eh η a := by
    rw [window_of_mem Gs Y w Eh hain]
    exact ⟨ENNReal.toReal_le_of_le_ofReal hspos.le hlt1.le,
      (ENNReal.ofReal_lt_iff_lt_toReal hspos.le hts).1 hlt2'⟩
  exact hsU (Set.mem_iUnion.2 ⟨a, hmem⟩)

/-- **The occupation clock at a chain time is the weighted holding sum — an equality.**  This
is `tsum_below_mul_le_setLIntegral` with the reverse inequality supplied. -/
theorem setLIntegral_Icc_tau_eq_tsum_below (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (Eh : (ℕ →₀ ℕ) → ℝ) (hc : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (q : V → ℝ≥0∞) {η : ℕ →₀ ℕ} (hη : Realized Gs Y η)
    (hfin : tau Gs Y w Eh η ≠ ⊤) :
    (∫⁻ s in Set.Icc (0 : ℝ) (tau Gs Y w Eh η).toReal,
        (X Gs Y w Eh (Real.toNNReal s)).elim 0 q)
      = ∑' a, (below Gs Y η).indicator
          (fun b => q (Yxi Gs Y b) * holding Gs Y w Eh b) a := by
  have hdisj : Pairwise (Function.onFun Disjoint (window Gs Y w Eh η)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro s hsa hsb
    exact hab (hc.inInterval_unique Gs Y w Eh hGm hcov
      (inInterval_of_mem_window Gs Y w Eh hc hGm hcov hη hfin hsa)
      (inInterval_of_mem_window Gs Y w Eh hc hGm hcov hη hfin hsb))
  have hsub : (⋃ a, window Gs Y w Eh η a) ⊆
      Set.Icc (0 : ℝ) (tau Gs Y w Eh η).toReal := by
    intro s hs
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hs
    by_cases hab : a ∈ below Gs Y η
    · rw [window_of_mem Gs Y w Eh hab] at ha
      refine ⟨le_trans ENNReal.toReal_nonneg ha.1, le_trans ha.2.le ?_⟩
      exact ENNReal.toReal_mono hfin (tau_succ_le_of_mem_below Gs Y w Eh hc hGm hcov hη hab)
    · rw [window_of_notMem Gs Y w Eh hab] at ha
      exact ha.elim
  have haeeq : Set.Icc (0 : ℝ) (tau Gs Y w Eh η).toReal
      =ᵐ[volume] ⋃ a, window Gs Y w Eh η a := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨volume_Icc_diff_iUnion_window Gs Y w Eh hc hGm hcov hη hfin, ?_⟩
    rw [Set.sdiff_eq_empty.2 hsub]
    exact measure_empty
  calc (∫⁻ s in Set.Icc (0 : ℝ) (tau Gs Y w Eh η).toReal,
        (X Gs Y w Eh (Real.toNNReal s)).elim 0 q)
      = ∫⁻ s in ⋃ a, window Gs Y w Eh η a, (X Gs Y w Eh (Real.toNNReal s)).elim 0 q :=
        setLIntegral_congr haeeq
    _ = ∑' a, ∫⁻ s in window Gs Y w Eh η a, (X Gs Y w Eh (Real.toNNReal s)).elim 0 q :=
        lintegral_iUnion (measurableSet_window Gs Y w Eh η) hdisj _
    _ = ∑' a, (below Gs Y η).indicator
          (fun b => q (Yxi Gs Y b) * holding Gs Y w Eh b) a :=
        tsum_congr fun a =>
          setLIntegral_window Gs Y w Eh hc hGm hcov q hη hfin a

end Deterministic

/-! ## The time-change identity at the chain times -/

section AreaOccupation

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] [DecidableEq V]

/-- **The clock identification at the chain times.**  The occupation clock of the area
density `cellArea / m`, for the speed measure `m = π/w` of the fast rate `w`, read along the
fast path at the fast chain time `τ^w_η`, is exactly the area chain time `τ^{areaRate}_η`.

This is the equality whose `≤` half is
`AreaClockFastSpeedOccupation.ae_tau_areaRate_le_areaClock`. -/
theorem setLIntegral_areaClockDensity_tau_eq_tau_areaRate
    (F : IndexedCells V) (hF : Geometry F) (hG : F.graph.toSimpleGraph.Connected)
    (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (Eh : (ℕ →₀ ℕ) → ℝ) (hc : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {η : ℕ →₀ ℕ} (hη : Realized Gs Y η)
    (hfin : tau Gs Y w Eh η ≠ ⊤) :
    (∫⁻ s in Set.Icc (0 : ℝ) (tau Gs Y w Eh η).toReal,
        (X Gs Y w Eh (Real.toNNReal s)).elim 0
          (AreaClockLocalFiniteness.areaClockDensity F (fun v => F.graph.pi v / w v)))
      = tau Gs Y (areaRate F) Eh η := by
  have hrhs : tau Gs Y (areaRate F) Eh η
      = ∑' a, (below Gs Y η).indicator (holding Gs Y (areaRate F) Eh) a := rfl
  rw [setLIntegral_Icc_tau_eq_tsum_below Gs Y w Eh hc hGm hcov
      (AreaClockLocalFiniteness.areaClockDensity F (fun v => F.graph.pi v / w v)) hη hfin,
    hrhs]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ below Gs Y η
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    exact (holding_areaRate_eq F hF hG Gs Y w hw Eh a).symm
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

end AreaOccupation

end ReflectedGMS.AreaFastClockIdentification
