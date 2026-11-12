/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P2E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P2D
import LatticeProb.Bonanno.LQGMetric.Meas.Internal
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2, Step 2: `D(·,·;W)` from the truncated metric (packet P-2 of D90)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
Step 2, T:1362–1363: "`O` can be covered by finitely many sets of the form
`{v ∈ O : D(u,v) < D(u,∂O')}` … By the definition of the internal metric `D(·,·;O)`, this shows
that `h|_V` a.s. determines `D(·,·;O)`". The countable chain formula for internal metrics
(`ContMetric.internal_eq_chainInf`, LM S-int (a)) only uses the steps `D(x,y)` with
`D(x,y) < D(x,∂W)`, and these are exactly the values of the truncation `truncD W D` below its
threshold:

* `tStep`, `tChainVal`, `tChainInf` — the chain formula written with a function `T` on `W̄ × W̄`;
* `chainStep_eq_tStep` — for a length metric `D`, `chainStep D W x y = tStep W (truncD W D) x y`;
* `internal_eq_tChainInf` — `D(z,w;W) = tChainInf W (truncD W D) z w`;
* `exists_subseq_internal_ae` — **P-2**: along a deterministic subsequence, a.s. for every dyadic
  `W`, the truncated localized LFPP converges and `D_h(·,·;W)` is the chain formula of its limit.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

open Classical in
/-- an admissible chain step, read off from a function `T` on `W̄ × W̄` -/
def tStep (W : dyadicDomainsC) (T : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)) (x y : ℂ) :
    ℝ≥0∞ :=
  if h : x ∈ (W : Set ℂ) ∧ y ∈ closure (W : Set ℂ) then
    if T (⟨x, subset_closure h.1⟩, ⟨y, h.2⟩) < infFr W T ⟨x, subset_closure h.1⟩ then
      ENNReal.ofReal (T (⟨x, subset_closure h.1⟩, ⟨y, h.2⟩)) else ⊤
  else ⊤

/-- the value of the chain `x, l, y` -/
def tChainVal (W : dyadicDomainsC) (T : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)) :
    ℂ → List ℂ → ℂ → ℝ≥0∞
  | x, [], y => tStep W T x y
  | x, q :: l, y => tStep W T x q + tChainVal W T q l y

/-- the chain formula with interior points in the dense sequence of `ℂ` -/
def tChainInf (W : dyadicDomainsC) (T : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ))
    (z w : ℂ) : ℝ≥0∞ :=
  ⨅ l : List ℕ, tChainVal W T z (l.map (TopologicalSpace.denseSeq ℂ)) w

theorem frontier_dy_nonempty (W : dyadicDomainsC) {x : ℂ} (hx : x ∈ (W : Set ℂ)) :
    (frontier (W : Set ℂ)).Nonempty := by
  refine nonempty_frontier_iff.2 ⟨⟨x, hx⟩, fun h => ?_⟩
  have := isCompact_closure_dyadicDomainsC W
  rw [h, closure_univ] at this
  exact noncompact_univ ℂ this

theorem chainStep_eq_tStep (D : ContMetric) (hD : D.IsLength) (W : dyadicDomainsC) (x y : ℂ) :
    D.chainStep W x y = tStep W (truncD W D.1) x y := by
  have hWo : IsOpen (W : Set ℂ) := W.2.1.isOpen
  unfold ContMetric.chainStep tStep
  by_cases hx : x ∈ (W : Set ℂ)
  swap
  · have h0 : D.bdDist W x = 0 :=
      Metric.infEDist_zero_of_mem ((D.mem_compl_image_pt).2 hx)
    rw [h0, dif_neg (fun h => hx h.1)]
    simp
  by_cases hy : y ∈ closure (W : Set ℂ)
  swap
  · have hle : D.bdDist W x ≤ edist (D.pt x) (D.pt y) :=
      Metric.infEDist_le_edist_of_mem ((D.mem_compl_image_pt).2 fun h => hy (subset_closure h))
    rw [if_neg (not_lt.2 hle), dif_neg (fun h => hy h.2)]
  rw [dif_pos ⟨hx, hy⟩]
  -- the closest boundary point
  have hFc : IsCompact (frontier (W : Set ℂ)) :=
    (isCompact_closure_dyadicDomainsC W).of_isClosed_subset isClosed_frontier
      frontier_subset_closure
  obtain ⟨w₀, hw₀, hmin⟩ := hFc.exists_isMinOn (frontier_dy_nonempty W hx)
    (f := fun w => D.1 (x, w)) (D.1.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hmin' : ∀ w ∈ frontier (W : Set ℂ), D.1 (x, w₀) ≤ D.1 (x, w) := fun w hw => by
    have := hmin hw; simpa using this
  have hD0 : ∀ u v : ℂ, 0 ≤ D.1 (u, v) := fun u v => dist_nonneg (x := D.pt u) (y := D.pt v)
  -- `D(x, Wᶜ) = D(x, w₀)`
  have hbd : D.bdDist W x = ENNReal.ofReal (D.1 (x, w₀)) := by
    have hfr : D.pt '' frontier (W : Set ℂ) = frontier (D.pt '' (W : Set ℂ)) :=
      D.ptHomeomorph.image_frontier _
    unfold ContMetric.bdDist
    rw [infEDist_compl_eq_infEDist_frontier hD (D.isOpen_image_pt hWo) (u := D.pt x) ⟨x, hx, rfl⟩,
      ← hfr]
    refine le_antisymm ?_ ?_
    · refine (Metric.infEDist_le_edist_of_mem (x := D.pt x) (y := D.pt w₀)
        (s := D.pt '' frontier (W : Set ℂ)) ⟨w₀, hw₀, rfl⟩).trans (le_of_eq ?_)
      rw [edist_dist]; rfl
    · refine Metric.le_infEDist.2 ?_
      rintro _ ⟨w, hw, rfl⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hmin' w hw)
  set x' : closure (W : Set ℂ) := ⟨x, subset_closure hx⟩
  set y' : closure (W : Set ℂ) := ⟨y, hy⟩
  have hw₀K : w₀ ∈ closure (W : Set ℂ) := frontier_subset_closure hw₀
  have hbdd : ∀ e : C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ), (∀ p, 0 ≤ e p) →
      BddBelow (range fun w : {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)} =>
        e (x', w.1)) := fun e he => ⟨0, by rintro _ ⟨w, rfl⟩; exact he _⟩
  -- `D(x, ∂W)` as `infFr`
  have hR : infFr W (restrSq (closure (W : Set ℂ)) D.1) x' = D.1 (x, w₀) := by
    refine le_antisymm ?_ ?_
    · exact ciInf_le (hbdd _ fun p => hD0 _ _) (⟨⟨w₀, hw₀K⟩, hw₀⟩ :
        {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)})
    · have : Nonempty {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)} :=
        ⟨⟨⟨w₀, hw₀K⟩, hw₀⟩⟩
      exact le_ciInf fun w => hmin' w.1.1 w.2
  have hT : ∀ v : closure (W : Set ℂ),
      truncD W D.1 (x', v) = min (D.1 (x, v.1)) (D.1 (x, w₀)) := fun v => by
    show truncW W (restrSq (closure (W : Set ℂ)) D.1) (x', v) = _
    rw [truncW_apply, hR]; rfl
  have hTF : infFr W (truncD W D.1) x' = D.1 (x, w₀) := by
    refine le_antisymm ?_ ?_
    · refine (ciInf_le (hbdd _ fun p => ?_) (⟨⟨w₀, hw₀K⟩, hw₀⟩ :
        {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)})).trans ?_
      · show 0 ≤ truncW W (restrSq (closure (W : Set ℂ)) D.1) p
        rw [truncW_apply]
        refine le_min (hD0 _ _) ?_
        refine Real.iInf_nonneg fun w => hD0 _ _
      · show truncD W D.1 (x', ⟨w₀, hw₀K⟩) ≤ _
        rw [hT]; exact min_le_right _ _
    · have : Nonempty {w : closure (W : Set ℂ) // w.1 ∈ frontier (W : Set ℂ)} :=
        ⟨⟨⟨w₀, hw₀K⟩, hw₀⟩⟩
      refine le_ciInf fun w => ?_
      show D.1 (x, w₀) ≤ truncD W D.1 (x', w.1)
      rw [hT]
      exact le_min (hmin' w.1.1 w.2) le_rfl
  have hTxy := hT y'
  rw [hbd, hTF, hTxy]
  have hlt : min (D.1 (x, y)) (D.1 (x, w₀)) < D.1 (x, w₀) ↔ D.1 (x, y) < D.1 (x, w₀) := by
    rw [min_lt_iff]; simp
  have hed : edist (D.pt x) (D.pt y) = ENNReal.ofReal (D.1 (x, y)) := by rw [edist_dist]; rfl
  by_cases hxy : D.1 (x, y) < D.1 (x, w₀)
  · rw [if_pos (hlt.2 hxy), hed, if_pos ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hD0 _ _)).2 hxy),
      min_eq_left hxy.le]
  · rw [if_neg (fun h => hxy (hlt.1 h)), hed,
      if_neg (fun h => hxy ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hD0 _ _)).1 h))]

theorem chainVal_eq_tChainVal (D : ContMetric) (hD : D.IsLength) (W : dyadicDomainsC) :
    ∀ (l : List ℂ) (x y : ℂ), D.chainVal W x l y = tChainVal W (truncD W D.1) x l y
  | [], x, y => by simp only [ContMetric.chainVal, tChainVal, chainStep_eq_tStep D hD]
  | q :: l, x, y => by
    simp only [ContMetric.chainVal, tChainVal, chainStep_eq_tStep D hD,
      chainVal_eq_tChainVal D hD W l]

/-- **`D(·,·;W)` from the truncation** (T:1362–1363): for a length metric `D`,
`D(z,w;W) = tChainInf W (truncD W D) z w`. -/
theorem internal_eq_tChainInf (D : ContMetric) (hD : D.IsLength) (W : dyadicDomainsC)
    (z w : ℂ) : D.internal W z w = tChainInf W (truncD W D.1) z w := by
  rw [D.internal_eq_chainInf hD W.2.1.isOpen]
  unfold ContMetric.chainInf tChainInf
  simp only [chainVal_eq_tChainVal D hD W]

end LQGMetric.DFGPS.T12
