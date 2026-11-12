/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.L46MeasE6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE5
import LatticeProb.Bonanno.LQGMetric.Metric.LengthGeodesic

/-!
# Paths avoiding a ball: Arzelà–Ascoli (task P2-E3d, decision D65 (iii))

GM = Gwynne–Miller, arXiv:1905.00383v3, the minimality clause of the avoiding geodesics
(l. 1695–1696, `IsAvoidGeod`). Own argument; it is the Arzelà–Ascoli route of
`MetricGeometry.exists_pathLength_eq_edist` (BBI Prop. 2.5.19 / Thm 2.5.14 and lower
semicontinuity of length, Prop. 2.3.4(iv)), applied to near-optimal paths in the open sets
`ℂ ∖ B̄_{r−1/(m+1)}(z)`:

* `gmE_properSpace`: a metric of `lenSet` is proper;
* `gmE_exists_avoid_path`: if `D(𝕫, x; ℂ ∖ B̄_{r−1/(m+1)}(z)) ≤ L < ∞` for all `m`, there is a
  path from `𝕫` to `x` in `ℂ ∖ B_r(z)` of `D`-length `≤ L`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM
open LocalEvent MetricGeometry BoundedContinuousFunction

theorem gmE_properSpace {d : ContMetric} (hd : d ∈ lenSet) : ProperSpace d.Space := by
  refine ProperSpace.of_isCompact_closedBall_of_le 0 fun x r _ => ?_
  have hA : IsCompact {u : ℂ | d.1 (d.unpt x, u) ≤ r} := by
    refine bcpt_of_mem_lenSet hd _ (isClosed_le (gmE_continuous_dist0 d _) continuous_const)
      ⟨2 * r, fun u hu v hv => ?_⟩
    have h1 := d.2.triangle u (d.unpt x) v
    have h2 := d.2.symm (d.unpt x) u
    simp only [mem_ofPred_eq] at hu hv
    linarith
  have h := hA.image d.continuous_pt
  convert h using 1
  ext w
  simp only [Metric.mem_closedBall, mem_image, mem_ofPred_eq]
  constructor
  · intro hw
    refine ⟨d.unpt w, ?_, rfl⟩
    rw [dist_comm] at hw
    exact hw
  · rintro ⟨u, hu, rfl⟩
    rw [dist_comm]
    exact hu

/-- **near-optimal paths avoiding shrinking balls converge** (Arzelà–Ascoli) -/
theorem gmE_exists_avoid_path {d : ContMetric} (hd : d ∈ lenSet) {𝕫 x z : ℂ} {r : ℝ}
    {L : ℝ≥0∞} (hLt : L ≠ ∞)
    (hL : ∀ m : ℕ, d.internal (closedBall z (r - 1 / ((m : ℝ) + 1)))ᶜ 𝕫 x ≤ L) :
    ∃ η : C(unitInterval, ℂ), η 0 = 𝕫 ∧ η 1 = x ∧ (∀ t, r ≤ dist (η t) z) ∧
      d.len (fun t => η (pj t)) 0 1 ≤ L := by
  have := gmE_properSpace hd
  set V : ℕ → Set ℂ := fun m => (closedBall z (r - 1 / ((m : ℝ) + 1)))ᶜ with hVdef
  have hγ : ∀ m : ℕ, ∃ γ : Path (d.pt 𝕫) (d.pt x), (∀ t, γ t ∈ d.pt '' V m) ∧
      pathLength γ ≤ L + ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
    intro m
    have hlt : internalEDist (d.pt '' V m) (d.pt 𝕫) (d.pt x) <
        L + ENNReal.ofReal (1 / ((m : ℝ) + 1)) :=
      (hL m).trans_lt (ENNReal.lt_add_right hLt (by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity))
    obtain ⟨⟨γ, hγ⟩, h⟩ := iInf_lt_iff.1 hlt
    exact ⟨γ, hγ, h.le⟩
  choose γ hγV hγle using hγ
  have hfin : ∀ n, pathLength (γ n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hLt, ENNReal.ofReal_ne_top⟩) (hγle n)
  choose δ hδlen hδrange hδlip using fun n => exists_lipschitz_path (γ n) (hfin n)
  set K : ℝ≥0 := (L + 1).toNNReal
  have hK : ∀ n, LipschitzWith K (δ n) := fun n => (hδlip n).weaken (by
    refine ENNReal.toNNReal_mono (ENNReal.add_ne_top.2 ⟨hLt, ENNReal.one_ne_top⟩)
      ((hγle n).trans (add_le_add le_rfl ?_))
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  let u : ℕ → unitInterval →ᵇ d.Space := fun n => mkOfCompact (δ n).toContinuousMap
  have hu : ∀ n t, u n t = δ n t := fun _ _ => rfl
  have hin : ∀ (f : unitInterval →ᵇ d.Space) (t : unitInterval), f ∈ range u →
      f t ∈ Metric.closedBall (d.pt 𝕫) K := by
    rintro _ t ⟨n, rfl⟩
    rw [Metric.mem_closedBall, hu]
    have h0 : δ n 0 = d.pt 𝕫 := (δ n).source
    refine (le_of_eq (by rw [h0])).trans (((hK n).dist_le_mul t 0).trans ?_)
    refine mul_le_of_le_one_right K.2 ?_
    rw [Subtype.dist_eq, Real.dist_eq]
    simp only [Set.Icc.coe_zero, sub_zero]
    rw [abs_of_nonneg t.2.1]; exact t.2.2
  have hequi : Equicontinuous ((↑) : range u → unitInterval → d.Space) := by
    refine Metric.equicontinuous_of_continuity_modulus (fun r => K * r) ?_ _ ?_
    · simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (K : ℝ)
    · rintro s t ⟨_, ⟨n, rfl⟩⟩
      exact (hK n).dist_le_mul s t
  have hcpt := arzela_ascoli (Metric.closedBall (d.pt 𝕫) K) (isCompact_closedBall _ _)
    (range u) hin hequi
  obtain ⟨f, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (x := u) fun n => subset_closure ⟨n, rfl⟩
  have hpt : ∀ t : unitInterval, Tendsto (fun n => δ (φ n) t) atTop (𝓝 (f t)) := fun t =>
    (tendsto_iff_tendstoUniformly.1 hlim).tendsto_at t
  have hf0 : f 0 = d.pt 𝕫 := tendsto_nhds_unique (hpt 0) (by simp)
  have hf1 : f 1 = d.pt x := tendsto_nhds_unique (hpt 1) (by simp)
  refine ⟨⟨fun t => d.unpt (f t), d.continuous_unpt.comp f.continuous⟩, by simp [hf0],
    by simp [hf1], fun t => ?_, ?_⟩
  · have hlim' : Tendsto (fun n => dist (d.unpt (δ (φ n) t)) z + 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (dist (d.unpt (f t)) z + 0)) :=
      (((d.continuous_unpt.tendsto _).comp (hpt t)).dist tendsto_const_nhds).add
        tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at hlim'
    refine ge_of_tendsto' hlim' fun n => ?_
    obtain ⟨s, hs⟩ := hδrange (φ n) ⟨t, rfl⟩
    obtain ⟨w, hwV, hw⟩ := hγV (φ n) s
    have hw' : d.unpt (δ (φ n) t) = w := by rw [← hs, ← hw]; rfl
    rw [hw']
    have h1 : r - 1 / ((φ n : ℝ) + 1) < dist w z := by
      simpa [hVdef, mem_closedBall, not_le] using hwV
    have h2 : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · show curveLength (fun t => f (pj t)) 0 1 ≤ L
    have e : ∀ m, curveLength (fun t => δ m (pj t)) 0 1 = pathLength (δ m) := fun m => rfl
    have hlsc : curveLength (fun t => f (pj t)) 0 1 ≤
        liminf (fun n => curveLength (fun t => δ (φ n) (pj t)) 0 1) atTop :=
      curveLength_le_liminf fun t _ => hpt (pj t)
    refine hlsc.trans ?_
    have hg : Tendsto (fun n : ℕ => L + ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 L) := by
      simpa using tendsto_const_nhds.add (ENNReal.tendsto_ofReal
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    rw [← hg.liminf_eq]
    refine Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)
    rw [e, hδlen]
    refine (hγle (φ n)).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

end LQGMetric.GM
