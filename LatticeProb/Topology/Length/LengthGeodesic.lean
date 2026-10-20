/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/LengthGeodesic.lean.
-/
import LatticeProb.Topology.Length.CurveNatural
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Shortest paths in proper length spaces

Throughout, `X` is a metric space which is *proper* (`[ProperSpace X]`: closed bounded sets are
compact) and a *length space* (`hX : IsLengthSpace X`: for all `x y : X` and every `ε > 0` there is
a path from `x` to `y` of length at most `edist x y + ε`).

`exists_pathLength_eq_edist`: in a proper length space, any two points are joined by a path whose
length equals their distance, i.e. a path of minimal length.
`exists_shortest_path`: in a proper length space, any two points are joined by a path which
minimizes length among all paths from `x` to `y`.

This is the statement that a proper length space is geodesic, in the sense of minimal-length paths,
as in Burago–Burago–Ivanov, *A course in metric geometry*, Cor. 2.5.20, and Petrunin, *Pure metric
geometry* (arXiv:2007.09846), Prop. 1.28 ("any proper length space is geodesic").

Proof (Burago–Burago–Ivanov's route, Prop. 2.5.19 via Arzelà–Ascoli Thm 2.5.14 and lower semicontinuity of
length Prop. 2.3.4(iv)): take paths `γₙ` of length `≤ d(x, y) + 1/(n+1)`, reparametrize them at
constant speed (so they are uniformly `(d(x,y)+1)`-Lipschitz on `[0,1]`, `exists_lipschitz_path`),
extract a uniformly convergent subsequence by mathlib's Arzelà–Ascoli
(`BoundedContinuousFunction.arzela_ascoli`; all curves lie in the compact ball
`closedBall x (d(x,y)+1)`), and conclude by lower semicontinuity of length
(`curveLength_le_liminf`).
-/

open Set Filter Topology unitInterval BoundedContinuousFunction
open scoped ENNReal NNReal

namespace LatticeProb.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- **Existence of shortest paths.** In a proper (`[ProperSpace X]`) length space
(`hX : IsLengthSpace X`), any two points `x y` are joined by a path `γ` of length equal to their
distance: `pathLength γ = edist x y`. -/
theorem exists_pathLength_eq_edist [ProperSpace X] (hX : IsLengthSpace X) (x y : X) :
    ∃ γ : Path x y, pathLength γ = edist x y := by
  -- almost minimizing paths
  have hγ : ∀ n : ℕ, ∃ γ : Path x y,
      pathLength γ ≤ edist x y + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    hX x y _ (by positivity)
  choose γ hγle using hγ
  have hfin : ∀ n, pathLength (γ n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨edist_ne_top x y, ENNReal.ofReal_ne_top⟩)
      (hγle n)
  -- constant-speed reparametrizations
  choose δ hδlen _hδrange hδlip using fun n => exists_lipschitz_path (γ n) (hfin n)
  set K : ℝ≥0 := (edist x y + 1).toNNReal
  have hK : ∀ n, LipschitzWith K (δ n) := fun n => (hδlip n).weaken (by
    refine ENNReal.toNNReal_mono (ENNReal.add_ne_top.2 ⟨edist_ne_top x y, ENNReal.one_ne_top⟩)
      ((hγle n).trans (add_le_add le_rfl ?_))
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  let u : ℕ → I →ᵇ X := fun n => mkOfCompact (δ n).toContinuousMap
  have hu : ∀ n t, u n t = δ n t := fun _ _ => rfl
  -- Arzelà–Ascoli
  have hin : ∀ (f : I →ᵇ X) (t : I), f ∈ range u → f t ∈ Metric.closedBall x K := by
    rintro _ t ⟨n, rfl⟩
    rw [Metric.mem_closedBall, hu]
    have h0 : δ n 0 = x := (δ n).source
    refine (le_of_eq (by rw [h0])).trans (((hK n).dist_le_mul t 0).trans ?_)
    refine mul_le_of_le_one_right K.2 ?_
    rw [Subtype.dist_eq, Real.dist_eq]
    simp only [Set.Icc.coe_zero, sub_zero]
    rw [abs_of_nonneg t.2.1]; exact t.2.2
  have hequi : Equicontinuous ((↑) : range u → I → X) := by
    refine Metric.equicontinuous_of_continuity_modulus (fun r => K * r) ?_ _ ?_
    · simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (K : ℝ)
    · rintro s t ⟨_, ⟨n, rfl⟩⟩
      exact (hK n).dist_le_mul s t
  have hcpt := arzela_ascoli (Metric.closedBall x K) (isCompact_closedBall x K) (range u) hin hequi
  obtain ⟨f, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (x := u) fun n => subset_closure ⟨n, rfl⟩
  have hpt : ∀ t : I, Tendsto (fun n => δ (φ n) t) atTop (𝓝 (f t)) := fun t =>
    (tendsto_iff_tendstoUniformly.1 hlim).tendsto_at t
  have hf0 : f 0 = x := tendsto_nhds_unique (hpt 0) (by simp)
  have hf1 : f 1 = y := tendsto_nhds_unique (hpt 1) (by simp)
  let γ₀ : Path x y := { toContinuousMap := f.toContinuousMap, source' := hf0, target' := hf1 }
  refine ⟨γ₀, le_antisymm ?_ (edist_le_pathLength γ₀)⟩
  -- lower semicontinuity
  have hlsc : pathLength γ₀ ≤ liminf (fun n => pathLength (δ (φ n))) atTop := by
    refine curveLength_le_liminf fun t ht => ?_
    rw [Path.extend_apply γ₀ ht]
    refine (hpt ⟨t, ht⟩).congr fun n => ?_
    exact (Path.extend_apply _ ht).symm
  refine hlsc.trans ?_
  have hg : Tendsto (fun n : ℕ => edist x y + ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (edist x y)) := by
    simpa using tendsto_const_nhds.add (ENNReal.tendsto_ofReal
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  rw [← hg.liminf_eq]
  refine Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)
  rw [hδlen]
  refine (hγle (φ n)).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **Shortest paths minimize length.** In a proper (`[ProperSpace X]`) length space
(`hX : IsLengthSpace X`), any two points `x y` are joined by a path `γ` with
`pathLength γ ≤ pathLength γ'` for every path `γ'` from `x` to `y`. -/
theorem exists_shortest_path [ProperSpace X] (hX : IsLengthSpace X) (x y : X) :
    ∃ γ : Path x y, ∀ γ' : Path x y, pathLength γ ≤ pathLength γ' := by
  obtain ⟨γ, hγ⟩ := exists_pathLength_eq_edist hX x y
  exact ⟨γ, fun γ' => hγ ▸ edist_le_pathLength γ'⟩

/-! ### Nonvacuity example -/

namespace LengthGeodesicExample

/-- `ℝ` is a length space: the segment from `x` to `y` has length `‖y - x‖ = d(x, y)`. Together
with `ProperSpace ℝ`, this shows that the hypotheses of `exists_pathLength_eq_edist` and
`exists_shortest_path` are satisfiable, so their conclusions are not vacuous. -/
example : (∀ x y : ℝ, ∃ γ : Path x y, pathLength γ = edist x y) ∧
    (∀ x y : ℝ, ∃ γ : Path x y, ∀ γ' : Path x y, pathLength γ ≤ pathLength γ') := by
  have hℝ : IsLengthSpace ℝ := by
    intro x y ε hε
    let γ : Path x y :=
      { toFun := fun t => x + (t : ℝ) • (y - x)
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by simp }
    have hlip : LipschitzWith ‖y - x‖₊ (fun s : ℝ => x + s • (y - x)) := by
      refine LipschitzWith.of_dist_le_mul fun s t => ?_
      show dist (x + s • (y - x)) (x + t • (y - x)) ≤ (‖y - x‖₊ : ℝ) * dist s t
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, Real.dist_eq,
        coe_nnnorm]
      exact le_of_eq (mul_comm _ _)
    have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t = x + t • (y - x) := fun t ht =>
      (Path.extend_apply γ ht).trans rfl
    refine ⟨γ, ?_⟩
    calc pathLength γ = curveLength (fun s : ℝ => x + s • (y - x)) 0 1 := by
          unfold pathLength
          exact curveLength_congr fun t ht => hγ t ht
      _ ≤ ‖y - x‖₊ * eVariationOn (id : ℝ → ℝ) (Icc 0 1) := by
          unfold curveLength
          exact hlip.lipschitzOnWith.comp_eVariationOn_le (g := id) (mapsTo_univ _ _)
      _ = edist x y := by
          rw [eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one, mul_one, edist_comm,
            edist_eq_enorm_sub, enorm_eq_nnnorm]
      _ ≤ edist x y + ENNReal.ofReal ε := le_self_add
  exact ⟨fun x y => exists_pathLength_eq_edist hℝ x y, fun x y => exists_shortest_path hℝ x y⟩

end LengthGeodesicExample

end LatticeProb.MetricGeometry
