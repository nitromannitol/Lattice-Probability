import LatticeProb.LQG.ContMetricLength

/-! # Euclidean length metrics are continuous length metrics

Converse of `LatticeProb.LQG.isEuclideanLengthMetric_of_isLength`. A Euclidean length metric `D` on `ℂ`
(`IsEuclideanLengthMetric D`: a metric inducing the Euclidean topology, equal to its internal metric) is
a jointly continuous function of `(u, v)`, its small balls are Euclidean-small, and `(ℂ, D)` is a length
space. Hence `D` is an element of `LQGMetric.ContMetric` (`IsEuclideanLengthMetric.contMetric`), which is a
length space (`IsEuclideanLengthMetric.isLength_contMetric`).

* `IsEuclideanLengthMetric.continuous`: `(u, v) ↦ D u v` is continuous on `ℂ × ℂ`.
* `IsEuclideanLengthMetric.isContinuousMetric`: it is a continuous metric in the sense of `LQGMetric`.
* `IsEuclideanLengthMetric.contMetric`, `contMetric_apply`, `isLength_contMetric`.
* `exists_contMetric_of_isEuclideanLengthMetric`: the existential form.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal

namespace LatticeProb.LQG

namespace IsEuclideanLengthMetric

variable {D : ℂ → ℂ → ℝ}

/-- The `D`-balls of a Euclidean length metric are open. -/
theorem isOpen_ball (hD : IsEuclideanLengthMetric D) (x : ℂ) (r : ℝ) :
    IsOpen {w : ℂ | D x w < r} := by
  rw [hD.isOpen_iff]
  intro z hz
  have hz' : D x z < r := hz
  refine ⟨r - D x z, by linarith, fun w hw => ?_⟩
  show D x w < r
  linarith [hD.triangle x z w]

/-- The `D`-distance from a point tends to `0` for the Euclidean topology. -/
theorem eventually_lt (hD : IsEuclideanLengthMetric D) (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 x, D x w < ε :=
  (hD.isOpen_ball x ε).mem_nhds (by show D x x < ε; rw [hD.self_eq_zero]; exact hε)

/-- A Euclidean length metric is jointly continuous for the Euclidean topology. -/
theorem continuous (hD : IsEuclideanLengthMetric D) : Continuous fun p : ℂ × ℂ => D p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨x, y⟩ := p
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have h1 : ∀ᶠ q : ℂ × ℂ in 𝓝 (x, y), D x q.1 < ε / 2 :=
    (continuous_fst.tendsto (x, y)).eventually (hD.eventually_lt x (by linarith))
  have h2 : ∀ᶠ q : ℂ × ℂ in 𝓝 (x, y), D y q.2 < ε / 2 :=
    (continuous_snd.tendsto (x, y)).eventually (hD.eventually_lt y (by linarith))
  filter_upwards [h1, h2] with q hq1 hq2
  rw [Real.dist_eq, abs_lt]
  have a1 := hD.triangle q.1 y q.2
  have a2 := hD.triangle q.1 x y
  have a3 := hD.triangle x q.2 y
  have a4 := hD.triangle x q.1 q.2
  have s1 := hD.symm q.1 x
  have s2 := hD.symm y q.2
  have s3 := hD.symm q.2 y
  constructor <;> linarith

/-- A Euclidean length metric is a continuous metric. -/
theorem isContinuousMetric (hD : IsEuclideanLengthMetric D) :
    LQGMetric.IsContinuousMetric ⟨fun p : ℂ × ℂ => D p.1 p.2, hD.continuous⟩ where
  self_eq_zero x := hD.self_eq_zero x
  eq_of_eq_zero x y h := hD.eq_of_eq_zero x y h
  symm x y := hD.symm x y
  triangle x y z := hD.triangle x y z
  euclidean_of_small x ε hε := by
    obtain ⟨δ, hδ, h⟩ := (hD.isOpen_iff _ |>.1 (Metric.isOpen_ball (x := x) (ε := ε))) x
      (Metric.mem_ball_self hε)
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have := h y hy
    rw [Metric.mem_ball, dist_comm] at this
    simpa [dist_eq_norm] using this

/-- The Euclidean length metric `D`, as an element of `LQGMetric.ContMetric`. -/
def contMetric (hD : IsEuclideanLengthMetric D) : LQGMetric.ContMetric :=
  ⟨⟨fun p : ℂ × ℂ => D p.1 p.2, hD.continuous⟩, hD.isContinuousMetric⟩

@[simp] theorem contMetric_apply (hD : IsEuclideanLengthMetric D) (u v : ℂ) :
    (hD.contMetric).1 (u, v) = D u v := rfl

/-- `(ℂ, D)` is a length space when `D` is a Euclidean length metric. -/
theorem isLength_contMetric (hD : IsEuclideanLengthMetric D) : hD.contMetric.IsLength := by
  intro x y ε hε
  have h1 : ENNReal.ofReal (D (hD.contMetric.unpt x) (hD.contMetric.unpt y)) =
      hD.contMetric.internal univ (hD.contMetric.unpt x) (hD.contMetric.unpt y) :=
    (hD.ofReal_eq_internalMetric _ _).trans (internalMetric_contMetric hD.contMetric univ _ _)
  have himg : hD.contMetric.pt '' (univ : Set ℂ) = univ :=
    image_univ_of_surjective (fun y => ⟨y, rfl⟩)
  rw [LQGMetric.ContMetric.internal, himg] at h1
  have h2 : ENNReal.ofReal (D (hD.contMetric.unpt x) (hD.contMetric.unpt y)) = edist x y := by
    rw [edist_dist]; rfl
  have hlt : LQGMetric.MetricGeometry.internalEDist univ x y <
      edist x y + ENNReal.ofReal ε := by
    have h3 : LQGMetric.MetricGeometry.internalEDist univ x y = edist x y := h1.symm.trans h2
    rw [h3]
    exact ENNReal.lt_add_right (edist_ne_top x y) (by simpa using hε)
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 hlt
  exact ⟨γ.1, hγ.le⟩

end IsEuclideanLengthMetric

/-- A Euclidean length metric is a continuous metric on `ℂ` for which `(ℂ, D)` is a length space. -/
theorem exists_contMetric_of_isEuclideanLengthMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength :=
  ⟨hD.contMetric, fun _ _ => rfl, hD.isLength_contMetric⟩

end LatticeProb.LQG
