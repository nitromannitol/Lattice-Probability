/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.InternalC at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import LatticeProb.Bonanno.LQGMetric.Statement.Metric

/-!
For `D : ContMetric` (FOUNDATIONS §4–5; `D.Space` is `ℂ` with the metric `D`):

* `ContMetric.ptHomeomorph`: the identity `ℂ → D.Space` is a homeomorphism (from
  `IsContinuousMetric`: `D` is continuous and small `D`-balls are Euclidean-small).
* `ContMetric.continuousOn_internal` (**LM Lemma 1.1**, continuity): for `D` a length metric and
  `V` open, `D(·,·;V)` is continuous on `V × V` (Euclidean topology).
* `ContMetric.infEDist_frontier_le_of_internal_eq`, `ContMetric.infEDist_frontier_eq_of_internal_eq`
  (**GM S3.1 (a)**, GM tex:1197, 1351): `D(u, ∂V)` is determined by `D(·,·;V)`: two continuous
  metrics with the same internal metric on `V`, the first a length metric, satisfy
  `D'(u, ∂V) ≤ D(u, ∂V)`, with equality when both are length metrics.
* `ContMetric.ball_eq_of_internal_eq` (**GM S3.1**, "hence the ball of radius `D(u, ∂V)` is
  determined by `D(·,·;V)`", GM tex:1197): the open `D`-ball of radius `D(u, ∂V)` at `u` only
  depends on `D(·,·;V)`.

Proof of GM S3.1 (a) (GM gives none; elementary, own write-up): a path `γ` from `u` to a point
outside `V`, stopped at its first exit time `s₀`, stays in `V` before `s₀`; there
`D'(u, γ t) ≤ D'(u, γ t; V) = D(u, γ t; V) ≤ len(γ; D)`, and `γ s₀ ∈ ∂V` by continuity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology unitInterval
open scoped ENNReal

namespace LQGMetric

open MetricGeometry

namespace ContMetric

/-- The identity `ℂ → D.Space` is continuous. -/
theorem continuous_pt (D : ContMetric) : Continuous D.pt := by
  refine Metric.continuous_iff.2 fun x ε hε => ?_
  have hc : Continuous fun y : ℂ => D.1 (y, x) :=
    D.1.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc x ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h' := h y hy
  rw [D.2.self_eq_zero x, Real.dist_eq, sub_zero] at h'
  exact (le_abs_self _).trans_lt h'

/-- The identity `D.Space → ℂ`. -/
def unpt (D : ContMetric) : D.Space → ℂ := id

@[simp] theorem unpt_pt (D : ContMetric) (z : ℂ) : D.unpt (D.pt z) = z := rfl

@[simp] theorem pt_unpt (D : ContMetric) (x : D.Space) : D.pt (D.unpt x) = x := rfl

/-- The identity `D.Space → ℂ` is continuous. -/
theorem continuous_unpt (D : ContMetric) : Continuous D.unpt := by
  refine Metric.continuous_iff.2 fun b ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := D.2.euclidean_of_small b ε hε
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have ha' : D.1 (b, a) < δ := lt_of_eq_of_lt (D.2.symm b a) ha
  rw [Complex.dist_eq, norm_sub_rev]
  exact h a ha'

/-- The identity `ℂ ≃ₜ D.Space`. -/
def ptHomeomorph (D : ContMetric) : ℂ ≃ₜ D.Space where
  toFun := D.pt
  invFun := D.unpt
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := D.continuous_pt
  continuous_invFun := D.continuous_unpt

theorem isOpen_image_pt (D : ContMetric) {V : Set ℂ} (hV : IsOpen V) : IsOpen (D.pt '' V) :=
  D.ptHomeomorph.isOpenMap V hV

theorem mem_image_pt (D : ContMetric) {V : Set ℂ} {z : ℂ} : D.pt z ∈ D.pt '' V ↔ z ∈ V :=
  ⟨fun ⟨w, hw, h⟩ => (show w = z from h) ▸ hw, fun h => ⟨z, h, rfl⟩⟩

/-- **LM Lemma 1.1** (continuity) on `ℂ`: for a length metric `D` and `V` open, `D(·,·;V)` is
continuous on `V × V`. -/
theorem continuousOn_internal (D : ContMetric) (hD : D.IsLength) {V : Set ℂ} (hV : IsOpen V) :
    ContinuousOn (fun p : ℂ × ℂ => D.internal V p.1 p.2) (V ×ˢ V) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let f : V → D.pt '' V := fun z => ⟨D.pt z, z, z.2, rfl⟩
  have hf : Continuous f := (D.continuous_pt.comp continuous_subtype_val).subtype_mk _
  have hc := InternalSpace.continuous_internalEDist hD (D.isOpen_image_pt hV)
  have h1 : Continuous fun p : V ×ˢ V => (⟨p.1.1, (mem_prod.1 p.2).1⟩ : V) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have h2 : Continuous fun p : V ×ˢ V => (⟨p.1.2, (mem_prod.1 p.2).2⟩ : V) :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  exact hc.comp ((hf.comp h1).prodMk (hf.comp h2))

/-- Points `D`-closer to `u ∈ V` than `D(u, ∂V)` lie in `V`, and there `D(u, v) = D(u, v; V)`
(LM tex:213–214 / GM tex:1197). -/
theorem internal_eq_of_lt_infEDist_frontier {D : ContMetric} (hD : D.IsLength) {V : Set ℂ}
    (hV : IsOpen V) {u v : ℂ} (hu : u ∈ V)
    (hv : edist (D.pt u) (D.pt v) < Metric.infEDist (D.pt u) (D.pt '' frontier V)) :
    v ∈ V ∧ D.internal V u v = edist (D.pt u) (D.pt v) := by
  have hfr : D.pt '' frontier V = frontier (D.pt '' V) := D.ptHomeomorph.image_frontier V
  rw [hfr, ← infEDist_compl_eq_infEDist_frontier hD (D.isOpen_image_pt hV) ⟨u, hu, rfl⟩] at hv
  have hball : Metric.eball (D.pt u) (Metric.infEDist (D.pt u) (D.pt '' V)ᶜ) ⊆ D.pt '' V :=
    fun x hx => by
      by_contra hxV
      rw [Metric.mem_eball, edist_comm] at hx
      exact (Metric.infEDist_le_edist_of_mem hxV).not_gt hx
  refine ⟨D.mem_image_pt.1 (hball (by rw [Metric.mem_eball, edist_comm]; exact hv)), ?_⟩
  exact internalEDist_eq_edist_of_ball_subset hD hball hv

end ContMetric

end LQGMetric
