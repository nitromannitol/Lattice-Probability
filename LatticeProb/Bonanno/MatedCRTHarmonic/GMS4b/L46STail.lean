/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46STail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.Lemma25Tail
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dtgt
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Uniform finite-region degree tail

This is the finite-union step in [18] Lemma 2.6, using the uniform
single-vertex exponential tail from the proof of Lemma 2.5.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4b

/-- Forgetting loops and parallel edges cannot increase degree: every
simple-graph neighbor is reached by at least one outgoing multigraph dart. -/
theorem l46s_simple_degree_le_multidegree {V E : Type*}
    (G : LFMultigraph V E) (x : V) :
    (G.adj.neighborSet x).Finite ∧
      (G.adj.neighborSet x).ncard ≤ G.deg x := by
  classical
  have hsub : G.adj.neighborSet x ⊆ G.dtgt '' (G.outDarts x : Set G.Dart) := by
    intro y hy
    have hxy : G.adj.Adj x y := (SimpleGraph.mem_neighborSet G.adj x y).mp hy
    obtain ⟨_, (⟨e, he₁, he₂⟩ | ⟨e, he₁, he₂⟩)⟩ :=
      (SimpleGraph.fromRel_adj (fun a b => ∃ e, G.src e = a ∧ G.tgt e = b) x y).mp hxy
    · refine ⟨(e, false), ?_, ?_⟩
      · have he : e ∈ (G.finite_inc x).toFinset := by
          simp [he₁]
        change (e, false) ∈ (((G.finite_inc x).toFinset ×ˢ
          (Finset.univ : Finset Bool)).filter fun d => G.dsrc d = x)
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩,
          by simp [LFMultigraph.dsrc, he₁]⟩
      · simp [LFMultigraph.dtgt, he₂]
    · refine ⟨(e, true), ?_, ?_⟩
      · have he : e ∈ (G.finite_inc x).toFinset := by
          simp [he₂]
        change (e, true) ∈ (((G.finite_inc x).toFinset ×ˢ
          (Finset.univ : Finset Bool)).filter fun d => G.dsrc d = x)
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩,
          by simp [LFMultigraph.dsrc, he₂]⟩
      · simp [LFMultigraph.dtgt, he₁]
  have hfin : (G.adj.neighborSet x).Finite :=
    ((G.outDarts x).finite_toSet.image G.dtgt).subset hsub
  have henc : (G.adj.neighborSet x).encard ≤ (G.deg x : ℕ∞) := by
    calc
      (G.adj.neighborSet x).encard ≤
          (G.dtgt '' (G.outDarts x : Set G.Dart)).encard := Set.encard_le_encard hsub
      _ ≤ (G.outDarts x : Set G.Dart).encard := Set.encard_image_le _ _
      _ = (G.deg x : ℕ∞) := by
        rw [Set.encard_coe_eq_coe_finsetCard]
        rfl
  refine ⟨hfin, ?_⟩
  rw [← hfin.cast_ncard_eq] at henc
  exact_mod_cast henc

/-- Inducing on any vertex set cannot increase the simple degree, which in
turn is bounded by the raw multigraph degree controlled by L25. -/
theorem l46s_induced_degree_le_multidegree {V E : Type*}
    (G : LFMultigraph V E) (S : Set V) (v : S) :
    ((G.adj.induce S).neighborSet v).ncard ≤ G.deg v.val := by
  have hmap : ∀ w ∈ (G.adj.induce S).neighborSet v,
      (w : V) ∈ G.adj.neighborSet v.val := by
    intro w hw
    exact hw
  exact (Set.ncard_le_ncard_of_injOn (fun w : S => (w : V))
      hmap Subtype.val_injective.injOn (l46s_simple_degree_le_multidegree G v.val).1).trans
    (l46s_simple_degree_le_multidegree G v.val).2

/-- The degree tail on any deterministic finite collection of mesh vertices.
The bound is uniform in the mesh and in the selected vertices. -/
theorem l46s_degree_tail_finset {γ : ℝ} {μ : Measure MatedCRT.Path2}
    (hμ : MatedCRT.IsCorrelatedBM2 γ μ) {ε : ℝ} (hε : 0 < ε)
    (s : Finset ℤ) (n : ℕ) :
    μ {ω | ∃ x ∈ s, (n : ℕ∞) < MatedCRT.lemma25Degree ε ω x} ≤
      ∑ _x ∈ s, ENNReal.ofReal
        (MatedCRT.lemma25TailC₀ * Real.exp (-(MatedCRT.lemma25TailC₁ * n))) := by
  let E : ℤ → Set MatedCRT.Path2 := fun x =>
    {ω | (n : ℕ∞) < MatedCRT.lemma25Degree ε ω x}
  have heq : {ω | ∃ x ∈ s, (n : ℕ∞) < MatedCRT.lemma25Degree ε ω x} =
      ⋃ x ∈ s, E x := by
    ext ω
    simp [E]
  rw [heq]
  calc
    μ (⋃ x ∈ s, E x) ≤ ∑ x ∈ s, μ (E x) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ s, ENNReal.ofReal
        (MatedCRT.lemma25TailC₀ * Real.exp (-(MatedCRT.lemma25TailC₁ * n))) := by
      apply Finset.sum_le_sum
      intro x _
      exact MatedCRT.lemma25Tail_degree_tail hμ hε x n

/-- Pull the finite-vertex L25 tail back through the bundle's Brownian
boundary-length coordinate. -/
theorem l46s_coupling_degree_tail_finset
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {ε : ℝ} (hε : 0 < ε) (s : Finset ℤ) (n : ℕ) :
    P {ω | ∃ x ∈ s, (n : ℕ∞) < MatedCRT.lemma25Degree ε (bm ω) x} ≤
      ∑ _x ∈ s, ENNReal.ofReal
        (MatedCRT.lemma25TailC₀ * Real.exp (-(MatedCRT.lemma25TailC₁ * n))) := by
  let E : Set MatedCRT.Path2 :=
    {ξ | ∃ x ∈ s, (n : ℕ∞) < MatedCRT.lemma25Degree ε ξ x}
  have hE : MeasurableSet E := by
    have heq : E = ⋃ x : ℤ, ⋃ _ : x ∈ s,
        {ξ : MatedCRT.Path2 | (n : ℕ∞) < MatedCRT.lemma25Degree ε ξ x} := by
      ext ξ
      simp [E]
    rw [heq]
    exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
      (MatedCRT.measurable_lemma25Degree ε x)
        (MeasurableSet.of_discrete (s := Ioi (n : ℕ∞)))
  change P (bm ⁻¹' E) ≤ _
  rw [← Measure.map_apply D.measurable_curves.2.2.2 hE]
  exact l46s_degree_tail_finset D.boundaryLawBM hε s n

end MatedCRTHarmonic.GMS4b
