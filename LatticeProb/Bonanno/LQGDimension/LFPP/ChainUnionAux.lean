/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ChainUnionAux at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Auxiliary lemmas for node `U49` (`Draft.ChainUnionBound`)

* Algebra of `SegComb.avg` (appending, scaling, flattening), and the test combinations
  `scomb` / `pcomb` whose averages are `cfgVal + k` and sums of these along a chain.
* Continuity of `cfgVal φ δ k` in the vertices of configurations with nondegenerate polygons, and
  the existence of a countable dense sequence in any family of such configurations.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension

namespace ChainUnion

open Blueprint.Draft

/-! ### Algebra of `SegComb.avg` -/

theorem avg_nil (φ : ℂ → ℝ) : SegComb.avg φ [] = 0 := by
  simp [SegComb.avg]

theorem avg_cons (φ : ℂ → ℝ) (p : ℝ × ℂ × ℂ) (c : SegComb) :
    SegComb.avg φ (p :: c) = p.1 * segAvg φ p.2.1 p.2.2 + SegComb.avg φ c := by
  simp [SegComb.avg]

theorem avg_append (φ : ℂ → ℝ) (c c' : SegComb) :
    SegComb.avg φ (c ++ c') = SegComb.avg φ c + SegComb.avg φ c' := by
  induction c with
  | nil => simp [avg_nil]
  | cons p c ih => rw [List.cons_append, avg_cons, avg_cons, ih]; ring

theorem avg_smul (φ : ℂ → ℝ) (r : ℝ) (c : SegComb) :
    SegComb.avg φ (SegComb.smul r c) = r * SegComb.avg φ c := by
  induction c with
  | nil => simp [SegComb.smul, avg_nil]
  | cons p c ih =>
    simp only [SegComb.smul, List.map_cons] at ih ⊢
    rw [avg_cons, avg_cons, ih]
    ring

theorem avg_negw (φ : ℂ → ℝ) (c : SegComb) :
    SegComb.avg φ (c.map fun (p : ℝ × ℂ × ℂ) => (-p.1, p.2)) = -SegComb.avg φ c := by
  induction c with
  | nil => simp [avg_nil]
  | cons p c ih =>
    rw [List.map_cons, avg_cons, avg_cons, ih]
    ring

theorem avg_sub (φ : ℂ → ℝ) (c c' : SegComb) :
    SegComb.avg φ (SegComb.sub c c') = SegComb.avg φ c - SegComb.avg φ c' := by
  rw [SegComb.sub, avg_append, avg_negw]
  ring

theorem avg_flatten (φ : ℂ → ℝ) (L : List SegComb) :
    SegComb.avg φ L.flatten = (L.map (SegComb.avg φ)).sum := by
  induction L with
  | nil => simp [avg_nil]
  | cons c L ih => rw [List.flatten_cons, avg_append, ih, List.map_cons, List.sum_cons]

/-- The scaled test combination `δ^{-1/2} (ν_{P₁} - ν_{P₂})` of a configuration. -/
def scomb (δ : ℝ) (c : Config) : SegComb :=
  SegComb.smul (δ ^ (-(1 / 2 : ℝ))) (cfgComb c)

theorem avg_scomb (φ : ℂ → ℝ) (δ : ℝ) (k : ℕ) (c : Config) :
    (scomb δ c).avg φ = cfgVal φ δ k c + k := by
  rw [scomb, avg_smul, cfgComb, avg_sub, cfgVal, polyAvg, polyAvg]
  ring

/-- The concatenated scaled test combination of a tuple of configurations. -/
def pcomb {l : ℕ} (δ : ℝ) (c : Fin l → Config) : SegComb :=
  (List.ofFn fun i => scomb δ (c i)).flatten

theorem avg_pcomb (φ : ℂ → ℝ) (δ : ℝ) {l : ℕ} (k : Fin l → ℕ) (c : Fin l → Config) :
    (pcomb δ c).avg φ = ∑ i, cfgVal φ δ (k i) (c i) + ∑ i, (k i : ℝ) := by
  rw [pcomb, avg_flatten, List.map_ofFn, List.sum_ofFn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  exact avg_scomb φ δ (k i) (c i)

/-! ### Continuity of `cfgVal` in the vertices -/

/-- Sum of a function over the edges of a vertex list. -/
def edgeSum (g : ℂ × ℂ → ℝ) (z : List ℂ) : ℝ := ((edges z).map g).sum

theorem edges_ofFn_succ {n : ℕ} (a : Fin (n + 1) → ℂ) :
    edges (List.ofFn a) = List.ofFn (fun i : Fin n => (a i.castSucc, a i.succ)) := by
  apply List.ext_getElem
  · simp [edges]
  · intro i h1 h2
    simp only [edges, List.getElem_zip, List.getElem_tail, List.getElem_ofFn]
    rfl

theorem continuous_edgeSum_ofFn {g : ℂ × ℂ → ℝ} (hg : Continuous g) (n : ℕ) :
    Continuous fun a : Fin n → ℂ => edgeSum g (List.ofFn a) := by
  cases n with
  | zero =>
    simp only [edgeSum, List.ofFn_zero, edges, List.tail_nil, List.zip_nil_left, List.map_nil,
      List.sum_nil]
    exact continuous_const
  | succ n =>
    simp only [edgeSum, edges_ofFn_succ, List.map_ofFn, List.sum_ofFn]
    refine continuous_finsetSum _ fun i _ => ?_
    exact hg.comp ((continuous_apply _).prodMk (continuous_apply _))

/-- Unnormalized polygon integral `Σ_e |e| ⟨φ, ν_e⟩`. -/
def polyInt (φ : ℂ → ℝ) (z : List ℂ) : ℝ :=
  edgeSum (fun e => ‖e.2 - e.1‖ * segAvg φ e.1 e.2) z

theorem polyLen_eq_edgeSum (z : List ℂ) : polyLen z = edgeSum (fun e => ‖e.2 - e.1‖) z := rfl

theorem polyAvg_eq (φ : ℂ → ℝ) (z : List ℂ) : polyAvg φ z = polyInt φ z / polyLen z := by
  simp only [polyAvg, polyComb, SegComb.avg, List.map_map, polyInt, edgeSum, div_eq_mul_inv]
  rw [← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply]
  ring

theorem continuous_segAvg {φ : ℂ → ℝ} (hφ : Continuous φ) :
    Continuous fun p : ℂ × ℂ => segAvg φ p.1 p.2 := by
  unfold segAvg
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hφ.comp (by fun_prop)

theorem continuousAt_polyAvg_ofFn {φ : ℂ → ℝ} (hφ : Continuous φ) {n : ℕ} (a : Fin n → ℂ)
    (ha : 0 < polyLen (List.ofFn a)) :
    ContinuousAt (fun b : Fin n → ℂ => polyAvg φ (List.ofFn b)) a := by
  simp_rw [polyAvg_eq, polyLen_eq_edgeSum]
  refine ContinuousAt.div ?_ ?_ ha.ne'
  · exact (continuous_edgeSum_ofFn
      ((continuous_norm.comp (continuous_snd.sub continuous_fst)).mul (continuous_segAvg hφ))
      n).continuousAt
  · exact (continuous_edgeSum_ofFn (continuous_norm.comp (continuous_snd.sub continuous_fst))
      n).continuousAt

theorem continuousAt_cfgVal_ofFn {φ : ℂ → ℝ} (hφ : Continuous φ) (δ : ℝ) (k : ℕ) {n₁ n₂ : ℕ}
    (p : (Fin n₁ → ℂ) × (Fin n₂ → ℂ)) (h₁ : 0 < polyLen (List.ofFn p.1))
    (h₂ : 0 < polyLen (List.ofFn p.2)) :
    ContinuousAt (fun q : (Fin n₁ → ℂ) × (Fin n₂ → ℂ) =>
      cfgVal φ δ k (List.ofFn q.1, List.ofFn q.2)) p := by
  unfold cfgVal
  have c1 : ContinuousAt (fun q : (Fin n₁ → ℂ) × (Fin n₂ → ℂ) => polyAvg φ (List.ofFn q.1)) p :=
    (continuousAt_polyAvg_ofFn hφ p.1 h₁).comp continuous_fst.continuousAt
  have c2 : ContinuousAt (fun q : (Fin n₁ → ℂ) × (Fin n₂ → ℂ) => polyAvg φ (List.ofFn q.2)) p :=
    (continuousAt_polyAvg_ofFn hφ p.2 h₂).comp continuous_snd.continuousAt
  exact (continuousAt_const.mul (c1.sub c2)).sub continuousAt_const

/-- A family of configurations with nondegenerate polygons contains a sequence which is dense for
the values of `cfgVal φ δ k`, simultaneously for all continuous `φ`. -/
theorem exists_dense_seq_config (S : Set Config) (hS : S.Nonempty)
    (hpos : ∀ c ∈ S, 0 < polyLen c.1 ∧ 0 < polyLen c.2) :
    ∃ e : ℕ → Config, (∀ j, e j ∈ S) ∧ ∀ c ∈ S, ∀ φ : ℂ → ℝ, Continuous φ → ∀ (δ : ℝ) (k : ℕ),
      ∀ η > 0, ∃ j, |cfgVal φ δ k (e j) - cfgVal φ δ k c| < η := by
  let T : ∀ n₁ n₂ : ℕ, Set ((Fin n₁ → ℂ) × (Fin n₂ → ℂ)) := fun n₁ n₂ =>
    {p | (List.ofFn p.1, List.ofFn p.2) ∈ S}
  have hsep : ∀ n₁ n₂, ∃ s : Set (T n₁ n₂), s.Countable ∧ Dense s := fun n₁ n₂ =>
    TopologicalSpace.exists_countable_dense (T n₁ n₂)
  choose s hsc hsd using hsep
  let emb : ∀ n₁ n₂, T n₁ n₂ → Config := fun n₁ n₂ q => (List.ofFn q.1.1, List.ofFn q.1.2)
  let D : Set Config := ⋃ n₁, ⋃ n₂, emb n₁ n₂ '' s n₁ n₂
  have hDS : D ⊆ S := by
    intro d hd
    simp only [D, mem_iUnion, mem_image] at hd
    obtain ⟨n₁, n₂, q, _, rfl⟩ := hd
    exact q.2
  have hDc : D.Countable :=
    countable_iUnion fun n₁ => countable_iUnion fun n₂ => (hsc n₁ n₂).image _
  -- the approximation property
  have happrox : ∀ c ∈ S, ∀ φ : ℂ → ℝ, Continuous φ → ∀ (δ : ℝ) (k : ℕ),
      ∀ η > 0, ∃ d ∈ D, |cfgVal φ δ k d - cfgVal φ δ k c| < η := by
    intro c hc φ hφ δ k η hη
    set n₁ := c.1.length
    set n₂ := c.2.length
    obtain ⟨p, hpc⟩ : ∃ p : (Fin n₁ → ℂ) × (Fin n₂ → ℂ), (List.ofFn p.1, List.ofFn p.2) = c :=
      ⟨(c.1.get, c.2.get), by simp only [List.ofFn_get]⟩
    have hpT : p ∈ T n₁ n₂ := by
      show (List.ofFn p.1, List.ofFn p.2) ∈ S
      rw [hpc]; exact hc
    have hp1 : List.ofFn p.1 = c.1 := congrArg Prod.fst hpc
    have hp2 : List.ofFn p.2 = c.2 := congrArg Prod.snd hpc
    have h₁ : 0 < polyLen (List.ofFn p.1) := by
      rw [hp1]; exact (hpos c hc).1
    have h₂ : 0 < polyLen (List.ofFn p.2) := by
      rw [hp2]; exact (hpos c hc).2
    have hcont := continuousAt_cfgVal_ofFn hφ δ k p h₁ h₂
    have hcont' : ContinuousAt (fun q : T n₁ n₂ =>
        cfgVal φ δ k (List.ofFn q.1.1, List.ofFn q.1.2)) ⟨p, hpT⟩ :=
      ContinuousAt.comp (g := fun q : (Fin n₁ → ℂ) × (Fin n₂ → ℂ) =>
        cfgVal φ δ k (List.ofFn q.1, List.ofFn q.2)) (f := fun q : T n₁ n₂ => q.1)
        (x := ⟨p, hpT⟩) hcont continuous_subtype_val.continuousAt
    have hU := hcont'.preimage_mem_nhds (Metric.ball_mem_nhds _ hη)
    have hcl : (⟨p, hpT⟩ : T n₁ n₂) ∈ closure (s n₁ n₂) := by
      rw [(hsd n₁ n₂).closure_eq]; exact mem_univ _
    obtain ⟨q, hqU, hqs⟩ := mem_closure_iff_nhds.1 hcl _ hU
    refine ⟨emb n₁ n₂ q, ?_, ?_⟩
    · simp only [D, mem_iUnion, mem_image]
      exact ⟨n₁, n₂, q, hqs, rfl⟩
    · have := hqU
      simp only [mem_preimage, Metric.mem_ball, Real.dist_eq] at this
      rw [hpc] at this
      exact this
  obtain ⟨c₀, hc₀⟩ := hS
  have hDne : D.Nonempty := by
    obtain ⟨d, hd, _⟩ := happrox c₀ hc₀ (fun _ => 0) continuous_const 1 0 1 one_pos
    exact ⟨d, hd⟩
  obtain ⟨e, he⟩ := hDc.exists_eq_range hDne
  refine ⟨e, fun j => hDS (he ▸ mem_range_self j), ?_⟩
  intro c hc φ hφ δ k η hη
  obtain ⟨d, hd, hdη⟩ := happrox c hc φ hφ δ k η hη
  rw [he] at hd
  obtain ⟨j, rfl⟩ := hd
  exact ⟨j, hdη⟩

/-! ### Gaussian vectors with law `gaussVecLaw` -/

section GaussVec

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}

theorem exists_inner_rep (F : Finset ι)
    (T : EuclideanSpace ℝ F →L[ℝ] EuclideanSpace ℝ F) :
    ∃ w : ι → EuclideanSpace ℝ F, ∀ (x : EuclideanSpace ℝ F) (i : F), T x i = ⟪w i, x⟫ := by
  refine ⟨fun j => if hj : j ∈ F then (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ F)).symm
    ((EuclideanSpace.proj (⟨j, hj⟩ : F)).comp T) else 0, ?_⟩
  intro x i
  simp only [i.2, dite_true, Subtype.coe_eta, InnerProductSpace.toDual_symm_apply,
    ContinuousLinearMap.comp_apply]
  rfl

theorem mvg_map_eq {F : Finset ι} [DecidableEq F] (S : Matrix F F ℝ) :
    ∃ w : ι → EuclideanSpace ℝ F, (multivariateGaussian 0 S).map (fun x (i : F) => x i) =
      (stdGaussian (EuclideanSpace ℝ F)).map (fun x (i : F) => ⟪w i, x⟫) := by
  obtain ⟨w, hw⟩ := exists_inner_rep F (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))
  refine ⟨w, ?_⟩
  rw [multivariateGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x i
  simp only [Function.comp_apply, zero_add]
  exact hw x i

/-- Gram-vector form of `gaussVecLaw`. -/
theorem gaussVecLaw_eq_map (F : Finset ι) (C : ι → ι → ℝ) :
    ∃ w : ι → EuclideanSpace ℝ F, gaussVecLaw F C =
      (stdGaussian (EuclideanSpace ℝ F)).map (fun x (i : F) => ⟪w i, x⟫) := by
  unfold gaussVecLaw
  exact mvg_map_eq _

theorem measurable_gramVec {F : Finset ι} (w : ι → EuclideanSpace ℝ F) :
    Measurable fun (x : EuclideanSpace ℝ F) (i : F) => ⟪w i, x⟫ :=
  (continuous_pi fun _ => continuous_const.inner continuous_id).measurable

theorem measurable_iSup_add {F : Finset ι} (b : ι → ℝ) :
    Measurable fun y : F → ℝ => ⨆ i : F, y i + b i :=
  Measurable.iSup fun i => (measurable_pi_apply i).add_const _

theorem integrable_iSup_of_hasLaw {F : Finset ι} {C : ι → ι → ℝ} {Y : Ω → F → ℝ}
    (hY : HasLaw Y (gaussVecLaw F C) P) (b : ι → ℝ) :
    Integrable (fun ω => ⨆ i : F, Y ω i + b i) P := by
  obtain ⟨w, hw⟩ := gaussVecLaw_eq_map F C
  have hg := measurable_iSup_add (F := F) b
  have h1 : Integrable (fun y : F → ℝ => ⨆ i : F, y i + b i) (P.map Y) := by
    rw [hY.map_eq, hw, integrable_map_measure hg.aestronglyMeasurable
      (measurable_gramVec w).aemeasurable]
    exact integrable_iSup_inner_add F w b
  exact (integrable_map_measure hg.aestronglyMeasurable hY.aemeasurable).1 h1

theorem variance_inner_stdGaussian {F : Finset ι} (v : EuclideanSpace ℝ F) :
    Var[fun x => ⟪v, x⟫; stdGaussian (EuclideanSpace ℝ F)] = ‖v‖ ^ 2 := by
  have e : (fun x : EuclideanSpace ℝ F => ⟪v, x⟫) = ⇑(innerSL ℝ v) :=
    funext fun x => (innerSL_apply_apply ℝ v x).symm
  rw [e, variance_dual_stdGaussian, innerSL_apply_norm]

theorem variance_eval_map_gram {F : Finset ι} (w : ι → EuclideanSpace ℝ F) (i : F) :
    Var[fun y : F → ℝ => y i;
      (stdGaussian (EuclideanSpace ℝ F)).map (fun x (j : F) => ⟪w j, x⟫)] = ‖w i‖ ^ 2 := by
  rw [variance_map (measurable_pi_apply i).aemeasurable (measurable_gramVec w).aemeasurable]
  exact variance_inner_stdGaussian (w i)

theorem variance_of_hasLaw [IsProbabilityMeasure P] {F : Finset ι} {Y : Ω → F → ℝ}
    {w : ι → EuclideanSpace ℝ F} (hYm : AEMeasurable Y P)
    (hw : P.map Y = (stdGaussian (EuclideanSpace ℝ F)).map (fun x (i : F) => ⟪w i, x⟫))
    (i : F) (b : ℝ) :
    Var[fun ω => Y ω i + b; P] = ‖w i‖ ^ 2 := by
  have hYi : AEMeasurable (fun ω => Y ω i) P :=
    (measurable_pi_apply i).comp_aemeasurable hYm
  rw [variance_add_const hYi.aestronglyMeasurable]
  have h1 : Var[fun y : F → ℝ => y i; P.map Y] = Var[(fun y : F → ℝ => y i) ∘ Y; P] :=
    variance_map (measurable_pi_apply i).aemeasurable hYm
  have h2 : Var[(fun y : F → ℝ => y i) ∘ Y; P] = Var[fun ω => Y ω i; P] := rfl
  rw [← h2, ← h1, hw]
  exact variance_eval_map_gram w i

/-- **Chernoff bound for a finite Gaussian maximum**, transferred through the law. -/
theorem measure_lt_iSup_le [IsProbabilityMeasure P] {F : Finset ι} (hF : F.Nonempty)
    {C : ι → ι → ℝ} {Y : Ω → F → ℝ} (hY : HasLaw Y (gaussVecLaw F C) P) (b : ι → ℝ) (V : ℝ)
    (hV : ∀ i : F, Var[fun ω => Y ω i + b i; P] ≤ V) (β t : ℝ) (ht : 0 ≤ t) :
    P {ω | β < ⨆ i : F, Y ω i + b i} ≤
      ENNReal.ofReal (Real.exp (-t * β + t * ∫ ω, (⨆ i : F, Y ω i + b i) ∂P +
        π ^ 2 / 8 * t ^ 2 * V)) := by
  obtain ⟨w, hw⟩ := gaussVecLaw_eq_map F C
  have hw' := hY.map_eq.trans hw
  have hL := measurable_gramVec w
  have hg := measurable_iSup_add (F := F) b
  have hV0 : 0 ≤ V := by
    obtain ⟨i, hi⟩ := hF
    exact le_trans (variance_nonneg _ _) (hV ⟨i, hi⟩)
  have hnorm : ∀ i ∈ F, ‖w i‖ ≤ Real.sqrt V := by
    intro i hi
    have := hV ⟨i, hi⟩
    rw [variance_of_hasLaw hY.aemeasurable hw' ⟨i, hi⟩ (b i)] at this
    exact Real.le_sqrt_of_sq_le this
  have hint : ∫ ω, (⨆ i : F, Y ω i + b i) ∂P = vecExpectedMax F w b := by
    have e1 : ∫ ω, (⨆ i : F, Y ω i + b i) ∂P =
        ∫ y, (⨆ i : F, y i + b i) ∂(P.map Y) :=
      (integral_map hY.aemeasurable hg.aestronglyMeasurable).symm
    rw [e1, hw', integral_map hL.aemeasurable hg.aestronglyMeasurable]
    rfl
  have hset : P {ω | β < ⨆ i : F, Y ω i + b i} =
      stdGaussian (EuclideanSpace ℝ F) {x | β < ⨆ i : F, ⟪w i, x⟫ + b i} := by
    have hU : MeasurableSet {y : F → ℝ | β < ⨆ i : F, y i + b i} :=
      measurableSet_lt measurable_const hg
    have e1 : {ω | β < ⨆ i : F, Y ω i + b i} = Y ⁻¹' {y : F → ℝ | β < ⨆ i : F, y i + b i} :=
      rfl
    rw [e1, ← Measure.map_apply_of_aemeasurable hY.aemeasurable hU, hw', Measure.map_apply hL hU]
    rfl
  rw [hset, hint]
  set EM := vecExpectedMax F w b with hEM
  have hch := measure_ge_le_exp_mul_mgf (μ := stdGaussian (EuclideanSpace ℝ F))
    (X := fun x => (⨆ i : F, ⟪w i, x⟫ + b i) - EM) (β - EM) ht
    (MaxConc.integrable_exp_max F w b hnorm t)
  have hmgf := MaxConc.integral_exp_max_le F w b hnorm t
  rw [mgf] at hch
  calc stdGaussian (EuclideanSpace ℝ F) {x | β < ⨆ i : F, ⟪w i, x⟫ + b i}
      ≤ stdGaussian (EuclideanSpace ℝ F) {x | β - EM ≤ (⨆ i : F, ⟪w i, x⟫ + b i) - EM} := by
        refine measure_mono fun x hx => ?_
        simp only [mem_ofPred_eq] at hx ⊢
        linarith
    _ = ENNReal.ofReal ((stdGaussian (EuclideanSpace ℝ F)).real
          {x | β - EM ≤ (⨆ i : F, ⟪w i, x⟫ + b i) - EM}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (Real.exp (-t * (β - EM)) * Real.exp (π ^ 2 / 8 * t ^ 2 * √V ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal (hch.trans ?_)
        exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = ENNReal.ofReal (Real.exp (-t * β + t * EM + π ^ 2 / 8 * t ^ 2 * V)) := by
        rw [← Real.exp_add, Real.sq_sqrt hV0]
        congr 2
        ring

end GaussVec

/-! ### Maxima over product families -/

theorem iSup_piFinset_sum {α : Type*} {l : ℕ} (G : Fin l → Finset α) (hG : ∀ i, (G i).Nonempty)
    (f : Fin l → α → ℝ) :
    (⨆ c : Fintype.piFinset G, ∑ i, f i ((c : Fin l → α) i)) = ∑ i, ⨆ a : G i, f i a := by
  have : ∀ i, Nonempty (G i) := fun i => (hG i).to_subtype
  have : Nonempty (Fintype.piFinset G) := (Fintype.piFinset_nonempty.2 hG).to_subtype
  apply le_antisymm
  · apply ciSup_le
    intro c
    apply Finset.sum_le_sum
    intro i _
    exact le_ciSup (f := fun a : G i => f i a) (Set.finite_range _).bddAbove
      (⟨(c : Fin l → α) i, Fintype.mem_piFinset.1 c.2 i⟩ : G i)
  · have hex : ∀ i, ∃ a : G i, f i a = ⨆ a : G i, f i a := fun i =>
      exists_eq_ciSup_of_finite (f := fun a : G i => f i a)
    choose a ha using hex
    have hmem : (fun i => (a i : α)) ∈ Fintype.piFinset G :=
      Fintype.mem_piFinset.2 fun i => (a i).2
    calc ∑ i, ⨆ a : G i, f i a = ∑ i, f i (a i) := Finset.sum_congr rfl fun i _ => (ha i).symm
      _ ≤ ⨆ c : Fintype.piFinset G, ∑ i, f i ((c : Fin l → α) i) :=
        le_ciSup (f := fun c : Fintype.piFinset G => ∑ i, f i ((c : Fin l → α) i))
          (Set.finite_range _).bddAbove ⟨_, hmem⟩

/-! ### The bound for one chain record -/

section Chain

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : ℝ → ℂ → Ω → ℝ}

/-- One chain record, finite subfamilies: the Chernoff bound for the supremum over the product. -/
theorem chain_bound_finite (hP1 : SegCombLaw) (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε)
    (δ : ℝ) {l : ℕ} (k : Fin l → ℕ) (G : Fin l → Finset Config) (hGne : ∀ i, (G i).Nonempty)
    (m : Fin l → ℝ) (V : ℝ)
    (hmean : ∀ i, ∫ ω, (⨆ c : G i, cfgVal (fun z => h ε z ω) δ (k i) c) ∂P ≤ m i)
    (hvar : ∀ c : Fin l → Config, (∀ i, c i ∈ G i) →
      Var[fun ω => ∑ i, cfgVal (fun z => h ε z ω) δ (k i) (c i); P] ≤ V)
    (β t : ℝ) (ht : 0 ≤ t) :
    P {ω | β < ⨆ c : Fintype.piFinset G,
        ∑ i, cfgVal (fun z => h ε z ω) δ (k i) ((c : Fin l → Config) i)} ≤
      ENNReal.ofReal (Real.exp (-t * β + t * ∑ i, m i + π ^ 2 / 8 * t ^ 2 * V)) := by
  have := hG.isProbabilityMeasure
  have hPi : (Fintype.piFinset G).Nonempty := Fintype.piFinset_nonempty.2 hGne
  have hlaw := hP1 Ω P h hG ε hε (Fin l → Config) (Fintype.piFinset G) (pcomb δ)
  set K : ℝ := ∑ i, (k i : ℝ) with hK
  have hYval : ∀ ω (c : Fin l → Config),
      (pcomb δ c).avg (fun z => h ε z ω) + -K =
        ∑ i, cfgVal (fun z => h ε z ω) δ (k i) (c i) := by
    intro ω c
    rw [avg_pcomb _ δ k c]
    ring
  have hV : ∀ c : Fintype.piFinset G,
      Var[fun ω => (pcomb δ (c : Fin l → Config)).avg (fun z => h ε z ω) + -K; P] ≤ V := by
    intro c
    simp only [hYval]
    exact hvar c (Fintype.mem_piFinset.1 c.2)
  have hmain := measure_lt_iSup_le hPi hlaw (fun _ => -K) V hV β t ht
  simp only [hYval] at hmain
  refine hmain.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  -- the mean of the product supremum
  have hsup : ∀ ω, (⨆ c : Fintype.piFinset G,
      ∑ i, cfgVal (fun z => h ε z ω) δ (k i) ((c : Fin l → Config) i)) =
        ∑ i, ⨆ c : G i, cfgVal (fun z => h ε z ω) δ (k i) c := fun ω =>
    iSup_piFinset_sum G hGne (fun i c => cfgVal (fun z => h ε z ω) δ (k i) c)
  have hintg : ∀ i, Integrable (fun ω => ⨆ c : G i, cfgVal (fun z => h ε z ω) δ (k i) c) P := by
    intro i
    have hl := hP1 Ω P h hG ε hε Config (G i) (scomb δ)
    have := integrable_iSup_of_hasLaw hl (fun _ => -(k i : ℝ))
    simp only [avg_scomb _ δ (k i), add_neg_cancel_right] at this
    exact this
  have hmean' : ∫ ω, (⨆ c : Fintype.piFinset G,
      ∑ i, cfgVal (fun z => h ε z ω) δ (k i) ((c : Fin l → Config) i)) ∂P ≤ ∑ i, m i := by
    simp_rw [hsup]
    rw [integral_finsetSum _ fun i _ => hintg i]
    exact Finset.sum_le_sum fun i _ => hmean i
  nlinarith [mul_le_mul_of_nonneg_left hmean' ht]

/-- One chain record, full (possibly infinite) families: separability through a dense sequence
and continuity from below of the outer measure. -/
theorem chain_bound_family (hP1 : SegCombLaw) (hG : IsGFFCircleAverage h P) {ε : ℝ} (hε : 0 < ε)
    (δ : ℝ) {l : ℕ} (k : Fin l → ℕ) (S : Fin l → Set Config)
    (hpos : ∀ i, ∀ c ∈ S i, 0 < polyLen c.1 ∧ 0 < polyLen c.2) (m : Fin l → ℝ) (V : ℝ)
    (hmean : ∀ i, ∀ F : Finset Config, F.Nonempty → ↑F ⊆ S i →
      ∫ ω, (⨆ c : F, cfgVal (fun z => h ε z ω) δ (k i) c) ∂P ≤ m i)
    (hvar : ∀ c : Fin l → Config, (∀ i, c i ∈ S i) →
      Var[fun ω => ∑ i, cfgVal (fun z => h ε z ω) δ (k i) (c i); P] ≤ V)
    (β t : ℝ) (ht : 0 ≤ t) :
    P {ω | ∃ c : Fin l → Config, (∀ i, c i ∈ S i) ∧
        β < ∑ i, cfgVal (fun z => h ε z ω) δ (k i) (c i)} ≤
      ENNReal.ofReal (Real.exp (-t * β + t * ∑ i, m i + π ^ 2 / 8 * t ^ 2 * V)) := by
  by_cases hne : ∀ i, (S i).Nonempty
  swap
  · obtain ⟨i, hi⟩ := not_forall.1 hne
    refine le_trans (measure_mono (t := ∅) ?_) (by simp)
    rintro ω ⟨c, hc, -⟩
    exact hi ⟨c i, hc i⟩
  choose e he happ using fun i => exists_dense_seq_config (S i) (hne i) (hpos i)
  let G : ℕ → Fin l → Finset Config := fun n i => (Finset.range (n + 1)).image (e i)
  have hGsub : ∀ n i, ↑(G n i) ⊆ S i := by
    intro n i x hx
    simp only [G, Finset.coe_image, mem_image, Finset.mem_coe] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact he i j
  have hGne : ∀ n i, (G n i).Nonempty := fun n i =>
    ⟨e i 0, Finset.mem_image_of_mem _ (by simp)⟩
  let A : ℕ → Set Ω := fun n => {ω | ∃ c : Fin l → Config, (∀ i, c i ∈ G n i) ∧
    β < ∑ i, cfgVal (fun z => h ε z ω) δ (k i) (c i)}
  have hAmono : Monotone A := by
    intro n n' hnn' ω hω
    obtain ⟨c, hc, hlt⟩ := hω
    refine ⟨c, fun i => ?_, hlt⟩
    have := hc i
    simp only [G, Finset.mem_image, Finset.mem_range] at this ⊢
    obtain ⟨j, hj, hje⟩ := this
    exact ⟨j, by omega, hje⟩
  have hsub : {ω | ∃ c : Fin l → Config, (∀ i, c i ∈ S i) ∧
      β < ∑ i, cfgVal (fun z => h ε z ω) δ (k i) (c i)} ⊆ ⋃ n, A n := by
    intro ω hω
    obtain ⟨c, hc, hlt⟩ := hω
    have hφ : Continuous fun z => h ε z ω := hG.continuous ε hε ω
    set gap := ∑ i, cfgVal (fun z => h ε z ω) δ (k i) (c i) - β with hgap
    have hgap0 : 0 < gap := sub_pos.2 hlt
    set η := gap / ((l : ℝ) + 1) with hη
    have hη0 : 0 < η := div_pos hgap0 (by positivity)
    have hj : ∀ i, ∃ j, |cfgVal (fun z => h ε z ω) δ (k i) (e i j) -
        cfgVal (fun z => h ε z ω) δ (k i) (c i)| < η :=
      fun i => happ i (c i) (hc i) _ hφ δ (k i) η hη0
    choose j hj using hj
    refine mem_iUnion.2 ⟨Finset.univ.sup j, ?_⟩
    refine ⟨fun i => e i (j i), fun i => ?_, ?_⟩
    · simp only [G, Finset.mem_image, Finset.mem_range]
      exact ⟨j i, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i)), rfl⟩
    · have hle : ∑ i, (cfgVal (fun z => h ε z ω) δ (k i) (c i) - η) ≤
          ∑ i, cfgVal (fun z => h ε z ω) δ (k i) (e i (j i)) :=
        Finset.sum_le_sum fun i _ => by linarith [(abs_lt.1 (hj i)).1]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hle
      show β < ∑ i, cfgVal (fun z => h ε z ω) δ (k i) (e i (j i))
      have hlη : (l : ℝ) * η < gap := by
        rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
  have hA : ∀ n, P (A n) ≤
      ENNReal.ofReal (Real.exp (-t * β + t * ∑ i, m i + π ^ 2 / 8 * t ^ 2 * V)) := by
    intro n
    refine le_trans (measure_mono ?_) (chain_bound_finite hP1 hG hε δ k (G n) (hGne n) m V
      (fun i => hmean i (G n i) (hGne n i) (hGsub n i))
      (fun c hc => hvar c fun i => hGsub n i (hc i)) β t ht)
    intro ω hω
    obtain ⟨c, hc, hlt⟩ := hω
    show β < ⨆ c' : Fintype.piFinset (G n),
      ∑ i, cfgVal (fun z => h ε z ω) δ (k i) ((c' : Fin l → Config) i)
    exact lt_of_lt_of_le hlt (le_ciSup (f := fun c' : Fintype.piFinset (G n) =>
      ∑ i, cfgVal (fun z => h ε z ω) δ (k i) ((c' : Fin l → Config) i))
      (Set.finite_range _).bddAbove ⟨c, Fintype.mem_piFinset.2 hc⟩)
  calc _ ≤ P (⋃ n, A n) := measure_mono hsub
    _ = ⨆ n, P (A n) := hAmono.measure_iUnion
    _ ≤ _ := iSup_le hA

end Chain

/-! ### Counting chains -/

section Count

variable {R : Type*} [Fintype R]

/-- Chain condition on tuples, with first element in `Q`. -/
def IsChainQ (next : R → R → Prop) (Q : R → Prop) {l : ℕ} (ρ : Fin l → R) : Prop :=
  (∀ h : 0 < l, Q (ρ ⟨0, h⟩)) ∧ ∀ i (h : i + 1 < l), next (ρ ⟨i, by omega⟩) (ρ ⟨i + 1, h⟩)

omit [Fintype R] in
theorem cons_mk_zero {l : ℕ} (x : R) (τ : Fin l → R) (h : 0 < l + 1) :
    (Fin.cons x τ : Fin (l + 1) → R) ⟨0, h⟩ = x := by
  have e : (⟨0, h⟩ : Fin (l + 1)) = 0 := rfl
  rw [e, Fin.cons_zero]

omit [Fintype R] in
theorem cons_mk_succ {l : ℕ} (x : R) (τ : Fin l → R) (i : ℕ) (h : i + 1 < l + 1) :
    (Fin.cons x τ : Fin (l + 1) → R) ⟨i + 1, h⟩ = τ ⟨i, by omega⟩ := by
  have e : (⟨i + 1, h⟩ : Fin (l + 1)) = Fin.succ (⟨i, by omega⟩ : Fin l) := rfl
  rw [e, Fin.cons_succ]

omit [Fintype R] in
theorem isChainQ_cons (next : R → R → Prop) (Q : R → Prop) {l : ℕ} (x : R) (τ : Fin l → R) :
    IsChainQ next Q (Fin.cons x τ : Fin (l + 1) → R) ↔ Q x ∧ IsChainQ next (next x) τ := by
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨?_, fun hl => ?_, fun i hi => ?_⟩
    · have := h0 (Nat.succ_pos l)
      rwa [cons_mk_zero] at this
    · have := hs 0 (by omega)
      rwa [cons_mk_zero, cons_mk_succ] at this
    · have := hs (i + 1) (by omega)
      rwa [cons_mk_succ, cons_mk_succ] at this
  · rintro ⟨hx, h0, hs⟩
    refine ⟨fun _ => by rw [cons_mk_zero]; exact hx, fun i hi => ?_⟩
    cases i with
    | zero =>
      rw [cons_mk_zero, cons_mk_succ]
      exact h0 (by omega)
    | succ i =>
      rw [cons_mk_succ, cons_mk_succ]
      exact hs i (by omega)

/-- The weighted number of chains of length `l` is at most `Z ^ l`. -/
theorem sum_chain_le (next : R → R → Prop) (a : R → ℝ) (ha : ∀ x, 0 ≤ a x) (Z : ℝ) (hZ : 0 ≤ Z)
    (hnext : ∀ x, ∑ y, (if next x y then a y else 0) ≤ Z) :
    ∀ (l : ℕ) (Q : R → Prop), (∑ y, (if Q y then a y else 0) ≤ Z) →
      ∑ ρ : Fin l → R, (if IsChainQ next Q ρ then ∏ i, a (ρ i) else 0) ≤ Z ^ l := by
  intro l
  induction l with
  | zero =>
    intro Q _
    simp [IsChainQ]
  | succ l ih =>
    intro Q hQ
    have e := Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (l + 1) => R)
      (fun p => (if IsChainQ next Q (Fin.cons p.1 p.2 : Fin (l + 1) → R) then
        ∏ i, a ((Fin.cons p.1 p.2 : Fin (l + 1) → R) i) else 0))
      (fun ρ => if IsChainQ next Q ρ then ∏ i, a (ρ i) else 0) (fun p => rfl)
    rw [← e, Fintype.sum_prod_type]
    calc ∑ x, ∑ τ : Fin l → R, (if IsChainQ next Q (Fin.cons x τ : Fin (l + 1) → R) then
          ∏ i, a ((Fin.cons x τ : Fin (l + 1) → R) i) else 0)
        = ∑ x, (if Q x then a x else 0) *
            ∑ τ : Fin l → R, (if IsChainQ next (next x) τ then ∏ i, a (τ i) else 0) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [isChainQ_cons, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          by_cases hx : Q x <;> by_cases hτ : IsChainQ next (next x) τ <;> simp [hx, hτ]
      _ ≤ ∑ x, (if Q x then a x else 0) * Z ^ l := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine mul_le_mul_of_nonneg_left (ih (next x) (hnext x)) ?_
          split_ifs
          · exact ha x
          · exact le_rfl
      _ = (∑ x, (if Q x then a x else 0)) * Z ^ l := by rw [Finset.sum_mul]
      _ ≤ Z * Z ^ l := mul_le_mul_of_nonneg_right hQ (pow_nonneg hZ l)
      _ = Z ^ (l + 1) := by ring

/-- Grouping by bins: a weighted count of the records in `S` is at most the series. -/
theorem sum_ite_le_tsum (S : R → Prop) (bin : R → ℕ) (N a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hN : ∀ k, (Set.ncard {y | S y ∧ bin y = k} : ℝ) ≤ N k)
    (hs : Summable fun k => N k * a k) :
    ∑ y, (if S y then a (bin y) else 0) ≤ ∑' k, N k * a k := by
  have hN0 : ∀ k, 0 ≤ N k := fun k => le_trans (Nat.cast_nonneg _) (hN k)
  set T := Finset.univ.image bin with hT
  have h1 : ∑ y, (if S y then a (bin y) else 0) =
      ∑ k ∈ T, ∑ y ∈ Finset.univ.filter (fun y => bin y = k),
        (if S y then a (bin y) else 0) :=
    (Finset.sum_fiberwise_of_maps_to
      (fun y _ => Finset.mem_image_of_mem bin (Finset.mem_univ y)) _).symm
  have h2 : ∀ k, ∑ y ∈ Finset.univ.filter (fun y => bin y = k),
      (if S y then a (bin y) else 0) = (Set.ncard {y | S y ∧ bin y = k} : ℝ) * a k := by
    intro k
    rw [Finset.sum_filter]
    have e1 : ∀ y, (if bin y = k then (if S y then a (bin y) else 0) else 0) =
        if (S y ∧ bin y = k) then a k else 0 := by
      intro y
      by_cases h1 : bin y = k <;> by_cases h2 : S y <;> simp [h1, h2]
    simp_rw [e1]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have e2 : {y | S y ∧ bin y = k} = ↑(Finset.univ.filter fun y => S y ∧ bin y = k) := by
      ext y
      simp
    rw [e2, Set.ncard_coe_finset]
  rw [h1]
  calc ∑ k ∈ T, ∑ y ∈ Finset.univ.filter (fun y => bin y = k),
        (if S y then a (bin y) else 0)
      = ∑ k ∈ T, (Set.ncard {y | S y ∧ bin y = k} : ℝ) * a k :=
        Finset.sum_congr rfl fun k _ => h2 k
    _ ≤ ∑ k ∈ T, N k * a k :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hN k) (ha k)
    _ ≤ ∑' k, N k * a k := hs.sum_le_tsum T fun k _ => mul_nonneg (hN0 k) (ha k)

end Count

end ChainUnion

end LQGDimension
