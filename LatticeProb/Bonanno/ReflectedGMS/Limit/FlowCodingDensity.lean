/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.FlowCodingDensity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationFlowGrid
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootedBracketMeasurability
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerationKernel
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualSpatialDensityBridge
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalBracketLLNGates

/-!
# The bracket density along the càdlàg carrier: `unmarked` and `hdensscale` hold POINTWISE

The regeneration-flow handoff (`outputs/regeneration-flow-handoff.2026-09-18.md` §5) warned that
the pointwise clauses `UnmarkedRootDensity.unmarked` and `hdensscale` need EXACT re-rooting
invariance of the bracket density of `Φ` at every environment, which a `Classical.choose`
coordinate might not provide.  It does, for every harmonic coordinate: the first clause of
`IsHarmonicCoordinate` is `GradientCovariant Φ`, stated at EVERY pair of similar environments (not
almost surely), and the bracket density `a_v⁻¹ ∑_w c_{vw} (Φ_w - Φ_v) ⊗ (Φ_w - Φ_v)` only sees
gradients, conductances (similarity invariant) and the cell area (degree `2`, cancelled by the
two gradient factors).  Hence (`bracketDensity_relabel`) the bracket density is similarity
invariant at every vertex of every environment, and:

* `labelBracket Φ ζ e y` — the directional bracket density at the label `y : ℕ∞` of `e`
  (`0` at the cemetery `⊤` and at inactive labels);
* `lineDensity Φ ζ ω s` — its reading along the carrier's label path at time `s`;
* `flowFdir Φ ζ ω = lineDensity Φ ζ ω 0` — the root-time functional.

`flowFdir_gridFlow` is the clause `unmarked` for the re-rooting flow at every point and every
grid, and `lineDensity_reScale` is `hdensscale` at every point; `measurable_flowFdir` and
`flowFdir_nonneg` are the clauses `measurable` and `nonneg`.  So the density suggestion of the flow
handoff (`dens ω t := Fdir (θΩ t ω)`) is not needed: the natural density satisfies `unmarked`
exactly (`lineDensity_eq_flowFdir_reRootFlow`), and the two densities coincide everywhere.

The two remaining clauses of `UnmarkedRootDensity` (`integrable`, `locallyIntegrable`) are
probabilistic and are stated as named binders of the frontier theorem.

Nothing here certifies `p:lem:bracketlimit` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace ReflectedGMS.FlowCodingDensity

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients StatementIngredients
open RootDensities MartingaleIngredients BracketTimeAverage
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TwoSidedRegenerationFlowGrid ReflectedGMS.DyadicApproximation
open ReflectedGMS.ActualMarkedBlockTransport ReflectedGMS.MarkedSimilarityActionLaws
open ReflectedGMS.CanonicalSimilarity

/-! ### 1. Exact similarity invariance of the bracket density -/

/-- **The bracket density is similarity invariant at every vertex of every environment** for a
gradient-covariant field. -/
theorem bracketDensity_relabel {Φ : CellField} (hΦ : GradientCovariant Φ) {s : ℝ} {u : Plane}
    {hs : 0 < s} {e e' : Env} {rl : Vertex e.val ≃ Vertex e'.val}
    (h : IsSimilarityRelabel s u hs e e' rl) (v : Vertex e.val) :
    bracketDensity (decode e') (Φ.at e') (rl v) = bracketDensity (decode e) (Φ.at e) v := by
  have hgrad : ∀ (w : Vertex e.val) (k : Fin 2),
      Φ.at e' (rl w) k - Φ.at e' (rl v) k = s * (Φ.at e w k - Φ.at e v k) := by
    intro w k
    have hk := congrArg (fun x : Plane => x k) (hΦ s u hs e e' rl h v w)
    simpa [CellField.gradient] using hk
  have hA := ActualSpatialDensityBridge.cellArea_relabel h v
  have hs2 : s ^ 2 ≠ 0 := by positivity
  ext i j
  show (cellArea (decode e') (rl v))⁻¹ * ∑' w' : Vertex e'.val, (decode e').graph.c (rl v) w' *
      (Φ.at e' w' i - Φ.at e' (rl v) i) * (Φ.at e' w' j - Φ.at e' (rl v) j) =
    (cellArea (decode e) v)⁻¹ * ∑' w : Vertex e.val, (decode e).graph.c v w *
      (Φ.at e w i - Φ.at e v i) * (Φ.at e w j - Φ.at e v j)
  rw [← Equiv.tsum_eq rl (fun w' : Vertex e'.val => (decode e').graph.c (rl v) w' *
      (Φ.at e' w' i - Φ.at e' (rl v) i) * (Φ.at e' w' j - Φ.at e' (rl v) j))]
  have hsum : ∀ w : Vertex e.val, (decode e').graph.c (rl v) (rl w) *
      (Φ.at e' (rl w) i - Φ.at e' (rl v) i) * (Φ.at e' (rl w) j - Φ.at e' (rl v) j) =
      s ^ 2 * ((decode e).graph.c v w * (Φ.at e w i - Φ.at e v i) *
        (Φ.at e w j - Φ.at e v j)) := by
    intro w
    rw [h.2 v w, hgrad w i, hgrad w j]
    ring
  simp_rw [hsum]
  rw [tsum_mul_left, hA, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hs2, one_mul]

/-! ### 2. The bracket density at a label of `ℕ∞` -/

/-- Decode a label of `ℕ∞` into a vertex of `e`: the cemetery `⊤` and inactive labels give
`none`. -/
def labelVertex (e : Env) (y : ℕ∞) : Option (Vertex e.val) :=
  (toOptLabel y).bind fun n => if h : (e.val.1 n).isSome then some ⟨n, h⟩ else none

theorem labelVertex_top (e : Env) : labelVertex e ⊤ = none := by
  unfold labelVertex toOptLabel
  rw [ENat.recTopCoe_top]
  rfl

theorem labelVertex_natCast (e : Env) (n : ℕ) :
    labelVertex e (n : ℕ∞) = if h : (e.val.1 n).isSome then some ⟨n, h⟩ else none := by
  unfold labelVertex toOptLabel
  rw [ENat.recTopCoe_natCast]
  rfl

/-- **The directional bracket density at a label** (`0` at the cemetery and inactive labels). -/
noncomputable def labelBracket (Φ : CellField) (ζ : Fin 2 → ℝ) (e : Env) (y : ℕ∞) : ℝ :=
  dirForm (stateBracketDensity (decode e) (Φ.at e) (labelVertex e y)) ζ

theorem labelBracket_nonneg (Φ : CellField) (ζ : Fin 2 → ℝ) (e : Env) (y : ℕ∞) :
    0 ≤ labelBracket Φ ζ e y :=
  dirForm_stateBracketDensity_nonneg (decode e) (decode_geometry e) (Φ.at e) _ ζ

/-- **The directional bracket density is invariant under every similarity**, read through the
canonical label map, at every label of every environment. -/
theorem labelBracket_simLabel {Φ : CellField} (hΦ : GradientCovariant Φ) (ζ : Fin 2 → ℝ)
    {s : ℝ} {u : Plane} (hs : 0 < s) (e : Env) (y : ℕ∞) :
    labelBracket Φ ζ (similarityTargetEnv s u hs e) (liftLabel (simLabel s u hs e) y)
      = labelBracket Φ ζ e y := by
  induction y using ENat.recTopCoe with
  | top =>
    unfold labelBracket
    rw [liftLabel_top, labelVertex_top, labelVertex_top]
    rfl
  | coe n =>
    unfold labelBracket
    rw [liftLabel_natCast, labelVertex_natCast, labelVertex_natCast]
    by_cases hn : (e.val.1 n).isSome
    · have hn' : ((similarityTargetEnv s u hs e).val.1 (simLabel s u hs e n)).isSome :=
        isSome_simLabel hn
      have hv : (⟨simLabel s u hs e n, hn'⟩ : Vertex (similarityTargetEnv s u hs e).val)
          = LabelBijectionProducer.similarityRelabel s u hs e ⟨n, hn⟩ :=
        Subtype.ext (simLabel_of_isSome hn)
      rw [dif_pos hn', dif_pos hn, hv, stateBracketDensity_some, stateBracketDensity_some,
        bracketDensity_relabel hΦ
          (LabelBijectionProducer.isSimilarityRelabel_similarityRelabel s u hs e)]
    · have hn' : ¬ ((similarityTargetEnv s u hs e).val.1 (simLabel s u hs e n)).isSome :=
        inact_simLabel (s := s) (u := u) (hs := hs) hn
      rw [dif_neg hn', dif_neg hn]
      rfl

/-- The label form of the directional density, through the measurable label bracket. -/
theorem labelBracket_natCast_eq (Φ : CellField) (ζ : Fin 2 → ℝ) (e : Env) (n : ℕ) :
    labelBracket Φ ζ e (n : ℕ∞) = ∑ i : Fin 2, ∑ j : Fin 2, ζ i *
      (if (e.val.1 n).isSome then RootedBracketMeasurability.labelBracketDensity Φ e n i j
        else 0) * ζ j := by
  unfold labelBracket
  rw [labelVertex_natCast]
  by_cases hn : (e.val.1 n).isSome
  · rw [dif_pos hn, stateBracketDensity_some]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos hn]
    exact congrArg (fun x => ζ i * x * ζ j)
      (RootedBracketMeasurability.labelBracketDensity_eq_bracketDensity Φ e ⟨n, hn⟩ i j).symm
  · rw [dif_neg hn, stateBracketDensity_none]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [if_neg hn]
    rfl

theorem measurable_labelBracket (Φ : CellField) (ζ : Fin 2 → ℝ) :
    Measurable fun p : Env × ℕ∞ => labelBracket Φ ζ p.1 p.2 := by
  refine measurable_from_prod_countable_left fun y => ?_
  induction y using ENat.recTopCoe with
  | top =>
    show Measurable fun e : Env => labelBracket Φ ζ e ⊤
    have h : (fun e : Env => labelBracket Φ ζ e ⊤) = fun _ => dirForm 0 ζ := by
      funext e
      unfold labelBracket
      rw [labelVertex_top]
      rfl
    rw [h]
    exact measurable_const
  | coe n =>
    show Measurable fun e : Env => labelBracket Φ ζ e (n : ℕ∞)
    have h : (fun e : Env => labelBracket Φ ζ e (n : ℕ∞)) = fun e => ∑ i : Fin 2, ∑ j : Fin 2,
        ζ i * (if (e.val.1 n).isSome then
          RootedBracketMeasurability.labelBracketDensity Φ e n i j else 0) * ζ j :=
      funext fun e => labelBracket_natCast_eq Φ ζ e n
    rw [h]
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact (measurable_const.mul (Measurable.ite (RegenerationKernel.measurableSet_slotPresent n)
      (RootedBracketMeasurability.measurable_labelBracketDensity Φ n i j)
      measurable_const)).mul measurable_const

/-! ### 3. The density along the carrier -/

/-- **The directional bracket density along the carrier's label path.** -/
noncomputable def lineDensity (Φ : CellField) (ζ : Fin 2 → ℝ) (ω : FlowSpace) (s : ℝ) : ℝ :=
  labelBracket Φ ζ ω.1 (ω.2.1.toFun s)

/-- **The root-time functional** `Fdir`: the directional bracket density at the walker's time-`0`
label. -/
noncomputable def flowFdir (Φ : CellField) (ζ : Fin 2 → ℝ) (ω : FlowSpace) : ℝ :=
  lineDensity Φ ζ ω 0

theorem flowFdir_nonneg (Φ : CellField) (ζ : Fin 2 → ℝ) (ω : FlowSpace) : 0 ≤ flowFdir Φ ζ ω :=
  labelBracket_nonneg Φ ζ ω.1 _

theorem measurable_flowFdir (Φ : CellField) (ζ : Fin 2 → ℝ) : Measurable (flowFdir Φ ζ) := by
  have hY : Measurable fun ω : FlowSpace => ω.2.1.toFun 0 :=
    (CadlagPath.measurable_eval _).comp (measurable_fst.comp measurable_snd)
  have h : Measurable ((fun p : Env × ℕ∞ => labelBracket Φ ζ p.1 p.2) ∘
      fun ω : FlowSpace => (ω.1, ω.2.1.toFun 0)) :=
    (measurable_labelBracket Φ ζ).comp (measurable_fst.prodMk hY)
  have heq : flowFdir Φ ζ = (fun p : Env × ℕ∞ => labelBracket Φ ζ p.1 p.2) ∘
      fun ω : FlowSpace => (ω.1, ω.2.1.toFun 0) := by
    funext ω
    rfl
  rw [heq]
  exact h

/-- **`unmarked`, pointwise**: flowing by `t` and reading the root-time functional is the density
at time `t`, at EVERY configuration. -/
theorem flowFdir_reRootFlow {Φ : CellField} (hΦ : GradientCovariant Φ) (ζ : Fin 2 → ℝ) (t : ℝ)
    (ω : FlowSpace) : flowFdir Φ ζ (reRootFlow t ω) = lineDensity Φ ζ ω t := by
  show labelBracket Φ ζ (reRootFlow t ω).1 ((reRootFlow t ω).2.1.toFun 0) = _
  rw [reRootFlow_label, zero_add, reRootFlow_fst]
  exact labelBracket_simLabel hΦ ζ one_pos ω.1 _

/-- The consumer's `UnmarkedRootDensity.unmarked` shape on the marked carrier. -/
theorem flowFdir_gridFlow {Φ : CellField} (hΦ : GradientCovariant Φ) (ζ : Fin 2 → ℝ) (t : ℝ)
    (ω : FlowSpace) (d : Grid) : flowFdir Φ ζ (gridFlow t (ω, d)).1 = lineDensity Φ ζ ω t :=
  flowFdir_reRootFlow hΦ ζ t ω

/-- **`hdensscale`, pointwise**: the density of the scaled configuration at time `s` is the
density at time `s / C²`, at EVERY configuration. -/
theorem lineDensity_reScale {Φ : CellField} (hΦ : GradientCovariant Φ) (ζ : Fin 2 → ℝ) {C : ℝ}
    (hC : 0 < C) (ω : FlowSpace) (s : ℝ) :
    lineDensity Φ ζ (reScale C ω) s = lineDensity Φ ζ ω (s / C ^ 2) := by
  unfold lineDensity
  rw [reScale_label hC, reScale_fst hC, labelBracket_simLabel hΦ ζ hC ω.1, div_eq_inv_mul]

/-- **`UnmarkedRootDensity` at the flow coding from its two probabilistic clauses.**  The
clauses `measurable`, `nonneg` and `unmarked` are proved; `integrable` and `locallyIntegrable` are
the inputs. -/
theorem unmarkedRootDensity_flowFdir {Φ : CellField} (hΦ : GradientCovariant Φ) (ζ : Fin 2 → ℝ)
    {Q : Measure FlowSpace} (hint : Integrable (flowFdir Φ ζ) Q)
    (hloc : ∀ᵐ ω ∂Q, LocallyIntegrable (lineDensity Φ ζ ω) volume) :
    BracketLLNRootChain.UnmarkedRootDensity Q gridFlow (flowFdir Φ ζ) (lineDensity Φ ζ) where
  measurable := measurable_flowFdir Φ ζ
  integrable := hint
  nonneg := flowFdir_nonneg Φ ζ
  unmarked := fun t ω d => flowFdir_gridFlow hΦ ζ t ω d
  locallyIntegrable := hloc

end ReflectedGMS.FlowCodingDensity
