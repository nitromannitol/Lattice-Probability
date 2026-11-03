/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.Polygon at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen

/-!
# Polygonal paths and polygon integrals in subsets of `ℂ` (EXT-CA node H1)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "H. Homology Cauchy", node H1.

* `Polygon`: a polygonal curve in `ℂ`, given by its initial vertex `head` and the list `rest` of
  the remaining vertices; `Polygon.carrier` is the union of the segments joining consecutive
  vertices, `Polygon.length` is the sum of their lengths, and `polyIntegral f p` is the integral
  of the 1-form `f dz` along `p`, each edge being integrated with mathlib's `curveIntegral`
  (`∫ᶜ`). Concatenation is `Polygon.append`, with `carrier`/`length`/integral additive over it.
* `norm_polyIntegral_le`: `‖∮_p f dz‖ ≤ length p · sup_p ‖f‖`.
* `exists_polygon_of_isPreconnected`: in an open preconnected `U ⊆ ℂ`, any two points of `U` are
  joined by a polygon lying in `U`.

## Sources and deviations

The polygon and its integral are Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser
2021), Definition 2.8, p. 59: a *chain* of curves `γ = (γ₁, …, γₙ)` (not necessarily joined end to
end) has integral `∫_γ f := Σ_j ∫_{γ_j} f`, and a piecewise smooth curve has length
`l(γ) := ∫ |γ'|`. Here the curves are the edges of the polygon, each integrated with
`curveIntegral` of `Path.segment`, and `f dz` is the 1-form `z ↦ f z • id`. The bound
`‖∮_p f dz‖ ≤ M · l(p)` is Burckel, Exercise 2.9(i), p. 60 (`|∫_γ f| ≤ M · l(γ)` for `M` a bound
on `|f|` on the range of `γ`), applied edge by edge; the per-edge form we feed it with is
mathlib's `norm_curveIntegral_segment_le`.

The existence of a polygon in `U` joining `a` to `b` is Burckel, Corollary 1.28 ("every region is
polygonally connected"), p. 34, whose proof combines the "Basic Connectedness Lemma"
(Theorem 1.27, p. 34, here with `θ = 1`): the set `A` of points of `U` reachable from a fixed
`a ∈ U` by a polygon in `U` is relatively clopen in `U`, so equals `U`. **Deviation in proof
route** (mathematics unchanged): instead of reproducing Burckel's relative-clopen argument we
apply mathlib's `IsPreconnected.induction₂'`, which is that argument in packaged form (a
symmetric, transitive relation holding on a relative neighbourhood of every point of a
preconnected set is universal there). The neighbourhood step is Burckel's `[a, …, z, w]` step —
the single segment `[z, w] ⊆ ball z r ⊆ U` — and the transitivity step is concatenation of vertex
lists. The blueprint also lists Ahlfors, *Complex Analysis* (3rd ed. 1979), Ch. 4 §4 for this
node; it was not consulted.
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology Convex

namespace QuantumZipper.CA.Homology

/-! ## Polygonal walks

A walk is a starting point together with a list of further points; for a polygon the starting
point is the initial vertex and the list is `Polygon.rest`. -/

/-- The terminal point of the walk `u → l₀ → l₁ → ⋯`; equals `u` if `l = []`. -/
def walkLast (u : ℂ) : List ℂ → ℂ
  | [] => u
  | v :: t => walkLast v t

@[simp] theorem walkLast_nil (u : ℂ) : walkLast u [] = u := rfl
theorem walkLast_cons (u v : ℂ) (t : List ℂ) : walkLast u (v :: t) = walkLast v t := rfl
@[simp] theorem walkLast_singleton (u v : ℂ) : walkLast u [v] = v := rfl

/-- The polyline traced by the walk `u → l₀ → l₁ → ⋯`: the union of the closed segments joining
consecutive points. -/
def walkCarrier (u : ℂ) : List ℂ → Set ℂ
  | [] => ∅
  | v :: t => segment ℝ u v ∪ walkCarrier v t

@[simp] theorem walkCarrier_nil (u : ℂ) : walkCarrier u [] = ∅ := rfl
theorem walkCarrier_cons (u v : ℂ) (t : List ℂ) :
    walkCarrier u (v :: t) = segment ℝ u v ∪ walkCarrier v t := rfl
@[simp] theorem walkCarrier_singleton (u v : ℂ) : walkCarrier u [v] = segment ℝ u v := by
  show segment ℝ u v ∪ walkCarrier v [] = segment ℝ u v
  simp

/-- The total (geometric) length of the walk. -/
def walkLength (u : ℂ) : List ℂ → ℝ
  | [] => 0
  | v :: t => ‖u - v‖ + walkLength v t

@[simp] theorem walkLength_nil (u : ℂ) : walkLength u [] = 0 := rfl
theorem walkLength_cons (u v : ℂ) (t : List ℂ) :
    walkLength u (v :: t) = ‖u - v‖ + walkLength v t := rfl
@[simp] theorem walkLength_singleton (u v : ℂ) : walkLength u [v] = ‖u - v‖ := by
  show ‖u - v‖ + walkLength v [] = ‖u - v‖
  simp

/-- Integral of a 1-form along the walk. -/
noncomputable def walkIntegralCLM (ω : ℂ → ℂ →L[ℂ] ℂ) (u : ℂ) : List ℂ → ℂ
  | [] => 0
  | v :: t => (∫ᶜ z in Path.segment u v, ω z) + walkIntegralCLM ω v t

@[simp] theorem walkIntegralCLM_nil (ω : ℂ → ℂ →L[ℂ] ℂ) (u : ℂ) :
    walkIntegralCLM ω u [] = 0 := rfl
theorem walkIntegralCLM_cons (ω : ℂ → ℂ →L[ℂ] ℂ) (u v : ℂ) (t : List ℂ) :
    walkIntegralCLM ω u (v :: t)
      = (∫ᶜ z in Path.segment u v, ω z) + walkIntegralCLM ω v t := rfl

/-- The 1-form `f dz`. -/
def dzForm (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ := f z • ContinuousLinearMap.id ℂ ℂ

/-- Integral of the 1-form `f dz` along the walk. -/
noncomputable def walkIntegral (f : ℂ → ℂ) (u : ℂ) (l : List ℂ) : ℂ :=
  walkIntegralCLM (dzForm f) u l

theorem walkLast_append (u : ℂ) (l₁ l₂ : List ℂ) :
    walkLast u (l₁ ++ l₂) = walkLast (walkLast u l₁) l₂ := by
  induction l₁ generalizing u with
  | nil => simp
  | cons v t ih =>
    simp only [List.cons_append, walkLast_cons]
    exact ih v

theorem walkCarrier_append (u : ℂ) (l₁ l₂ : List ℂ) :
    walkCarrier u (l₁ ++ l₂) = walkCarrier u l₁ ∪ walkCarrier (walkLast u l₁) l₂ := by
  induction l₁ generalizing u with
  | nil => simp
  | cons v t ih =>
    simp only [List.cons_append, walkCarrier_cons, walkLast_cons]
    rw [ih v, Set.union_assoc]

theorem walkIntegralCLM_append (ω : ℂ → ℂ →L[ℂ] ℂ) (u : ℂ) (l₁ l₂ : List ℂ) :
    walkIntegralCLM ω u (l₁ ++ l₂)
      = walkIntegralCLM ω u l₁ + walkIntegralCLM ω (walkLast u l₁) l₂ := by
  induction l₁ generalizing u with
  | nil => simp
  | cons v t ih =>
    simp only [List.cons_append, walkIntegralCLM_cons, walkLast_cons]
    rw [ih v, add_assoc]

/-! ## Norm bounds -/

/-- The integral of a 1-form along a walk is bounded by the length of the walk times a bound on
the 1-form over the polyline traced out (Burckel, Exercise 2.9(i), p. 60). -/
theorem norm_walkIntegralCLM_le (ω : ℂ → ℂ →L[ℂ] ℂ) (u : ℂ) (l : List ℂ) {C : ℝ}
    (hC : ∀ z ∈ walkCarrier u l, ‖ω z‖ ≤ C) :
    ‖walkIntegralCLM ω u l‖ ≤ walkLength u l * C := by
  induction l generalizing u with
  | nil => simp [walkLength]
  | cons v t ih =>
    have h₁ : ∀ z ∈ segment ℝ u v, ‖ω z‖ ≤ C := fun z hz => hC z (Or.inl hz)
    have h₂ : ∀ z ∈ walkCarrier v t, ‖ω z‖ ≤ C := fun z hz => hC z (Or.inr hz)
    have h₃ := norm_curveIntegral_segment_le (ω := ω) (a := u) (b := v) h₁
    have h₄ := ih v h₂
    simp only [walkIntegralCLM_cons, walkLength_cons]
    calc ‖(∫ᶜ z in Path.segment u v, ω z) + walkIntegralCLM ω v t‖
        ≤ ‖∫ᶜ z in Path.segment u v, ω z‖ + ‖walkIntegralCLM ω v t‖ := norm_add_le _ _
      _ ≤ C * ‖v - u‖ + walkLength v t * C := add_le_add h₃ h₄
      _ = (‖u - v‖ + walkLength v t) * C := by rw [norm_sub_rev]; ring

/-- The integral of `f dz` along a walk is bounded by the length of the walk times a bound on
`‖f‖` over the polyline traced out. -/
theorem norm_walkIntegral_le (f : ℂ → ℂ) (u : ℂ) (l : List ℂ) {C : ℝ}
    (hC : ∀ z ∈ walkCarrier u l, ‖f z‖ ≤ C) :
    ‖walkIntegral f u l‖ ≤ walkLength u l * C :=
  norm_walkIntegralCLM_le (dzForm f) u l fun z hz =>
    calc ‖dzForm f z‖ ≤ ‖f z‖ * ‖ContinuousLinearMap.id ℂ ℂ‖ := by
          simp only [dzForm]
          exact norm_smul_le (f z) (ContinuousLinearMap.id ℂ ℂ)
      _ ≤ ‖f z‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖f z‖ := mul_one _
      _ ≤ C := hC z hz

/-! ## Polygons -/

/-- A polygon in `ℂ`: the polygonal curve with initial vertex `head` running through the further
vertices `rest` in order (an empty `rest` is the constant polygon at `head`). -/
structure Polygon where
  /-- The initial vertex. -/
  head : ℂ
  /-- The remaining vertices, in order. -/
  rest : List ℂ

namespace Polygon

/-- The list of all vertices. -/
def vertices (p : Polygon) : List ℂ := p.head :: p.rest

/-- The terminal vertex. -/
def last (p : Polygon) : ℂ := walkLast p.head p.rest

/-- The set traced out by the polygon: the union of the closed segments joining consecutive
vertices. -/
def carrier (p : Polygon) : Set ℂ := walkCarrier p.head p.rest

/-- The total (geometric) length of the polygon: the sum of the lengths of its edges. -/
def length (p : Polygon) : ℝ := walkLength p.head p.rest

/-- Integral of a 1-form along the polygon, one `curveIntegral` per edge. -/
def integralCLM (ω : ℂ → ℂ →L[ℂ] ℂ) (p : Polygon) : ℂ := walkIntegralCLM ω p.head p.rest

/-- The polygon with the single vertex `a`; its carrier is empty. -/
def singleton (a : ℂ) : Polygon := ⟨a, []⟩

/-- The polygon with the two vertices `a`, `b`: a single segment. -/
def segment (a b : ℂ) : Polygon := ⟨a, [b]⟩

/-- Concatenation: the vertices of `q` are appended after those of `p`. It is a single polygonal
curve when `p.last = q.head`, which is the hypothesis of the lemmas below. -/
def append (p q : Polygon) : Polygon := ⟨p.head, p.rest ++ q.rest⟩

@[simp] theorem vertices_def (p : Polygon) : p.vertices = p.head :: p.rest := rfl
@[simp] theorem last_def (p : Polygon) : p.last = walkLast p.head p.rest := rfl
@[simp] theorem carrier_def (p : Polygon) : p.carrier = walkCarrier p.head p.rest := rfl
@[simp] theorem length_def (p : Polygon) : p.length = walkLength p.head p.rest := rfl

@[simp] theorem head_singleton (a : ℂ) : (singleton a).head = a := rfl
@[simp] theorem rest_singleton (a : ℂ) : (singleton a).rest = [] := rfl
@[simp] theorem last_singleton (a : ℂ) : (singleton a).last = a := by
  show walkLast a [] = a
  simp
@[simp] theorem carrier_singleton (a : ℂ) : (singleton a).carrier = ∅ := rfl

@[simp] theorem head_segment (a b : ℂ) : (segment a b).head = a := rfl
@[simp] theorem rest_segment (a b : ℂ) : (segment a b).rest = [b] := rfl
@[simp] theorem last_segment (a b : ℂ) : (segment a b).last = b := by
  show walkLast a [b] = b
  simp
@[simp] theorem carrier_segment (a b : ℂ) : (segment a b).carrier = _root_.segment ℝ a b := by
  show walkCarrier a [b] = _root_.segment ℝ a b
  simp

@[simp] theorem head_append (p q : Polygon) : (p.append q).head = p.head := rfl
@[simp] theorem rest_append (p q : Polygon) : (p.append q).rest = p.rest ++ q.rest := rfl

/-- If the terminal vertex of `p` is the initial vertex of `q`, then the walk of `p` ends at the
initial vertex of `q`. -/
theorem walkLast_eq_of_last_eq {p q : Polygon} (h : p.last = q.head) :
    walkLast p.head p.rest = q.head := by
  rw [← last, h]

theorem last_append {p q : Polygon} (h : p.last = q.head) : (p.append q).last = q.last := by
  have hq := walkLast_eq_of_last_eq h
  show walkLast p.head (p.rest ++ q.rest) = walkLast q.head q.rest
  rw [walkLast_append, hq]

theorem carrier_append {p q : Polygon} (h : p.last = q.head) :
    (p.append q).carrier = p.carrier ∪ q.carrier := by
  have hq := walkLast_eq_of_last_eq h
  show walkCarrier p.head (p.rest ++ q.rest)
    = walkCarrier p.head p.rest ∪ walkCarrier q.head q.rest
  rw [walkCarrier_append, hq]

theorem integralCLM_append (ω : ℂ → ℂ →L[ℂ] ℂ) {p q : Polygon} (h : p.last = q.head) :
    integralCLM ω (p.append q) = integralCLM ω p + integralCLM ω q := by
  have hq := walkLast_eq_of_last_eq h
  show walkIntegralCLM ω p.head (p.rest ++ q.rest)
    = walkIntegralCLM ω p.head p.rest + walkIntegralCLM ω q.head q.rest
  rw [walkIntegralCLM_append, hq]

end Polygon

/-- Integral of the 1-form `f dz` along a polygon, one `curveIntegral` (`∫ᶜ`) per edge. -/
def polyIntegral (f : ℂ → ℂ) (p : Polygon) : ℂ :=
  walkIntegralCLM (dzForm f) p.head p.rest

theorem polyIntegral_append (f : ℂ → ℂ) {p q : Polygon} (h : p.last = q.head) :
    polyIntegral f (p.append q) = polyIntegral f p + polyIntegral f q :=
  Polygon.integralCLM_append (dzForm f) h

@[simp] theorem polyIntegral_segment (f : ℂ → ℂ) (a b : ℂ) :
    polyIntegral f (Polygon.segment a b) = ∫ᶜ z in Path.segment a b, dzForm f z := by
  show (∫ᶜ z in Path.segment a b, dzForm f z) + walkIntegralCLM (dzForm f) b []
    = ∫ᶜ z in Path.segment a b, dzForm f z
  simp

/-! ## Polygonal connectivity of open preconnected sets -/

/-- **Polygonal connectivity of open preconnected sets.** In an open preconnected set `U ⊆ ℂ`, any
two points of `U` are joined by a polygon lying in `U` (Burckel, Corollary 1.28, p. 34). -/
theorem exists_polygon_of_isPreconnected {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    ∃ p : Polygon, p.head = a ∧ p.last = b ∧ ∀ z ∈ p.carrier, z ∈ U := by
  have hjoin : ∀ x ∈ U, ∀ y ∈ U,
      ∃ p : Polygon, p.head = x ∧ p.last = y ∧ ∀ z ∈ p.carrier, z ∈ U := by
    intro x hx y hy
    refine IsPreconnected.induction₂' hc
      (fun x y => ∃ p : Polygon, p.head = x ∧ p.last = y ∧ ∀ z ∈ p.carrier, z ∈ U)
      ?hstep ?htrans hx hy
    case hstep =>
      -- a segment stays inside a ball around its initial point, hence inside `U`
      intro z hz
      obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz)
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds z hr)]
        with w hwU hw
      constructor
      · refine ⟨Polygon.segment z w, rfl, rfl, ?_⟩
        rw [Polygon.carrier_segment]
        exact fun u hu =>
          hrU ((convex_ball z r).segment_subset (mem_ball_self hr) hw hu)
      · refine ⟨Polygon.segment w z, rfl, rfl, ?_⟩
        rw [Polygon.carrier_segment]
        exact fun u hu =>
          hrU ((convex_ball z r).segment_subset hw (mem_ball_self hr) hu)
    case htrans =>
      -- concatenate the two vertex lists
      intro x y z hx hy hz ⟨p, hp, hp', hp''⟩ ⟨q, hq, hq', hq''⟩
      have hpq : p.last = q.head := by rw [hp', hq]
      refine ⟨p.append q, ?_, ?_, ?_⟩
      · rw [Polygon.head_append]; exact hp
      · rw [Polygon.last_append hpq]; exact hq'
      · rw [Polygon.carrier_append hpq]
        exact fun w hw => hw.elim (hp'' w) (hq'' w)
  obtain ⟨p, hp, hp', hp''⟩ := hjoin a ha b hb
  exact ⟨p, hp, hp', hp''⟩

end QuantumZipper.CA.Homology
