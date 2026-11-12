/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.BlockConstructionAux1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan

/-!
# Node `B57`, auxiliary file 1: Riemann weights, similarities and gluing of polygons

Deterministic list/polygon bookkeeping for the discrete block construction
(see `LQGDimension/LFPP/BlockConstruction.lean` for the architecture).

* `ew N g e`, `rcW N z g`: the Riemann weight functional
  `Σ_e |e| (1/N) Σ_{q<N} g(e(q/N))`; `riemannCost ξ N z φ = rcW N z (exp ∘ ξφ)`.
* linearity of `rcW` in `g`, the point decomposition `rcW N z g = Σ_{p ∈ S} rcW N z (dlt p g)`,
  and `rcW N z (dlt p g) = g p * rcW N z (dlt p 1)`.
* `app L z = L.1 * z + L.2` (similarities); `rcW N (z.map (app L)) g = ‖L.1‖ rcW N z (g ∘ app L)`.
* `glueFn m f`: concatenation of `m` polygons with matching endpoints; its edge list is the
  concatenation of the edge lists.
-/

noncomputable section

open MeasureTheory Set Real
open scoped Classical

namespace LQGDimension.BlockCons

open Blueprint.Draft

/-! ## Edges -/

theorem edges_single (x : ℂ) : edges [x] = [] := rfl

theorem edges_cons_cons (x y : ℂ) (l : List ℂ) : edges (x :: y :: l) = (x, y) :: edges (y :: l) :=
  rfl

theorem edges_map (f : ℂ → ℂ) (z : List ℂ) :
    edges (z.map f) = (edges z).map fun e => (f e.1, f e.2) := by
  unfold edges
  rw [← List.map_tail, List.zip_map]
  rfl

/-- `edges (P ++ R.tail) = edges P ++ edges R` when `R` starts where `P` ends. -/
theorem edges_append_tail : ∀ (P R : List ℂ), P ≠ [] → R.head? = P.getLast? →
    edges (P ++ R.tail) = edges P ++ edges R
  | [], _, h, _ => absurd rfl h
  | [x], R, _, hR => by
    cases R with
    | nil => simp at hR
    | cons y R' =>
      simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hR
      subst hR
      simp [edges_single]
  | x :: y :: P, R, _, hR => by
    have ih := edges_append_tail (y :: P) R (List.cons_ne_nil _ _) (by
      rw [hR, List.getLast?_cons_cons])
    rw [List.cons_append, List.cons_append, edges_cons_cons, ← List.cons_append, ih,
      edges_cons_cons, List.cons_append]

theorem getLast?_append_tail (P R : List ℂ) (hR : R ≠ []) (h : R.head? = P.getLast?) :
    (P ++ R.tail).getLast? = R.getLast? := by
  cases R with
  | nil => exact absurd rfl hR
  | cons y R' =>
    cases R' with
    | nil =>
      simp only [List.head?_cons] at h
      simp [h]
    | cons y' R'' =>
      rw [List.getLast?_append, List.tail_cons,
        List.getLast?_eq_some_getLast (List.cons_ne_nil y' R''), Option.some_or,
        List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil y' R'')]

/-! ## Gluing polygons -/

/-- Concatenation of the polygons `f 0, …, f (m-1)` (consecutive ones share an endpoint). -/
def glueFn : (m : ℕ) → (Fin m → List ℂ) → List ℂ
  | 0, _ => []
  | m + 1, f => f 0 ++ (glueFn m fun i => f i.succ).tail

theorem head?_glueFn (m : ℕ) (f : Fin (m + 1) → List ℂ) (h0 : f 0 ≠ []) :
    (glueFn (m + 1) f).head? = (f 0).head? := by
  simp only [glueFn]
  exact List.head?_append_of_ne_nil _ h0

theorem mem_glueFn : ∀ (m : ℕ) (f : Fin m → List ℂ) (v : ℂ), v ∈ glueFn m f → ∃ i, v ∈ f i
  | 0, _, _, h => by simp [glueFn] at h
  | m + 1, f, v, h => by
    simp only [glueFn, List.mem_append] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨i, hi⟩ := mem_glueFn m _ v (List.mem_of_mem_tail h)
      exact ⟨i.succ, hi⟩

/-- Junction condition: consecutive polygons share an endpoint. -/
def Junction (m : ℕ) (f : Fin m → List ℂ) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < m), (f ⟨i, by omega⟩).getLast? = (f ⟨i + 1, h⟩).head?

theorem Junction.succ {m : ℕ} {f : Fin (m + 1) → List ℂ} (h : Junction (m + 1) f) :
    Junction m fun i => f i.succ := by
  intro i hi
  exact h (i + 1) (by omega)

theorem getLast?_glueFn : ∀ (m : ℕ) (f : Fin (m + 1) → List ℂ), (∀ i, f i ≠ []) →
    Junction (m + 1) f → (glueFn (m + 1) f).getLast? = (f (Fin.last m)).getLast?
  | 0, f, _, _ => by simp [glueFn]
  | m + 1, f, hne, hJ => by
    have ih := getLast?_glueFn m (fun i => f i.succ) (fun i => hne _) hJ.succ
    have hB : glueFn (m + 1) (fun i => f i.succ) ≠ [] := by
      intro hc
      have := head?_glueFn m (fun i => f i.succ) (hne _)
      rw [hc] at this
      simp only [List.head?_nil] at this
      cases hf : f (0 : Fin (m + 1)).succ with
      | nil => exact hne _ hf
      | cons a l => rw [hf] at this; simp at this
    have hh : (glueFn (m + 1) (fun i => f i.succ)).head? = (f 0).getLast? := by
      rw [head?_glueFn m _ (hne _)]
      exact (hJ 0 (by omega)).symm
    change (f 0 ++ (glueFn (m + 1) fun i => f i.succ).tail).getLast? = _
    rw [getLast?_append_tail _ _ hB hh, ih]
    rfl

theorem edges_glueFn : ∀ (m : ℕ) (f : Fin m → List ℂ), (∀ i, f i ≠ []) → Junction m f →
    edges (glueFn m f) = (List.ofFn fun i => edges (f i)).flatten
  | 0, _, _, _ => rfl
  | m + 1, f, hne, hJ => by
    rw [List.ofFn_succ, List.flatten_cons]
    cases m with
    | zero =>
      simp [glueFn]
    | succ m =>
      have ih := edges_glueFn (m + 1) (fun i => f i.succ) (fun i => hne _) hJ.succ
      have hh : (glueFn (m + 1) (fun i => f i.succ)).head? = (f 0).getLast? := by
        rw [head?_glueFn m _ (hne _)]
        exact (hJ 0 (by omega)).symm
      change edges (f 0 ++ (glueFn (m + 1) fun i => f i.succ).tail) = _
      rw [edges_append_tail _ _ (hne 0) hh, ih]

theorem mem_edges_glueFn (m : ℕ) (f : Fin m → List ℂ) (hne : ∀ i, f i ≠ []) (hJ : Junction m f)
    (e : ℂ × ℂ) (he : e ∈ edges (glueFn m f)) : ∃ i, e ∈ edges (f i) := by
  rw [edges_glueFn m f hne hJ, List.mem_flatten] at he
  obtain ⟨l, hl, he⟩ := he
  rw [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  exact ⟨i, he⟩

/-! ## The Riemann weight functional -/

/-- Riemann weight of one edge: `|e| (1/N) Σ_{q<N} g(e(q/N))`. -/
def ew (N : ℕ) (g : ℂ → ℝ) (e : ℂ × ℂ) : ℝ :=
  ‖e.2 - e.1‖ * ((1 : ℝ) / N) * ∑ q ∈ Finset.range N, g (e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (e.2 - e.1))

/-- Riemann weight functional of a polygon. -/
def rcW (N : ℕ) (z : List ℂ) (g : ℂ → ℝ) : ℝ := ((edges z).map (ew N g)).sum

theorem riemannCost_eq_rcW (ξ : ℝ) (N : ℕ) (z : List ℂ) (φ : ℂ → ℝ) :
    riemannCost ξ N z φ = rcW N z (fun w => Real.exp (ξ * φ w)) := rfl

theorem rcW_glueFn (N : ℕ) (m : ℕ) (f : Fin m → List ℂ) (hne : ∀ i, f i ≠ []) (hJ : Junction m f)
    (g : ℂ → ℝ) : rcW N (glueFn m f) g = ∑ i, rcW N (f i) g := by
  unfold rcW
  rw [edges_glueFn m f hne hJ, List.map_flatten, List.sum_flatten]
  simp only [List.map_ofFn, List.sum_ofFn]
  rfl

theorem list_sum_map_finset_sum {α ι : Type*} (l : List α) (s : Finset ι) (F : ι → α → ℝ) :
    (l.map fun a => ∑ i ∈ s, F i a).sum = ∑ i ∈ s, (l.map (F i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

theorem rcW_congr (N : ℕ) (z : List ℂ) {g h : ℂ → ℝ} (hgh : ∀ p ∈ riemannPts N z, g p = h p) :
    rcW N z g = rcW N z h := by
  unfold rcW
  congr 1
  refine List.map_congr_left fun e he => ?_
  unfold ew
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  exact hgh _ ⟨e, he, q, Finset.mem_range.1 hq, rfl⟩

theorem ew_finset_sum {ι : Type*} (N : ℕ) (s : Finset ι) (G : ι → ℂ → ℝ) (e : ℂ × ℂ) :
    ew N (fun w => ∑ i ∈ s, G i w) e = ∑ i ∈ s, ew N (G i) e := by
  unfold ew
  rw [Finset.sum_comm, Finset.mul_sum]

theorem rcW_finset_sum {ι : Type*} (N : ℕ) (z : List ℂ) (s : Finset ι) (G : ι → ℂ → ℝ) :
    rcW N z (fun w => ∑ i ∈ s, G i w) = ∑ i ∈ s, rcW N z (G i) := by
  unfold rcW
  rw [show ew N (fun w => ∑ i ∈ s, G i w) = fun e => ∑ i ∈ s, ew N (G i) e from
    funext (ew_finset_sum N s G)]
  exact list_sum_map_finset_sum _ _ _

theorem rcW_const_mul (N : ℕ) (z : List ℂ) (c : ℝ) (g : ℂ → ℝ) :
    rcW N z (fun w => c * g w) = c * rcW N z g := by
  unfold rcW ew
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  rw [← Finset.mul_sum]
  ring

theorem ew_nonneg (N : ℕ) {g : ℂ → ℝ} (hg : ∀ w, 0 ≤ g w) (e : ℂ × ℂ) : 0 ≤ ew N g e :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity)) (Finset.sum_nonneg fun q _ => hg _)

theorem rcW_nonneg (N : ℕ) (z : List ℂ) {g : ℂ → ℝ} (hg : ∀ w, 0 ≤ g w) : 0 ≤ rcW N z g :=
  List.sum_nonneg fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
    exact ew_nonneg N hg e

/-! ## Point decomposition -/

/-- `g` restricted to the point `p`. -/
def dlt (p : ℂ) (g : ℂ → ℝ) : ℂ → ℝ := fun w => if w = p then g w else 0

theorem rcW_eq_sum_dlt (N : ℕ) (z : List ℂ) (S : Finset ℂ) (hS : riemannPts N z ⊆ ↑S)
    (g : ℂ → ℝ) : rcW N z g = ∑ p ∈ S, rcW N z (dlt p g) := by
  rw [← rcW_finset_sum]
  refine rcW_congr N z fun w hw => ?_
  have hwS : w ∈ S := hS hw
  simp only [dlt]
  rw [Finset.sum_ite_eq]; simp [hwS]

theorem dlt_eq_mul (p : ℂ) (g : ℂ → ℝ) : dlt p g = fun w => g p * dlt p (fun _ => 1) w := by
  funext w
  simp only [dlt]
  split_ifs with h
  · subst h; ring
  · ring

theorem rcW_dlt (N : ℕ) (z : List ℂ) (p : ℂ) (g : ℂ → ℝ) :
    rcW N z (dlt p g) = g p * rcW N z (dlt p fun _ => 1) := by
  rw [dlt_eq_mul p g, rcW_const_mul]

theorem dlt_one_nonneg (p w : ℂ) : 0 ≤ dlt p (fun _ => (1 : ℝ)) w := by
  simp only [dlt]; split_ifs <;> norm_num

/-! ## Similarities -/

/-- The complex-affine map `z ↦ L.1 z + L.2`. -/
def app (L : ℂ × ℂ) (z : ℂ) : ℂ := L.1 * z + L.2

/-- Composition of similarities: `app (comp L L') = app L ∘ app L'`. -/
def comp (L L' : ℂ × ℂ) : ℂ × ℂ := (L.1 * L'.1, L.1 * L'.2 + L.2)

theorem app_comp (L L' : ℂ × ℂ) (z : ℂ) : app (comp L L') z = app L (app L' z) := by
  simp only [app, comp]; ring

theorem app_sub (L : ℂ × ℂ) (z w : ℂ) : app L z - app L w = L.1 * (z - w) := by
  simp only [app]; ring

theorem ew_app (N : ℕ) (g : ℂ → ℝ) (L : ℂ × ℂ) (e : ℂ × ℂ) :
    ew N g (app L e.1, app L e.2) = ‖L.1‖ * ew N (fun w => g (app L w)) e := by
  unfold ew
  simp only
  rw [app_sub, norm_mul]
  have : ∀ q : ℕ, app L e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (L.1 * (e.2 - e.1)) =
      app L (e.1 + (((q : ℝ) / N : ℝ) : ℂ) * (e.2 - e.1)) := fun q => by simp only [app]; ring
  simp_rw [this]
  ring

theorem rcW_map_app (N : ℕ) (z : List ℂ) (L : ℂ × ℂ) (g : ℂ → ℝ) :
    rcW N (z.map (app L)) g = ‖L.1‖ * rcW N z (fun w => g (app L w)) := by
  unfold rcW
  rw [edges_map, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  exact ew_app N g L e

/-- Riemann points of an edge `(app L 0, app L 1)` are the points `app L (q/N)`. -/
theorem ew_edge_pt (L : ℂ × ℂ) (N q : ℕ) :
    app L 0 + (((q : ℝ) / N : ℝ) : ℂ) * (app L 1 - app L 0) = app L (((q : ℝ) / N : ℝ) : ℂ) := by
  simp only [app]; ring

end LQGDimension.BlockCons
