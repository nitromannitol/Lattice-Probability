/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Families at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Tiles
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonalUpperBound




 












set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Convex

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.LFPP

 

 
def famUnionFin : (N : ℕ) → (Fin (N + 1) → Exponent.PolygonalCost.RatPolygonFamily) → Exponent.PolygonalCost.RatPolygonFamily
  | 0, G => G 0
  | N + 1, G => Exponent.InwardMap.appendFamilies (famUnionFin N fun i => G i.castSucc) (G (Fin.last (N + 1)))

theorem famUnionFin_trace : ∀ (N : ℕ) (G : Fin (N + 1) → Exponent.PolygonalCost.RatPolygonFamily),
    (famUnionFin N G).trace = ⋃ i, (G i).trace
  | 0, G => by
    ext z
    simp only [famUnionFin, mem_iUnion]
    exact ⟨fun h => ⟨0, h⟩, fun ⟨i, hi⟩ => by rwa [Fin.fin_one_eq_zero i] at hi⟩
  | N + 1, G => by
    rw [famUnionFin, Exponent.InwardMap.appendFamilies_trace, famUnionFin_trace N]
    ext z
    simp only [mem_union, mem_iUnion]
    rw [Fin.exists_fin_succ' (P := fun i => z ∈ (G i).trace)]

theorem famUnionFin_cost : ∀ (N : ℕ) (G : Fin (N + 1) → Exponent.PolygonalCost.RatPolygonFamily) (ξ : ℝ)
    (f : ℂ → ℝ), (famUnionFin N G).cost ξ f = ∑ i, (G i).cost ξ f
  | 0, G, ξ, f => by simp [famUnionFin]
  | N + 1, G, ξ, f => by
    rw [famUnionFin, Exponent.InwardMap.appendFamilies_cost, famUnionFin_cost N]
    exact (Fin.sum_univ_castSucc (fun i => (G i).cost ξ f)).symm

 
theorem exists_famUnion {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (G : ι → Exponent.PolygonalCost.RatPolygonFamily) :
    ∃ H : Exponent.PolygonalCost.RatPolygonFamily, H.trace = (⋃ i ∈ s, (G i).trace) ∧
      ∀ (ξ : ℝ) (f : ℂ → ℝ), H.cost ξ f = ∑ i ∈ s, (G i).cost ξ f := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨G a, by simp, fun ξ f => by simp⟩
  | cons a s h hs ih =>
    obtain ⟨H, hH, hc⟩ := ih
    refine ⟨Exponent.InwardMap.appendFamilies (G a) H, ?_, fun ξ f => ?_⟩
    · rw [Exponent.InwardMap.appendFamilies_trace, hH, Finset.cons_eq_insert, Finset.set_biUnion_insert]
    · rw [Exponent.InwardMap.appendFamilies_cost, hc, Finset.sum_cons]

 

 
def famEdges (F : Exponent.PolygonalCost.RatPolygonFamily) : Finset (Σ _ : Fin (F.last + 1), ℕ) :=
  Exponent.PaidDuality.polygonFullEdges Finset.univ fun i => (F.paths i).edges

 
def famA (F : Exponent.PolygonalCost.RatPolygonFamily) (e : Σ _ : Fin (F.last + 1), ℕ) : ℂ :=
  (F.paths e.1).vertex e.2

 
def famB (F : Exponent.PolygonalCost.RatPolygonFamily) (e : Σ _ : Fin (F.last + 1), ℕ) : ℂ :=
  (F.paths e.1).vertex (min (e.2 + 1) (F.paths e.1).edges)

theorem famTrace_eq_segments (F : Exponent.PolygonalCost.RatPolygonFamily) :
    F.trace = ⋃ e ∈ famEdges F, [famA F e -[ℝ] famB F e] :=
  (Exponent.PaidDuality.polygonFullTrace_eq_pathsTrace Finset.univ (fun i => (F.paths i).vertex)
    (fun i => (F.paths i).edges)).symm

theorem famCost_eq_segments (F : Exponent.PolygonalCost.RatPolygonFamily) (ξ : ℝ) (f : ℂ → ℝ) :
    F.cost ξ f = ∑ e ∈ famEdges F, segCost ξ f (famA F e) (famB F e) :=
  (Exponent.PaidDuality.polygonFull_cost_eq_paths_cost Finset.univ (fun i => (F.paths i).vertex)
    (fun i => (F.paths i).edges) ξ f).symm

 

theorem openSquareAnnulus_subset_closed :
    Exponent.PolygonalCost.openSquareAnnulus ⊆ Exponent.PolygonalCost.closedSquareAnnulus := by
  rintro z ⟨⟨h1, h2⟩, h3⟩
  refine ⟨⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩, fun h4 => h3 ?_⟩
  exact ⟨Ioo_subset_Icc_self h4.1, Ioo_subset_Icc_self h4.2⟩

 
def imageFamily (b : ℚ) (F : Exponent.PolygonalCost.RatPolygonFamily) : Exponent.PolygonalCost.RatPolygonFamily :=
  famUnionFin F.last fun i => Exponent.InwardMap.canonicalImagePolygonFamily b (F.paths i)

theorem imageFamily_trace (b : ℚ) (hb : 0 ≤ b) (F : Exponent.PolygonalCost.RatPolygonFamily) :
    (imageFamily b F).trace = Exponent.InwardMap.inwardMap (b : ℝ) '' F.trace := by
  rw [imageFamily, famUnionFin_trace, Exponent.InwardMap.ratFamily_trace_iUnion F, image_iUnion]
  simp only [Exponent.InwardMap.canonicalImagePolygonFamily_trace b hb]

theorem path_subset_trace (F : Exponent.PolygonalCost.RatPolygonFamily) (i : Fin (F.last + 1)) :
    (F.paths i).path '' Icc (0 : ℝ) 1 ⊆ F.trace := by
  rw [Exponent.InwardMap.ratFamily_trace_iUnion F]
  exact subset_iUnion (fun i => (F.paths i).path '' Icc (0 : ℝ) 1) i

theorem imageFamily_cost_le (b : ℚ) (hb0 : 0 ≤ b) (hb : (b : ℝ) ≤ 1 / 256) (ξ G : ℝ)
    (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G) (f : ℂ → ℝ)
    (hfd : ∀ z ∈ Exponent.InwardMap.gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ Exponent.InwardMap.gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    (F : Exponent.PolygonalCost.RatPolygonFamily) (hF : F.trace ⊆ Exponent.PolygonalCost.closedSquareAnnulus) :
    (imageFamily b F).cost ξ f ≤
      ENNReal.ofReal ((5 / 4 : ℝ) * Real.exp (32 * Real.sqrt 2 * ξ * ((b : ℝ) * G))) *
        F.cost ξ f := by
  rw [imageFamily, famUnionFin_cost, Exponent.PolygonalCost.RatPolygonFamily.cost, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    Exponent.InwardMap.canonicalImagePolygonFamily_cost_le b hb0 hb ξ G hξ hG0 f hfd hG (F.paths i)
      ((path_subset_trace F i).trans hF)

theorem imageFamily_admitted (b : ℚ) (hb0 : 0 < b) (hb : (b : ℝ) ≤ 1 / 256)
    (F : Exponent.PolygonalCost.RatPolygonFamily) (hF : F.Admitted) :
    (imageFamily b F).Admitted ∧
      (imageFamily b F).trace ⊆ Exponent.InwardMap.clearedSquareAnnulus (b : ℝ) := by
  have hb0' : (0 : ℝ) < b := by exact_mod_cast hb0
  have hcl : (imageFamily b F).trace ⊆ Exponent.InwardMap.clearedSquareAnnulus (b : ℝ) := by
    rw [imageFamily_trace b hb0.le]
    rintro _ ⟨z, hz, rfl⟩
    exact Exponent.InwardMap.inwardMap_closed_to_cleared (b : ℝ) hb0'.le hb
      (openSquareAnnulus_subset_closed (hF.1 hz))
  refine ⟨⟨fun z hz => Exponent.InwardMap.clearedSquareAnnulus_subset_open (b : ℝ) hb0' z (hcl hz), ?_⟩, hcl⟩
  rw [imageFamily_trace b hb0.le]
  exact Exponent.InwardMap.inwardMap_preserves_disconnects (b : ℝ) hb0' hb _ hF.2

 

 
def ratC (v : ℚ × ℚ) : ℂ := ((v.1 : ℝ) : ℂ) + ((v.2 : ℝ) : ℂ) * Complex.I

 
def ratPolygonAffine (a : ℚ) (v : ℚ × ℚ) (P : Exponent.PolygonalCost.RatPolygon) : Exponent.PolygonalCost.RatPolygon where
  edges := P.edges
  vertices k := (a * (P.vertices k).1 + v.1, a * (P.vertices k).2 + v.2)

theorem ratPolygonAffine_vertex (a : ℚ) (v : ℚ × ℚ) (P : Exponent.PolygonalCost.RatPolygon) (j : ℕ) :
    (ratPolygonAffine a v P).vertex j = ((a : ℝ) : ℂ) * P.vertex j + ratC v := by
  simp only [Exponent.PolygonalCost.RatPolygon.vertex, ratPolygonAffine, ratC]
  push_cast
  ring

theorem segPath_affine (α β p q : ℂ) (s : ℝ) :
    segPath (α * p + β) (α * q + β) s = α * segPath p q s + β := by
  simp only [segPath, Complex.real_smul]
  ring

theorem polygonPath_affine (α β : ℂ) (w : ℕ → ℂ) :
    ∀ (n : ℕ) (t : ℝ), Exponent.PolygonCofinality.polygonPath (fun j => α * w j + β) n t =
      α * Exponent.PolygonCofinality.polygonPath w n t + β
  | 0, t => by simp [Exponent.PolygonCofinality.polygonPath]
  | n + 1, t => by
    simp only [Exponent.PolygonCofinality.polygonPath, concatPath]
    split_ifs
    · exact polygonPath_affine α β w n _
    · exact segPath_affine α β _ _ _

theorem ratPolygonAffine_path (a : ℚ) (v : ℚ × ℚ) (P : Exponent.PolygonalCost.RatPolygon) (t : ℝ) :
    (ratPolygonAffine a v P).path t = ((a : ℝ) : ℂ) * P.path t + ratC v := by
  have e : (ratPolygonAffine a v P).vertex = fun j => ((a : ℝ) : ℂ) * P.vertex j + ratC v :=
    funext (ratPolygonAffine_vertex a v P)
  simp only [Exponent.PolygonalCost.RatPolygon.path]
  rw [show (ratPolygonAffine a v P).edges = P.edges from rfl, e]
  exact polygonPath_affine _ _ _ _ _

theorem lfppLen_affine (ξ : ℝ) (ψ : ℂ → ℝ) (α β : ℂ) (P : ℝ → ℂ) :
    lfppLen ξ ψ (fun t => α * P t + β) =
      ENNReal.ofReal ‖α‖ * lfppLen ξ (fun z => ψ (α * z + β)) P := by
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [deriv_add_const, deriv_const_mul_field, norm_mul, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  ring

 
def famAffine (a : ℚ) (v : ℚ × ℚ) (F : Exponent.PolygonalCost.RatPolygonFamily) : Exponent.PolygonalCost.RatPolygonFamily where
  last := F.last
  paths i := ratPolygonAffine a v (F.paths i)

theorem famAffine_trace (a : ℚ) (v : ℚ × ℚ) (F : Exponent.PolygonalCost.RatPolygonFamily) :
    (famAffine a v F).trace = (fun z => ((a : ℝ) : ℂ) * z + ratC v) '' F.trace := by
  rw [Exponent.InwardMap.ratFamily_trace_iUnion, Exponent.InwardMap.ratFamily_trace_iUnion F, image_iUnion]
  refine iUnion_congr fun i => ?_
  change (ratPolygonAffine a v (F.paths i)).path '' Icc (0 : ℝ) 1 = _
  rw [image_image]
  exact image_congr fun t _ => ratPolygonAffine_path a v _ t

theorem famAffine_cost (a : ℚ) (ha : 0 < a) (v : ℚ × ℚ) (F : Exponent.PolygonalCost.RatPolygonFamily)
    (ξ : ℝ) (ψ : ℂ → ℝ) :
    (famAffine a v F).cost ξ ψ = ENNReal.ofReal (a : ℝ) *
      F.cost ξ (fun z => ψ (((a : ℝ) : ℂ) * z + ratC v)) := by
  simp only [Exponent.PolygonalCost.RatPolygonFamily.cost, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change lfppLen ξ ψ (ratPolygonAffine a v (F.paths i)).path = _
  rw [show (ratPolygonAffine a v (F.paths i)).path =
      fun t => ((a : ℝ) : ℂ) * (F.paths i).path t + ratC v from
    funext (ratPolygonAffine_path a v _), lfppLen_affine]
  congr 2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by exact_mod_cast ha)]

 
theorem disconnects_affine {K I J : Set ℂ} (α β : ℂ) (hα : α ≠ 0)
    (h : LQGMetric.Disconnects K I J) :
    LQGMetric.Disconnects ((fun z => α * z + β) '' K) ((fun z => α * z + β) '' I)
      ((fun z => α * z + β) '' J) := by
  intro x y γ hx hy
  set g : ℂ → ℂ := fun z => α⁻¹ * (z - β)
  have hg : Continuous g := by fun_prop
  have hgA : ∀ u, g (α * u + β) = u := fun u => by
    simp only [g, add_sub_cancel_right]; field_simp
  have hAg : ∀ z, α * g z + β = z := fun z => by
    simp only [g]; field_simp; ring
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  have hu' : g (α * u + β) ∈ I := by rw [hgA]; exact hu
  have hw' : g (α * w + β) ∈ J := by rw [hgA]; exact hw
  obtain ⟨z, ⟨t, ht⟩, hzK⟩ := h _ _ (γ.map hg) hu' hw'
  refine ⟨γ t, mem_range_self t, ⟨z, hzK, ?_⟩⟩
  rw [← ht]
  simp only [Path.map_coe, Function.comp_apply]
  exact hAg _



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
