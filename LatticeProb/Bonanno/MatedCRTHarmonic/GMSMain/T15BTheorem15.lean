/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T15BTheorem15 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BInterior
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BStatement
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15BH2

/-!
# [18] Theorem 1.5 (Hölder continuity), deterministic on the good event

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18], Theorem 1.5 ((1.9), `[18]`), deduced as in [18]'s assembly of (3.33)
from (3.30), (3.31), (3.32), in the boundary-sensitive form: the interior estimate (3.30′) (`interior_estimate`, from (3.35)), the boundary estimate (3.31′)
(the named input `BoundaryEstimate`), and Hölder boundary data (bounds for (1.6)).

**Statement** (`theorem15_deterministic`). On one environment — a cellular embedding `H` of a connected graph, marked
points `pt x ∈ H_x` (in [18] `pt x = η(x)`), a bounded open `D`, a mesh `ε ∈ (0, 1]` and exponents `0 < β ≤ q ≤ 1`
such that the cells of `V(D)` have diameter `≤ ε^q` (Lemma 2.7), (3.35) holds with probability `p > 0` at every radius
`r ≥ ε^β` with `B_{2r}(z) ⊆ D`, and (3.31′) holds with floor `ε^β` and constants `(C₁, ξ₁)` — every discrete harmonic
extension `g` of the (1.6) data of a `χ`-Hölder `f` (constant `C_f`, `|f| ≤ M_f` on `∂D`) satisfies
`|g(x) − g(y)| ≤ A₀ (ε ∨ |pt x − pt y|)^ξ` for all `x, y ∈ V(D)`, with
`ξ = min(β ξ₀/2, β χ/4, β ξ₁/4, q χ)` (`ξ₀ = holderExponent p`) and `A₀` explicit in `(p, C₁, ξ₁, β, χ, C_f, M_f)`
(`theorem15Exponent`, `theorem15Const`): neither depends on `ε`, on the environment, or on `D` beyond `C_f, M_f`.

**Proof**. Put `w = ε ∨ d`, `d = |pt x − pt y|`, `δ = ε^β ∨ d ≤ w^β`, `τ = δ^{1/4}`. If
`w ≥ w₀ = 16^{−1/β}` the bound is trivial (`|g| ≤ M_f` by the maximum principle). Otherwise `τ < 1/2`:
1. `x, y ∈ V(∂D)`: Hölder data and cell diameters, `|g(x) − g(y)| ≤ C_f (2ε^q + d)^χ ≤ 3^χ C_f w^{qχ}`.
2. `x` interior, `dist(pt x, ∂D) ≥ τ²`: (3.30′) gives `A M_f δ^{ξ₀}/τ^{2ξ₀} = A M_f τ^{2ξ₀}`.
3. `x` interior, `dist(pt x, ∂D) < τ²`: (3.31′) at `x` (and at `y` if `y` is interior, `dist(pt y, ∂D) < 2τ² < τ`)
   with `t = τ`, comparing boundary values within `5τ` of each other: `2·5^χ C_f τ^χ + (1 + 2^{ξ₁}) C₁ M_f τ^{ξ₁}`.
4. `x ∈ V(∂D)`, `y` interior: cases 2–3 with `x, y` exchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Topology

namespace MatedCRTHarmonic.GMSMain.T15B

open LFMultigraph Harmonic Markov

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-! ### Cells at the boundary -/

/-- Every point of `∂D` (for open `D`) lies in the cell of some vertex of `V(D)` (local finiteness of the cells). -/
theorem exists_mem_cell_of_mem_frontier {D : Set ℂ} {p : ℂ} (hp : p ∈ frontier D) :
    ∃ a ∈ verticesMeeting H.cell D, p ∈ H.cell a := by
  obtain ⟨t, ht, hfin⟩ := H.locallyFinite_cell p
  set F : Set V := {i | (H.cell i ∩ t).Nonempty ∧ p ∉ H.cell i} with hFdef
  have hFfin : F.Finite := hfin.subset fun i hi => hi.1
  have hclosed : IsClosed (⋃ i ∈ F, H.cell i) :=
    hFfin.isClosed_biUnion fun i _ => (H.isCompact_cell i).isClosed
  have hpF : p ∉ ⋃ i ∈ F, H.cell i := by
    simp only [mem_iUnion, not_exists]
    intro i hi
    exact hi.2
  have hnhds : t ∩ (⋃ i ∈ F, H.cell i)ᶜ ∈ 𝓝 p :=
    Filter.inter_mem ht (hclosed.isOpen_compl.mem_nhds hpF)
  obtain ⟨d, hd1, hd2⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hp) _ hnhds
  obtain ⟨a, ha⟩ : ∃ a, d ∈ H.cell a := by
    have : d ∈ ⋃ a, H.cell a := by rw [H.iUnion_cell]; exact mem_univ d
    simpa using this
  refine ⟨a, ⟨d, ha, hd2⟩, ?_⟩
  by_contra hpa
  exact hd1.2 (mem_biUnion (show a ∈ F from ⟨⟨d, ha, hd1.1⟩, hpa⟩) ha)

/-- A bounded nonempty set in `ℂ` has nonempty frontier. -/
theorem frontier_nonempty_of_bounded {D : Set ℂ} (hDb : Bornology.IsBounded D) (hne : D.Nonempty) :
    (frontier D).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨hne, fun h => ?_⟩
  rw [h] at hDb
  exact NormedSpace.unbounded_univ ℝ ℂ hDb

/-- If `t > dist(z, ∂D)`, some vertex of `V(D)` has a cell meeting `∂D ∩ B_t(z)`. -/
theorem exists_bdry_vertex_near {D : Set ℂ} (hDb : Bornology.IsBounded D) (hne : D.Nonempty) {z : ℂ}
    {t : ℝ} (ht : infDist z (frontier D) < t) :
    ∃ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D ∩ ball z t) := by
  obtain ⟨p, hp, hpz⟩ := (infDist_lt_iff (frontier_nonempty_of_bounded hDb hne)).mp ht
  obtain ⟨a, ha, hpa⟩ := exists_mem_cell_of_mem_frontier H hp
  exact ⟨a, ha, p, hpa, hp, mem_ball.mpr (by rwa [dist_comm])⟩

/-! ### (3.30′) in ratio form -/

/-- **[18] (3.30′) in ratio form** (deterministic): under the hypotheses of
`interior_estimate`, with `D` bounded, for an interior vertex `x`, `y ∈ V(D)`, `z_x ∈ H_x`, `z_y ∈ H_y`:
`dist(z_x, ∂D) > 0` and `|u(x) − u(y)| ≤ A M ((s ∨ |z_x − z_y|)/dist(z_x, ∂D))^ξ`. -/
theorem interior_estimate_ratio (hconn : G.adj.Connected) (u : V → ℝ) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {p s Mb : ℝ} (hp : 0 < p) (hs : 0 < s)
    (hharm : ∀ v, (H.cell v ∩ D).Nonempty → ¬ (H.cell v ∩ frontier D).Nonempty → GMS3.lap G u v = 0)
    (hMb : ∀ v ∈ verticesMeeting H.cell D, |u v| ≤ Mb)
    (hdisc : ∀ (z : ℂ) (r : ℝ), s ≤ r → ball z (2 * r) ⊆ D → ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    {x y : V} (hx : x ∈ verticesMeeting H.cell D) (hxA : x ∉ verticesMeeting H.cell (frontier D))
    (hy : y ∈ verticesMeeting H.cell D) {zx zy : ℂ} (hzx : zx ∈ H.cell x) (hzy : zy ∈ H.cell y) :
    0 < infDist zx (frontier D) ∧
      |u x - u y| ≤ holderConst p * Mb *
        (max s (dist zx zy) / infDist zx (frontier D)) ^ holderExponent p := by
  have hzxD : zx ∈ D := GMS3.cell_subset_of_inter_frontier_eq_empty H hDo hx
    (Set.not_nonempty_iff_eq_empty.mp hxA) hzx
  have hR : 0 < infDist zx (frontier D) := by
    rw [← infDist_pos_iff_notMem_closure (frontier_nonempty_of_bounded hDb ⟨zx, hzxD⟩),
      isClosed_frontier.closure_eq]
    exact fun h => (Set.eq_empty_iff_forall_notMem.mp hDo.inter_frontier_eq) zx ⟨hzxD, h⟩
  refine ⟨hR, ?_⟩
  have h := interior_estimate H hconn u hDo hp hs hharm hMb hdisc hx hxA hy hzx hzy
  have hRξ : 0 < infDist zx (frontier D) ^ holderExponent p := Real.rpow_pos_of_pos hR _
  rw [Real.div_rpow (le_max_of_le_left hs.le) hR.le, ← mul_div_assoc, le_div_iff₀ hRξ]
  exact h

/-! ### The maximum principle on `V(D)` -/

/-- The Laplacian of `c − u`. -/
theorem lap_const_sub (u : V → ℝ) (c : ℝ) (v : V) :
    GMS3.lap G (fun w => c - u w) v = -GMS3.lap G u v := by
  unfold GMS3.lap
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- The Laplacian of `c + u`. -/
theorem lap_const_add (u : V → ℝ) (c : ℝ) (v : V) :
    GMS3.lap G (fun w => c + u w) v = GMS3.lap G u v := by
  unfold GMS3.lap
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- **The maximum principle for the (1.6) Dirichlet problem**: a discrete harmonic extension of boundary data `f`
with `|f| ≤ M` on `∂D` satisfies `|g| ≤ M` on `V(D)` (`D` bounded open, the graph connected). -/
theorem abs_le_of_isHarmonicExtension (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {f : ℂ → ℝ} {g : V → ℝ} (hg : IsHarmonicExtension G H.cell D f g)
    {M : ℝ} (hM : ∀ z ∈ frontier D, |f z| ≤ M) : ∀ v ∈ verticesMeeting H.cell D, |g v| ≤ M := by
  have : Infinite V := infinite_vertex H
  -- boundary vertices
  have hbd : ∀ v ∈ verticesMeeting H.cell D, v ∈ verticesMeeting H.cell (frontier D) → |g v| ≤ M := by
    intro v hv hvb
    rw [hg.1 v hv hvb]
    exact T15BH2.abs_sSup_image_le H hM hvb
  set K : Set V := {v | v ∈ verticesMeeting H.cell D ∧ v ∉ verticesMeeting H.cell (frontier D)} with hKdef
  have hKfin : K.Finite := (GMS3.finite_verticesMeeting H hDb).subset fun v hv => hv.1
  have hesc := exists_reachable_notMem G hconn hKfin
  -- outer neighbours of `K` are boundary vertices of `V(D)`
  have hout : ∀ v ∈ K, ∀ w, G.adj.Adj v w → w ∉ K → |g w| ≤ M := by
    intro v hv w hvw hwK
    have hsub : H.cell v ⊆ D := GMS3.cell_subset_of_inter_frontier_eq_empty H hDo hv.1
      (Set.not_nonempty_iff_eq_empty.mp hv.2)
    have hwD : w ∈ verticesMeeting H.cell D := by
      obtain ⟨c, hcv, hcw⟩ := H.inter_of_adj v w hvw
      exact ⟨c, hcw, hsub hcv⟩
    have hwb : w ∈ verticesMeeting H.cell (frontier D) := by
      by_contra h
      exact hwK ⟨hwD, h⟩
    exact hbd w hwD hwb
  have h1 := nonneg_of_lap_eq_zero G hKfin (g := fun w => M - g w)
    (fun v hv => by rw [lap_const_sub, hg.2 v hv.1 hv.2, neg_zero])
    (fun v hv w hvw hwK => by have := abs_le.mp (hout v hv w hvw hwK); linarith) hesc
  have h2 := nonneg_of_lap_eq_zero G hKfin (g := fun w => M + g w)
    (fun v hv => by rw [lap_const_add, hg.2 v hv.1 hv.2])
    (fun v hv w hvw hwK => by have := abs_le.mp (hout v hv w hvw hwK); linarith) hesc
  intro v hv
  by_cases hvb : v ∈ verticesMeeting H.cell (frontier D)
  · exact hbd v hv hvb
  · have a1 := h1 v ⟨hv, hvb⟩
    have a2 := h2 v ⟨hv, hvb⟩
    rw [abs_le]
    constructor <;> linarith

/-! ### Boundary values -/

/-- **Comparison of boundary values** ((3.32) from Hölder data, via): for boundary vertices `a, b` of
`V(D)` with cells of diameter `≤ s₁` and points `p ∈ H_a`, `q ∈ H_b`:
`|g(a) − g(b)| ≤ C_f (2 s₁ + |p − q|)^χ`. -/
theorem abs_sub_le_of_bdry {D : Set ℂ} {f : ℂ → ℝ} {g : V → ℝ} (hg : IsHarmonicExtension G H.cell D f g)
    {Cf χ s₁ : ℝ} (hCf : 0 ≤ Cf) (hχ : 0 < χ)
    (hf : ∀ z ∈ frontier D, ∀ w ∈ frontier D, |f z - f w| ≤ Cf * dist z w ^ χ)
    {a b : V} (ha : a ∈ verticesMeeting H.cell D) (hab : a ∈ verticesMeeting H.cell (frontier D))
    (hb : b ∈ verticesMeeting H.cell D) (hbb : b ∈ verticesMeeting H.cell (frontier D))
    (hsa : diam (H.cell a) ≤ s₁) (hsb : diam (H.cell b) ≤ s₁) {p q : ℂ} (hp : p ∈ H.cell a)
    (hq : q ∈ H.cell b) : |g a - g b| ≤ Cf * (2 * s₁ + dist p q) ^ χ := by
  rw [hg.1 a ha hab, hg.1 b hb hbb]
  refine (T15BH2.abs_sSup_image_sub_le H hCf hχ hf hab hbb hp hq).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hχ.le) hCf

/-! ### The interior vertex: cases 2 and 3 of DB5 Details (c) -/

/-- **Theorem 1.5, an interior vertex** (DB5 Details (c), cases 2–3). Under the good-event hypotheses of
`theorem15_deterministic`, let `x` be an interior vertex of `V(D)`, `y ∈ V(D)`, and `0 < τ < 1/2` with
`ε^β ∨ |pt x − pt y| ≤ τ⁴`. Then
`|g(x) − g(y)| ≤ A M_f (τ²)^{ξ₀} + 2 C_f (5τ)^χ + (1 + 2^{ξ₁}) C₁ M_f τ^{ξ₁}` (`ξ₀ = holderExponent p`,
`A = holderConst p`): by (3.30′) if `dist(pt x, ∂D) ≥ τ²`, by (3.31′) at scale `t = τ` otherwise. -/
theorem abs_sub_le_of_interior (hconn : G.adj.Connected) (pt : V → ℂ) (hpt : ∀ v, pt v ∈ H.cell v)
    {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {ε β q p C₁ ξ₁ : ℝ} (hε0 : 0 < ε) (hβq : ε ^ q ≤ ε ^ β) (hp : 0 < p) (hC₁ : 0 ≤ C₁) (hξ₁ : 0 < ξ₁)
    (hsmall : ∀ v ∈ verticesMeeting H.cell D, diam (H.cell v) ≤ ε ^ q)
    (h335 : ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z (2 * r) ⊆ D → ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    (h331 : BoundaryEstimate G H.cell pt D (ε ^ β) C₁ ξ₁)
    {f : ℂ → ℝ} {Cf χ Mf : ℝ} (hCf : 0 ≤ Cf) (hχ : 0 < χ) (hMf : 0 ≤ Mf)
    (hf : ∀ z ∈ frontier D, ∀ w ∈ frontier D, |f z - f w| ≤ Cf * dist z w ^ χ)
    (hfM : ∀ z ∈ frontier D, |f z| ≤ Mf) {g : V → ℝ} (hg : IsHarmonicExtension G H.cell D f g)
    {x y : V} (hx : x ∈ verticesMeeting H.cell D) (hxA : x ∉ verticesMeeting H.cell (frontier D))
    (hy : y ∈ verticesMeeting H.cell D) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2)
    (hδ : max (ε ^ β) (dist (pt x) (pt y)) ≤ τ ^ 4) :
    |g x - g y| ≤ holderConst p * Mf * (τ ^ 2) ^ holderExponent p + 2 * (Cf * (5 * τ) ^ χ) +
      (1 + 2 ^ ξ₁) * (C₁ * Mf * τ ^ ξ₁) := by
  have hgM := abs_le_of_isHarmonicExtension H hconn hDo hDb hg hfM
  have hgM' : ∀ v ∈ verticesMeeting H.cell D, |(fun w => -g w) v| ≤ Mf := fun v hv => by
    rw [abs_neg]; exact hgM v hv
  have hharm' : ∀ v ∈ verticesMeeting H.cell D, v ∉ verticesMeeting H.cell (frontier D) →
      GMS3.lap G (fun w => -g w) v = 0 := fun v hv hvb => by rw [lap_neg, hg.2 v hv hvb, neg_zero]
  set d := dist (pt x) (pt y) with hddef
  have hd : d ≤ τ ^ 4 := (le_max_right _ _).trans hδ
  have hsβ : ε ^ β ≤ τ ^ 4 := (le_max_left _ _).trans hδ
  have hsq : ε ^ q ≤ τ ^ 4 := hβq.trans hsβ
  have hd0 : 0 ≤ d := dist_nonneg
  have hτ4τ2 : τ ^ 4 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ0.le (by linarith) (by norm_num)
  have hτ2 : τ ^ 2 < τ := by nlinarith
  have hτ4 : 2 * τ ^ 4 < τ := by nlinarith [pow_pos hτ0 3]
  have hτ4' : τ ^ 4 ≤ τ := by nlinarith [pow_pos hτ0 3]
  have hτ2' : 2 * τ ^ 2 < τ := by nlinarith
  set A := holderConst p with hAdef
  set ξ₀ := holderExponent p with hξ₀def
  have hξ₀ : 0 < ξ₀ := holderExponent_pos hp
  have hA : 0 ≤ A := (holderConst_pos p).le
  set K5 := Cf * (5 * τ) ^ χ with hK5def
  have hK5 : 0 ≤ K5 := mul_nonneg hCf (Real.rpow_nonneg (by linarith) _)
  have hT1 : 0 ≤ A * Mf * (τ ^ 2) ^ ξ₀ := mul_nonneg (mul_nonneg hA hMf) (Real.rpow_nonneg (by positivity) _)
  have hT3 : 0 ≤ C₁ * Mf * τ ^ ξ₁ := mul_nonneg (mul_nonneg hC₁ hMf) (Real.rpow_nonneg hτ0.le _)
  have h2ξ : (1 : ℝ) ≤ 2 ^ ξ₁ := Real.one_le_rpow (by norm_num) hξ₁.le
  set R := infDist (pt x) (frontier D) with hRdef
  have hR0 : 0 ≤ R := infDist_nonneg
  have hDne : D.Nonempty := by
    obtain ⟨c, _, hc⟩ := hx
    exact ⟨c, hc⟩
  -- comparison of boundary values within distance `3τ`
  have hcmp : ∀ a ∈ verticesMeeting H.cell D, a ∈ verticesMeeting H.cell (frontier D) →
      ∀ b ∈ verticesMeeting H.cell D, b ∈ verticesMeeting H.cell (frontier D) →
      ∀ pa ∈ H.cell a, ∀ pb ∈ H.cell b, dist pa pb ≤ 3 * τ → |g a - g b| ≤ K5 := by
    intro a ha hab b hb hbb pa hpa pb hpb hdist
    refine (abs_sub_le_of_bdry H hg hCf hχ hf ha hab hb hbb (hsmall a ha) (hsmall b hb) hpa hpb).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hχ.le) hCf
  rcases le_or_gt (τ ^ 2) R with hRτ | hRτ
  · /- Case 2: `dist(pt x, ∂D) ≥ τ²`, the interior estimate (3.30′). -/
    have h := interior_estimate H hconn g hDo hp (Real.rpow_pos_of_pos hε0 β) (fun v hv hvb => hg.2 v hv hvb)
      hgM h335 hx hxA hy (hpt x) (hpt y)
    rw [← hAdef, ← hξ₀def, ← hRdef] at h
    have hpos : 0 < (τ ^ 2) ^ ξ₀ := Real.rpow_pos_of_pos (by positivity) _
    have h1 : max (ε ^ β) d ^ ξ₀ ≤ (τ ^ 2) ^ ξ₀ * (τ ^ 2) ^ ξ₀ := by
      rw [← Real.mul_rpow (by positivity) (by positivity), show τ ^ 2 * τ ^ 2 = τ ^ 4 by ring]
      exact Real.rpow_le_rpow (le_max_of_le_left (Real.rpow_nonneg hε0.le _)) hδ hξ₀.le
    have h2 : (τ ^ 2) ^ ξ₀ ≤ R ^ ξ₀ := Real.rpow_le_rpow (by positivity) hRτ hξ₀.le
    have h3 : |g x - g y| * (τ ^ 2) ^ ξ₀ ≤ (A * Mf * (τ ^ 2) ^ ξ₀) * (τ ^ 2) ^ ξ₀ := by
      calc |g x - g y| * (τ ^ 2) ^ ξ₀ ≤ |g x - g y| * R ^ ξ₀ :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ ≤ A * Mf * max (ε ^ β) d ^ ξ₀ := h
        _ ≤ A * Mf * ((τ ^ 2) ^ ξ₀ * (τ ^ 2) ^ ξ₀) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hA hMf)
        _ = (A * Mf * (τ ^ 2) ^ ξ₀) * (τ ^ 2) ^ ξ₀ := by ring
    have h4 := le_of_mul_le_mul_right h3 hpos
    have h5 : 0 ≤ (1 + 2 ^ ξ₁) * (C₁ * Mf * τ ^ ξ₁) := mul_nonneg (by positivity) hT3
    linarith [h4, h5, hK5]
  · /- Case 3: `dist(pt x, ∂D) < τ²`, the boundary estimate (3.31′) at scale `τ`. -/
    have ht : R < τ := lt_trans hRτ hτ2
    -- the error term of (3.31′) at `x`
    have herrx : C₁ * Mf * (max R (ε ^ β) / τ) ^ ξ₁ ≤ C₁ * Mf * τ ^ ξ₁ := by
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ hξ₁.le) (mul_nonneg hC₁ hMf)
      rw [div_le_iff₀ hτ0]
      have : max R (ε ^ β) ≤ τ ^ 2 := max_le hRτ.le (hsβ.trans hτ4τ2)
      nlinarith
    -- (3.31′) at `x`, for `g` and for `-g`
    have hup : ∀ c : ℝ, (∀ a ∈ verticesMeeting H.cell D,
        a ∈ verticesMeeting H.cell (frontier D ∩ ball (pt x) τ) → g a ≤ c) → -Mf ≤ c →
        g x ≤ c + C₁ * Mf * τ ^ ξ₁ := fun c hc hcM =>
      (h331 g Mf (fun v hv hvb => hg.2 v hv hvb) hgM x hx hxA τ ht c hc hcM).trans (by linarith)
    have hlo : ∀ c : ℝ, (∀ a ∈ verticesMeeting H.cell D,
        a ∈ verticesMeeting H.cell (frontier D ∩ ball (pt x) τ) → -g a ≤ c) → -Mf ≤ c →
        -g x ≤ c + C₁ * Mf * τ ^ ξ₁ := fun c hc hcM =>
      (h331 (fun w => -g w) Mf hharm' hgM' x hx hxA τ ht c hc hcM).trans (by linarith)
    by_cases hyA : y ∈ verticesMeeting H.cell (frontier D)
    · /- `y` is a boundary vertex: compare with `g(y)` directly. -/
      obtain ⟨qy, hqy, hqyD⟩ := hyA
      have hqyx : dist qy (pt x) < τ := by
        have h1 : dist qy (pt y) ≤ ε ^ q :=
          (dist_le_diam_of_mem (H.isCompact_cell y).isBounded hqy (hpt y)).trans (hsmall y hy)
        have h2 := dist_triangle qy (pt y) (pt x)
        rw [dist_comm (pt y) (pt x)] at h2
        linarith
      have hnear : ∀ a ∈ verticesMeeting H.cell D,
          a ∈ verticesMeeting H.cell (frontier D ∩ ball (pt x) τ) → |g a - g y| ≤ K5 := by
        intro a ha hab
        obtain ⟨pa, hpa, hpaD, hpab⟩ := hab
        refine hcmp a ha ⟨pa, hpa, hpaD⟩ y hy ⟨qy, hqy, hqyD⟩ pa hpa qy hqy ?_
        have h1 := dist_triangle pa (pt x) qy
        rw [mem_ball] at hpab
        rw [dist_comm (pt x) qy] at h1
        linarith
      have hgy := abs_le.mp (hgM y hy)
      have hu := hup (g y + K5) (fun a ha hab => by
        have := abs_le.mp (hnear a ha hab); linarith) (by linarith)
      have hl := hlo (-g y + K5) (fun a ha hab => by
        have := abs_le.mp (hnear a ha hab); linarith) (by linarith)
      have h2T3 : 0 ≤ 2 ^ ξ₁ * (C₁ * Mf * τ ^ ξ₁) := mul_nonneg (by positivity) hT3
      rw [abs_le]
      constructor
      · linarith [hu, hl, hT1, hT3, h2T3, hK5]
      · linarith [hu, hl, hT1, hT3, h2T3, hK5]
    · /- `y` is interior: (3.31′) at `y` too, comparing with a boundary vertex near `pt y`. -/
      have hRy : infDist (pt y) (frontier D) ≤ R + d := by
        have := infDist_le_infDist_add_dist (x := pt y) (y := pt x) (s := frontier D)
        rw [dist_comm] at this
        linarith
      have hty : infDist (pt y) (frontier D) < τ := by linarith
      have herry : C₁ * Mf * (max (infDist (pt y) (frontier D)) (ε ^ β) / τ) ^ ξ₁ ≤
          2 ^ ξ₁ * (C₁ * Mf * τ ^ ξ₁) := by
        have hm : max (infDist (pt y) (frontier D)) (ε ^ β) / τ ≤ 2 * τ := by
          rw [div_le_iff₀ hτ0]
          have : max (infDist (pt y) (frontier D)) (ε ^ β) ≤ 2 * τ ^ 2 :=
            max_le (by linarith) (by linarith)
          nlinarith
        calc C₁ * Mf * (max (infDist (pt y) (frontier D)) (ε ^ β) / τ) ^ ξ₁
            ≤ C₁ * Mf * (2 * τ) ^ ξ₁ :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hm hξ₁.le)
                (mul_nonneg hC₁ hMf)
          _ = 2 ^ ξ₁ * (C₁ * Mf * τ ^ ξ₁) := by
              rw [Real.mul_rpow (by norm_num) hτ0.le]; ring
      have hupy : ∀ c : ℝ, (∀ b ∈ verticesMeeting H.cell D,
          b ∈ verticesMeeting H.cell (frontier D ∩ ball (pt y) τ) → g b ≤ c) → -Mf ≤ c →
          g y ≤ c + 2 ^ ξ₁ * (C₁ * Mf * τ ^ ξ₁) := fun c hc hcM =>
        (h331 g Mf (fun v hv hvb => hg.2 v hv hvb) hgM y hy hyA τ hty c hc hcM).trans (by linarith)
      have hloy : ∀ c : ℝ, (∀ b ∈ verticesMeeting H.cell D,
          b ∈ verticesMeeting H.cell (frontier D ∩ ball (pt y) τ) → -g b ≤ c) → -Mf ≤ c →
          -g y ≤ c + 2 ^ ξ₁ * (C₁ * Mf * τ ^ ξ₁) := fun c hc hcM =>
        (h331 (fun w => -g w) Mf hharm' hgM' y hy hyA τ hty c hc hcM).trans (by linarith)
      obtain ⟨b₀, hb₀, q₀, hq₀, hq₀D, hq₀b⟩ := exists_bdry_vertex_near H hDb hDne hty
      rw [mem_ball] at hq₀b
      have hb₀b : b₀ ∈ verticesMeeting H.cell (frontier D) := ⟨q₀, hq₀, hq₀D⟩
      have hnearx : ∀ a ∈ verticesMeeting H.cell D,
          a ∈ verticesMeeting H.cell (frontier D ∩ ball (pt x) τ) → |g a - g b₀| ≤ K5 := by
        intro a ha hab
        obtain ⟨pa, hpa, hpaD, hpab⟩ := hab
        refine hcmp a ha ⟨pa, hpa, hpaD⟩ b₀ hb₀ hb₀b pa hpa q₀ hq₀ ?_
        rw [mem_ball] at hpab
        have h1 := dist_triangle4 pa (pt x) (pt y) q₀
        rw [dist_comm (pt y) q₀] at h1
        linarith
      have hneary : ∀ b ∈ verticesMeeting H.cell D,
          b ∈ verticesMeeting H.cell (frontier D ∩ ball (pt y) τ) → |g b - g b₀| ≤ K5 := by
        intro b hb hbb
        obtain ⟨pb, hpb, hpbD, hpbb⟩ := hbb
        refine hcmp b hb ⟨pb, hpb, hpbD⟩ b₀ hb₀ hb₀b pb hpb q₀ hq₀ ?_
        rw [mem_ball] at hpbb
        have h1 := dist_triangle pb (pt y) q₀
        rw [dist_comm (pt y) q₀] at h1
        linarith
      have hgb := abs_le.mp (hgM b₀ hb₀)
      have hu := hup (g b₀ + K5) (fun a ha hab => by
        have := abs_le.mp (hnearx a ha hab); linarith) (by linarith)
      have hl := hlo (-g b₀ + K5) (fun a ha hab => by
        have := abs_le.mp (hnearx a ha hab); linarith) (by linarith)
      have huy := hupy (g b₀ + K5) (fun b hb hbb => by
        have := abs_le.mp (hneary b hb hbb); linarith) (by linarith)
      have hly := hloy (-g b₀ + K5) (fun b hb hbb => by
        have := abs_le.mp (hneary b hb hbb); linarith) (by linarith)
      rw [abs_le]
      constructor
      · linarith [hu, hly, hT1, hT3, h2ξ]
      · linarith [huy, hl, hT1, hT3, h2ξ]

/-! ### The constants and the deterministic Theorem 1.5 -/

/-- The exponent of Theorem 1.5: `ξ = min(β ξ₀/2, β χ/4, β ξ₁/4, q χ)` with `ξ₀ = holderExponent p` (DB5 Details (c):
`min(β ξ₀/4, β χ/4, q χ)`, here with the exponents of (3.30′) and (3.31′) kept apart). -/
def theorem15Exponent (p ξ₁ β q χ : ℝ) : ℝ :=
  min (min (β * holderExponent p / 2) (β * χ / 4)) (min (β * ξ₁ / 4) (q * χ))

/-- The threshold `w₀ = (1/16)^{1/β}` below which the main cases of Theorem 1.5 apply. -/
def theorem15Threshold (β : ℝ) : ℝ := (1 / 16) ^ (1 / β)

/-- The main-case constant `3^χ C_f + A M_f + 2·5^χ C_f + (1 + 2^{ξ₁}) C₁ M_f` of Theorem 1.5. -/
def theorem15MainConst (p C₁ ξ₁ χ Cf Mf : ℝ) : ℝ :=
  3 ^ χ * Cf + holderConst p * Mf + 2 * (5 ^ χ * Cf) + (1 + 2 ^ ξ₁) * (C₁ * Mf)

/-- The constant `A₀` of Theorem 1.5. -/
def theorem15Const (p C₁ ξ₁ β q χ Cf Mf : ℝ) : ℝ :=
  max (theorem15MainConst p C₁ ξ₁ χ Cf Mf)
    (2 * Mf / theorem15Threshold β ^ theorem15Exponent p ξ₁ β q χ)

theorem theorem15Exponent_pos {p ξ₁ β q χ : ℝ} (hp : 0 < p) (hξ₁ : 0 < ξ₁) (hβ : 0 < β) (hq : 0 < q)
    (hχ : 0 < χ) : 0 < theorem15Exponent p ξ₁ β q χ := by
  have h0 := holderExponent_pos hp
  unfold theorem15Exponent
  refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_) <;> positivity

/-- **[18] Theorem 1.5, deterministic on the good event** (`[18]`, (1.9); proof: DB5 Details (c) from
(3.30′), (3.31′) and the boundary data). Let `H` be a cellular embedding of a connected graph with marked points
`pt v ∈ H_v`, `D` bounded open, `0 < ε ≤ 1` and `0 < β ≤ q ≤ 1`, and assume on this environment:
* the cells of `V(D)` have diameter `≤ ε^q` ([18] Lemma 2.7);
* (3.35) with probability `p > 0` at every `(z, r)` with `r ≥ ε^β`, `B_{2r}(z) ⊆ D` (`DiscEvent`; T15A);
* (3.31′) with floor `ε^β` and constants `C₁ ≥ 0`, `ξ₁ > 0` (`BoundaryEstimate`; T15C).
Let `f` be `χ`-Hölder on `∂D` with constant `C_f ≥ 0` and `|f| ≤ M_f` there, and `g` a discrete harmonic extension
of the (1.6) data of `f`. Then for all `x, y ∈ V(D)`:
`|g(x) − g(y)| ≤ A₀ (ε ∨ |pt x − pt y|)^ξ`, `A₀ = theorem15Const`, `ξ = theorem15Exponent`. -/
theorem theorem15_deterministic (hconn : G.adj.Connected) (pt : V → ℂ) (hpt : ∀ v, pt v ∈ H.cell v)
    {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {ε β q p C₁ ξ₁ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hβq : β ≤ q) (hq1 : q ≤ 1)
    (hp : 0 < p) (hC₁ : 0 ≤ C₁) (hξ₁ : 0 < ξ₁)
    (hsmall : ∀ v ∈ verticesMeeting H.cell D, diam (H.cell v) ≤ ε ^ q)
    (h335 : ∀ (z : ℂ) (r : ℝ), ε ^ β ≤ r → ball z (2 * r) ⊆ D → ∀ v ∈ verticesMeeting H.cell (ball z r),
      ENNReal.ofReal p ≤ G.walkLaw v {ω | DiscEvent G H.cell z r (G.vertexPath ω)})
    (h331 : BoundaryEstimate G H.cell pt D (ε ^ β) C₁ ξ₁)
    {f : ℂ → ℝ} {Cf χ Mf : ℝ} (hCf : 0 ≤ Cf) (hχ : 0 < χ) (hMf : 0 ≤ Mf)
    (hf : ∀ z ∈ frontier D, ∀ w ∈ frontier D, |f z - f w| ≤ Cf * dist z w ^ χ)
    (hfM : ∀ z ∈ frontier D, |f z| ≤ Mf) {g : V → ℝ} (hg : IsHarmonicExtension G H.cell D f g) :
    ∀ x ∈ verticesMeeting H.cell D, ∀ y ∈ verticesMeeting H.cell D,
      |g x - g y| ≤ theorem15Const p C₁ ξ₁ β q χ Cf Mf *
        max ε (dist (pt x) (pt y)) ^ theorem15Exponent p ξ₁ β q χ := by
  intro x hx y hy
  have hq : 0 < q := lt_of_lt_of_le hβ hβq
  have hβ1 : β ≤ 1 := hβq.trans hq1
  set ξ := theorem15Exponent p ξ₁ β q χ with hξdef
  have hξ : 0 < ξ := theorem15Exponent_pos hp hξ₁ hβ hq hχ
  set A₀ := theorem15Const p C₁ ξ₁ β q χ Cf Mf with hA₀def
  set K := theorem15MainConst p C₁ ξ₁ χ Cf Mf with hKdef
  set w := max ε (dist (pt x) (pt y)) with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le hε0 (le_max_left _ _)
  set w₀ := theorem15Threshold β with hw₀def
  have hw₀0 : 0 < w₀ := Real.rpow_pos_of_pos (by norm_num) _
  have hw₀1 : w₀ ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hgM := abs_le_of_isHarmonicExtension H hconn hDo hDb hg hfM
  have hdiff : |g x - g y| ≤ 2 * Mf := by
    have h1 := abs_le.mp (hgM x hx)
    have h2 := abs_le.mp (hgM y hy)
    rw [abs_le]
    constructor <;> linarith
  have hKA : K ≤ A₀ := le_max_left _ _
  have hwξ0 : 0 ≤ w ^ ξ := Real.rpow_nonneg hw0.le _
  rcases le_or_gt w₀ w with hww | hww
  · -- the trivial range `w ≥ w₀`
    have h1 : w₀ ^ ξ ≤ w ^ ξ := Real.rpow_le_rpow hw₀0.le hww hξ.le
    have h2 : 0 < w₀ ^ ξ := Real.rpow_pos_of_pos hw₀0 ξ
    have h3 : 2 * Mf / w₀ ^ ξ ≤ A₀ := le_max_right _ _
    calc |g x - g y| ≤ 2 * Mf := hdiff
      _ = (2 * Mf / w₀ ^ ξ) * w₀ ^ ξ := by field_simp
      _ ≤ (2 * Mf / w₀ ^ ξ) * w ^ ξ := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ A₀ * w ^ ξ := mul_le_mul_of_nonneg_right h3 hwξ0
  · -- the main range `w < w₀ ≤ 1`
    have hw1 : w < 1 := lt_of_lt_of_le hww hw₀1
    set τ := w ^ (β / 4) with hτdef
    have hτ0 : 0 < τ := Real.rpow_pos_of_pos hw0 _
    have hτ4 : τ ^ 4 = w ^ β := by
      rw [hτdef, ← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
      norm_num
    have hτ1 : τ < 1 / 2 := by
      have h1 : τ < w₀ ^ (β / 4) := Real.rpow_lt_rpow hw0.le hww (by positivity)
      have h2 : w₀ ^ (β / 4) = 1 / 2 := by
        rw [hw₀def, theorem15Threshold, ← Real.rpow_mul (by norm_num),
          show (1 / β) * (β / 4) = (1 / 4 : ℝ) by field_simp,
          show (1 / 16 : ℝ) = (1 / 2) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      linarith
    have hdw : dist (pt x) (pt y) ≤ w ^ β :=
      calc dist (pt x) (pt y) ≤ w := le_max_right _ _
        _ = w ^ (1 : ℝ) := (Real.rpow_one w).symm
        _ ≤ w ^ β := Real.rpow_le_rpow_of_exponent_ge hw0 hw1.le hβ1
    have hδ : max (ε ^ β) (dist (pt x) (pt y)) ≤ τ ^ 4 := by
      rw [hτ4]
      exact max_le (Real.rpow_le_rpow hε0.le (le_max_left _ _) hβ.le) hdw
    have hεq : ε ^ q ≤ ε ^ β := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 hβq
    have hconv : ∀ e : ℝ, ξ ≤ e → w ^ e ≤ w ^ ξ := fun e he =>
      Real.rpow_le_rpow_of_exponent_ge hw0 hw1.le he
    -- the three powers of `τ`
    have hP1 : (τ ^ 2) ^ holderExponent p ≤ w ^ ξ := by
      have : (τ ^ 2) ^ holderExponent p = w ^ (β * holderExponent p / 2) := by
        rw [hτdef, ← Real.rpow_natCast, ← Real.rpow_mul hw0.le, ← Real.rpow_mul hw0.le]
        congr 1
        push_cast
        ring
      rw [this]
      exact hconv _ ((min_le_left _ _).trans (min_le_left _ _))
    have hP2 : (5 * τ) ^ χ ≤ 5 ^ χ * w ^ ξ := by
      rw [Real.mul_rpow (by norm_num) hτ0.le]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : τ ^ χ = w ^ (β * χ / 4) := by
        rw [hτdef, ← Real.rpow_mul hw0.le]
        congr 1
        ring
      rw [this]
      exact hconv _ ((min_le_left _ _).trans (min_le_right _ _))
    have hP3 : τ ^ ξ₁ ≤ w ^ ξ := by
      have : τ ^ ξ₁ = w ^ (β * ξ₁ / 4) := by
        rw [hτdef, ← Real.rpow_mul hw0.le]
        congr 1
        ring
      rw [this]
      exact hconv _ ((min_le_right _ _).trans (min_le_left _ _))
    have hK0 : 0 ≤ 3 ^ χ * Cf := mul_nonneg (by positivity) hCf
    have hA0 : 0 ≤ holderConst p * Mf := mul_nonneg (holderConst_pos p).le hMf
    have hB0 : 0 ≤ 5 ^ χ * Cf := mul_nonneg (by positivity) hCf
    have hC0 : 0 ≤ (1 + 2 ^ ξ₁) * (C₁ * Mf) := mul_nonneg (by positivity) (mul_nonneg hC₁ hMf)
    -- the bound of an interior vertex, in terms of `w`
    have hint : holderConst p * Mf * (τ ^ 2) ^ holderExponent p + 2 * (Cf * (5 * τ) ^ χ) +
        (1 + 2 ^ ξ₁) * (C₁ * Mf * τ ^ ξ₁) ≤ A₀ * w ^ ξ := by
      have e1 : holderConst p * Mf * (τ ^ 2) ^ holderExponent p ≤ holderConst p * Mf * w ^ ξ :=
        mul_le_mul_of_nonneg_left hP1 hA0
      have e2 : 2 * (Cf * (5 * τ) ^ χ) ≤ 2 * (5 ^ χ * Cf) * w ^ ξ := by
        have h := mul_le_mul_of_nonneg_left hP2 hCf
        calc 2 * (Cf * (5 * τ) ^ χ) ≤ 2 * (Cf * (5 ^ χ * w ^ ξ)) := by linarith only [h]
          _ = 2 * (5 ^ χ * Cf) * w ^ ξ := by ring
      have e3 : (1 + 2 ^ ξ₁) * (C₁ * Mf * τ ^ ξ₁) ≤ (1 + 2 ^ ξ₁) * (C₁ * Mf) * w ^ ξ := by
        have h := mul_le_mul_of_nonneg_left hP3 (mul_nonneg hC₁ hMf)
        have h2 : (0 : ℝ) ≤ 1 + 2 ^ ξ₁ := by positivity
        calc (1 + 2 ^ ξ₁) * (C₁ * Mf * τ ^ ξ₁) ≤ (1 + 2 ^ ξ₁) * (C₁ * Mf * w ^ ξ) :=
              mul_le_mul_of_nonneg_left h h2
          _ = (1 + 2 ^ ξ₁) * (C₁ * Mf) * w ^ ξ := by ring
      have e4 : 0 ≤ 3 ^ χ * Cf * w ^ ξ := mul_nonneg hK0 hwξ0
      have eK : K * w ^ ξ = 3 ^ χ * Cf * w ^ ξ + holderConst p * Mf * w ^ ξ +
          2 * (5 ^ χ * Cf) * w ^ ξ + (1 + 2 ^ ξ₁) * (C₁ * Mf) * w ^ ξ := by
        rw [hKdef, theorem15MainConst]; ring
      have eA := mul_le_mul_of_nonneg_right hKA hwξ0
      linarith only [e1, e2, e3, e4, eK, eA]
    by_cases hxA : x ∈ verticesMeeting H.cell (frontier D)
    · by_cases hyA : y ∈ verticesMeeting H.cell (frontier D)
      · -- case 1: two boundary vertices
        have h := abs_sub_le_of_bdry H hg hCf hχ hf hx hxA hy hyA (hsmall x hx) (hsmall y hy) (hpt x) (hpt y)
        have h1 : 2 * ε ^ q + dist (pt x) (pt y) ≤ 3 * w ^ q := by
          have a1 : ε ^ q ≤ w ^ q := Real.rpow_le_rpow hε0.le (le_max_left _ _) hq.le
          have a2 : dist (pt x) (pt y) ≤ w ^ q :=
            calc dist (pt x) (pt y) ≤ w := le_max_right _ _
              _ = w ^ (1 : ℝ) := (Real.rpow_one w).symm
              _ ≤ w ^ q := Real.rpow_le_rpow_of_exponent_ge hw0 hw1.le hq1
          linarith
        have h2 : (2 * ε ^ q + dist (pt x) (pt y)) ^ χ ≤ 3 ^ χ * w ^ ξ := by
          calc (2 * ε ^ q + dist (pt x) (pt y)) ^ χ ≤ (3 * w ^ q) ^ χ :=
                Real.rpow_le_rpow (by positivity) h1 hχ.le
            _ = 3 ^ χ * w ^ (q * χ) := by
                rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hw0.le]
            _ ≤ 3 ^ χ * w ^ ξ :=
                mul_le_mul_of_nonneg_left (hconv _ ((min_le_right _ _).trans (min_le_right _ _)))
                  (by positivity)
        have h3 : |g x - g y| ≤ 3 ^ χ * Cf * w ^ ξ := by
          calc |g x - g y| ≤ Cf * (2 * ε ^ q + dist (pt x) (pt y)) ^ χ := h
            _ ≤ Cf * (3 ^ χ * w ^ ξ) := mul_le_mul_of_nonneg_left h2 hCf
            _ = 3 ^ χ * Cf * w ^ ξ := by ring
        have h4 : 3 ^ χ * Cf * w ^ ξ ≤ K * w ^ ξ := by
          refine mul_le_mul_of_nonneg_right ?_ hwξ0
          rw [hKdef, theorem15MainConst]
          linarith only [hA0, hB0, hC0]
        linarith only [h3, h4, mul_le_mul_of_nonneg_right hKA hwξ0]
      · -- case 4: `x` boundary, `y` interior — exchange the roles
        have hδ' : max (ε ^ β) (dist (pt y) (pt x)) ≤ τ ^ 4 := by rwa [dist_comm]
        have h := abs_sub_le_of_interior H hconn pt hpt hDo hDb hε0 (hεq) hp hC₁ hξ₁ hsmall h335 h331
          hCf hχ hMf hf hfM hg hy hyA hx hτ0 hτ1 hδ'
        rw [abs_sub_comm] at h
        linarith only [h, hint]
    · -- cases 2–3: `x` interior
      have h := abs_sub_le_of_interior H hconn pt hpt hDo hDb hε0 hεq hp hC₁ hξ₁ hsmall h335 h331
        hCf hχ hMf hf hfM hg hx hxA hy hτ0 hτ1 hδ
      linarith only [h, hint]

end MatedCRTHarmonic.GMSMain.T15B
