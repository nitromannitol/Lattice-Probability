/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Red at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Sep

/-!
# GM Lemma 5.8: reduction of `L58Geom` to the construction of `U_r^{x,y}` (task P2-M2L58)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Steps 2–3 (l. 3079–3126).

* `geom58_perZ`: the per-`u` clause of `L58Geom` (GM (5.25), l. 3119, and the condition-2
  transfer, l. 3120–3126) for one `z = z_k`, from `u`-independent geometric data: `U ∖ V` is
  covered by an `x`-side `X` (GM's `W_k(x)`) and a `y`-side `Y` (`W_k(y)`), both missing
  `B_{1.7ρr}(z)`, `s`-separated, joined to `z ∓ 2ρr` in `U ∖ B_{1.7ρr}(z)`, and every point of
  `V` within distance `< s` of `X` (resp. `Y`) has its component of `V ∖ B_{1.7ρr}(z)` `s`-near
  that of `z − 2ρr` (resp. `z + 2ρr`) (the junction, decision D69). Since `O_u ⊆ B_{20ε₁ρr}(u) ⊆
  B_{1.7ρr}(z)` for `|u − z| < 3ρr/2`, this gives the hypotheses of `sepFrom_transfer`.
* `L58Junction`: the junction data, used in `l58Geom` (`Geom58T5`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology

namespace LQGMetric.GM
open Blueprint

lemma nearComp_subset_ball (V : Set ℂ) (δ : ℝ) (u : ℂ) : nearComp V δ u ⊆ ball u δ :=
  (connectedComponentIn_subset _ _).trans inter_subset_right

/-- **GM (5.25) and l. 3120–3126** for one `z = z_k`, from `u`-independent data; see the module
docstring -/
theorem geom58_perZ {U V X Y : Set ℂ} {z x y : ℂ} {R s : ℝ} (hs : 0 < s) (hsR : 20 * s ≤ R / 5)
    (hVU : V ⊆ U) (hUV : U ⊆ V ∪ X ∪ Y)
    (hXB : Disjoint X (ball z (17 / 10 * R))) (hYB : Disjoint Y (ball z (17 / 10 * R)))
    (ha : z - 2 * (R : ℂ) ∈ V) (hb : z + 2 * (R : ℂ) ∈ V)
    (hxU : x ∈ U) (hxX : x ∈ X) (hyU : y ∈ U) (hyY : y ∈ Y)
    (hX : ∀ w ∈ U, w ∈ X → w ∈ connectedComponentIn (U \ ball z (17 / 10 * R)) (z - 2 * (R : ℂ)))
    (hY : ∀ w ∈ U, w ∈ Y → w ∈ connectedComponentIn (U \ ball z (17 / 10 * R)) (z + 2 * (R : ℂ)))
    (hXY : ∀ p ∈ X, ∀ q ∈ Y, s ≤ dist p q)
    (hAX : ∀ p ∈ X, ∀ q ∈ V, dist p q < s →
      CompNear (V \ ball z (17 / 10 * R)) s q (z - 2 * (R : ℂ)))
    (hAY : ∀ p ∈ Y, ∀ q ∈ V, dist p q < s →
      CompNear (V \ ball z (17 / 10 * R)) s q (z + 2 * (R : ℂ)))
    (u : ℂ) (hu : u ∈ ball z (3 / 2 * R)) :
    nearComp U (20 * s) u = nearComp V (20 * s) u ∧
    (SepFrom V (nearComp V (20 * s) u) (z - 2 * (R : ℂ)) s →
      SepFrom U (nearComp U (20 * s) u) x s) ∧
    (SepFrom V (nearComp V (20 * s) u) (z + 2 * (R : ℂ)) s →
      SepFrom U (nearComp U (20 * s) u) y s) ∧
    (SepFrom V (nearComp V (20 * s) u) (z - 2 * (R : ℂ)) s →
      z + 2 * (R : ℂ) ∉ connectedComponentIn (V \ nearComp V (20 * s) u) (z - 2 * (R : ℂ)) →
      y ∉ connectedComponentIn (U \ nearComp U (20 * s) u) x) ∧
    (SepFrom V (nearComp V (20 * s) u) (z + 2 * (R : ℂ)) s →
      z - 2 * (R : ℂ) ∉ connectedComponentIn (V \ nearComp V (20 * s) u) (z + 2 * (R : ℂ)) →
      x ∉ connectedComponentIn (U \ nearComp U (20 * s) u) y) := by
  have hR : 0 < R := by linarith
  set B := ball z (17 / 10 * R) with hBdef
  have hball : ball u (20 * s) ⊆ B := by
    intro w hw
    rw [mem_ball] at hw hu ⊢
    linarith [dist_triangle w u z]
  have hloc : U ∩ ball u (20 * s) = V ∩ ball u (20 * s) := by
    apply le_antisymm
    · rintro w ⟨hwU, hw⟩
      refine ⟨?_, hw⟩
      rcases hUV hwU with (h | h) | h
      · exact h
      · exact absurd (hball hw) (Set.disjoint_left.1 hXB h)
      · exact absurd (hball hw) (Set.disjoint_left.1 hYB h)
    · exact inter_subset_inter_left _ hVU
  have hEq : nearComp U (20 * s) u = nearComp V (20 * s) u := by
    unfold nearComp; rw [hloc]
  set O := nearComp V (20 * s) u with hOdef
  have hO : O ⊆ B := (nearComp_subset_ball V _ u).trans hball
  have hdiff : ∀ W : Set ℂ, W \ B ⊆ W \ O := fun W w hw => ⟨hw.1, fun h => hw.2 (hO h)⟩
  have hnotB : ∀ c : ℂ, ‖c‖ = 2 * R → z + c ∉ B := by
    intro c hc h
    rw [hBdef, mem_ball, dist_eq_norm, add_sub_cancel_left, hc] at h
    linarith
  have haB : z - 2 * (R : ℂ) ∉ B := by
    rw [sub_eq_add_neg]
    refine hnotB _ ?_
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]; norm_num
  have hbB : z + 2 * (R : ℂ) ∉ B := by
    refine hnotB _ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]; norm_num
  have hUV' : U ⊆ V ∪ Y ∪ X := by
    intro w hw
    rcases hUV hw with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have hA1 := connectedComponentIn_mono _ (hdiff U) (hX x hxU hxX)
  have hA2 : ∀ w ∈ U \ O, w ∈ X → w ∈ connectedComponentIn (U \ O) (z - 2 * (R : ℂ)) :=
    fun w hw hwX => connectedComponentIn_mono _ (hdiff U) (hX w hw.1 hwX)
  have hA3 : ∀ w ∈ U \ O, w ∈ Y → w ∈ connectedComponentIn (U \ O) (z + 2 * (R : ℂ)) :=
    fun w hw hwY => connectedComponentIn_mono _ (hdiff U) (hY w hw.1 hwY)
  have hA4 : ∀ p ∈ X, ∀ q ∈ V \ O, dist p q < s → CompNear (V \ O) s q (z - 2 * (R : ℂ)) :=
    fun p hp q hq hd => (hAX p hp q hq.1 hd).mono (hdiff V)
  have hA5 : ∀ p ∈ Y, ∀ q ∈ V \ O, dist p q < s → CompNear (V \ O) s q (z + 2 * (R : ℂ)) :=
    fun p hp q hq hd => (hAY p hp q hq.1 hd).mono (hdiff V)
  have hB1 := connectedComponentIn_mono _ (hdiff U) (hY y hyU hyY)
  have hXY' : ∀ p ∈ Y, ∀ q ∈ X, s ≤ dist p q := fun p hp q hq => by
    rw [dist_comm]; exact hXY q hq p hp
  have haO : z - 2 * (R : ℂ) ∈ V \ O := ⟨ha, fun h => haB (hO h)⟩
  have hbO : z + 2 * (R : ℂ) ∈ V \ O := ⟨hb, fun h => hbB (hO h)⟩
  refine ⟨hEq, ?_, ?_, ?_, ?_⟩
  · rw [hEq]
    exact sepFrom_transfer hs hVU hUV haO hbO hA1 hA2 hA3 hXY hA4 hA5
  · rw [hEq]
    exact sepFrom_transfer hs hVU hUV' hbO haO hB1 hA3 hA2 hXY' hA5 hA4
  · rw [hEq]
    exact fun hsep hbC => discFrom_transfer hs hVU hUV haO hbO hA1 hA2 hA3 hXY hA4 hA5 hsep hbC hyY
  · rw [hEq]
    exact fun hsep hbC => discFrom_transfer hs hVU hUV' hbO haO hB1 hA3 hA2 hXY' hA5 hA4 hsep hbC hxX

/-- the `u`-independent junction data of GM Step 2 for `U = U_r^{x,y}`, `V = V_{ρr}(z_k)`
(`R = ρr`, grid side `s = ε₁ρr`): the `x`-side `X` (GM's `W_k(x)`) and the `y`-side `Y`
(`W_k(y)`); see `geom58_perZ` -/
def L58Junction (U V : Set ℂ) (z x y : ℂ) (R s : ℝ) : Prop :=
  ∃ X Y : Set ℂ, U ⊆ V ∪ X ∪ Y ∧
    Disjoint X (ball z (17 / 10 * R)) ∧ Disjoint Y (ball z (17 / 10 * R)) ∧ x ∈ X ∧ y ∈ Y ∧
    (∀ w ∈ U, w ∈ X → w ∈ connectedComponentIn (U \ ball z (17 / 10 * R)) (z - 2 * (R : ℂ))) ∧
    (∀ w ∈ U, w ∈ Y → w ∈ connectedComponentIn (U \ ball z (17 / 10 * R)) (z + 2 * (R : ℂ))) ∧
    (∀ p ∈ X, ∀ q ∈ Y, s ≤ dist p q) ∧
    (∀ p ∈ X, ∀ q ∈ V, dist p q < s →
      CompNear (V \ ball z (17 / 10 * R)) s q (z - 2 * (R : ℂ))) ∧
    (∀ p ∈ Y, ∀ q ∈ V, dist p q < s →
      CompNear (V \ ball z (17 / 10 * R)) s q (z + 2 * (R : ℂ)))

end LQGMetric.GM
