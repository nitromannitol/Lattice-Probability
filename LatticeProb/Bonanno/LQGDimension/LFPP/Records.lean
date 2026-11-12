/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Records at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux4

/-!
# Node `R44`: chain records and the count (4.4)

`recordAssignment : Blueprint.Draft.RecordAssignment`.

For `M = 16^n`, `0 < δ < 1` and `0 < ε < 1`, the record system `recSys n δ ε`
(`LQGDimension/LFPP/RecordsAux4.lean`) is finite and satisfies `RecordSystem.Good` with the
universal constants `C = Ccount = 1.25 · 10¹¹`, `D = 19` (`recSys_good`).

Along the ancestry `u_j = v.take j` of a leaf `v` of a well-formed partition tree, the record
of `u_j` is `(location of u_j, (k_{u_j}, [A_{u_j} > 1]), location of u_{j+1})`, where the
location of a chord is its dyadic scale exponent and the grid cells (side `η δ 2^σ`) of its
endpoints.  The configuration is
* `([x_u, y_u], Q_u)` (chord and child polygon) when `A_u ≤ 1`, with `cfgVal` *equal* to
  `δ^{-1/2} G_u - k_u` because `polyComb` weights edges by `R_v / S_u`;
* `([x_u, y_u], [x_v, y_v])` for an adverse child `v` maximizing `H_u - H_v` when `A_u > 1`.
Both lie in the image of the normalized local family under the record's similarity.
-/

noncomputable section

open Real
open scoped Classical

namespace LQGDimension.LFPPRecords

open Blueprint.Draft

variable {γ : ℝ → ℂ} {T : CutTree}

/-- Location of the chord of node `u`. -/
def nodeLoc (n : ℕ) (δ : ℝ) (T : CutTree) (γ : ℝ → ℂ) (u : List ℕ) : Loc :=
  locOf n δ (T.x γ u) (T.y γ u)

/-- Large-excess flag of node `u`. -/
def lgOf (T : CutTree) (γ : ℝ → ℂ) (u : List ℕ) : Bool := if T.A γ u ≤ 1 then false else true

/-- Record data of node `u` whose followed child is `w`. -/
def recOf (n : ℕ) (δ : ℝ) (T : CutTree) (γ : ℝ → ℂ) (u w : List ℕ) : RecData :=
  (nodeLoc n δ T γ u, (T.kbin γ δ u, lgOf T γ u), nodeLoc n δ T γ w)

theorem A_le_of_lgOf {u : List ℕ} (h : lgOf T γ u = false) : T.A γ u ≤ 1 := by
  unfold lgOf at h; split_ifs at h with h'; exact h'

theorem not_A_le_of_lgOf {u : List ℕ} (h : lgOf T γ u = true) : ¬ T.A γ u ≤ 1 := by
  unfold lgOf at h; split_ifs at h with h'; exact h'

/-- Locations of chords of length in `[ε/(2M), 1]` with endpoints of norm `≤ 4` lie in the box. -/
theorem locOf_mem_box {n : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {x y : ℂ}
    (hR : 0 < ‖y - x‖) (hR1 : ε / (2 * (Mn n : ℝ)) ≤ ‖y - x‖) (hR2 : ‖y - x‖ ≤ 1)
    (hx : ‖x‖ ≤ 4) (hy : ‖y‖ ≤ 4) : locOf n δ x y ∈ locBox n δ ε := by
  have hM := Mn_pos n
  have hσ1 : sigMin n ε ≤ scl x y := Int.log_mono_right (by positivity) hR1
  have hσ2 : scl x y ≤ 0 := by
    have := Int.log_mono_right (b := 2) hR hR2
    rwa [Int.log_one_right] at this
  have hs := side_pos hδ n (scl x y)
  have hsmin := side_pos hδ n (sigMin n ε)
  have hmono := side_mono hδ.le n hσ1
  have hB : 4 / side n δ (scl x y) + 1 ≤ (boxB n δ ε : ℝ) := by
    unfold boxB; push_cast
    have : 4 / side n δ (scl x y) ≤ 4 / side n δ (sigMin n ε) :=
      div_le_div_of_nonneg_left (by norm_num) hsmin hmono
    have := Int.le_ceil (4 / side n δ (sigMin n ε))
    linarith
  obtain ⟨hx1, hx2⟩ := gridIdx_mem_Icc hs hx hB
  obtain ⟨hy1, hy2⟩ := gridIdx_mem_Icc hs hy hB
  simp only [locBox, locOf, sqBox, Finset.mem_product, Finset.mem_Icc] at hx1 hx2 hy1 hy2 ⊢
  exact ⟨⟨hσ1, hσ2⟩, ⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩

theorem M_two' {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 16 ^ n := by
  have : 16 ≤ 16 ^ n := by
    calc 16 = 16 ^ 1 := by norm_num
      _ ≤ 16 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

section node

variable {n : ℕ} {δ ε : ℝ} (hn : 1 ≤ n) (hδ : 0 < δ) (hδ1 : δ < 1)
  (hT : T.WF γ (16 ^ n) ε) {u : List ℕ} (hu : u ∈ T.nodes) (hm : 0 < T.nch u)
  (hR : 0 < T.R γ u)
include hn hδ hδ1 hT hu hm hR

omit hδ1 in
/-- Vertices of the child polygon are close to straight positions when `A_u ≤ 1`. -/
theorem small_vertices (hA : T.A γ u ≤ 1) {i' : ℕ} (hi' : i' ≤ T.nch u) :
    ∃ j ≤ 3 * Mn n, ‖vf T γ u i' - (T.x γ u + ((j : ℝ) / (Mn n : ℝ)) • (T.y γ u - T.x γ u))‖ ≤
      6 * (Mn n : ℝ) * ‖T.y γ u - T.x γ u‖ * δ * √((T.kbin γ δ u : ℝ) + 1) := by
  have hM := Mn_pos n
  have hM2 := M_two' hn
  have hm3 : T.nch u ≤ 3 * Mn n := nch_le hT hu hm hR hM2 hA
  have hRd : ‖T.y γ u - T.x γ u‖ = T.R γ u := rfl
  have hbound : 0 ≤ 6 * (Mn n : ℝ) * ‖T.y γ u - T.x γ u‖ * δ * √((T.kbin γ δ u : ℝ) + 1) := by
    positivity
  rcases lt_or_eq_of_le hi' with hlt | heq
  · refine ⟨i', by omega, ?_⟩
    have hdev := vertex_dev (f := vf T γ u) (m := T.nch u) (M := Mn n) (by positivity)
      (by rw [vf_chord hT hu hm]; exact hR)
      (fun i hi => by
        rw [vf_edge hT hu hm (by omega), vf_chord hT hu hm]
        exact hT.regular u hu i hi)
      (fun i hi => by
        rw [vf_edge hT hu hm hi, vf_chord hT hu hm]
        exact R_child_le hT hM2 hu hi) hlt
    rw [vf_chord hT hu hm, vf_sum hT hu hm, vf_zero hT hu hm, vf_nch] at hdev
    have e : vf T γ u i' - (T.x γ u + ((i' : ℝ) / (Mn n : ℝ)) • (T.y γ u - T.x γ u)) =
        vf T γ u i' - T.x γ u - ((i' : ℝ) / (Mn n : ℝ)) • (T.y γ u - T.x γ u) := by abel
    rw [e]
    refine hdev.trans ?_
    -- `√(2R(S - R)) ≤ 2Rδ√(k+1)`
    have hA0 := A_nonneg hT hu hm hR
    obtain ⟨_, hk2⟩ := kbin_small (δ := δ) hδ hA0 hA
    have hSR := S_sub_R_le hT hu hm hR hA
    have hsq : √(2 * T.R γ u * (T.S γ u - T.R γ u)) ≤
        2 * T.R γ u * δ * √((T.kbin γ δ u : ℝ) + 1) := by
      have hk0 : (0 : ℝ) ≤ (T.kbin γ δ u : ℝ) + 1 := by positivity
      have e2 : (2 * T.R γ u * δ * √((T.kbin γ δ u : ℝ) + 1)) ^ 2 =
          4 * T.R γ u ^ 2 * (((T.kbin γ δ u : ℝ) + 1) * δ ^ 2) := by
        rw [mul_pow, Real.sq_sqrt hk0]; ring
      rw [← Real.sqrt_sq (show 0 ≤ 2 * T.R γ u * δ * √((T.kbin γ δ u : ℝ) + 1) by positivity),
        e2]
      apply Real.sqrt_le_sqrt
      have h1 := mul_le_mul_of_nonneg_left hSR (by positivity : (0 : ℝ) ≤ 2 * T.R γ u)
      have h2 := mul_le_mul_of_nonneg_left hk2.le (by positivity : (0 : ℝ) ≤ 4 * T.R γ u ^ 2)
      nlinarith
    have hi3 : (i' : ℝ) ≤ 3 * (Mn n : ℝ) := by exact_mod_cast (show i' ≤ 3 * Mn n by omega)
    rw [hRd]
    calc (i' : ℝ) * √(2 * T.R γ u * (T.S γ u - T.R γ u))
        ≤ (3 * (Mn n : ℝ)) * (2 * T.R γ u * δ * √((T.kbin γ δ u : ℝ) + 1)) := by
          gcongr
      _ = 6 * (Mn n : ℝ) * T.R γ u * δ * √((T.kbin γ δ u : ℝ) + 1) := by ring
  · refine ⟨Mn n, by omega, ?_⟩
    rw [heq, vf_nch, div_self hM.ne', one_smul, add_sub_cancel, sub_self, norm_zero]
    exact hbound

/-- The configuration of an internal node lies in the record family and dominates the local
variable (with equality). -/
theorem node_config (φ : ℂ → ℝ) :
    ∃ c, c ∈ cfgMap (locAlpha n δ (nodeLoc n δ T γ u), refX n δ (nodeLoc n δ T γ u)) ''
        localFamily (16 ^ n) δ (lgOf T γ u) (T.kbin γ δ u) ∧
      δ ^ (-(1 / 2 : ℝ)) * T.G γ φ u - T.kbin γ δ u ≤ cfgVal φ δ (T.kbin γ δ u) c := by
  have hM := Mn_pos n
  have hM2 := M_two' hn
  have hα := alpha_ne_zero (n := n) hn hδ hδ1 (x := T.x γ u) (y := T.y γ u) hR
  have hcx := cell_x (n := n) hn hδ hδ1 (x := T.x γ u) (y := T.y γ u) hR
  have hcy := cell_y (n := n) hn hδ hδ1 (x := T.x γ u) (y := T.y γ u) hR
  by_cases hA : T.A γ u ≤ 1
  · -- small excess: chord and child polygon
    have hlg : lgOf T γ u = false := by simp [lgOf, hA]
    rw [hlg]
    simp only [localFamily, Bool.false_eq_true, ↓reduceIte]
    refine ⟨([T.x γ u, T.y γ u], childPoly T γ u), ?_, ?_⟩
    · have hA0 := A_nonneg hT hu hm hR
      obtain ⟨hk1, hk2⟩ := kbin_small (δ := δ) hδ hA0 hA
      have hlogeq : Real.log ((∑ i ∈ Finset.range (T.nch u), ‖vf T γ u (i + 1) - vf T γ u i‖) /
          ‖vf T γ u (T.nch u) - vf T γ u 0‖) = T.A γ u := by
        rw [vf_sum hT hu hm, vf_chord hT hu hm]; rfl
      have hlast : ‖vf T γ u (T.nch u) - vf T γ u (T.nch u - 1)‖ = T.R γ (u ++ [T.nch u - 1]) := by
        have := vf_edge hT hu hm (i := T.nch u - 1) (by omega)
        rwa [show T.nch u - 1 + 1 = T.nch u by omega] at this
      have hsc := hT.scale u hu (T.nch u - 1) (by omega)
      have hmem := mem_image_smallFamily (M := 16 ^ n) (δ := δ) (k := T.kbin γ δ u)
        (s := (locAlpha n δ (nodeLoc n δ T γ u), refX n δ (nodeLoc n δ T γ u))) hα
        (f := vf T γ u) (m := T.nch u) hm (nch_le hT hu hm hR hM2 hA)
        (by rw [vf_zero hT hu hm]; exact hcx) (by rw [vf_nch]; exact hcy)
        (fun i hi => by
          rw [vf_edge hT hu hm (by omega), vf_chord hT hu hm]
          exact hT.regular u hu i hi)
        (by rw [hlast, vf_chord hT hu hm]; exact hsc.1)
        (by rw [hlast, vf_chord hT hu hm]; exact hsc.2)
        (by rw [hlogeq]; exact hk1) (by rw [hlogeq]; exact hk2) (by rw [hlogeq]; exact hA)
      rw [vf_zero hT hu hm, vf_nch] at hmem
      exact hmem
    · rw [G_small hT hu hm hR φ hA]
      exact le_rfl
  · -- large excess: chord and adverse child chord
    have hlg : lgOf T γ u = true := by simp [lgOf, hA]
    rw [hlg]
    simp only [localFamily, ↓reduceIte]
    obtain ⟨i, hi, hG⟩ := G_large hT hu hm (by positivity) hR φ hA
    refine ⟨([T.x γ u, T.y γ u], [T.x γ (u ++ [i]), T.y γ (u ++ [i])]), ?_, ?_⟩
    · obtain ⟨hb1, hb2⟩ := child_ball hT hu hi
      obtain ⟨hs1, hs2⟩ := hT.scale u hu i hi
      exact mem_image_largeFamily hα hcx hcy hb1 hb2 hs1 hs2
    · rw [hG]
      exact le_rfl

/-- The record of an internal node and its followed child is a valid record. -/
theorem rec_mem (hε : 0 < ε) (hγ0 : γ 0 = 0) (hγ1 : γ 1 = 1) (ht0 : 0 ≤ T.t₀ u)
    (ht1 : T.t₁ u ≤ 1) (hR1 : T.R γ u ≤ 1) (hRε : ε < T.R γ u) {i : ℕ} (hi : i < T.nch u) :
    recOf n δ T γ u (u ++ [i]) ∈ recSet n δ ε := by
  have hM := Mn_pos n
  have hM2 := M_two' hn
  have hw := hT.child_mem u hu i hi
  obtain ⟨hs1, hs2⟩ := hT.scale u hu i hi
  have hRw : 0 < T.R γ (u ++ [i]) := by
    have : 0 < T.R γ u / (2 * ((16 ^ n : ℕ) : ℝ)) := div_pos hR (by positivity)
    linarith
  have hRwu := R_child_le hT hM2 hu hi
  have htu := hT.time_le u hu
  have htw := hT.time_le _ hw
  have hw0 := child_t0_ge hT hu i hi
  have hw1 := child_t1_le hT hu i hi
  have hxu : ‖T.x γ u‖ ≤ 4 := norm_path_le_four hT hγ0 hγ1 ht0 (by linarith)
  have hyu : ‖T.y γ u‖ ≤ 4 := norm_path_le_four hT hγ0 hγ1 (by linarith) ht1
  have hxw : ‖T.x γ (u ++ [i])‖ ≤ 4 := norm_path_le_four hT hγ0 hγ1 (by linarith) (by linarith)
  have hyw : ‖T.y γ (u ++ [i])‖ ≤ 4 := norm_path_le_four hT hγ0 hγ1 (by linarith) (by linarith)
  have hεM : ε / (2 * (Mn n : ℝ)) ≤ T.R γ u := by
    have : ε / (2 * (Mn n : ℝ)) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ 2 * (Mn n : ℝ) := by have := Mn_ge_sixteen hn; linarith
      nlinarith
    linarith
  have hεMw : ε / (2 * (Mn n : ℝ)) ≤ T.R γ (u ++ [i]) := by
    have : ε / (2 * (Mn n : ℝ)) ≤ T.R γ u / (2 * (Mn n : ℝ)) :=
      div_le_div_of_nonneg_right hRε.le (by positivity)
    exact this.trans hs1
  have hbu := locOf_mem_box (n := n) hδ hε (x := T.x γ u) (y := T.y γ u) hR hεM hR1 hxu hyu
  have hbw := locOf_mem_box (n := n) hδ hε (x := T.x γ (u ++ [i])) (y := T.y γ (u ++ [i]))
    hRw hεMw (hRwu.trans hR1) hxw hyw
  have hσ1 : scl (T.x γ (u ++ [i])) (T.y γ (u ++ [i])) ≤ scl (T.x γ u) (T.y γ u) :=
    scl_child_le hR hRw hRwu
  have hσ2 : scl (T.x γ u) (T.y γ u) ≤ scl (T.x γ (u ++ [i])) (T.y γ (u ++ [i])) + (4 * n + 2) :=
    scl_le_child (n := n) hR hRw hs1
  unfold recSet
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · simp only [recOf, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    refine ⟨hbu, ?_, hbw⟩
    have := kbin_le (T := T) (γ := γ) (δ := δ) u
    unfold kmax; omega
  · refine ⟨cells_ne (x := T.x γ u) (y := T.y γ u) hn hδ hδ1 hR, hσ1, hσ2, ?_, ?_⟩
    · intro hlg
      have hA := not_A_le_of_lgOf hlg
      obtain ⟨hb1, hb2⟩ := child_ball hT hu hi
      refine ⟨kbin_large hA, ?_, ?_⟩
      · exact large_pos (x := T.x γ u) (y := T.y γ u) hn hδ hδ1 hR hσ1 hb1
      · exact large_pos (x := T.x γ u) (y := T.y γ u) hn hδ hδ1 hR hσ1 hb2
    · intro hlg
      have hA := A_le_of_lgOf hlg
      refine ⟨?_, ?_⟩
      · have hz := small_vertices hn hδ hT hu hm hR hA (i' := i) hi.le
        rw [vf_of_lt hi] at hz
        exact small_pos (x := T.x γ u) (y := T.y γ u) hn hδ hδ1 hR hσ1 hz
      · have hz := small_vertices hn hδ hT hu hm hR hA (i' := i + 1) hi
        rw [vf_succ hT hu hm hi] at hz
        exact small_pos (x := T.x γ u) (y := T.y γ u) hn hδ hδ1 hR hσ1 hz

omit hm in
/-- Scale separation along a chain. -/
theorem alpha_node_child {i : ℕ} (hi : i < T.nch u) :
    ‖locAlpha n δ (nodeLoc n δ T γ (u ++ [i]))‖ ≤
      4 / ((16 ^ n : ℕ) : ℝ) * ‖locAlpha n δ (nodeLoc n δ T γ u)‖ := by
  obtain ⟨hs1, hs2⟩ := hT.scale u hu i hi
  have hRw : 0 < T.R γ (u ++ [i]) := by
    have : 0 < T.R γ u / (2 * ((16 ^ n : ℕ) : ℝ)) := div_pos hR (by positivity)
    linarith
  exact alpha_child hn hδ hδ1 hR hRw hs2

end node

/-! ## Node `R44` -/

theorem recordAssignment : Blueprint.Draft.RecordAssignment := by
  refine ⟨Ccount, 19, fun n hn => ⟨1, one_pos, fun δ hδ => ⟨1, one_pos, fun ε hε => ?_⟩⟩⟩
  obtain ⟨hδ0, hδ1⟩ := hδ
  obtain ⟨hε0, hε1⟩ := hε
  refine ⟨recSys n δ ε, recSys_good hn hδ0, ?_⟩
  intro γ hγ T hT φ _ v hv
  obtain ⟨hvn, hv0⟩ := Finset.mem_filter.mp hv
  have hM2 := M_two' hn
  have hγ0 := hγ.source
  have hγ1 := hγ.target
  -- facts along the ancestry of `v`
  have hanc : ∀ j < v.length, v.take j ∈ T.nodes ∧ 0 ≤ T.t₀ (v.take j) ∧
      T.t₁ (v.take j) ≤ 1 ∧ T.R γ (v.take j) ≤ 1 ∧
      ∃ i < T.nch (v.take j), v.take (j + 1) = v.take j ++ [i] := by
    intro j hj
    obtain ⟨h1, h2, h3, h4⟩ := chain_props hT hM2 hvn j hj.le
    obtain ⟨_, i, hi, he⟩ := wf_take hT v.length v hvn rfl j hj
    rw [root_R hT hγ0 hγ1] at h4
    exact ⟨h1, h2, h3, h4, i, hi, he⟩
  have hint : ∀ j < v.length, ε < T.R γ (v.take j) := by
    intro j hj
    obtain ⟨h1, -, -, -, i, hi, -⟩ := hanc j hj
    exact (hT.internal_iff _ h1).mp (by omega)
  have hlen : 0 < v.length := by
    rcases Nat.eq_zero_or_pos v.length with h | h
    · exfalso
      have hv' : v = [] := List.eq_nil_of_length_eq_zero h
      have := (hT.internal_iff v hvn).mpr (by
        rw [hv', root_R hT hγ0 hγ1]; exact hε1)
      omega
    · exact h
  have hmem : ∀ j < v.length, recOf n δ T γ (v.take j) (v.take (j + 1)) ∈ recSet n δ ε := by
    intro j hj
    obtain ⟨h1, h2, h3, h4, i, hi, he⟩ := hanc j hj
    rw [he]
    exact rec_mem hn hδ0 hδ1 hT h1 (by omega) (lt_trans hε0 (hint j hj)) hε0 hγ0 hγ1 h2 h3 h4
      (hint j hj) hi
  have hcfg : ∀ j < v.length, ∃ c, c ∈ cfgMap (locAlpha n δ (nodeLoc n δ T γ (v.take j)),
        refX n δ (nodeLoc n δ T γ (v.take j))) ''
        localFamily (16 ^ n) δ (lgOf T γ (v.take j)) (T.kbin γ δ (v.take j)) ∧
      δ ^ (-(1 / 2 : ℝ)) * T.G γ φ (v.take j) - T.kbin γ δ (v.take j) ≤
        cfgVal φ δ (T.kbin γ δ (v.take j)) c := by
    intro j hj
    obtain ⟨h1, -, -, -, i, hi, -⟩ := hanc j hj
    exact node_config hn hδ0 hδ1 hT h1 (by omega) (lt_trans hε0 (hint j hj)) φ
  choose! cf hcf using hcfg
  let r : ℕ → (recSys n δ ε).Rec := fun j =>
    if h : j < v.length then ⟨recOf n δ T γ (v.take j) (v.take (j + 1)), hmem j h⟩
    else ⟨recOf n δ T γ (v.take 0) (v.take 1), hmem 0 hlen⟩
  have hr : ∀ j (h : j < v.length),
      r j = ⟨recOf n δ T γ (v.take j) (v.take (j + 1)), hmem j h⟩ := fun j h => dif_pos h
  refine ⟨r, cf, ⟨?_, ?_⟩, ?_⟩
  · intro _
    rw [hr 0 hlen]
    show nodeLoc n δ T γ (v.take 0) = rootLoc n δ
    simp only [List.take_zero, nodeLoc, rootLoc]
    rw [root_x hT hγ0, root_y hT hγ1]
  · intro i hi
    rw [hr i (by omega), hr (i + 1) hi]
    refine ⟨rfl, ?_⟩
    obtain ⟨h1, -, -, -, a, ha, he⟩ := hanc i (by omega)
    show ‖locAlpha n δ (nodeLoc n δ T γ (v.take (i + 1)))‖ ≤
      4 / ((16 ^ n : ℕ) : ℝ) * ‖locAlpha n δ (nodeLoc n δ T γ (v.take i))‖
    rw [he]
    exact alpha_node_child hn hδ0 hδ1 hT h1 (lt_trans hε0 (hint i (by omega))) ha
  · intro j hj
    rw [hr j hj]
    exact ⟨(hcf j hj).1, rfl, (hcf j hj).2⟩

end LQGDimension.LFPPRecords
