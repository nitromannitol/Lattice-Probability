/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanLimitAux4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanLimitAux2
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordMeanLimitAux3

/-!
# Node `M46` (`Draft.RecordMeanLimit`), auxiliary part 4: small-excess configurations are
constrained configurations

For fixed `n ≥ 1`, `k` and small `δ`, every configuration `c ∈ smallFamily (16 ^ n) δ k` has
exactly `M = 16 ^ n` edges, all but the last pointing forwards, and
`c = constrCfg M δ (fOf n p) (p0Of M p) (p1Of M p)` for its parameter vector `p = prm M δ c`,
which lies in a fixed box (`prm_spec`).
-/

noncomputable section

open Filter Topology Set Real

namespace LQGDimension.RML

open Blueprint.Draft LFPPRecords

/-- The parameter vector of a configuration `([x, y], z)` at scale `δ`: the node values
`Im rot(z_i) / (δ R)` (`i < M`, `R = |y - x|`), and the offsets `x / δ`, `(y - 1) / δ`. -/
def prm (M : ℕ) (δ : ℝ) (c : Config) : Fin (M + 4) → ℝ := fun i =>
  if i.val < M then (rot (c.1.getD 0 0) (c.1.getD 1 0) (c.2.getD i.val 0)).im /
      (δ * ‖c.1.getD 1 0 - c.1.getD 0 0‖)
  else if i.val = M then (c.1.getD 0 0 / (δ : ℂ)).re
  else if i.val = M + 1 then (c.1.getD 0 0 / (δ : ℂ)).im
  else if i.val = M + 2 then ((c.1.getD 1 0 - 1) / (δ : ℂ)).re
  else ((c.1.getD 1 0 - 1) / (δ : ℂ)).im

lemma getD_map_range (Z : ℕ → ℂ) {m i : ℕ} (hi : i < m) : ((List.range m).map Z).getD i 0 = Z i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

lemma prm_lt (M : ℕ) (δ : ℝ) (x y : ℂ) (L : List ℂ) (i : Fin (M + 4)) (h : i.val < M) :
    prm M δ ([x, y], L) i = (rot x y (L.getD i.val 0)).im / (δ * ‖y - x‖) := by
  unfold prm
  rw [if_pos h]
  rfl

lemma prm_ge (M : ℕ) (δ : ℝ) (x y : ℂ) (L : List ℂ) (i : Fin (M + 4)) (h : ¬ i.val < M) :
    |prm M δ ([x, y], L) i| ≤ max (‖x / (δ : ℂ)‖) (‖(y - 1) / (δ : ℂ)‖) := by
  unfold prm
  rw [if_neg h]
  have g0 : ([x, y] : List ℂ).getD 0 0 = x := rfl
  have g1 : ([x, y] : List ℂ).getD 1 0 = y := rfl
  simp only [g0, g1]
  split_ifs
  · exact (Complex.abs_re_le_norm _).trans (le_max_left _ _)
  · exact (Complex.abs_im_le_norm _).trans (le_max_left _ _)
  · exact (Complex.abs_re_le_norm _).trans (le_max_right _ _)
  · exact (Complex.abs_im_le_norm _).trans (le_max_right _ _)

lemma p0Of_prm (M : ℕ) (δ : ℝ) (x y : ℂ) (L : List ℂ) :
    p0Of M (prm M δ ([x, y], L)) = x / (δ : ℂ) := by
  have h1 : prm M δ ([x, y], L) ⟨M, by omega⟩ = (x / (δ : ℂ)).re := by
    unfold prm
    rw [if_neg (lt_irrefl M), if_pos rfl]
    rfl
  have h2 : prm M δ ([x, y], L) ⟨M + 1, by omega⟩ = (x / (δ : ℂ)).im := by
    unfold prm
    rw [if_neg (by dsimp only; omega), if_neg (by dsimp only; omega), if_pos rfl]
    rfl
  unfold p0Of
  rw [h1, h2]
  exact Complex.re_add_im _

lemma p1Of_prm (M : ℕ) (δ : ℝ) (x y : ℂ) (L : List ℂ) :
    p1Of M (prm M δ ([x, y], L)) = (y - 1) / (δ : ℂ) := by
  have h1 : prm M δ ([x, y], L) ⟨M + 2, by omega⟩ = ((y - 1) / (δ : ℂ)).re := by
    unfold prm
    rw [if_neg (by dsimp only; omega), if_neg (by dsimp only; omega), if_neg (by dsimp only; omega), if_pos rfl]
    rfl
  have h2 : prm M δ ([x, y], L) ⟨M + 3, by omega⟩ = ((y - 1) / (δ : ℂ)).im := by
    unfold prm
    rw [if_neg (by dsimp only; omega), if_neg (by dsimp only; omega), if_neg (by dsimp only; omega), if_neg (by dsimp only; omega)]
    rfl
  unfold p1Of
  rw [h1, h2]
  exact Complex.re_add_im _

lemma norm_div_delta_le {z : ℂ} {δ ρ : ℝ} (hδ : 0 < δ) (hz : ‖z‖ ≤ ρ * δ) :
    ‖z / (δ : ℂ)‖ ≤ ρ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, div_le_iff₀ hδ]
  exact hz

lemma cellRad_le {M : ℕ} (hM : 16 ≤ M) : cellRad M ≤ 1 / 64 := by
  have hMr : (16 : ℝ) ≤ M := by exact_mod_cast hM
  unfold cellRad
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma cellRad_nonneg (M : ℕ) : 0 ≤ cellRad M := by
  unfold cellRad; positivity

/-- **Small-excess configurations are constrained configurations.** -/
theorem prm_spec {n k : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hk1 : ((k : ℝ) + 1) * δ ^ 2 ≤ 1)
    (hk2 : 2 * (((k : ℝ) + 1) * δ ^ 2) < 1 / (2 * ((16 ^ n : ℕ) : ℝ)))
    {c : Config} (hc : c ∈ smallFamily (16 ^ n) δ k) :
    (∀ i, |prm (16 ^ n) δ c i| ≤ 2 * ((16 ^ n : ℕ) : ℝ) * ((k : ℝ) + 1) + 1) ∧
    ‖p0Of (16 ^ n) (prm (16 ^ n) δ c)‖ ≤ cellRad (16 ^ n) ∧
    ‖p1Of (16 ^ n) (prm (16 ^ n) δ c)‖ ≤ cellRad (16 ^ n) ∧
    constrCfg (16 ^ n) δ (fOf n (prm (16 ^ n) δ c)) (p0Of (16 ^ n) (prm (16 ^ n) δ c))
      (p1Of (16 ^ n) (prm (16 ^ n) δ c)) = c := by
  obtain ⟨x, y, N, Z, rfl, hZ0, hZN, hx, hy, hreg, hl1, hl2, hlog⟩ := smallFamily_vertices hc
  have hM16 : 16 ≤ 16 ^ n := Nat.le_self_pow (by omega) 16
  have hMr : (16 : ℝ) ≤ ((16 ^ n : ℕ) : ℝ) := by exact_mod_cast hM16
  have hMpos : (0 : ℝ) < ((16 ^ n : ℕ) : ℝ) := by linarith
  have hcell := cellRad_le hM16
  have hcell0 := cellRad_nonneg (16 ^ n)
  -- the chord
  set R := ‖y - x‖ with hRdef
  have hR : 1 / 2 ≤ R := by
    have e : (1 : ℂ) = (y - x) - (y - 1) + x := by ring
    have h1 : ‖(1 : ℂ)‖ ≤ ‖y - x‖ + ‖y - 1‖ + ‖x‖ := by
      calc ‖(1 : ℂ)‖ = ‖(y - x) - (y - 1) + x‖ := by rw [← e]
        _ ≤ ‖(y - x) - (y - 1)‖ + ‖x‖ := norm_add_le _ _
        _ ≤ ‖y - x‖ + ‖y - 1‖ + ‖x‖ := by gcongr; exact norm_sub_le _ _
    rw [norm_one] at h1
    have h2 : cellRad (16 ^ n) * δ ≤ 1 / 64 := by nlinarith
    linarith
  have hRpos : 0 < R := by linarith
  -- the length
  set S := ∑ j ∈ Finset.range (N + 1), ‖Z (j + 1) - Z j‖ with hSdef
  have hSR : R ≤ S := by
    calc R = ‖∑ j ∈ Finset.range (N + 1), (Z (j + 1) - Z j)‖ := by
          rw [Finset.sum_range_sub, hZN, hZ0]
      _ ≤ S := norm_sum_le _ _
  set t := ((k : ℝ) + 1) * δ ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hexc : S - R < 2 * t * R := by
    have h1 : S / R < Real.exp t :=
      (Real.log_lt_iff_lt_exp (div_pos (hRpos.trans_le hSR) hRpos)).1 hlog
    have h2 : Real.exp t ≤ 1 + 2 * t := by
      have := Real.abs_exp_sub_one_le (x := t) (by rw [abs_of_nonneg ht0]; exact hk1)
      rw [abs_of_nonneg ht0] at this
      linarith [le_abs_self (Real.exp t - 1)]
    rw [div_lt_iff₀ hRpos] at h1
    nlinarith
  -- exactly `M` edges
  have hsplit : S = N * (R / ((16 ^ n : ℕ) : ℝ)) + ‖Z (N + 1) - Z N‖ := by
    rw [hSdef, Finset.sum_range_succ,
      Finset.sum_congr rfl (fun j hj => hreg j (Finset.mem_range.1 hj)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hNM : N + 1 = 16 ^ n := by
    have hlow : 2 * ((16 ^ n : ℕ) : ℝ) ≤ 2 * N + 3 := by
      have h' : R ≤ N * (R / ((16 ^ n : ℕ) : ℝ)) + 3 * R / (2 * ((16 ^ n : ℕ) : ℝ)) := by
        linarith
      have e : N * (R / ((16 ^ n : ℕ) : ℝ)) + 3 * R / (2 * ((16 ^ n : ℕ) : ℝ)) =
          R * (2 * N + 3) / (2 * ((16 ^ n : ℕ) : ℝ)) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)] at h'
      nlinarith
    have hup : (N : ℝ) < ((16 ^ n : ℕ) : ℝ) := by
      have h3 : 2 * t * R < R / (2 * ((16 ^ n : ℕ) : ℝ)) := by
        calc 2 * t * R < 1 / (2 * ((16 ^ n : ℕ) : ℝ)) * R := mul_lt_mul_of_pos_right hk2 hRpos
          _ = R / (2 * ((16 ^ n : ℕ) : ℝ)) := by ring
      have h4 : N * (R / ((16 ^ n : ℕ) : ℝ)) < R := by linarith
      have e : N * (R / ((16 ^ n : ℕ) : ℝ)) = R * N / ((16 ^ n : ℕ) : ℝ) := by ring
      rw [e, div_lt_iff₀ hMpos] at h4
      nlinarith
    have h1 : 2 * 16 ^ n ≤ 2 * N + 3 := by exact_mod_cast hlow
    have h2 : N < 16 ^ n := by exact_mod_cast hup
    omega
  -- rewrite everything in terms of `M = 16 ^ n` edges
  have hlist : (List.range (N + 2)).map Z = (List.range (16 ^ n + 1)).map Z := by rw [← hNM]
  have hZM : Z (16 ^ n) = y := by rw [← hNM]; exact hZN
  have hreg' : ∀ j, j + 1 < 16 ^ n → ‖Z (j + 1) - Z j‖ = R / ((16 ^ n : ℕ) : ℝ) :=
    fun j hj => hreg j (by omega)
  have hS' : (∑ j ∈ Finset.range (16 ^ n), ‖Z (j + 1) - Z j‖) - R ≤ (2 * t) * R := by
    rw [← hNM]; linarith
  have hη : 2 * t < 1 / ((16 ^ n : ℕ) : ℝ) := by
    refine hk2.trans_le ?_
    gcongr
    linarith
  obtain ⟨hfwd, him⟩ := geom_core (M := 16 ^ n) (by omega) hZ0 hZM hRpos hreg' hS' hη
  rw [hlist]
  set L := (List.range (16 ^ n + 1)).map Z with hL
  have hLZ : ∀ i ≤ 16 ^ n, L.getD i 0 = Z i := fun i hi => getD_map_range Z (by omega)
  -- transversal bounds
  have hW : ∀ i ≤ 16 ^ n, rot x y (Z i) = ∑ j ∈ Finset.range i, (rot x y (Z (j + 1)) - rot x y (Z j)) := by
    intro i _
    rw [Finset.sum_range_sub (fun j => rot x y (Z j)) i, hZ0, rot_self, sub_zero]
  have himb : ∀ j, j + 1 < 16 ^ n →
      |(rot x y (Z (j + 1)) - rot x y (Z j)).im| ≤ 2 * R * ((k : ℝ) + 1) * δ := by
    intro j hj
    apply abs_le_of_sq_le_sq _ (by positivity)
    have h1 := him j hj
    have hk : ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    calc (rot x y (Z (j + 1)) - rot x y (Z j)).im ^ 2 ≤ 2 * R ^ 2 * (2 * t) := h1
      _ = 4 * R ^ 2 * δ ^ 2 * ((k : ℝ) + 1) := by rw [ht]; ring
      _ ≤ 4 * R ^ 2 * δ ^ 2 * ((k : ℝ) + 1) ^ 2 := by gcongr
      _ = (2 * R * ((k : ℝ) + 1) * δ) ^ 2 := by ring
  have hnodeb : ∀ i < 16 ^ n,
      |(rot x y (Z i)).im / (δ * R)| ≤ 2 * ((16 ^ n : ℕ) : ℝ) * ((k : ℝ) + 1) := by
    intro i hi
    rw [abs_div, abs_of_pos (mul_pos hδ0 hRpos), div_le_iff₀ (mul_pos hδ0 hRpos),
      hW i hi.le, Complex.im_sum]
    calc |∑ j ∈ Finset.range i, (rot x y (Z (j + 1)) - rot x y (Z j)).im|
        ≤ ∑ j ∈ Finset.range i, |(rot x y (Z (j + 1)) - rot x y (Z j)).im| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range i, 2 * R * ((k : ℝ) + 1) * δ := by
          refine Finset.sum_le_sum fun j hj => himb j ?_
          rw [Finset.mem_range] at hj
          omega
      _ = i * (2 * R * ((k : ℝ) + 1) * δ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((16 ^ n : ℕ) : ℝ) * (2 * R * ((k : ℝ) + 1) * δ) := by
          gcongr
      _ = 2 * ((16 ^ n : ℕ) : ℝ) * ((k : ℝ) + 1) * (δ * R) := by ring
  -- the offsets
  have hp0 := p0Of_prm (16 ^ n) δ x y L
  have hp1 := p1Of_prm (16 ^ n) δ x y L
  have hx' : ‖x / (δ : ℂ)‖ ≤ cellRad (16 ^ n) := norm_div_delta_le hδ0 hx
  have hy' : ‖(y - 1) / (δ : ℂ)‖ ≤ cellRad (16 ^ n) := norm_div_delta_le hδ0 hy
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ0.ne'
  refine ⟨fun i => ?_, by rw [hp0]; exact hx', by rw [hp1]; exact hy', ?_⟩
  · by_cases hi : i.val < 16 ^ n
    · rw [prm_lt _ _ _ _ _ _ hi, hLZ _ hi.le]
      linarith [hnodeb i hi]
    · refine (prm_ge _ _ _ _ _ _ hi).trans ?_
      have : (0 : ℝ) ≤ 2 * ((16 ^ n : ℕ) : ℝ) * ((k : ℝ) + 1) := by positivity
      refine max_le ?_ ?_ <;> linarith
  · -- the node values of the profile
    have hnode : ∀ j ≤ 16 ^ n, nodeV (16 ^ n) (prm (16 ^ n) δ ([x, y], L)) j =
        (rot x y (Z j)).im / (δ * R) := by
      intro j hj
      unfold nodeV
      split_ifs with h
      · rw [prm_lt _ _ _ _ _ _ h.2, hLZ _ hj]
      · rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, hZ0, rot_self, Complex.zero_im, zero_div]
        · have : j = 16 ^ n := by omega
          rw [this, hZM, rot_end hRpos, Complex.ofReal_im, zero_div]
    have hf : ∀ j : ℕ, j ≤ 16 ^ n → fOf n (prm (16 ^ n) δ ([x, y], L)) ((j : ℝ) / ((16 ^ n : ℕ) : ℝ)) =
        (rot x y (Z j)).im / (δ * R) := fun j hj => (fOf_node n _ j).trans (hnode j hj)
    have hpoly := constrPoly_eq_of_nodes (M := 16 ^ n) (by omega) hδ0 hZ0 hZM hRpos hreg' hfwd hf
    unfold constrCfg
    rw [hp0, hp1, mul_div_cancel₀ _ hδc, mul_div_cancel₀ _ hδc, add_sub_cancel, hpoly]

end LQGDimension.RML
