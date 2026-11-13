/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Paths.Polygon at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Paths.DistOn

/-!
# Polygonal paths and polygonal approximation of piecewise `C¹` paths

Packet P-X1, target T3 (audit HA5, Details D1(a); source App. A.1, "piecewise `C¹` … the same
infimum").

* `polygonPath p N`: the polygonal path through `p 0, p 1, …, p N`, built as an iterated
  concatenation of segments; it is a piecewise `C¹` path from `p 0` to `p N`
  (`isPcwC1Path_polygonPath`), lies in `V` when its edges do (`mapsTo_polygonPath`), and its LFPP
  length is the sum of the segment lengths (`lfppLength_polygonPath`, continuous field).
* **Polygonal approximation** (`exists_polygonPath_le`): for an open `V`, a continuous field and a
  piecewise `C¹` path `γ ⊆ V` from `x` to `y`, and any dense set `S`, for every `η > 0` there is a
  polygonal path inside `V` from `x` to `y`, all of whose interior vertices lie in `S`, with
  LFPP length at most `lfppLength γ + η`.

Proof of the approximation (HA5 D1(a), written out for the parametrized length).  Let `K = γ[0,1]`,
`K' = K_r ⊆ V` a closed `r`-neighbourhood (compact), `w = e^{ζ φ}`, `W = max_{K'} w`,
`ℓ = ∫₀¹ |γ'|`, `ϖ = η/(4(ℓ+1))`, `ρ` a modulus of uniform continuity of `w` on `K'` for `ϖ`,
`ρ₁ = min ρ r`, `δ` a modulus of uniform continuity of `γ` on `[0,1]` for `ρ₁/4`, `N > 1/δ`,
`t_i = i/N`, `δ' = min(ρ₁/8, η/(4N(W+ϖ+1)))`, and vertices `p_0 = x`, `p_N = y`, `p_i ∈ S` with
`|p_i - γ(t_i)| < δ'`.  On the `i`-th edge every point is within `3δ' + ρ₁/4 < ρ₁` of `γ(t_i)`, so
the edge lies in `K' ⊆ V` and `w ≤ w(γ t_i) + ϖ` there, while `w(γ u) ≥ w(γ t_i) - ϖ` for
`u ∈ [t_i, t_{i+1}]`.  With `ℓ_i = ∫_{t_i}^{t_{i+1}} |γ'| ≥ |γ(t_{i+1}) - γ(t_i)|` (chord ≤
arclength) and `|p_{i+1} - p_i| ≤ ℓ_i + 2δ'`:
`cost(edge i) ≤ (w(γ t_i) + ϖ)(ℓ_i + 2δ') ≤ ∫_{t_i}^{t_{i+1}} w(γ)|γ'| + 2ϖ ℓ_i + 2δ'(W + ϖ)`
(`lfppLength_segPath_le_piece`).  Summing:
`cost ≤ lfppLength γ + 2ϖℓ + 2Nδ'(W+ϖ) ≤ lfppLength γ + η`.

2D source: none in `LQGMetric` (it uses a separability argument); the template for the
countable-family consequence is `LQGMetric/Papers/DDDF/LenCountable.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLFPP

variable {d : ℕ}

/-! ## Polygonal paths -/

/-- The polygonal path through `p 0, p 1, …, p N`: `[p 0, p 1]` followed by the polygonal path
through `p 1, …, p N` (the constant path at `p 0` if `N = 0`). -/
def polygonPath (p : ℕ → Rd d) : ℕ → ℝ → Rd d
  | 0 => segPath (p 0) (p 0)
  | n + 1 => concatPath (segPath (p 0) (p 1)) (polygonPath (fun i => p (i + 1)) n)

theorem isPcwC1Path_polygonPath (p : ℕ → Rd d) (N : ℕ) :
    IsPcwC1Path (polygonPath p N) (p 0) (p N) := by
  induction N generalizing p with
  | zero => exact isPcwC1Path_segPath (p 0) (p 0)
  | succ n ih => exact (isPcwC1Path_segPath (p 0) (p 1)).concat (ih fun i => p (i + 1))

theorem polygonPath_congr {p p' : ℕ → Rd d} {N : ℕ} (h : ∀ i ≤ N, p i = p' i) :
    polygonPath p N = polygonPath p' N := by
  induction N generalizing p p' with
  | zero => simp only [polygonPath, h 0 le_rfl]
  | succ n ih =>
    simp only [polygonPath]
    rw [h 0 (Nat.zero_le _), h 1 (by omega),
      ih (p := fun i => p (i + 1)) (p' := fun i => p' (i + 1)) fun i hi => h (i + 1) (by omega)]

/-- A polygonal path lies in `V` if its first vertex and all its edges do. -/
theorem mapsTo_polygonPath {V : Set (Rd d)} (p : ℕ → Rd d) (N : ℕ) (h0 : p 0 ∈ V)
    (h : ∀ i < N, MapsTo (segPath (p i) (p (i + 1))) (Icc 0 1) V) :
    MapsTo (polygonPath p N) (Icc 0 1) V := by
  induction N generalizing p with
  | zero => exact fun u _ => by simp [polygonPath, segPath, h0]
  | succ n ih =>
    refine mapsTo_concatPath (h 0 (Nat.succ_pos n)) (ih (fun i => p (i + 1)) ?_ ?_)
    · have := h 0 (Nat.succ_pos n) (right_mem_Icc.2 zero_le_one)
      rwa [segPath_one] at this
    · intro i hi
      exact h (i + 1) (by omega)

/-- The LFPP length of a polygonal path is the sum of the LFPP lengths of its edges. -/
theorem lfppLength_polygonPath {ζ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) (p : ℕ → Rd d)
    (N : ℕ) : lfppLength ζ φ (polygonPath p N) =
      ∑ i ∈ Finset.range N, lfppLength ζ φ (segPath (p i) (p (i + 1))) := by
  induction N generalizing p with
  | zero => simp only [polygonPath, lfppLength_segPath_self, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    simp only [polygonPath]
    rw [lfppLength_concatPath hφ (isPcwC1Path_segPath (p 0) (p 1))
      (isPcwC1Path_polygonPath (fun i => p (i + 1)) n), ih, Finset.sum_range_succ', add_comm]

/-! ## Polygonal approximation -/

/-- **One edge of the polygonal approximation**: if the edge `[P, Q]` has its endpoints within `δ'`
of `γ(a)`, `γ(b)`, the weight on the edge is at most `w(γ a) + ϖ` and the weight along `γ|_{[a,b]}`
is at least `w(γ a) - ϖ` (`w = e^{ζ φ}`), then
`cost([P,Q]) ≤ ∫_a^b w(γ)|γ'| + 2ϖ ∫_a^b |γ'| + 2δ'(w(γ a) + ϖ)`. -/
theorem lfppLength_segPath_le_piece {ζ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {γ : ℝ → Rd d} {x y : Rd d} (hγ : IsPcwC1Path γ x y) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) {P Q : Rd d} {ϖ δ' : ℝ} (hP : ‖P - γ a‖ ≤ δ') (hQ : ‖Q - γ b‖ ≤ δ')
    (hseg : ∀ u ∈ Icc (0 : ℝ) 1,
      Real.exp (ζ * φ (segPath P Q u)) ≤ Real.exp (ζ * φ (γ a)) + ϖ)
    (hpiece : ∀ u ∈ Icc a b, Real.exp (ζ * φ (γ a)) - ϖ ≤ Real.exp (ζ * φ (γ u))) :
    lfppLength ζ φ (segPath P Q) ≤ (∫ u in a..b, lfppIntegrand ζ φ γ u) +
      2 * ϖ * (∫ u in a..b, ‖deriv γ u‖) + 2 * δ' * (Real.exp (ζ * φ (γ a)) + ϖ) := by
  set wa := Real.exp (ζ * φ (γ a)) with hwa
  set ℓ := ∫ u in a..b, ‖deriv γ u‖ with hℓ
  have hϖ : 0 ≤ ϖ := by have := hpiece a ⟨le_rfl, hab⟩; linarith
  have hB : 0 ≤ wa + ϖ := add_nonneg (Real.exp_pos _).le hϖ
  have hchord : ‖γ b - γ a‖ ≤ ℓ := hγ.norm_sub_le_integral ha hab hb
  have hQP : ‖Q - P‖ ≤ ℓ + 2 * δ' := by
    have e : Q - P = (Q - γ b) + (γ b - γ a) + (γ a - P) := by abel
    have hP' : ‖γ a - P‖ ≤ δ' := by rw [norm_sub_rev]; exact hP
    calc ‖Q - P‖ ≤ ‖Q - γ b‖ + ‖γ b - γ a‖ + ‖γ a - P‖ := by rw [e]; exact norm_add₃_le
      _ ≤ ℓ + 2 * δ' := by linarith
  have hI : IntervalIntegrable (lfppIntegrand ζ φ γ) volume a b :=
    intervalIntegrable_of_sub (hγ.intervalIntegrable_lfppIntegrand hφ ζ) ha hab hb
  have hD : IntervalIntegrable (fun u => ‖deriv γ u‖) volume a b :=
    (intervalIntegrable_of_sub hγ.intervalIntegrable_deriv ha hab hb).norm
  have hlow : (wa - ϖ) * ℓ ≤ ∫ u in a..b, lfppIntegrand ζ φ γ u := by
    rw [hℓ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hab (hD.const_mul _) hI fun u hu => ?_
    exact mul_le_mul_of_nonneg_right (hpiece u hu) (norm_nonneg _)
  calc lfppLength ζ φ (segPath P Q) ≤ (wa + ϖ) * ‖Q - P‖ := lfppLength_segPath_le hφ P Q hseg
    _ ≤ (wa + ϖ) * (ℓ + 2 * δ') := mul_le_mul_of_nonneg_left hQP hB
    _ = (wa - ϖ) * ℓ + 2 * ϖ * ℓ + 2 * δ' * (wa + ϖ) := by ring
    _ ≤ _ := by linarith [hlow]

/-- **Polygonal approximation** (HA5 D1(a)): inside an open set, every piecewise `C¹` path is
approximated in LFPP length (from above, up to any `η > 0`) by polygonal paths with the same
endpoints whose interior vertices lie in a prescribed dense set. -/
theorem exists_polygonPath_le {S : Set (Rd d)} (hS : Dense S) {V : Set (Rd d)} (hV : IsOpen V)
    {ζ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ) {γ : ℝ → Rd d} {x y : Rd d}
    (hγ : IsPcwC1Path γ x y) (hγV : MapsTo γ (Icc 0 1) V) {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (p : ℕ → Rd d), 0 < N ∧ p 0 = x ∧ p N = y ∧ (∀ i, 0 < i → i < N → p i ∈ S) ∧
      MapsTo (polygonPath p N) (Icc 0 1) V ∧
      lfppLength ζ φ (polygonPath p N) ≤ lfppLength ζ φ γ + η := by
  classical
  -- the compact trace of `γ` and a compact neighbourhood inside `V`
  set K := γ '' Icc (0 : ℝ) 1 with hKdef
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hγ.continuousOn
  have hKV : K ⊆ V := by rintro _ ⟨t, ht, rfl⟩; exact hγV ht
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  set K' := Metric.cthickening r K with hK'def
  have hK' : IsCompact K' := hK.cthickening
  have hKK' : K ⊆ K' := Metric.self_subset_cthickening K
  have hγK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K := fun t ht => ⟨t, ht, rfl⟩
  -- the weight and its bound on `K'`
  set w : Rd d → ℝ := fun z => Real.exp (ζ * φ z) with hwdef
  have hw : Continuous w := Real.continuous_exp.comp (continuous_const.mul hφ)
  obtain ⟨W, hW⟩ := hK'.exists_bound_of_continuousOn hw.continuousOn
  have hWw : ∀ z ∈ K', w z ≤ W := fun z hz =>
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hW z hz)
  have hW0 : 0 ≤ W :=
    (Real.exp_pos _).le.trans (hWw (γ 0) (hKK' (hγK 0 ⟨le_rfl, zero_le_one⟩)))
  -- the constants
  set ℓ := ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ with hℓdef
  have hℓ : 0 ≤ ℓ := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  set ϖ := η / (4 * (ℓ + 1)) with hϖdef
  have hϖ : 0 < ϖ := by positivity
  obtain ⟨ρ, hρ, hwρ⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hw.continuousOn) ϖ hϖ
  set ρ₁ := min ρ r with hρ₁def
  have hρ₁ : 0 < ρ₁ := lt_min hρ hr
  have hρ₁ρ : ρ₁ ≤ ρ := min_le_left _ _
  have hρ₁r : ρ₁ ≤ r := min_le_right _ _
  obtain ⟨δ, hδ, hγδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hγ.continuousOn) (ρ₁ / 4) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set N : ℕ := n + 1 with hNdef
  have hNpos : (0 : ℝ) < N := by positivity
  have hNinv : 1 / (N : ℝ) < δ := by
    have : ((n : ℝ) + 1) = (N : ℝ) := by push_cast [hNdef]; ring
    rwa [this] at hn
  set δ' := min (ρ₁ / 8) (η / (4 * N * (W + ϖ + 1))) with hδ'def
  have hδ' : 0 < δ' := lt_min (by positivity) (by positivity)
  have hδ'ρ : δ' ≤ ρ₁ / 8 := min_le_left _ _
  have hδ'η : δ' ≤ η / (4 * N * (W + ϖ + 1)) := min_le_right _ _
  -- the mesh and the vertices
  set t : ℕ → ℝ := fun i => (i : ℝ) / N with htdef
  have ht0 : t 0 = 0 := by simp [htdef]
  have htN : t N = 1 := by simp only [htdef]; exact div_self hNpos.ne'
  have ht_mem : ∀ i ≤ N, t i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast hi
  have ht_succ : ∀ i, t (i + 1) - t i = 1 / N := by
    intro i; simp only [htdef]; push_cast; ring
  have ht_le : ∀ i, t i ≤ t (i + 1) := fun i => by
    have := ht_succ i; have : (0 : ℝ) < 1 / N := by positivity
    linarith
  have hpt : ∀ i : ℕ, ∃ s ∈ S, dist (γ (t i)) s < δ' := fun i =>
    hS.exists_dist_lt (γ (t i)) hδ'
  choose s hsS hsd using hpt
  set p : ℕ → Rd d := fun i => if i = 0 then x else if i < N then s i else y with hpdef
  have hp0 : p 0 = x := by simp [hpdef]
  have hpN : p N = y := by
    simp only [hpdef]; rw [ite_eq_right (by omega : N ≠ 0), ite_eq_right (lt_irrefl N)]
  have hpS : ∀ i, 0 < i → i < N → p i ∈ S := by
    intro i hi hiN
    simp only [hpdef]; rw [ite_eq_right (by omega : i ≠ 0), ite_eq_left hiN]; exact hsS i
  -- (P1) the vertices are close to the path
  have hP1 : ∀ i ≤ N, ‖p i - γ (t i)‖ ≤ δ' := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hp0, ht0, hγ.source, sub_self, norm_zero]; exact hδ'.le
    rcases hi.lt_or_eq with hiN | rfl
    · have hpi : p i = s i := by
        simp only [hpdef]; rw [ite_eq_right (by omega : i ≠ 0), ite_eq_left hiN]
      rw [hpi, ← dist_eq_norm, dist_comm]; exact (hsd i).le
    · rw [hpN, htN, hγ.target, sub_self, norm_zero]; exact hδ'.le
  -- (P2) the path stays close to its value at the left end of each piece
  have hP2 : ∀ i < N, ∀ u ∈ Icc (t i) (t (i + 1)), dist (γ u) (γ (t i)) < ρ₁ / 4 := by
    intro i hi u hu
    have hti := ht_mem i hi.le
    have hti' := ht_mem (i + 1) hi
    refine hγδ u ⟨hti.1.trans hu.1, hu.2.trans hti'.2⟩ (t i) hti ?_
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hu.1)]
    have := ht_succ i
    linarith [hu.2]
  -- (P4) the edges stay close to the path
  have hP4 : ∀ i < N, ∀ u ∈ Icc (0 : ℝ) 1,
      dist (segPath (p i) (p (i + 1)) u) (γ (t i)) < ρ₁ := by
    intro i hi u hu
    have h1 := hP1 i hi.le
    have h2 := hP1 (i + 1) hi
    have h3 := hP2 i hi (t (i + 1)) ⟨ht_le i, le_rfl⟩
    rw [dist_eq_norm] at h3 ⊢
    have hseg := norm_segPath_sub (p i) (p (i + 1)) hu
    have hedge : ‖p (i + 1) - p i‖ ≤ ‖p (i + 1) - γ (t (i + 1))‖ +
        ‖γ (t (i + 1)) - γ (t i)‖ + ‖γ (t i) - p i‖ := by
      have e : p (i + 1) - p i = (p (i + 1) - γ (t (i + 1))) + (γ (t (i + 1)) - γ (t i)) +
          (γ (t i) - p i) := by abel
      rw [e]; exact norm_add₃_le
    have h1' : ‖γ (t i) - p i‖ ≤ δ' := by rw [norm_sub_rev]; exact h1
    have e2 : segPath (p i) (p (i + 1)) u - γ (t i) =
        (segPath (p i) (p (i + 1)) u - p i) + (p i - γ (t i)) := by abel
    calc ‖segPath (p i) (p (i + 1)) u - γ (t i)‖
        ≤ ‖segPath (p i) (p (i + 1)) u - p i‖ + ‖p i - γ (t i)‖ := by
          rw [e2]; exact norm_add_le _ _
      _ < ρ₁ := by linarith
  -- per-edge estimate
  have hedge : ∀ i ∈ Finset.range N, lfppLength ζ φ (segPath (p i) (p (i + 1))) ≤
      (∫ u in t i..t (i + 1), lfppIntegrand ζ φ γ u) +
        2 * ϖ * (∫ u in t i..t (i + 1), ‖deriv γ u‖) + 2 * δ' * (W + ϖ) := by
    intro i hi
    have hiN : i < N := Finset.mem_range.1 hi
    have hti := ht_mem i hiN.le
    have hti' := ht_mem (i + 1) hiN
    have hγti : γ (t i) ∈ K' := hKK' (hγK _ hti)
    have hw_le : w (γ (t i)) ≤ W := hWw _ hγti
    refine (lfppLength_segPath_le_piece hφ hγ hti.1 (ht_le i) hti'.2 (hP1 i hiN.le)
      (hP1 (i + 1) hiN) (ϖ := ϖ) ?_ ?_).trans ?_
    · intro u hu
      have hd := hP4 i hiN u hu
      have hz : segPath (p i) (p (i + 1)) u ∈ K' :=
        Metric.mem_cthickening_of_dist_le _ (γ (t i)) r K (hγK _ hti) (hd.le.trans hρ₁r)
      have := hwρ _ hz _ hγti (hd.trans_le hρ₁ρ)
      rw [Real.dist_eq] at this
      have := (le_abs_self _).trans this.le
      show w (segPath (p i) (p (i + 1)) u) ≤ w (γ (t i)) + ϖ
      linarith
    · intro u hu
      have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hti.1.trans hu.1, hu.2.trans hti'.2⟩
      have hd := hP2 i hiN u hu
      have := hwρ _ (hKK' (hγK _ hu01)) _ hγti (hd.trans_le (by linarith))
      rw [Real.dist_eq] at this
      have := (neg_le_abs (w (γ u) - w (γ (t i)))).trans this.le
      show w (γ (t i)) - ϖ ≤ w (γ u)
      linarith
    · have : 2 * δ' * (w (γ (t i)) + ϖ) ≤ 2 * δ' * (W + ϖ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
  -- summing the edges
  have hI := hγ.intervalIntegrable_lfppIntegrand hφ ζ
  have hD := hγ.intervalIntegrable_deriv.norm
  have hsum1 : ∑ i ∈ Finset.range N, ∫ u in t i..t (i + 1), lfppIntegrand ζ φ γ u =
      lfppLength ζ φ γ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun k hk =>
      intervalIntegrable_of_sub hI (ht_mem k hk.le).1 (ht_le k) (ht_mem (k + 1) hk).2,
      ht0, htN, lfppLength_eq_integral]
  have hsum2 : ∑ i ∈ Finset.range N, ∫ u in t i..t (i + 1), ‖deriv γ u‖ = ℓ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun k hk =>
      intervalIntegrable_of_sub hD (ht_mem k hk.le).1 (ht_le k) (ht_mem (k + 1) hk).2,
      ht0, htN]
  refine ⟨N, p, Nat.succ_pos n, hp0, hpN, hpS, ?_, ?_⟩
  · refine mapsTo_polygonPath p N (by rw [hp0]; exact hKV (hγK 0 ⟨le_rfl, zero_le_one⟩ |>
      fun h => by rwa [hγ.source] at h)) fun i hi u hu => hrV ?_
    exact Metric.mem_cthickening_of_dist_le _ (γ (t i)) r K (hγK _ (ht_mem i hi.le))
      ((hP4 i hi u hu).le.trans hρ₁r)
  · rw [lfppLength_polygonPath hφ]
    have hstep := Finset.sum_le_sum hedge
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum1, ← Finset.mul_sum, hsum2,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hstep
    have hA : 2 * ϖ * ℓ ≤ η / 2 := by
      have e : ϖ * (ℓ + 1) = η / 4 := by
        rw [hϖdef]; field_simp
      nlinarith
    have hB : (N : ℝ) * (2 * δ' * (W + ϖ)) ≤ η / 2 := by
      have e : δ' * (4 * N * (W + ϖ + 1)) ≤ η := by
        have hpos : 0 < 4 * (N : ℝ) * (W + ϖ + 1) := by positivity
        calc δ' * (4 * N * (W + ϖ + 1)) ≤ η / (4 * N * (W + ϖ + 1)) * (4 * N * (W + ϖ + 1)) :=
              mul_le_mul_of_nonneg_right hδ'η hpos.le
          _ = η := div_mul_cancel₀ η hpos.ne'
      nlinarith
    linarith

end HigherDimLFPP
