/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.UpperAssemblyAux1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan

/-!
# Auxiliary lemmas for the conditional assembly of (1.7) (`Draft.UpperAssembly`), part 1

Elementary facts used by `LQGDimension.LFPP.UpperAssembly`:

* algebra of `SegComb.avg` (append, negation, `sub`, `flatten`), and the identity
  `Σ_i cfgVal φ δ kᵢ cᵢ = δ^{-1/2} ⟨φ, sumComb c l⟩ - Σ_i kᵢ`;
* polygon lengths: images under similarities, positivity on the normalized local families;
* `0 ≤ a n`;
* the straight segment `t ↦ t` is an admissible path.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped Classical

namespace LQGDimension

namespace UpperAssemblyAux

open Blueprint.Draft

/-! ### Algebra of `SegComb.avg` -/

theorem avg_nil' (φ : ℂ → ℝ) : SegComb.avg φ [] = 0 := by
  simp [SegComb.avg]

theorem avg_cons' (φ : ℂ → ℝ) (p : ℝ × ℂ × ℂ) (c : SegComb) :
    SegComb.avg φ (p :: c) = p.1 * segAvg φ p.2.1 p.2.2 + SegComb.avg φ c := by
  simp [SegComb.avg]

theorem avg_append' (φ : ℂ → ℝ) (c c' : SegComb) :
    SegComb.avg φ (c ++ c') = SegComb.avg φ c + SegComb.avg φ c' := by
  induction c with
  | nil => simp [avg_nil']
  | cons p c ih => rw [List.cons_append, avg_cons', avg_cons', ih]; ring

theorem avg_negw' (φ : ℂ → ℝ) (c : SegComb) :
    SegComb.avg φ (c.map fun (p : ℝ × ℂ × ℂ) => (-p.1, p.2)) = -SegComb.avg φ c := by
  induction c with
  | nil => simp [avg_nil']
  | cons p c ih =>
    rw [List.map_cons, avg_cons', avg_cons', ih]
    ring

theorem avg_sub' (φ : ℂ → ℝ) (c c' : SegComb) :
    SegComb.avg φ (SegComb.sub c c') = SegComb.avg φ c - SegComb.avg φ c' := by
  rw [SegComb.sub, avg_append', avg_negw']
  ring

theorem avg_cfgComb (φ : ℂ → ℝ) (c : Config) :
    (cfgComb c).avg φ = polyAvg φ c.1 - polyAvg φ c.2 := by
  rw [cfgComb, avg_sub']
  rfl

theorem avg_sumComb (φ : ℂ → ℝ) (c : ℕ → Config) (l : ℕ) :
    (sumComb c l).avg φ = ∑ i ∈ Finset.range l, (polyAvg φ (c i).1 - polyAvg φ (c i).2) := by
  induction l with
  | zero => simp [sumComb, avg_nil']
  | succ l ih =>
    rw [Finset.sum_range_succ, ← ih, ← avg_cfgComb]
    simp only [sumComb, List.range_succ, List.map_append, List.flatten_append, List.map_cons,
      List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [avg_append']

/-- The sum of the local variables along a chain is an affine function of one segment
functional. -/
theorem sum_cfgVal_eq (φ : ℂ → ℝ) (δ : ℝ) (k : ℕ → ℕ) (c : ℕ → Config) (l : ℕ) :
    ∑ i ∈ Finset.range l, cfgVal φ δ (k i) (c i) =
      δ ^ (-(1 / 2 : ℝ)) * (sumComb c l).avg φ - ∑ i ∈ Finset.range l, (k i : ℝ) := by
  rw [avg_sumComb, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rfl

/-! ### Polygon lengths -/

theorem edges_map (f : ℂ → ℂ) (z : List ℂ) :
    edges (z.map f) = (edges z).map (Prod.map f f) := by
  rw [edges, edges, ← List.map_tail, List.zip_map]

theorem polyLen_map_simMap (s : ℂ × ℂ) (z : List ℂ) :
    polyLen (z.map (simMap s)) = ‖s.1‖ * polyLen z := by
  simp only [polyLen, edges_map, List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, simMap]
  rw [show s.1 * e.2 + s.2 - (s.1 * e.1 + s.2) = s.1 * (e.2 - e.1) by ring, norm_mul]

theorem polyLen_pair (x y : ℂ) : polyLen [x, y] = ‖y - x‖ := by
  simp [polyLen, edges]

theorem le_polyLen_of_mem {z : List ℂ} {e : ℂ × ℂ} (he : e ∈ edges z) :
    ‖e.2 - e.1‖ ≤ polyLen z := by
  unfold polyLen
  apply List.single_le_sum
  · intro x hx
    obtain ⟨e', _, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  · exact List.mem_map.2 ⟨e, he, rfl⟩

/-- The parent chord of a normalized configuration has length at least `1/2`. -/
theorem chord_ge {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) {x y : ℂ}
    (hx : ‖x‖ ≤ cellRad M * δ) (hy : ‖y - 1‖ ≤ cellRad M * δ) : 1 / 2 ≤ ‖y - x‖ := by
  have hM' : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have hcr : cellRad M * δ ≤ 1 / 64 := by
    unfold cellRad
    have h1 : 4 / (M : ℝ) ^ 2 ≤ 4 / 256 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have h2 : 0 ≤ 4 / (M : ℝ) ^ 2 := by positivity
    nlinarith [hδ.1, hδ.2]
  have htri : ‖(1 : ℂ)‖ ≤ ‖y - x‖ + ‖x‖ + ‖y - 1‖ := by
    have e : (1 : ℂ) = (y - x) + x - (y - 1) := by ring
    calc ‖(1 : ℂ)‖ = ‖(y - x) + x - (y - 1)‖ := by rw [← e]
      _ ≤ ‖(y - x) + x‖ + ‖y - 1‖ := norm_sub_le _ _
      _ ≤ ‖y - x‖ + ‖x‖ + ‖y - 1‖ := by gcongr; exact norm_add_le _ _
  rw [norm_one] at htri
  linarith

/-- Both polygons of a normalized local configuration have positive length. -/
theorem localFamily_polyLen_pos {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    {large : Bool} {k : ℕ} {c : Config} (hc : c ∈ localFamily M δ large k) :
    0 < polyLen c.1 ∧ 0 < polyLen c.2 := by
  have hMpos : (0 : ℝ) < M := by
    have : (16 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  cases large with
  | true =>
    simp only [localFamily, ite_true] at hc
    obtain ⟨x, y, x', y', rfl, hx, hy, -, -, hlo, -⟩ := hc
    have hR := chord_ge hM hδ hx hy
    refine ⟨?_, ?_⟩
    · simp only [polyLen_pair]; linarith
    · simp only [polyLen_pair]
      refine lt_of_lt_of_le ?_ hlo
      have : 0 < ‖y - x‖ := by linarith
      positivity
  | false =>
    simp only [localFamily, Bool.false_eq_true, ite_false] at hc
    obtain ⟨x, y, z, rfl, -, -, hx, hy, hz2, -, -, hlast, -⟩ := hc
    have hR := chord_ge hM hδ hx hy
    refine ⟨?_, ?_⟩
    · simp only [polyLen_pair]; linarith
    · have hne : edges z ≠ [] := by
        intro h0
        have hl : (edges z).length = 0 := by rw [h0]; rfl
        simp only [edges, List.length_zip, List.length_tail] at hl
        omega
      have hmem : (edges z).getLast hne ∈ (edges z).getLast? := by
        rw [List.getLast?_eq_some_getLast hne]; rfl
      have h1 := (hlast _ hmem).1
      have h2 := le_polyLen_of_mem (List.getLast_mem hne)
      have : 0 < ‖y - x‖ / (2 * M) := by
        have : 0 < ‖y - x‖ := by linarith
        positivity
      simp only
      linarith

/-- Both polygons of the image of a normalized local configuration under a similarity have
positive length. -/
theorem cfgMap_polyLen_pos {M : ℕ} (hM : 16 ≤ M) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    {large : Bool} {k : ℕ} {s : ℂ × ℂ} (hs : s.1 ≠ 0) {c : Config}
    (hc : c ∈ cfgMap s '' localFamily M δ large k) :
    0 < polyLen c.1 ∧ 0 < polyLen c.2 := by
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  obtain ⟨h1, h2⟩ := localFamily_polyLen_pos hM hδ hc₀
  have hs' : 0 < ‖s.1‖ := norm_pos_iff.2 hs
  simp only [cfgMap, polyLen_map_simMap]
  exact ⟨mul_pos hs' h1, mul_pos hs' h2⟩

/-! ### `a n ≥ 0` -/

theorem a_nonneg' (n : ℕ) : 0 ≤ a n := by
  apply EReal.toReal_nonneg
  unfold aE
  refine le_trans ?_ (le_iSup _ (∅ : Finset (V n)))
  have h0 : gaussianExpectedMax (∅ : Finset (V n)) (fun f g => zCov f g)
      (fun f => -energy f) = 0 := by
    unfold gaussianExpectedMax
    have : ∀ x : EuclideanSpace ℝ ↥(∅ : Finset (V n)),
        (⨆ i : ↥(∅ : Finset (V n)), x i + -energy (i : V n)) = 0 := by
      intro x
      have : IsEmpty ↥(∅ : Finset (V n)) := ⟨fun i => Finset.notMem_empty _ i.2⟩
      exact Real.iSup_of_isEmpty _
    simp only [this, integral_zero]
  rw [h0]
  rfl

/-! ### The straight path -/

theorem straight_admissible : IsAdmissiblePath (fun t : ℝ => (t : ℂ)) where
  source := by simp
  target := by simp
  mapsTo := by
    intro t ht
    simp only [U, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    refine ⟨?_, by norm_num⟩
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  continuousOn := Complex.continuous_ofReal.continuousOn
  piecewise_contDiff := by
    refine ⟨1, ![0, 1], ?_, rfl, rfl, fun i => ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · exact Complex.ofRealCLM.contDiff.contDiffOn

end UpperAssemblyAux

end LQGDimension
