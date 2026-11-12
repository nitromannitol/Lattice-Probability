import LatticeProb.Prob.KolmogorovBound

/-!
# Kolmogorov's modulus of continuity on a box, with an explicit rate

For a process `X` indexed by a box `[a, b] ⊆ ℝ^k` with continuous sample paths (almost surely)
and the Kolmogorov–Chentsov moment bound `E|X_u - X_v|^p ≤ M dist(u, v)^q`, dyadic chaining gives,
for every `c ∈ (0, 1)` with `θ = 2^{k - q} / c^p < 1` and every level `N` at least the radius
of the box,

`P(∃ u v ∈ [a, b], dist(u, v) < 2^{-N}, |X_u - X_v| > (2k + 1) c^N / (1 - c))
  ≤ M k 3^k S (N + 1)^k θ^N`,

with `S = ∑_j (j + 1)^k θ^j`. The bound depends on the process only through `p`, `q`, `M`, so it
is uniform over families of processes with a common moment bound: this is the form needed for
union bounds over many boxes (for instance, moduli of continuity of rescaled Gaussian fields).

## Main results

* `LatticeProb.exists_mem_badSetPi_of_modulus`: the pointwise form of `event_subset_badSetPi`,
  valid for sample spaces in any universe.
* `LatticeProb.tsum_ofReal_poly_geom_le`: the tail of a polynomial-geometric series.
* `LatticeProb.measure_modulus_gt_le`: the quantitative modulus bound above.
-/

open MeasureTheory Filter Set
open scoped ENNReal

noncomputable section

namespace LatticeProb

/-- Pointwise form of `event_subset_badSetPi`: if a continuous sample path has an increment
larger than the dyadic tail bound between two points of the box within `2^{-N}`, then it lies
in a dyadic bad event of some level at least `N`. The sample space may live in any universe. -/
theorem exists_mem_badSetPi_of_modulus {k : ℕ} {a b : Fin k → ℝ} (hab : a ≤ b)
    {Ω : Type*} {X : (Fin k → ℝ) → Ω → ℝ} {ω : Ω}
    (hcont : ContinuousOn (fun u => X u ω) (Set.Icc a b))
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {R N : ℕ} (hN : R ≤ N)
    (hR : ∀ u ∈ Set.Icc a b, ∀ i, |u i| ≤ (R : ℝ))
    {η : ℝ} (hmod : 2 * ((k : ℝ) * dtail (fun n => c ^ n) N) + (k : ℝ) * c ^ N < η)
    {u v : Fin k → ℝ} (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b)
    (huv : dist u v < 1 / 2 ^ N) (hη : η < |X u ω - X v ω|) :
    ∃ n, N ≤ n ∧ ω ∈ badSetPi (fun u => X (boxClamp a b hab u)) (fun n => c ^ n) (n + 1) n := by
  have h := event_subset_badSetPi (Ω := Unit) (X := fun u (_ : Unit) => X u ω) hab
    (fun _ => hcont) hc hc1 hN hR hmod
    (show () ∈ {ω' : Unit | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b,
        dist u v < 1 / 2 ^ N ∧ η < |X u ω - X v ω|} from ⟨u, hu, v, hv, huv, hη⟩)
  simp only [mem_iUnion, mem_Ici] at h
  obtain ⟨n, hn, hmem⟩ := h
  refine ⟨n, hn, ?_⟩
  simpa [badSetPi] using hmem

/-- The geometric dyadic tail: `∑_{i ≥ N + 1} c^i = c^N c / (1 - c)`. -/
theorem dtail_geometric {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) (N : ℕ) :
    dtail (fun n => c ^ n) N = c ^ N * c / (1 - c) := by
  unfold dtail
  simp_rw [pow_add]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hc hc1]
  field_simp

/-- The dyadic tail bound at level `N` is below the threshold `(2k + 1) c^N / (1 - c)`. -/
theorem dtail_bound_lt {k : ℕ} {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (N : ℕ) :
    2 * ((k : ℝ) * dtail (fun n => c ^ n) N) + (k : ℝ) * c ^ N
      < (2 * k + 1) * c ^ N / (1 - c) := by
  rw [dtail_geometric hc.le hc1]
  have h1c : 0 < 1 - c := by linarith
  have hcN : 0 < c ^ N := pow_pos hc N
  have key : (2 * k + 1) * c ^ N / (1 - c) - (2 * ((k : ℝ) * (c ^ N * c / (1 - c))) + k * c ^ N)
      = c ^ N * (1 + k * (1 - c)) / (1 - c) := by
    field_simp
    ring
  have hpos : 0 < c ^ N * (1 + k * (1 - c)) / (1 - c) := by positivity
  linarith

/-- The tail of a polynomial-geometric series from index `N` on:
`∑_j C ((j + N) + 1)^k θ^{j + N} ≤ C S (N + 1)^k θ^N` with `S = ∑_j (j + 1)^k θ^j`. -/
theorem tsum_ofReal_poly_geom_le (k : ℕ) {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (N : ℕ) :
    ∑' j : ℕ, ENNReal.ofReal (C * (((j + N : ℕ) : ℝ) + 1) ^ k * θ ^ (j + N))
      ≤ ENNReal.ofReal (C * (∑' j : ℕ, ((j : ℝ) + 1) ^ k * θ ^ j) * ((N : ℝ) + 1) ^ k * θ ^ N) := by
  set f : ℕ → ℝ := fun j => C * ((N : ℝ) + 1) ^ k * θ ^ N * (((j : ℝ) + 1) ^ k * θ ^ j) with hf
  have hS : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ k * θ ^ j) := by
    simpa using summable_polynomial_geometric k (C := 1) hθ0 hθ1
  have hfs : Summable f := hS.mul_left _
  have hfn : ∀ j, 0 ≤ f j := fun j => by positivity
  have hle : ∀ j : ℕ, C * (((j + N : ℕ) : ℝ) + 1) ^ k * θ ^ (j + N) ≤ f j := by
    intro j
    have hb : ((j + N : ℕ) : ℝ) + 1 ≤ ((j : ℝ) + 1) * ((N : ℝ) + 1) := by
      push_cast
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hp : (((j + N : ℕ) : ℝ) + 1) ^ k ≤ ((j : ℝ) + 1) ^ k * ((N : ℝ) + 1) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hb k
    rw [hf, pow_add]
    have hθj : 0 ≤ θ ^ j * θ ^ N := by positivity
    calc C * (((j + N : ℕ) : ℝ) + 1) ^ k * (θ ^ j * θ ^ N)
        ≤ C * (((j : ℝ) + 1) ^ k * ((N : ℝ) + 1) ^ k) * (θ ^ j * θ ^ N) := by
          gcongr
      _ = C * ((N : ℝ) + 1) ^ k * θ ^ N * (((j : ℝ) + 1) ^ k * θ ^ j) := by ring
  calc ∑' j : ℕ, ENNReal.ofReal (C * (((j + N : ℕ) : ℝ) + 1) ^ k * θ ^ (j + N))
      ≤ ∑' j : ℕ, ENNReal.ofReal (f j) :=
        ENNReal.tsum_le_tsum (fun j => ENNReal.ofReal_le_ofReal (hle j))
    _ = ENNReal.ofReal (∑' j, f j) := (ENNReal.ofReal_tsum_of_nonneg hfn hfs).symm
    _ = ENNReal.ofReal (C * (∑' j : ℕ, ((j : ℝ) + 1) ^ k * θ ^ j) * ((N : ℝ) + 1) ^ k * θ ^ N) := by
        rw [hf, tsum_mul_left]
        ring_nf

/-- **Kolmogorov's modulus of continuity on a box, with an explicit rate.** Let `X` be a process
on the box `[a, b] ⊆ ℝ^k` (contained in `[-R, R]^k`) with almost surely continuous sample paths
and `E|X_u - X_v|^p ≤ M dist(u, v)^q` on the box. For `c ∈ (0, 1)` with
`θ = 2^{k - q} / c^p < 1` and every `N ≥ R`, the probability that two points of the box within
`2^{-N}` have an increment larger than `(2k + 1) c^N / (1 - c)` is at most
`M k 3^k S (N + 1)^k θ^N`, where `S = ∑_j (j + 1)^k θ^j`. -/
theorem measure_modulus_gt_le {k : ℕ} {a b : Fin k → ℝ} (hab : a ≤ b)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : (Fin k → ℝ) → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc a b))
    {p q M c : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hM : 0 ≤ M) (hc : 0 < c) (hc1 : c < 1)
    (hθ : (2 : ℝ) ^ ((k : ℝ) - q) / c ^ p < 1)
    (hint : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      Integrable (fun ω => |X u ω - X v ω| ^ p) P)
    (hbound : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q)
    {R N : ℕ} (hN : R ≤ N) (hR : ∀ u ∈ Set.Icc a b, ∀ i, |u i| ≤ (R : ℝ)) :
    P {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b, dist u v < 1 / 2 ^ N ∧
        (2 * k + 1) * c ^ N / (1 - c) < |X u ω - X v ω|}
      ≤ ENNReal.ofReal (M * k * 3 ^ k *
          (∑' j : ℕ, ((j : ℝ) + 1) ^ k * ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ j) *
          ((N : ℝ) + 1) ^ k * ((2 : ℝ) ^ ((k : ℝ) - q) / c ^ p) ^ N) := by
  classical
  set θ : ℝ := (2 : ℝ) ^ ((k : ℝ) - q) / c ^ p with hθdef
  have hθ0 : 0 < θ := by positivity
  -- the version of `X` that is continuous on the box for every sample
  set Y : (Fin k → ℝ) → Ω → ℝ := fun u ω =>
    if ContinuousOn (fun u => X u ω) (Set.Icc a b) then X u ω else 0 with hY
  have hYcont : ∀ ω, ContinuousOn (fun u => Y u ω) (Set.Icc a b) := by
    intro ω
    by_cases h : ContinuousOn (fun u => X u ω) (Set.Icc a b)
    · simp [hY, h]
    · simpa [hY, h] using (continuousOn_const : ContinuousOn (fun _ : Fin k → ℝ => (0 : ℝ)) _)
  have hYX : ∀ u v, (fun ω => |Y u ω - Y v ω| ^ p) =ᵐ[P] (fun ω => |X u ω - X v ω| ^ p) := by
    intro u v
    filter_upwards [hcont] with ω h
    simp [hY, h]
  set Z : (Fin k → ℝ) → Ω → ℝ := fun u => Y (boxClamp a b hab u) with hZ
  have hintZ : ∀ u v, Integrable (fun ω => |Z u ω - Z v ω| ^ p) P := fun u v =>
    (hint _ (boxClamp_mem a b hab u) _ (boxClamp_mem a b hab v)).congr (hYX _ _).symm
  have hboundZ : ∀ u v, ∫ ω, |Z u ω - Z v ω| ^ p ∂P ≤ M * dist u v ^ q := by
    intro u v
    rw [integral_congr_ae (hYX _ _)]
    refine (hbound _ (boxClamp_mem a b hab u) _ (boxClamp_mem a b hab v)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (dist_boxClamp_le a b hab u v) hq) hM
  -- the event is contained in the discontinuity set and the dyadic bad events from level `N`
  have hsub : {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b, dist u v < 1 / 2 ^ N ∧
        (2 * k + 1) * c ^ N / (1 - c) < |X u ω - X v ω|}
      ⊆ {ω | ¬ ContinuousOn (fun u => X u ω) (Set.Icc a b)} ∪
        ⋃ j : ℕ, badSetPi Z (fun n => c ^ n) (j + N + 1) (j + N) := by
    rintro ω ⟨u, hu, v, hv, huv, hη⟩
    by_cases h : ContinuousOn (fun u => X u ω) (Set.Icc a b)
    · right
      have hη' : (2 * k + 1) * c ^ N / (1 - c) < |Y u ω - Y v ω| := by simpa [hY, h] using hη
      obtain ⟨n, hn, hmem⟩ := exists_mem_badSetPi_of_modulus hab (hYcont ω) hc hc1 hN hR
        (dtail_bound_lt hc hc1 N) hu hv huv hη'
      refine mem_iUnion.2 ⟨n - N, ?_⟩
      rw [Nat.sub_add_cancel hn]
      exact hmem
    · exact Or.inl h
  have hnull : P {ω | ¬ ContinuousOn (fun u => X u ω) (Set.Icc a b)} = 0 := ae_iff.1 hcont
  calc P {ω | ∃ u ∈ Set.Icc a b, ∃ v ∈ Set.Icc a b, dist u v < 1 / 2 ^ N ∧
        (2 * k + 1) * c ^ N / (1 - c) < |X u ω - X v ω|}
      ≤ P ({ω | ¬ ContinuousOn (fun u => X u ω) (Set.Icc a b)} ∪
          ⋃ j : ℕ, badSetPi Z (fun n => c ^ n) (j + N + 1) (j + N)) := measure_mono hsub
    _ ≤ P {ω | ¬ ContinuousOn (fun u => X u ω) (Set.Icc a b)} +
          P (⋃ j : ℕ, badSetPi Z (fun n => c ^ n) (j + N + 1) (j + N)) := measure_union_le _ _
    _ = P (⋃ j : ℕ, badSetPi Z (fun n => c ^ n) (j + N + 1) (j + N)) := by rw [hnull, zero_add]
    _ ≤ ∑' j : ℕ, P (badSetPi Z (fun n => c ^ n) (j + N + 1) (j + N)) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (M * (k : ℝ) * 3 ^ k * (((j + N : ℕ) : ℝ) + 1) ^ k *
          θ ^ (j + N)) := by
        refine ENNReal.tsum_le_tsum (fun j => ?_)
        exact measure_badSetPi_le_geometric P hp hM hc hintZ hboundZ (j + N)
    _ ≤ ENNReal.ofReal (M * k * 3 ^ k * (∑' j : ℕ, ((j : ℝ) + 1) ^ k * θ ^ j) *
          ((N : ℝ) + 1) ^ k * θ ^ N) :=
        tsum_ofReal_poly_geom_le k (by positivity) hθ0 hθ N

end LatticeProb
