/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Lemma33 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma31

/-!
# GMS [18] Lemma 3.3 and Theorem 3.2, deterministic form

Source: GMS [18] Lemma 3.3 and Theorem 3.2. Definition 1.2: the Dirichlet energy of
a function on a domain, `Energy(f; D) = ∫_D |∇f|²` (`eucEnergy`).

**Setting of the analytic hypothesis.** [18] takes `(D, f) ∈ 𝒞_C(ε^β)`: `D` has `C`-bounded convexity and
`∇f` is `ε^{-β}`-Lipschitz on `D`; the edge estimate of its proof only uses the mean value inequality
along a path of length `≲ diam(H_x) + diam(H_y)` between points of two adjacent cells. We state the edge
estimate with `f` differentiable on an open set `O` with `Λ`-Lipschitz derivative there, and with the
segments between the reference points of adjacent cells of `V(D)` contained in `O` (this holds as soon
as `O` contains the `2δ`-neighbourhood of `D`, `δ` bounding the cell diameters; it is how both
applications in [18], the annuli of Lemmas 3.4 and 3.8 with logarithmic `f`, are used, `LogAnnulus.lean`).
No convexity of `D` is needed.

* `sq_sub_le_of_adj` (the edge estimate of [18]): for adjacent `x, y`,
  `(f(p x) − f(p y))² ≤ 3 d_x² |∇f(p x)|² + 3 d_y² |∇f(p y)|² + 24 Λ² (d_x⁴ + d_y⁴)`;
* `energy_comp_le_sum` ([18] (3.14)): `Energy(f ∘ p; G(V(D))) ≤ ∑_{x ∈ V(D)} deg(x) (3 d_x² |∇f(p x)|² + 24 Λ² d_x⁴)`;
* `energy_le_of_lap_eq_zero` (**Theorem 3.2 from Lemma 3.3**, Dirichlet's principle, [18]): a
  function discrete harmonic at the interior vertices of `V(D)` with the boundary values `f(p x)` has
  energy at most `Energy(f ∘ p; G(V(D)))`;
* `lemma33` (**[18] Lemma 3.3**) and `theorem32` (**[18] Theorem 3.2**): with the Lemma 2.7 bound and the
  Proposition 2.10 inputs for `(D, |∇f|²)`, `(D, 1)`, `(Ω, g)`,
  `Energy ≤ 3 [A Energy(f; D) + η + L_F δ (A area(D) + η) + M_F (A ∫_Ω g + η)]
     + 24 Λ² δ² [A area(D) + η + A ∫_Ω g + η]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Classical

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- **Definition 1.2 of [18]**: the Dirichlet energy `∫_D |∇f|²` of `f` on `D`. -/
def eucEnergy (f : ℂ → ℝ) (D : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)

/-- Mean value inequality with a Lipschitz derivative: if the segment `[u, v]` lies in the open set `O`
where `f` is differentiable with `Λ`-Lipschitz derivative, then
`|f u − f v| ≤ |u − v| (|∇f(u)| + Λ |u − v|)`. -/
theorem abs_sub_le_of_segment_subset {O : Set ℂ} (hO : IsOpen O) {f : ℂ → ℝ}
    (hdf : DifferentiableOn ℝ f O) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hLip : ∀ u ∈ O, ∀ v ∈ O, ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ Λ * ‖u - v‖) {u v : ℂ}
    (hseg : segment ℝ u v ⊆ O) :
    |f v - f u| ≤ (‖fderiv ℝ f u‖ + Λ * ‖v - u‖) * ‖v - u‖ := by
  have hu : u ∈ O := hseg (left_mem_segment ℝ u v)
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := f)
    (f' := fun w => fderiv ℝ f w) (s := segment ℝ u v) (C := ‖fderiv ℝ f u‖ + Λ * ‖v - u‖)
    (fun w hw => ((hdf.differentiableAt (hO.mem_nhds (hseg hw))).hasFDerivAt).hasFDerivWithinAt)
    (fun w hw => ?_) (convex_segment u v) (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
  · rwa [Real.norm_eq_abs] at h
  · have hΛ : ‖fderiv ℝ f w - fderiv ℝ f u‖ ≤ Λ * ‖w - u‖ := hLip w (hseg hw) u hu
    have hwu : ‖w - u‖ ≤ ‖v - u‖ := norm_sub_le_of_mem_segment hw
    calc ‖fderiv ℝ f w‖ ≤ ‖fderiv ℝ f u‖ + ‖fderiv ℝ f w - fderiv ℝ f u‖ := by
          have := norm_add_le (fderiv ℝ f u) (fderiv ℝ f w - fderiv ℝ f u)
          rwa [add_sub_cancel] at this
      _ ≤ ‖fderiv ℝ f u‖ + Λ * ‖v - u‖ := by
          gcongr
          exact hΛ.trans (mul_le_mul_of_nonneg_left hwu hΛ0)

/-- **The edge estimate of [18] Lemma 3.3**. -/
theorem sq_sub_le_of_adj {O : Set ℂ} (hO : IsOpen O) {f : ℂ → ℝ} (hdf : DifferentiableOn ℝ f O)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hLip : ∀ u ∈ O, ∀ v ∈ O, ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ Λ * ‖u - v‖)
    (p : V → ℂ) (hp : ∀ x, p x ∈ H.cell x) {x y : V} (hadj : G.adj.Adj x y)
    (hseg : segment ℝ (p x) (p y) ⊆ O) :
    (f (p x) - f (p y)) ^ 2 ≤
      (3 * cellDiam H x ^ 2 * ‖fderiv ℝ f (p x)‖ ^ 2 + 24 * Λ ^ 2 * cellDiam H x ^ 4) +
        (3 * cellDiam H y ^ 2 * ‖fderiv ℝ f (p y)‖ ^ 2 + 24 * Λ ^ 2 * cellDiam H y ^ 4) := by
  set dx := cellDiam H x
  set dy := cellDiam H y
  set a := ‖fderiv ℝ f (p x)‖
  set b := ‖fderiv ℝ f (p y)‖
  set r := ‖p y - p x‖ with hr
  have hdx := cellDiam_nonneg H x
  have hdy := cellDiam_nonneg H y
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrs : r ≤ dx + dy := by
    rw [hr, ← dist_eq_norm, dist_comm]
    exact dist_le_cellDiam_add_of_adj H hadj (hp x) (hp y)
  have h1 : |f (p y) - f (p x)| ≤ (a + Λ * r) * r :=
    abs_sub_le_of_segment_subset hO hdf hΛ hLip hseg
  have h2 : |f (p x) - f (p y)| ≤ (b + Λ * r) * r := by
    have := abs_sub_le_of_segment_subset hO hdf hΛ hLip (u := p y) (v := p x)
      (by rwa [segment_symm])
    rwa [← norm_neg (p x - p y), neg_sub] at this
  rw [abs_sub_comm] at h1
  set s := dx + dy with hs
  have hmin : |f (p x) - f (p y)| ≤ s * min a b + Λ * s ^ 2 := by
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab]
      calc |f (p x) - f (p y)| ≤ (a + Λ * r) * r := h1
        _ ≤ (a + Λ * s) * s := by gcongr
        _ = s * a + Λ * s ^ 2 := by ring
    · rw [min_eq_right hab]
      calc |f (p x) - f (p y)| ≤ (b + Λ * r) * r := h2
        _ ≤ (b + Λ * s) * s := by gcongr
        _ = s * b + Λ * s ^ 2 := by ring
  have hsplit : s * min a b ≤ dx * a + dy * b := by
    rw [hs, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left a b) hdx)
      (mul_le_mul_of_nonneg_left (min_le_right a b) hdy)
  have habs : |f (p x) - f (p y)| ≤ dx * a + dy * b + Λ * s ^ 2 := by linarith
  have hsq : (f (p x) - f (p y)) ^ 2 ≤ (dx * a + dy * b + Λ * s ^ 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hs4 : s ^ 4 ≤ 8 * (dx ^ 4 + dy ^ 4) := by
    rw [hs]
    nlinarith [sq_nonneg (dx - dy), sq_nonneg (dx + dy), sq_nonneg (dx ^ 2 - dy ^ 2),
      mul_nonneg hdx hdy, sq_nonneg (dx * dy)]
  calc (f (p x) - f (p y)) ^ 2 ≤ (dx * a + dy * b + Λ * s ^ 2) ^ 2 := hsq
    _ ≤ 3 * ((dx * a) ^ 2 + (dy * b) ^ 2 + (Λ * s ^ 2) ^ 2) := by
        nlinarith [sq_nonneg (dx * a - dy * b), sq_nonneg (dx * a - Λ * s ^ 2),
          sq_nonneg (dy * b - Λ * s ^ 2)]
    _ = 3 * dx ^ 2 * a ^ 2 + 3 * dy ^ 2 * b ^ 2 + 3 * Λ ^ 2 * s ^ 4 := by ring
    _ ≤ 3 * dx ^ 2 * a ^ 2 + 3 * dy ^ 2 * b ^ 2 + 3 * Λ ^ 2 * (8 * (dx ^ 4 + dy ^ 4)) := by
        gcongr
    _ = _ := by ring

/-- **[18] (3.14)**: `Energy(f ∘ p; G(V(D))) ≤ ∑_{x ∈ V(D)} deg(x) (3 d_x² |∇f(p x)|² + 24 Λ² d_x⁴)`. -/
theorem energy_comp_le_sum (D : Set ℂ) {O : Set ℂ} (hO : IsOpen O) {f : ℂ → ℝ}
    (hdf : DifferentiableOn ℝ f O) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hLip : ∀ u ∈ O, ∀ v ∈ O, ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ Λ * ‖u - v‖)
    (p : V → ℂ) (hp : ∀ x, p x ∈ H.cell x)
    (hseg : ∀ x ∈ vFin H D, ∀ y ∈ vFin H D, G.adj.Adj x y → segment ℝ (p x) (p y) ⊆ O) :
    energy G (vFin H D) (f ∘ p) ≤ ∑ x ∈ vFin H D, (G.deg x : ℝ) *
      (3 * cellDiam H x ^ 2 * ‖fderiv ℝ f (p x)‖ ^ 2 + 24 * Λ ^ 2 * cellDiam H x ^ 4) := by
  set φ : V → ℝ := fun x =>
    3 * cellDiam H x ^ 2 * ‖fderiv ℝ f (p x)‖ ^ 2 + 24 * Λ ^ 2 * cellDiam H x ^ 4 with hφ
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => by positivity
  refine le_trans ?_ (sum_edgesIn_add_le G (vFin H D) fun x _ => hφ0 x)
  unfold energy
  refine Finset.sum_le_sum fun e he => ?_
  rw [mem_edgesIn] at he
  simp only [Function.comp]
  by_cases hloop : G.src e = G.tgt e
  · rw [hloop, sub_self, sq, mul_zero]
    exact add_nonneg (hφ0 _) (hφ0 _)
  · exact sq_sub_le_of_adj H hO hdf hΛ hLip p hp (adj_of_edge G hloop)
      (hseg _ he.1 _ he.2 (adj_of_edge G hloop))

/-- **Theorem 3.2 from Lemma 3.3** ([18], Dirichlet's principle): a function discrete harmonic
at the interior vertices of `V(D)` (cells not meeting `∂D`) and equal to `f ∘ p` at the boundary vertices
has energy at most `Energy(f ∘ p; G(V(D)))`. -/
theorem energy_le_of_lap_eq_zero {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    (q : V → ℝ) (h : V → ℝ)
    (hharm : ∀ x ∈ vFin H D, ¬ (H.cell x ∩ frontier D).Nonempty → lap G h x = 0)
    (hbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty → h x = q x) :
    energy G (vFin H D) h ≤ energy G (vFin H D) q := by
  refine energy_le_of_harmonic G (B := {x | (H.cell x ∩ frontier D).Nonempty}) ?_ hharm
    fun x hx hxB => (hbd x hx hxB).symm
  intro x hx hxB d hd
  have hsub := cell_subset_of_inter_frontier_eq_empty H hDo ((mem_vFin H hDb).mp hx)
    (Set.not_nonempty_iff_eq_empty.mp hxB)
  exact dtgt_mem_vFin_of_subset H hDb hsub hx hd

/-- The sum of `(3.14)`, bounded through Lemma 3.1 (deterministic core, no probabilistic input). -/
theorem energy_comp_le_lintegral {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {O : Set ℂ} (hO : IsOpen O) {f : ℂ → ℝ} (hdf : DifferentiableOn ℝ f O) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hLip : ∀ u ∈ O, ∀ v ∈ O, ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ Λ * ‖u - v‖)
    (p : V → ℂ) (hp : ∀ x, p x ∈ H.cell x)
    (hseg : ∀ x ∈ vFin H D, ∀ y ∈ vFin H D, G.adj.Adj x y → segment ℝ (p x) (p y) ⊆ O)
    {LF MF δ : ℝ} (hLF : 0 ≤ LF)
    (hLipF : ∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z‖ ^ 2 ≤ ‖fderiv ℝ f w‖ ^ 2 + LF * dist z w)
    (hMF : ∀ x ∈ vFin H D, ‖fderiv ℝ f (p x)‖ ^ 2 ≤ MF)
    (hδ : ∀ x ∈ vFin H D, cellDiam H x ≤ δ)
    {Ω : Set ℂ} {g : ℂ → ℝ}
    (hbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      H.cell x ⊆ Ω ∧ ∀ z ∈ H.cell x, 1 ≤ g z) :
    ENNReal.ofReal (energy G (vFin H D) (f ∘ p)) ≤
      3 * ((∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) * uDens H z) +
        ENNReal.ofReal (LF * δ) * (∫⁻ z in D, uDens H z) +
        ENNReal.ofReal MF * (∫⁻ z in Ω, ENNReal.ofReal (g z) * uDens H z)) +
      ENNReal.ofReal (24 * Λ ^ 2 * δ ^ 2) * ((∫⁻ z in D, uDens H z) +
        ∫⁻ z in Ω, ENNReal.ofReal (g z) * uDens H z) := by
  have hE := energy_comp_le_sum H D hO hdf hΛ hLip p hp hseg
  have hsplit : ∑ x ∈ vFin H D, (G.deg x : ℝ) *
      (3 * cellDiam H x ^ 2 * ‖fderiv ℝ f (p x)‖ ^ 2 + 24 * Λ ^ 2 * cellDiam H x ^ 4) ≤
      3 * ∑ x ∈ vFin H D, ‖fderiv ℝ f (p x)‖ ^ 2 * (cellDiam H x ^ 2 * G.deg x) +
        24 * Λ ^ 2 * δ ^ 2 * ∑ x ∈ vFin H D, cellDiam H x ^ 2 * G.deg x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x hx => ?_
    have hd0 := cellDiam_nonneg H x
    have hd2 : cellDiam H x ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hd0 (hδ x hx) 2
    have hdeg : (0 : ℝ) ≤ G.deg x := Nat.cast_nonneg _
    have : cellDiam H x ^ 4 = cellDiam H x ^ 2 * cellDiam H x ^ 2 := by ring
    rw [this]
    have h24 : 0 ≤ 24 * Λ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hd2 (mul_nonneg h24 (mul_nonneg hdeg (sq_nonneg
      (cellDiam H x))))]
  have hF := cellSum_le_lintegral H hDo hDb p hp hLipF hLF hδ hMF hbd
  have h1 := cellSum_one_le H hDo hDb hbd
  calc ENNReal.ofReal (energy G (vFin H D) (f ∘ p))
      ≤ ENNReal.ofReal (3 * ∑ x ∈ vFin H D, ‖fderiv ℝ f (p x)‖ ^ 2 * (cellDiam H x ^ 2 * G.deg x) +
        24 * Λ ^ 2 * δ ^ 2 * ∑ x ∈ vFin H D, cellDiam H x ^ 2 * G.deg x) :=
        ENNReal.ofReal_le_ofReal (hE.trans hsplit)
    _ ≤ 3 * ∑ x ∈ vFin H D, ENNReal.ofReal (‖fderiv ℝ f (p x)‖ ^ 2 * (cellDiam H x ^ 2 * G.deg x)) +
        ENNReal.ofReal (24 * Λ ^ 2 * δ ^ 2) *
          ∑ x ∈ vFin H D, ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x) := by
        refine ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_)
        · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg fun x _ => by
            positivity]
          simp
        · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg fun x _ => by
            positivity]
    _ ≤ _ := by gcongr

/-- **[18] Lemma 3.3**, deterministic form: on the Lemma 2.7 event (`δ` bounds the cell diameters) and
The Proposition 2.10 inputs for `(D, |∇f|²)`, `(D, 1)` and `(Ω, g)`,
`Energy(f^ε; G(D)) ≤ 3 [A Energy(f; D) + η + L_F δ (A area(D) + η) + M_F (A ∫_Ω g + η)]
  + 24 Λ² δ² [A area(D) + η + A ∫_Ω g + η]`. -/
theorem lemma33 {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {O : Set ℂ} (hO : IsOpen O) {f : ℂ → ℝ} (hdf : DifferentiableOn ℝ f O) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hLip : ∀ u ∈ O, ∀ v ∈ O, ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ Λ * ‖u - v‖)
    (p : V → ℂ) (hp : ∀ x, p x ∈ H.cell x)
    (hseg : ∀ x ∈ vFin H D, ∀ y ∈ vFin H D, G.adj.Adj x y → segment ℝ (p x) (p y) ⊆ O)
    {LF MF δ : ℝ} (hLF : 0 ≤ LF)
    (hLipF : ∀ z ∈ D, ∀ w ∈ D, ‖fderiv ℝ f z‖ ^ 2 ≤ ‖fderiv ℝ f w‖ ^ 2 + LF * dist z w)
    (hMF : ∀ x ∈ vFin H D, ‖fderiv ℝ f (p x)‖ ^ 2 ≤ MF)
    (hδ : ∀ x ∈ vFin H D, cellDiam H x ≤ δ)
    {Ω : Set ℂ} {g : ℂ → ℝ}
    (hbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      H.cell x ⊆ Ω ∧ ∀ z ∈ H.cell x, 1 ≤ g z)
    {A η : ℝ} (hF : Prop210Bound H D (fun z => ‖fderiv ℝ f z‖ ^ 2) A η)
    (h1 : Prop210Bound H D (fun _ => 1) A η) (hg : Prop210Bound H Ω g A η) :
    ENNReal.ofReal (energy G (vFin H D) (f ∘ p)) ≤
      3 * ((ENNReal.ofReal A * eucEnergy f D + ENNReal.ofReal η) +
        ENNReal.ofReal (LF * δ) * (ENNReal.ofReal A * volume D + ENNReal.ofReal η) +
        ENNReal.ofReal MF * (ENNReal.ofReal A * (∫⁻ z in Ω, ENNReal.ofReal (g z)) +
          ENNReal.ofReal η)) +
      ENNReal.ofReal (24 * Λ ^ 2 * δ ^ 2) * ((ENNReal.ofReal A * volume D + ENNReal.ofReal η) +
        (ENNReal.ofReal A * (∫⁻ z in Ω, ENNReal.ofReal (g z)) + ENNReal.ofReal η)) := by
  refine (energy_comp_le_lintegral H hDo hDb hO hdf hΛ hLip p hp hseg hLF hLipF hMF hδ
    hbd).trans ?_
  have h1' : (∫⁻ z in D, uDens H z) ≤ ENNReal.ofReal A * volume D + ENNReal.ofReal η := by
    have := h1
    unfold Prop210Bound at this
    simpa only [ENNReal.ofReal_one, one_mul, setLIntegral_const, Measure.restrict_apply_univ]
      using this
  have hF' := hF
  unfold Prop210Bound at hF'
  gcongr
  · exact hF'
  · exact hg
  · exact hg

end MatedCRTHarmonic.GMS3
