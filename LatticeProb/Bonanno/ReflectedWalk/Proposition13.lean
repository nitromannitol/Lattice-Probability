/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Proposition13 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.DirichletSpace
import LatticeProb.Bonanno.ReflectedWalk.LaplacianSummable
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Data.Prod.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.FieldSimp

/-!
# Proposition 1.3: energy-minimizing extensions (Gwynne–Sung, Section 2.1)

For a non-empty finite `A ⊆ V` and `φ : V → ℝ`, the paper's `h_φ` is the unique function
agreeing with `φ` on `A` whose Dirichlet energy is minimal among all such functions; it is
discrete harmonic off `A`, has finite energy, and depends linearly on `φ`.

## Construction (paper (2.4)–(2.5), in the function-space model of `DirichletSpace.lean`)

Fix a basepoint `a₀ ∈ A`.  Let `φ̂` be `φ` on `A` and `0` off `A`; it has finite energy
because `A` is finite and `π < ∞` on `A` (`hasFiniteEnergy_extendZero`).  Then
`v := φ̂ − φ(a₀)·1 ∈ D₀`, and with `P` the orthogonal projection of `D₀` onto the closed
subspace `D_A = zeroOn a₀ A`,

  `f_φ := P v`,   `h_φ := φ̂ − f_φ`   (`energyMinAux`).

Every competitor `f` (finite energy, `f = φ` on `A`) is `φ̂ − w` for `w := φ̂ − f ∈ D_A`, and
`Energy f = ‖v − w‖²` by translation invariance of the energy (`energy_extendZero_sub`).  So
minimality and uniqueness of `h_φ` are exactly the minimizing property and the uniqueness of
the orthogonal projection (`Submodule.starProjection_minimal`,
`Submodule.norm_eq_iInf_iff_inner_eq_zero`), and linearity of `φ ↦ h_φ` is linearity of `P`.

Harmonicity off `A` is the paper's contradiction argument (p. 14): absolute convergence of the
Laplacian sum is Contract D (`absSummableAt_of_hasFiniteEnergy`), and if the Laplacian at
`x ∉ A` did not vanish, moving the value at `x` to the `π`-average would strictly lower the
energy (`energy_update`), contradicting minimality.

The public interface `energyMin` / `energyMin_*` (Contract A) is basepoint-free: the basepoint
is chosen once from `A.Nonempty`, and uniqueness shows the choice is immaterial.
-/

namespace ReflectedWalk

namespace ConductanceGraph

open Classical

variable {V : Type*} (G : ConductanceGraph V)

/-! ### Finitely supported functions have finite energy -/

/-- A function supported on a finite set has finite energy, because `π < ∞` on the support
(Gwynne–Sung, proof of Proposition 1.3: `Energy(φ̂) < ∞`). -/
lemma hasFiniteEnergy_of_support_subset {f : V → ℝ} (A : Finset V) (hf : ∀ x ∉ A, f x = 0) :
    G.HasFiniteEnergy f := by
  have hF : Summable fun p : V × V => G.c p.1 p.2 * f p.1 ^ 2 := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (G.c_nonneg _ _) (sq_nonneg _))]
    refine ⟨fun x => ?_, ?_⟩
    · show Summable fun y => G.c x y * f x ^ 2
      exact (G.summable_c x).mul_right _
    · show Summable fun x => ∑' y, G.c x y * f x ^ 2
      refine summable_of_ne_finset_zero (s := A) fun x hx => ?_
      simp [hf x hx]
  have hF' : Summable fun p : V × V => G.c p.1 p.2 * f p.2 ^ 2 := by
    refine hF.prod_symm.congr fun p => ?_
    show G.c p.swap.1 p.swap.2 * f p.swap.1 ^ 2 = G.c p.1 p.2 * f p.2 ^ 2
    rw [Prod.fst_swap, Prod.snd_swap, G.c_symm]
  refine Summable.of_nonneg_of_le (fun p => G.gradSq_nonneg f p) (fun p => ?_)
    ((hF.mul_left 2).add (hF'.mul_left 2))
  simp only [gradSq]
  have hc := G.c_nonneg p.1 p.2
  nlinarith [mul_nonneg hc (sq_nonneg (f p.2 + f p.1))]

/-- `φ̂`: the extension of `φ|_A` by zero (Gwynne–Sung, proof of Proposition 1.3). -/
noncomputable def extendZero (A : Finset V) (φ : V → ℝ) : V → ℝ :=
  fun x => if x ∈ A then φ x else 0

lemma extendZero_of_mem {A : Finset V} (φ : V → ℝ) {x : V} (hx : x ∈ A) :
    extendZero A φ x = φ x := ite_eq_left hx

lemma extendZero_of_not_mem {A : Finset V} (φ : V → ℝ) {x : V} (hx : x ∉ A) :
    extendZero A φ x = 0 := ite_eq_right hx

lemma hasFiniteEnergy_extendZero (A : Finset V) (φ : V → ℝ) :
    G.HasFiniteEnergy (extendZero A φ) :=
  G.hasFiniteEnergy_of_support_subset A fun _ hx => extendZero_of_not_mem φ hx

lemma extendZero_add (A : Finset V) (φ ψ : V → ℝ) :
    extendZero A (φ + ψ) = extendZero A φ + extendZero A ψ := by
  funext x
  simp only [extendZero, Pi.add_apply]
  split_ifs <;> simp

lemma extendZero_smul (A : Finset V) (a : ℝ) (φ : V → ℝ) :
    extendZero A (a • φ) = a • extendZero A φ := by
  funext x
  simp only [extendZero, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-! ### Two facts about orthogonal projections -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal projection minimizes the distance to the subspace
(unbundled form of `Submodule.starProjection_minimal`). -/
lemma norm_sub_starProjection_le (K : Submodule ℝ E) [K.HasOrthogonalProjection] (v : E)
    {w : E} (hw : w ∈ K) : ‖v - K.starProjection v‖ ≤ ‖v - w‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨w, hw⟩ : K)

/-- A point of `K` at least as close to `v` as every point of `K` is the projection of `v`
(uniqueness of the minimizer, via `Submodule.norm_eq_iInf_iff_inner_eq_zero`). -/
lemma eq_starProjection_of_forall_norm_le {K : Submodule ℝ E} [K.HasOrthogonalProjection]
    {v w : E} (hw : w ∈ K) (h : ∀ w' ∈ K, ‖v - w‖ ≤ ‖v - w'‖) : K.starProjection v = w := by
  have hinf : ‖v - w‖ = ⨅ w' : K, ‖v - w'‖ :=
    le_antisymm (le_ciInf fun w' => h w' w'.2)
      (ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨w, hw⟩ : K))
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hw
    ((Submodule.norm_eq_iInf_iff_inner_eq_zero K hw).1 hinf)

end Projection

/-! ### The construction with an explicit basepoint -/

section Construction

variable (hG : G.toSimpleGraph.Connected) {A : Finset V} {a₀ : V}

/-- The vector `v = φ̂ − φ(a₀)·1 ∈ D₀` whose projection onto `D_A` defines `f_φ` (2.4). -/
noncomputable def shiftedExt (ha₀ : a₀ ∈ A) (φ : V → ℝ) : G.DirichletSpace hG a₀ :=
  DirichletSpace.mk (fun x => extendZero A φ x - φ a₀)
    ((G.hasFiniteEnergy_extendZero A φ).sub_const _)
    (by simp [extendZero_of_mem φ ha₀])

@[simp] lemma shiftedExt_apply (ha₀ : a₀ ∈ A) (φ : V → ℝ) (x : V) :
    G.shiftedExt hG ha₀ φ x = extendZero A φ x - φ a₀ := rfl

lemma shiftedExt_add (ha₀ : a₀ ∈ A) (φ ψ : V → ℝ) :
    G.shiftedExt hG ha₀ (φ + ψ) = G.shiftedExt hG ha₀ φ + G.shiftedExt hG ha₀ ψ := by
  ext x
  simp only [DirichletSpace.add_apply, shiftedExt_apply, extendZero_add, Pi.add_apply]
  ring

lemma shiftedExt_smul (ha₀ : a₀ ∈ A) (a : ℝ) (φ : V → ℝ) :
    G.shiftedExt hG ha₀ (a • φ) = a • G.shiftedExt hG ha₀ φ := by
  ext x
  simp only [DirichletSpace.smul_apply, shiftedExt_apply, extendZero_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The energy-minimizing extension with an explicit basepoint `a₀ ∈ A`:
`h_φ = φ̂ − f_φ` with `f_φ = P(φ̂ − φ(a₀))`, `P` the orthogonal projection onto `D_A`
(Gwynne–Sung (2.4)–(2.5)). -/
noncomputable def energyMinAux (ha₀ : a₀ ∈ A) (φ : V → ℝ) : V → ℝ :=
  fun x => extendZero A φ x - (G.zeroOn hG a₀ A).starProjection (G.shiftedExt hG ha₀ φ) x

/-- `h_φ = (v − P v) + φ(a₀)` pointwise. -/
lemma energyMinAux_eq (ha₀ : a₀ ∈ A) (φ : V → ℝ) (x : V) :
    G.energyMinAux hG ha₀ φ x =
      (G.shiftedExt hG ha₀ φ - (G.zeroOn hG a₀ A).starProjection (G.shiftedExt hG ha₀ φ)) x
        + φ a₀ := by
  simp only [energyMinAux, DirichletSpace.sub_apply, shiftedExt_apply]
  ring

lemma energyMinAux_hasFiniteEnergy (ha₀ : a₀ ∈ A) (φ : V → ℝ) :
    G.HasFiniteEnergy (G.energyMinAux hG ha₀ φ) := by
  have h := (G.shiftedExt hG ha₀ φ -
    (G.zeroOn hG a₀ A).starProjection (G.shiftedExt hG ha₀ φ)).hasFiniteEnergy.add_const (φ a₀)
  convert h using 1
  exact funext (G.energyMinAux_eq hG ha₀ φ)

/-- `Energy(h_φ) = ‖v − P v‖²`. -/
lemma energy_energyMinAux (ha₀ : a₀ ∈ A) (φ : V → ℝ) :
    G.Energy (G.energyMinAux hG ha₀ φ) =
      ‖G.shiftedExt hG ha₀ φ - (G.zeroOn hG a₀ A).starProjection (G.shiftedExt hG ha₀ φ)‖ ^ 2 := by
  rw [funext (G.energyMinAux_eq hG ha₀ φ), G.Energy_add_const, DirichletSpace.norm_sq_eq_energy]

lemma energyMinAux_eqOn (ha₀ : a₀ ∈ A) (φ : V → ℝ) :
    Set.EqOn (G.energyMinAux hG ha₀ φ) φ ↑A := by
  intro a ha
  have ha' : a ∈ A := Finset.mem_coe.1 ha
  simp only [energyMinAux, extendZero_of_mem φ ha']
  rw [G.mem_zeroOn.1 ((G.zeroOn hG a₀ A).starProjection_apply_mem _) a ha', sub_zero]

/-- For `w ∈ D₀`, the function `φ̂ − w` has finite energy. -/
lemma hasFiniteEnergy_extendZero_sub (φ : V → ℝ) (w : G.DirichletSpace hG a₀) :
    G.HasFiniteEnergy (fun x => extendZero A φ x - w x) :=
  (G.hasFiniteEnergy_extendZero A φ).sub w.hasFiniteEnergy

/-- For `w ∈ D_A`, the function `φ̂ − w` agrees with `φ` on `A`. -/
lemma extendZero_sub_eqOn (φ : V → ℝ) {w : G.DirichletSpace hG a₀} (hw : w ∈ G.zeroOn hG a₀ A) :
    Set.EqOn (fun x => extendZero A φ x - w x) φ ↑A := by
  intro a ha
  have ha' : a ∈ A := Finset.mem_coe.1 ha
  show extendZero A φ a - w a = φ a
  rw [extendZero_of_mem φ ha', G.mem_zeroOn.1 hw a ha', sub_zero]

/-- `Energy(φ̂ − w) = ‖v − w‖²` for `w ∈ D₀` (translation invariance of the energy). -/
lemma energy_extendZero_sub (ha₀ : a₀ ∈ A) (φ : V → ℝ) (w : G.DirichletSpace hG a₀) :
    G.Energy (fun x => extendZero A φ x - w x) = ‖G.shiftedExt hG ha₀ φ - w‖ ^ 2 := by
  rw [DirichletSpace.norm_sq_eq_energy]
  have h : ⇑(G.shiftedExt hG ha₀ φ - w) = fun x => (extendZero A φ x - w x) - φ a₀ := by
    funext x
    simp only [DirichletSpace.sub_apply, shiftedExt_apply]
    ring
  rw [h, G.Energy_sub_const]

/-- A competitor `f` — finite energy, `f = φ` on `A` — gives the vector `w = φ̂ − f ∈ D_A`. -/
noncomputable def competitor (ha₀ : a₀ ∈ A) (φ : V → ℝ) {f : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hfA : Set.EqOn f φ ↑A) : G.DirichletSpace hG a₀ :=
  DirichletSpace.mk (fun x => extendZero A φ x - f x)
    ((G.hasFiniteEnergy_extendZero A φ).sub hf)
    (by simp [extendZero_of_mem φ ha₀, hfA (Finset.mem_coe.2 ha₀)])

lemma competitor_mem (ha₀ : a₀ ∈ A) (φ : V → ℝ) {f : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hfA : Set.EqOn f φ ↑A) : G.competitor hG ha₀ φ hf hfA ∈ G.zeroOn hG a₀ A := by
  intro a ha
  show extendZero A φ a - f a = 0
  rw [extendZero_of_mem φ ha, hfA (Finset.mem_coe.2 ha), sub_self]

/-- `Energy f = ‖v − w‖²` for a competitor `f` with `w = φ̂ − f`. -/
lemma energy_eq_norm_sub_competitor (ha₀ : a₀ ∈ A) (φ : V → ℝ) {f : V → ℝ}
    (hf : G.HasFiniteEnergy f) (hfA : Set.EqOn f φ ↑A) :
    G.Energy f = ‖G.shiftedExt hG ha₀ φ - G.competitor hG ha₀ φ hf hfA‖ ^ 2 := by
  rw [← G.energy_extendZero_sub hG ha₀ φ]
  congr 1
  funext x
  simp [competitor]

/-- **Minimality** (Proposition 1.3): `h_φ` has the least energy among finite-energy functions
agreeing with `φ` on `A`. -/
theorem energyMinAux_le_energy (ha₀ : a₀ ∈ A) (φ : V → ℝ) {f : V → ℝ}
    (hf : G.HasFiniteEnergy f) (hfA : Set.EqOn f φ ↑A) :
    G.Energy (G.energyMinAux hG ha₀ φ) ≤ G.Energy f := by
  rw [G.energy_energyMinAux, G.energy_eq_norm_sub_competitor hG ha₀ φ hf hfA]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_sub_starProjection_le _ _ (G.competitor_mem hG ha₀ φ hf hfA)) 2

/-- **Uniqueness** (Proposition 1.3): any minimizer equals `h_φ`. -/
theorem energyMinAux_unique (ha₀ : a₀ ∈ A) (φ : V → ℝ) {f : V → ℝ}
    (hf : G.HasFiniteEnergy f) (hfA : Set.EqOn f φ ↑A)
    (hmin : ∀ g : V → ℝ, G.HasFiniteEnergy g → Set.EqOn g φ ↑A → G.Energy f ≤ G.Energy g) :
    f = G.energyMinAux hG ha₀ φ := by
  have hP : (G.zeroOn hG a₀ A).starProjection (G.shiftedExt hG ha₀ φ) =
      G.competitor hG ha₀ φ hf hfA := by
    refine eq_starProjection_of_forall_norm_le (G.competitor_mem hG ha₀ φ hf hfA)
      fun w' hw' => ?_
    have h1 := hmin _ (G.hasFiniteEnergy_extendZero_sub hG (A := A) φ w')
      (G.extendZero_sub_eqOn hG φ hw')
    rw [G.energy_eq_norm_sub_competitor hG ha₀ φ hf hfA,
      G.energy_extendZero_sub hG ha₀ φ w'] at h1
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
  funext x
  simp only [energyMinAux, hP]
  simp [competitor]

/-! ### Harmonicity off `A` -/

/-- Moving the value of `h` at a single vertex `x` by `t` changes the energy by
`t² π(x) − 2t ∑_y c(x,y)(h y − h x)`: the "differentiate" step of Gwynne–Sung p. 14.
Absolute summability of the Laplacian at `x` is the hypothesis of footnote 2. -/
lemma energy_update {h : V → ℝ} (hh : G.HasFiniteEnergy h) {x : V} (hx : G.AbsSummableAt h x)
    (t : ℝ) :
    G.HasFiniteEnergy (Function.update h x (h x + t)) ∧
      G.Energy (Function.update h x (h x + t)) =
        G.Energy h + (t ^ 2 * G.pi x - 2 * t * ∑' y, G.lapTerm h x y) := by
  have hlap : Summable (G.lapTerm h x) := Summable.of_abs ((G.absSummableAt_iff h x).1 hx)
  have hsum : HasSum (fun y => t ^ 2 * G.c x y - 2 * t * G.lapTerm h x y)
      (t ^ 2 * G.pi x - 2 * t * ∑' y, G.lapTerm h x y) :=
    ((G.summable_c x).hasSum.mul_left _).sub (hlap.hasSum.mul_left _)
  have hd₁ : HasSum
      (fun p : V × V => if p.1 = x then t ^ 2 * G.c x p.2 - 2 * t * G.lapTerm h x p.2 else 0)
      (t ^ 2 * G.pi x - 2 * t * ∑' y, G.lapTerm h x y) := by
    refine ((Prod.mk_right_injective x).hasSum_iff ?_).1 ?_
    · rintro ⟨a, b⟩ hp
      simp only [Set.mem_range, Prod.mk.injEq, not_exists] at hp
      exact ite_eq_right fun hax => hp b ⟨hax.symm, rfl⟩
    · simpa [Function.comp_def] using hsum
  have hd₂ : HasSum
      (fun p : V × V => if p.2 = x then t ^ 2 * G.c x p.1 - 2 * t * G.lapTerm h x p.1 else 0)
      (t ^ 2 * G.pi x - 2 * t * ∑' y, G.lapTerm h x y) := by
    refine ((Prod.mk_left_injective x).hasSum_iff ?_).1 ?_
    · rintro ⟨a, b⟩ hp
      simp only [Set.mem_range, Prod.mk.injEq, not_exists] at hp
      exact ite_eq_right fun hbx => hp a ⟨rfl, hbx.symm⟩
    · simpa [Function.comp_def] using hsum
  have hpt : ∀ p : V × V, G.gradSq (Function.update h x (h x + t)) p =
      G.gradSq h p +
        ((if p.1 = x then t ^ 2 * G.c x p.2 - 2 * t * G.lapTerm h x p.2 else 0) +
          (if p.2 = x then t ^ 2 * G.c x p.1 - 2 * t * G.lapTerm h x p.1 else 0)) := by
    rintro ⟨a, b⟩
    simp only [gradSq, lapTerm]
    by_cases ha : a = x <;> by_cases hb : b = x
    · simp [ha, hb, G.c_self]
    · simp [ha, hb]
      ring
    · simp [hb, ha]
      rw [G.c_symm a x]
      ring
    · simp [ha, hb]
  have htot : HasSum (G.gradSq (Function.update h x (h x + t)))
      (2 * G.Energy h + ((t ^ 2 * G.pi x - 2 * t * ∑' y, G.lapTerm h x y) +
        (t ^ 2 * G.pi x - 2 * t * ∑' y, G.lapTerm h x y))) := by
    have h1 := hh.hasSum.add (hd₁.add hd₂)
    rw [G.tsum_gradSq_eq] at h1
    rw [funext hpt]
    exact h1
  refine ⟨htot.summable, ?_⟩
  rw [Energy, htot.tsum_eq]
  ring

/-- **Harmonicity off `A`** (Proposition 1.3, Gwynne–Sung p. 14): if the Laplacian of `h_φ` at
`x ∉ A` did not vanish, replacing `h_φ(x)` by the `π`-average `(1/π(x)) ∑_y c(x,y) h_φ(y)` would
strictly lower the energy while keeping the boundary values, contradicting minimality. -/
theorem energyMinAux_isHarmonicOn (ha₀ : a₀ ∈ A) (φ : V → ℝ) :
    G.IsHarmonicOn (G.energyMinAux hG ha₀ φ) (↑A : Set V)ᶜ := by
  intro x hx
  have hxA : x ∉ A := fun h => hx (Finset.mem_coe.2 h)
  set h := G.energyMinAux hG ha₀ φ with hh
  have hfe : G.HasFiniteEnergy h := G.energyMinAux_hasFiniteEnergy hG ha₀ φ
  have habs := G.absSummableAt_of_hasFiniteEnergy hfe x
  refine ⟨habs, ?_⟩
  by_contra hne
  have : Nontrivial V := ⟨⟨a₀, x, fun h' => hxA (h' ▸ ha₀)⟩⟩
  have hπ : 0 < G.pi x := G.pi_pos_of_connected hG x
  obtain ⟨L, hL⟩ : ∃ L, ∑' y, G.lapTerm h x y = L := ⟨_, rfl⟩
  rw [hL] at hne
  obtain ⟨hfin, hE⟩ := G.energy_update hfe habs (L / G.pi x)
  rw [hL] at hE
  have hlt : G.Energy (Function.update h x (h x + L / G.pi x)) < G.Energy h := by
    rw [hE]
    have hπ' : G.pi x ≠ 0 := hπ.ne'
    have h1 : (L / G.pi x) ^ 2 * G.pi x - 2 * (L / G.pi x) * L = -(L ^ 2 / G.pi x) := by
      field_simp
      ring
    have h2 : 0 < L ^ 2 / G.pi x := div_pos (sq_pos_iff.2 hne) hπ
    linarith
  have hEq : Set.EqOn (Function.update h x (h x + L / G.pi x)) φ ↑A := by
    intro a ha
    have hax : a ≠ x := fun h' => hxA (h' ▸ Finset.mem_coe.1 ha)
    rw [Function.update_of_ne hax]
    exact G.energyMinAux_eqOn hG ha₀ φ ha
  exact absurd (G.energyMinAux_le_energy hG ha₀ φ hfin hEq) (not_le.2 hlt)

/-! ### Linearity -/

lemma energyMinAux_add (ha₀ : a₀ ∈ A) (φ ψ : V → ℝ) :
    G.energyMinAux hG ha₀ (φ + ψ) = G.energyMinAux hG ha₀ φ + G.energyMinAux hG ha₀ ψ := by
  funext x
  simp only [energyMinAux, shiftedExt_add, map_add, extendZero_add, Pi.add_apply,
    DirichletSpace.add_apply]
  ring

lemma energyMinAux_smul (ha₀ : a₀ ∈ A) (a : ℝ) (φ : V → ℝ) :
    G.energyMinAux hG ha₀ (a • φ) = a • G.energyMinAux hG ha₀ φ := by
  funext x
  simp only [energyMinAux, shiftedExt_smul, map_smul, extendZero_smul, Pi.smul_apply,
    DirichletSpace.smul_apply, smul_eq_mul]
  ring

end Construction

/-! ### Contract A: the basepoint-free interface -/

/-- **Proposition 1.3**: the energy-minimizing extension of `φ` off the finite set `A`.
Junk for `A = ∅`; every theorem about it assumes `A.Nonempty`.  The basepoint `a₀ ∈ A` of the
construction is chosen from `A.Nonempty`; by uniqueness (`energyMin_unique`) the result does
not depend on that choice. -/
noncomputable def energyMin (hG : G.toSimpleGraph.Connected) (A : Finset V) (φ : V → ℝ) :
    V → ℝ :=
  if h : A.Nonempty then G.energyMinAux hG h.choose_spec φ else 0

lemma energyMin_eq_aux (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (φ : V → ℝ) : G.energyMin hG A φ = G.energyMinAux hG hA.choose_spec φ := dite_eq_left hA

/-- Proposition 1.3: `h_φ|_A = φ`. -/
theorem energyMin_eqOn (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (φ : V → ℝ) : Set.EqOn (G.energyMin hG A φ) φ ↑A := by
  rw [G.energyMin_eq_aux hG hA]
  exact G.energyMinAux_eqOn hG hA.choose_spec φ

/-- Proposition 1.3: `h_φ` has finite Dirichlet energy. -/
theorem energyMin_hasFiniteEnergy (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) (φ : V → ℝ) : G.HasFiniteEnergy (G.energyMin hG A φ) := by
  rw [G.energyMin_eq_aux hG hA]
  exact G.energyMinAux_hasFiniteEnergy hG hA.choose_spec φ

/-- Proposition 1.3: `Energy(h_φ)` is minimal among finite-energy `f` with `f|_A = φ`.
Competitors are restricted to finite energy because mathlib's `tsum` of a non-summable family
is `0` (see `INTERFACES.md`). -/
theorem energyMin_le_energy (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) (φ : V → ℝ) {f : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hfA : Set.EqOn f φ ↑A) : G.Energy (G.energyMin hG A φ) ≤ G.Energy f := by
  rw [G.energyMin_eq_aux hG hA]
  exact G.energyMinAux_le_energy hG hA.choose_spec φ hf hfA

/-- Proposition 1.3: uniqueness of the energy minimizer. -/
theorem energyMin_unique (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) (φ : V → ℝ) {f : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hfA : Set.EqOn f φ ↑A)
    (hmin : ∀ g : V → ℝ, G.HasFiniteEnergy g → Set.EqOn g φ ↑A → G.Energy f ≤ G.Energy g) :
    f = G.energyMin hG A φ := by
  rw [G.energyMin_eq_aux hG hA]
  exact G.energyMinAux_unique hG hA.choose_spec φ hf hfA hmin

/-- Proposition 1.3: `h_φ` is discrete harmonic on `V ∖ A` (Definition 1.2, including the
absolute convergence of footnote 2). -/
theorem energyMin_isHarmonicOn (hG : G.toSimpleGraph.Connected) {A : Finset V}
    (hA : A.Nonempty) (φ : V → ℝ) : G.IsHarmonicOn (G.energyMin hG A φ) (↑A : Set V)ᶜ := by
  rw [G.energyMin_eq_aux hG hA]
  exact G.energyMinAux_isHarmonicOn hG hA.choose_spec φ

/-- `h_φ` depends only on `φ|_A` (the paper's `ϕ : A → ℝ`). -/
theorem energyMin_congr (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {φ ψ : V → ℝ} (h : Set.EqOn φ ψ ↑A) : G.energyMin hG A φ = G.energyMin hG A ψ :=
  G.energyMin_unique hG hA ψ (G.energyMin_hasFiniteEnergy hG hA φ)
    (fun _ ha => (G.energyMin_eqOn hG hA φ ha).trans (h ha))
    (fun _ hg hgA => G.energyMin_le_energy hG hA φ hg fun _ ha => (hgA ha).trans (h ha).symm)

/-- Proposition 1.3: `φ ↦ h_φ` is additive. -/
theorem energyMin_add (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (φ ψ : V → ℝ) :
    G.energyMin hG A (φ + ψ) = G.energyMin hG A φ + G.energyMin hG A ψ := by
  simp only [G.energyMin_eq_aux hG hA]
  exact G.energyMinAux_add hG hA.choose_spec φ ψ

/-- Proposition 1.3: `φ ↦ h_φ` is homogeneous. -/
theorem energyMin_smul (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (a : ℝ) (φ : V → ℝ) : G.energyMin hG A (a • φ) = a • G.energyMin hG A φ := by
  simp only [G.energyMin_eq_aux hG hA]
  exact G.energyMinAux_smul hG hA.choose_spec a φ

/-- Constants are their own energy-minimizing extensions (they have zero energy). -/
theorem energyMin_const (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    (a : ℝ) : G.energyMin hG A (Function.const V a) = Function.const V a :=
  (G.energyMin_unique hG hA (Function.const V a) (f := Function.const V a)
    (G.hasFiniteEnergy_const a) (fun _ _ => rfl)
    fun g _ _ => (le_of_eq (G.Energy_const a)).trans (G.Energy_nonneg g)).symm

end ConductanceGraph

end ReflectedWalk
