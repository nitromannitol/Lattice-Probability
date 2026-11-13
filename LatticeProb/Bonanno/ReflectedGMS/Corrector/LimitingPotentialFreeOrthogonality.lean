/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.LimitingPotentialFreeOrthogonality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteMinimizerPointwiseConvergence
import LatticeProb.Bonanno.ReflectedGMS.Forms.AnchoredTraceMinimizer

/-!
# The local free-orthogonality identity for the limiting potential (`s:eq:freeorth`)

`Corrector/LimitingHarmonicPotential.lean` constructs the anchored limit `Φ` of the
approximants `φ_j` and supplies, on every patch, pointwise convergence, finite patch energy
of `Φ - φ_j`, patch-energy convergence `restrictedEnergy G S (Φ - φ_j) → 0`, and pointwise
discrete harmonicity of `Φ`. Pointwise harmonicity is *not* the variational identity: on an
infinite patch it does not by itself give
`⟪∇Φ, ∇v⟫ = 0` for every finite-energy variation `v` vanishing off a bounded rectangle,
because that pairing is an infinite sum which pointwise harmonicity cannot be summed into.

This file proves the missing identity, for the **full** finite-energy zero-trace variation
space `zeroTraceSubmodule G Rᶜ` of `Analysis/AnchoredEnergy.lean` — the same space used by
`exists_anchored_trace_minimizer` — with no finite-support closure and no finiteness
assumption on the rectangle `R`.

## Mechanism

*Localization.* If `v` vanishes off `R` and the patch `S` contains `R` together with all
`G`-neighbours of `R`, then the Dirichlet density `gradProd f v` is supported in `S × S`
for **every** `f`. Hence `G.dirichletForm f v` equals the Dirichlet form of the restricted
graph `restrictGraph G S` applied to the restrictions (`dirichletForm_eq_restricted`); no
global finite energy of `f` is needed, which matters because the corrector has infinite
total energy.

*Transfer.* Inside the restricted graph the pairing is the inner product of the existing
edge Hilbert space (`inner_weightedGradient`), so it is continuous in the energy norm:
`|⟪∇(Ψ - ψ_j), ∇v⟫| ≤ √(Energy (Ψ - ψ_j)) √(Energy v)`. Splitting
`⟪∇Ψ, ∇v⟫ = ⟪∇ψ_j, ∇v⟫ + ⟪∇(Ψ - ψ_j), ∇v⟫` and using the exact patch-energy convergence
supplied by the limit theorem passes the *actual* orthogonality of the approximants to the
limit (`dirichletForm_eq_zero_of_tendsto_energy`).

*Compatibility.* The eventual orthogonality of the approximants is the only non-metric
input. It is exactly the free-orthogonality clause of `exists_anchored_trace_minimizer` at
level `j`, valid for variations vanishing off the selected block `B j`; a variation
vanishing off `R` qualifies as soon as `R ⊆ B j`, i.e. eventually along a selected-block
exhaustion (`forall_dirichletForm_limit_eq_zero_of_block_exhaustion`).

*Consumer form.* From the identity, `Φ` restricted to the patch `S` is an honest full-energy
Dirichlet minimizer of `restrictGraph G S` for its own trace on `S \ R`
(`restrictedEnergy_le_of_free_orthogonality`), which is precisely the `hmin` hypothesis of
the componentwise maximum principle `FullEnergyTraceBounds`.
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace LimitingPotentialFreeOrthogonality

open Filter Topology
open FiniteDirichletEnergyLimit

/-! ### The Dirichlet pairing is continuous in the energy norm -/

section CauchySchwarz

variable {W : Type*} (H : ReflectedWalk.ConductanceGraph W)

/-- **Cauchy–Schwarz for the Dirichlet form.** The pairing is the inner product of the
existing edge Hilbert space, so it is bounded by the product of the energy norms. -/
theorem abs_dirichletForm_le_sqrt_mul_sqrt {f g : W → ℝ}
    (hf : H.HasFiniteEnergy f) (hg : H.HasFiniteEnergy g) :
    |H.dirichletForm f g| ≤ Real.sqrt (H.Energy f) * Real.sqrt (H.Energy g) := by
  have hinner := abs_real_inner_le_norm (weightedGradient H f hf) (weightedGradient H g hg)
  rw [inner_weightedGradient H f g hf hg] at hinner
  have hnf : Real.sqrt (H.Energy f) = ‖weightedGradient H f hf‖ := by
    rw [← weightedGradient_norm_sq H f hf, Real.sqrt_sq (norm_nonneg _)]
  have hng : Real.sqrt (H.Energy g) = ‖weightedGradient H g hg‖ := by
    rw [← weightedGradient_norm_sq H g hg, Real.sqrt_sq (norm_nonneg _)]
  rw [hnf, hng]
  exact hinner

/-- **Orthogonality passes to an energy limit.** If the approximants `ψ_j` are eventually
orthogonal to the finite-energy variation `v` and the energies of `Ψ - ψ_j` tend to zero,
then the limit is orthogonal to `v`. -/
theorem dirichletForm_eq_zero_of_tendsto_energy {ψ : ℕ → W → ℝ} {Ψ v : W → ℝ}
    (hψ : ∀ j, H.HasFiniteEnergy (ψ j))
    (hΔ : ∀ j, H.HasFiniteEnergy (Ψ - ψ j))
    (hv : H.HasFiniteEnergy v)
    (hE : Tendsto (fun j => H.Energy (Ψ - ψ j)) atTop (𝓝 0))
    (horth : ∀ᶠ j in atTop, H.dirichletForm (ψ j) v = 0) :
    H.dirichletForm Ψ v = 0 := by
  have hbound : ∀ᶠ j in atTop, |H.dirichletForm Ψ v|
      ≤ Real.sqrt (H.Energy (Ψ - ψ j)) * Real.sqrt (H.Energy v) := by
    filter_upwards [horth] with j hj
    have hfun : ψ j + (Ψ - ψ j) = Ψ := by
      funext z
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have hadd := H.dirichletForm_add_left (hψ j) (hΔ j) hv
    rw [hfun, hj, zero_add] at hadd
    rw [hadd]
    exact abs_dirichletForm_le_sqrt_mul_sqrt H (hΔ j) hv
  have hnull : Tendsto (fun j => Real.sqrt (H.Energy (Ψ - ψ j)) * Real.sqrt (H.Energy v))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => Real.sqrt (H.Energy (Ψ - ψ j))) atTop (𝓝 0) := by
      simpa using hE.sqrt
    simpa using h1.mul_const (Real.sqrt (H.Energy v))
  have hle : |H.dirichletForm Ψ v| ≤ 0 := ge_of_tendsto hnull hbound
  exact abs_eq_zero.1 (le_antisymm hle (abs_nonneg _))

end CauchySchwarz

/-! ### Localization of the pairing against a variation supported in a rectangle -/

section Localization

variable {V : Type*}

/-- The pair embedding of a patch into all ordered vertex pairs. -/
def pairEmbed (S : Set V) : ↥S × ↥S → V × V := fun q => ((q.1 : V), (q.2 : V))

theorem pairEmbed_injective (S : Set V) : Function.Injective (pairEmbed S) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [pairEmbed, Prod.mk.injEq] at h
  simp only [Prod.mk.injEq]
  exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

variable (G : ReflectedWalk.ConductanceGraph V)

theorem gradProd_pairEmbed (S : Set V) (f v : V → ℝ) (q : ↥S × ↥S) :
    G.gradProd f v (pairEmbed S q)
      = (restrictGraph G S).gradProd (fun z : S => f ↑z) (fun z : S => v ↑z) q := rfl

/-- Restricting a finite-energy function to a patch keeps finite energy in the patch
graph. -/
theorem hasFiniteEnergy_restrict (S : Set V) {v : V → ℝ} (hv : G.HasFiniteEnergy v) :
    (restrictGraph G S).HasFiniteEnergy (fun z : S => v ↑z) :=
  (hv.comp_injective (pairEmbed_injective S)).congr fun _ => rfl

/-- **The Dirichlet density of a rectangle variation lives on the patch.** If `v` vanishes
off `R`, the patch `S` contains `R`, and `S` contains every neighbour of every vertex of
`R`, then every ordered pair outside `S × S` contributes nothing to `gradProd f v`, for an
arbitrary `f`. -/
theorem gradProd_eq_zero_of_not_mem_range {R S : Set V} (hRS : R ⊆ S)
    (hnbr : ∀ x ∈ R, ∀ y : V, G.Adj x y → y ∈ S) {v : V → ℝ}
    (hv0 : ∀ x, x ∉ R → v x = 0) (f : V → ℝ) {p : V × V}
    (hp : p ∉ Set.range (pairEmbed S)) : G.gradProd f v p = 0 := by
  have hmem : ¬ (p.1 ∈ S ∧ p.2 ∈ S) := by
    rintro ⟨h1, h2⟩
    exact hp ⟨(⟨p.1, h1⟩, ⟨p.2, h2⟩), rfl⟩
  rcases (G.c_nonneg p.1 p.2).lt_or_eq with hc | hc
  · by_cases h1 : p.1 ∈ R
    · exact absurd ⟨hRS h1, hnbr p.1 h1 p.2 hc⟩ hmem
    · by_cases h2 : p.2 ∈ R
      · have hc' : G.Adj p.2 p.1 := by
          show (0:ℝ) < G.c p.2 p.1
          rw [G.c_symm]
          exact hc
        exact absurd ⟨hnbr p.2 h2 p.1 hc', hRS h2⟩ hmem
      · simp [ReflectedWalk.ConductanceGraph.gradProd, hv0 _ h1, hv0 _ h2]
  · simp [ReflectedWalk.ConductanceGraph.gradProd, ← hc]

/-- **The pairing against a rectangle variation is a patch quantity.** No finite energy of
`f` is assumed: only the support condition on `v` is used. -/
theorem dirichletForm_eq_restricted {R S : Set V} (hRS : R ⊆ S)
    (hnbr : ∀ x ∈ R, ∀ y : V, G.Adj x y → y ∈ S) {v : V → ℝ}
    (hv0 : ∀ x, x ∉ R → v x = 0) (f : V → ℝ) :
    G.dirichletForm f v
      = (restrictGraph G S).dirichletForm (fun z : S => f ↑z) (fun z : S => v ↑z) := by
  have hsupport : Function.support (G.gradProd f v) ⊆ Set.range (pairEmbed S) := by
    intro p hp
    by_contra hnot
    exact hp (gradProd_eq_zero_of_not_mem_range G hRS hnbr hv0 f hnot)
  have h := (pairEmbed_injective S).tsum_eq (f := G.gradProd f v) hsupport
  simp only [ReflectedWalk.ConductanceGraph.dirichletForm]
  rw [← h, tsum_congr fun q => gradProd_pairEmbed G S f v q]

/-- The zero extension of a patch variation vanishing off `R`. -/
noncomputable def extendZero (S : Set V) (w : ↥S → ℝ) : V → ℝ :=
  Function.extend (fun z : ↥S => (z : V)) w (fun _ => 0)

theorem extendZero_apply_coe (S : Set V) (w : ↥S → ℝ) (z : ↥S) :
    extendZero S w ↑z = w z :=
  Subtype.coe_injective.extend_apply w (fun _ => 0) z

theorem extendZero_restrict (S : Set V) (w : ↥S → ℝ) :
    (fun z : S => extendZero S w ↑z) = w :=
  funext fun z => extendZero_apply_coe S w z

theorem extendZero_eq_zero_of_not_mem (S : Set V) (w : ↥S → ℝ) {x : V} (hx : x ∉ S) :
    extendZero S w x = 0 :=
  Function.extend_apply' w (fun _ => 0) x (by rintro ⟨z, rfl⟩; exact hx z.2)

/-- The zero extension of a patch variation vanishing on `S \ R` vanishes off `R`. -/
theorem extendZero_eq_zero_of_not_mem_rectangle {R S : Set V} (w : ↥S → ℝ)
    (hw0 : ∀ z : ↥S, (z : V) ∉ R → w z = 0) :
    ∀ x, x ∉ R → extendZero S w x = 0 := by
  intro x hx
  by_cases hxS : x ∈ S
  · exact (extendZero_apply_coe S w ⟨x, hxS⟩).trans (hw0 ⟨x, hxS⟩ hx)
  · exact extendZero_eq_zero_of_not_mem S w hxS

/-- **The zero extension of a patch variation supported in the rectangle has finite full
energy.** The same support argument shows that its energy density lives on `S × S`. -/
theorem hasFiniteEnergy_extendZero {R S : Set V} (hRS : R ⊆ S)
    (hnbr : ∀ x ∈ R, ∀ y : V, G.Adj x y → y ∈ S) {w : ↥S → ℝ}
    (hw : (restrictGraph G S).HasFiniteEnergy w)
    (hw0 : ∀ z : ↥S, (z : V) ∉ R → w z = 0) :
    G.HasFiniteEnergy (extendZero S w) := by
  have hv0 : ∀ x, x ∉ R → extendZero S w x = 0 :=
    extendZero_eq_zero_of_not_mem_rectangle w hw0
  have hsupp : ∀ p, p ∉ Set.range (pairEmbed S) → G.gradSq (extendZero S w) p = 0 := by
    intro p hp
    rw [← G.gradProd_self (extendZero S w)]
    exact gradProd_eq_zero_of_not_mem_range G hRS hnbr hv0 _ hp
  have hcomp : ∀ q : ↥S × ↥S,
      (restrictGraph G S).gradSq w q = G.gradSq (extendZero S w) (pairEmbed S q) := by
    intro q
    show G.c ↑q.1 ↑q.2 * (w q.2 - w q.1) ^ 2
      = G.c ↑q.1 ↑q.2 * (extendZero S w ↑q.2 - extendZero S w ↑q.1) ^ 2
    rw [extendZero_apply_coe, extendZero_apply_coe]
  exact ((pairEmbed_injective S).summable_iff hsupp).1 (hw.congr hcomp)

end Localization

/-! ### The local variational identity for the limit -/

section FreeOrthogonality

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

end FreeOrthogonality

end LimitingPotentialFreeOrthogonality

end ReflectedGMS
