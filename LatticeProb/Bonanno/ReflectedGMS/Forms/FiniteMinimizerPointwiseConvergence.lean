/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteMinimizerPointwiseConvergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteDirichletEnergyLimit
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact

/-!
# The finite-level minimizers converge pointwise

`FiniteDirichletEnergyLimit` compares the finite anchored levels of
`AnchoredFiniteExhaustion` with the full anchored minimizer of `AnchoredTraceMinimizer`,
but its two main results are *conditional*: they assume a supplied pointwise limit `g` of
the extended level minimizers. This module discharges that premise.

The argument is the anchor-walk argument already used in `Analysis/AnchoredEnergy`, run at
the level of the restricted energies. For each vertex `x` we pin **one** finite walk `w`
from an anchor `a ∈ A` to `x`; its support is finite, hence contained in a single level
`L m`, and therefore in every later level. For `n ≥ m` the walk lives inside `L n`, so the
walk estimate `abs_sub_le_walkConst_mul` applied edge by edge inside the level (through the
already-checked block bound `sum_gradSq_le_two_restrictedEnergy`) gives

`|F n x - F n a| ≤ walkConst w * √(2 · restrictedEnergy G (L n) (F n))`,

and the level minimality tested against `u` bounds the level energies by `G.Energy u`
uniformly in `n`. Since `a` lies in `A ∩ L n` the trace hypothesis gives `F n a = u a`, so
`|F n x|` is bounded uniformly over the tail `n ≥ m`; adding the finite prefix
`∑_{k < m} |F k x|` gives a bound valid for *every* `n`.

The sequence `F` therefore lives in the product `∏ x, [-B x, B x]`, which is compact; on a
countable vertex type the product topology is second countable, hence first countable, so
`IsCompact.tendsto_subseq` extracts a subsequence converging pointwise. Every such cluster
point is the unique full anchored minimizer by
`eq_anchored_trace_minimizer_of_tendsto_pointwise`, and the usual subsequence criterion
upgrades this to convergence of the full sequence. Feeding the result back into
`tendsto_levelEnergy_of_tendsto_pointwise` makes the energy-limit theorem unconditional.

The graph may be disconnected, `A` may be infinite, no level is assumed connected, and no
finite-support closure is taken.
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace FiniteMinimizerPointwiseConvergence

open Filter Topology
open FiniteDirichletEnergyLimit

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-! ### The anchor-walk estimate inside a restricted energy -/

/-- **The single-edge increment bound for a restricted energy.** Both endpoints of the edge
lie in `S`, so the edge contributes to the restricted energy and the usual Cauchy–Schwarz
step applies with the restricted energy in place of the full one. -/
theorem abs_sub_le_of_adj_restrictedEnergy {S : Set V} {h : V → ℝ}
    (hS : (restrictGraph G S).HasFiniteEnergy (fun x : S => h ↑x))
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : G.toSimpleGraph.Adj x y) :
    |h y - h x| ≤ Real.sqrt (2 * restrictedEnergy G S h) / Real.sqrt (G.c x y) := by
  have hc : 0 < G.c x y := hxy
  have hkey : G.c x y * (h y - h x) ^ 2 ≤ 2 * restrictedEnergy G S h := by
    have hsum := sum_gradSq_le_two_restrictedEnergy G h hS {(x, y)} (by
      intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact ⟨hx, hy⟩)
    simpa [ReflectedWalk.ConductanceGraph.gradSq] using hsum
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hc)]
  have h1 : |h y - h x| * Real.sqrt (G.c x y) = Real.sqrt ((h y - h x) ^ 2 * G.c x y) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rw [h1]
  apply Real.sqrt_le_sqrt
  rw [mul_comm ((h y - h x) ^ 2)]
  exact hkey

/-- **The anchor-walk estimate for a restricted energy.** Along any walk of the full graph
whose support stays inside `S`, the increment of `h` is controlled by the *restricted*
energy on `S`, with the same walk constant as in `abs_sub_le_walkConst_mul`. -/
theorem abs_sub_le_walkConst_mul_restrictedEnergy {S : Set V} {h : V → ℝ}
    (hS : (restrictGraph G S).HasFiniteEnergy (fun x : S => h ↑x))
    {a b : V} (w : G.toSimpleGraph.Walk a b) (hsupp : ∀ y ∈ w.support, y ∈ S) :
    |h b - h a| ≤ G.walkConst w * Real.sqrt (2 * restrictedEnergy G S h) := by
  revert hsupp
  induction w with
  | nil =>
      intro _
      simp [ReflectedWalk.ConductanceGraph.walkConst]
  | @cons a' v' b' hadj p ih =>
      intro hsupp
      have hcons : (SimpleGraph.Walk.cons hadj p).support = a' :: p.support :=
        SimpleGraph.Walk.support_cons hadj p
      have ha' : a' ∈ S := hsupp a' (by rw [hcons]; exact List.Mem.head _)
      have hv' : v' ∈ S := hsupp v' (by rw [hcons]; exact List.Mem.tail _ p.start_mem_support)
      have hp : ∀ y ∈ p.support, y ∈ S := fun y hy =>
        hsupp y (by rw [hcons]; exact List.Mem.tail _ hy)
      have hstep : |h v' - h a'| ≤
          Real.sqrt (2 * restrictedEnergy G S h) / Real.sqrt (G.c a' v') :=
        abs_sub_le_of_adj_restrictedEnergy G hS ha' hv' hadj
      have hrest : |h b' - h v'| ≤ G.walkConst p * Real.sqrt (2 * restrictedEnergy G S h) :=
        ih hp
      have htri : |h b' - h a'| ≤ |h v' - h a'| + |h b' - h v'| := by
        have he : h b' - h a' = (h v' - h a') + (h b' - h v') := by ring
        rw [he]
        exact abs_add_le _ _
      refine htri.trans (le_of_le_of_eq (add_le_add hstep hrest) ?_)
      rw [ReflectedWalk.ConductanceGraph.walkConst]
      ring

section Levels

variable {A : Set V} {u : V → ℝ} {L : ℕ → Finset V} {F : ℕ → V → ℝ}

/-! ### Uniform pointwise bounds on the level minimizers -/

/-- **The level minimizers are bounded at every vertex, uniformly in the level.** One
finite anchor walk per vertex is pinned once and for all; it is eventually contained in
every level, where the walk estimate and the uniform energy bound `levelEnergy_le_energy`
apply, and the finitely many earlier levels are absorbed into the bound. -/
theorem exists_pointwise_uniform_bound (hA : BoundaryAnchored G A)
    (hu : G.HasFiniteEnergy u) (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n)) (F n) ≤ restrictedEnergy G (↑(L n)) w) :
    ∃ B : V → ℝ, ∀ (n : ℕ) (x : V), |F n x| ≤ B x := by
  classical
  have hEle : ∀ n, restrictedEnergy G (↑(L n) : Set V) (F n) ≤ G.Energy u := fun n =>
    levelEnergy_le_energy G hmin hu (fun a _ => rfl) n
  have key : ∀ x : V, ∃ b : ℝ, ∀ n : ℕ, |F n x| ≤ b := by
    intro x
    obtain ⟨a, haA, hreach⟩ := hA x
    obtain ⟨w⟩ := hreach.symm
    obtain ⟨m, hm⟩ := exists_level_superset hmono hcover w.support.toFinset
    have hwc : 0 ≤ G.walkConst w := G.walkConst_nonneg w
    have htail : ∀ n : ℕ, m ≤ n →
        |F n x| ≤ |u a| + G.walkConst w * Real.sqrt (2 * G.Energy u) := by
      intro n hn
      have hsupp : ∀ y ∈ w.support, y ∈ (↑(L n) : Set V) := by
        intro y hy
        have hym : y ∈ L m := hm (by simpa using hy)
        exact Finset.mem_coe.2 (hmono hn hym)
      have hbound := abs_sub_le_walkConst_mul_restrictedEnergy G
        (hasFiniteEnergy_restrict_finset G (L n) (F n)) w hsupp
      have haL : a ∈ L n := Finset.mem_coe.1 (hsupp a w.start_mem_support)
      have hFa : F n a = u a := htrace n a haA haL
      have habs : |F n a| = |u a| := by rw [hFa]
      have hsq : Real.sqrt (2 * restrictedEnergy G (↑(L n) : Set V) (F n))
          ≤ Real.sqrt (2 * G.Energy u) := Real.sqrt_le_sqrt (by linarith [hEle n])
      have hchain : |F n x - F n a| ≤ G.walkConst w * Real.sqrt (2 * G.Energy u) :=
        hbound.trans (mul_le_mul_of_nonneg_left hsq hwc)
      have hx1 : |F n x| - |F n a| ≤ |F n x - F n a| := abs_sub_abs_le_abs_sub _ _
      linarith
    refine ⟨|u a| + G.walkConst w * Real.sqrt (2 * G.Energy u)
      + ∑ k ∈ Finset.range m, |F k x|, ?_⟩
    intro n
    have hnn : (0:ℝ) ≤ ∑ k ∈ Finset.range m, |F k x| :=
      Finset.sum_nonneg fun k _ => abs_nonneg _
    rcases le_or_gt m n with hmn | hnm
    · have := htail n hmn
      linarith
    · have hmem : n ∈ Finset.range m := Finset.mem_range.2 hnm
      have hle : |F n x| ≤ ∑ k ∈ Finset.range m, |F k x| :=
        Finset.single_le_sum (f := fun k => |F k x|)
          (fun k _ => abs_nonneg (F k x)) hmem
      have h0 : (0:ℝ) ≤ |u a| + G.walkConst w * Real.sqrt (2 * G.Energy u) :=
        le_trans (abs_nonneg (F m x)) (htail m le_rfl)
      linarith
  choose B hB using key
  exact ⟨B, fun n x => hB x n⟩

/-! ### A pointwise convergent subsequence -/

/-- **An actual pointwise convergent subsequence of the level minimizers.** The uniform
bounds confine the sequence to a product of compact intervals; on a countable vertex type
the product topology is second countable, hence first countable, so compactness is
sequential. -/
theorem exists_subseq_tendsto_pointwise [Countable V] (hA : BoundaryAnchored G A)
    (hu : G.HasFiniteEnergy u) (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n)) (F n) ≤ restrictedEnergy G (↑(L n)) w) :
    ∃ (φ : ℕ → ℕ) (g : V → ℝ), StrictMono φ ∧
      ∀ x : V, Tendsto (fun n => F (φ n) x) atTop (𝓝 (g x)) := by
  obtain ⟨B, hB⟩ := exists_pointwise_uniform_bound G hA hu hmono hcover htrace hmin
  have hcompact : IsCompact (Set.pi Set.univ (fun x : V => Set.Icc (-B x) (B x))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmemF : ∀ n : ℕ, F n ∈ Set.pi Set.univ (fun x : V => Set.Icc (-B x) (B x)) := by
    intro n x _
    exact abs_le.1 (hB n x)
  obtain ⟨g, -, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmemF
  exact ⟨φ, g, hφ, fun x => tendsto_pi_nhds.1 hlim x⟩

/-! ### Identification of every cluster point and full pointwise convergence -/

/-- **Every subsequence has a further subsequence converging pointwise to the full anchored
minimizer.** The subsampled levels are still monotone and exhausting, so the conditional
cluster-point theorem of `FiniteDirichletEnergyLimit` identifies the limit. -/
theorem exists_subseq_tendsto_minimizer [Countable V] (hA : BoundaryAnchored G A)
    (hu : G.HasFiniteEnergy u) (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n)) (F n) ≤ restrictedEnergy G (↑(L n)) w)
    {f : V → ℝ} (hfE : G.HasFiniteEnergy f) (hftrace : ∀ a ∈ A, f a = u a)
    (hfmin : ∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
      G.Energy f ≤ G.Energy h)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ x : V, Tendsto (fun n => F (φ (ψ n)) x) atTop (𝓝 (f x)) := by
  have hcoverφ : ∀ x : V, ∃ n, x ∈ L (φ n) := by
    intro x
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, hmono hφ.le_apply hn⟩
  have hmonoφ : Monotone fun n => L (φ n) := fun i j hij => hmono (hφ.monotone hij)
  obtain ⟨ψ, g, hψ, hg⟩ :=
    exists_subseq_tendsto_pointwise G (L := fun n => L (φ n)) (F := fun n => F (φ n)) hA hu
      hmonoφ hcoverφ (fun n => htrace (φ n)) (fun n => hmin (φ n))
  have hcoverψ : ∀ x : V, ∃ n, x ∈ L (φ (ψ n)) := by
    intro x
    obtain ⟨n, hn⟩ := hcoverφ x
    exact ⟨n, hmono (hφ.monotone hψ.le_apply) hn⟩
  have hmonoψ : Monotone fun n => L (φ (ψ n)) := fun i j hij =>
    hmono (hφ.monotone (hψ.monotone hij))
  have hgf : g = f :=
    eq_anchored_trace_minimizer_of_tendsto_pointwise G
      (L := fun n => L (φ (ψ n))) (F := fun n => F (φ (ψ n))) hA hu
      hmonoψ hcoverψ
      (fun n => htrace (φ (ψ n))) (fun n => hmin (φ (ψ n))) hg hfE hftrace hfmin
  refine ⟨ψ, hψ, fun x => ?_⟩
  have := hg x
  rwa [hgf] at this

/-- **The level minimizers converge pointwise.** This is the premise assumed by
`FiniteDirichletEnergyLimit.tendsto_levelEnergy_of_tendsto_pointwise`, here proved. -/
theorem tendsto_pointwise_of_levelMinimizers [Countable V] (hA : BoundaryAnchored G A)
    (hu : G.HasFiniteEnergy u) (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n)) (F n) ≤ restrictedEnergy G (↑(L n)) w)
    {f : V → ℝ} (hfE : G.HasFiniteEnergy f) (hftrace : ∀ a ∈ A, f a = u a)
    (hfmin : ∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
      G.Energy f ≤ G.Energy h) (x : V) :
    Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push_neg at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  have hfr : ∃ᶠ n in atTop, ε ≤ dist (F n x) (f x) := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hd⟩ := hfreq N
    exact ⟨n, hn, hd⟩
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfr
  obtain ⟨ψ, -, hconv⟩ :=
    exists_subseq_tendsto_minimizer G hA hu hmono hcover htrace hmin hfE hftrace hfmin hφ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv x) ε hε
  exact absurd (hN N le_rfl) (not_lt.2 (hφP (ψ N)))

/-- **Unconditional pointwise convergence of the level minimizers to the full anchored
minimizer.** No pointwise limit is supplied: it is produced. -/
theorem exists_tendsto_pointwise_anchored_minimizer [Countable V] (hA : BoundaryAnchored G A)
    (hu : G.HasFiniteEnergy u) (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n)) (F n) ≤ restrictedEnergy G (↑(L n)) w) :
    ∃ g : V → ℝ, (∀ x : V, Tendsto (fun n => F n x) atTop (𝓝 (g x))) ∧
      G.HasFiniteEnergy g ∧ (∀ a ∈ A, g a = u a) ∧
      ∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
        G.Energy g ≤ G.Energy h := by
  obtain ⟨f, hfE, hftrace, -, hfmin⟩ := exists_anchored_trace_minimizer G hA hu
  exact ⟨f, fun x => tendsto_pointwise_of_levelMinimizers G hA hu hmono hcover htrace hmin
    hfE hftrace hfmin x, hfE, hftrace, hfmin⟩

end Levels

end FiniteMinimizerPointwiseConvergence

end ReflectedGMS
