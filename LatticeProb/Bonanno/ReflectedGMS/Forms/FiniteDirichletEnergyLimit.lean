/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteDirichletEnergyLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteDirichletMinimizers

/-!
# Finite-level Dirichlet energies converge to the full anchored minimum

The finite anchored levels of `AnchoredFiniteExhaustion` carry actual Dirichlet minimizers
(`FiniteDirichletMinimizers.existsUnique_finite_anchored_minimizer`), and the full anchored
problem carries its own minimizer for a finite-energy reference
(`exists_anchored_trace_minimizer`, `existsUnique_anchored_trace_minimizer`). This module
compares the two.

The elementary half is unconditional. Restricting a function to a smaller vertex set only
deletes nonnegative energy terms, so `restrictedEnergy` is monotone along an increasing
family of vertex sets and bounded above by the full energy. Testing the level-`m` minimizer
against the restriction of the level-`n` minimizer (`m ≤ n`) therefore shows that the level
minimum energies increase, and testing them against the restriction of any full competitor
with the prescribed trace bounds them by that competitor's energy.

The second half is the actual free-cut approximation step, stated with an explicitly
supplied pointwise limit of the extended level minimizers: such a limit automatically has
the prescribed trace on the whole of `A`, its energy is bounded by the supremum of the
level minimum energies (lower semicontinuity, proved through finite blocks of edges which
are eventually contained in a single level), and it is therefore a full anchored minimizer;
consequently the level minimum energies converge to the full minimum energy. The pointwise
convergence hypothesis is *not* proved here: this is a conditional cluster-point statement,
not the unconditional convergence theorem.

The graph may be disconnected, the boundary `A` may be infinite, the levels need only be a
monotone exhausting family of finite vertex sets, and the competition class is always the
full energy space.
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace FiniteDirichletEnergyLimit

open Filter Topology

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-! ### Energy under a conductance-preserving injection -/

/-- **Energy is monotone under conductance-preserving injections.** If `i` embeds the
vertices of `H` into the vertices of `H'` preserving all conductances, then the energy of a
pulled back function is at most the energy of the original. -/
theorem energy_comp_injective_le {W W' : Type*} (H : ReflectedWalk.ConductanceGraph W)
    (H' : ReflectedWalk.ConductanceGraph W') (i : W → W') (hi : Function.Injective i)
    (hc : ∀ x y : W, H.c x y = H'.c (i x) (i y)) {g : W' → ℝ}
    (hg : H'.HasFiniteEnergy g) :
    H.Energy (fun x => g (i x)) ≤ H'.Energy g := by
  have hpt : ∀ p : W × W,
      H.gradSq (fun x => g (i x)) p = H'.gradSq g (i p.1, i p.2) := by
    intro p
    simp only [ReflectedWalk.ConductanceGraph.gradSq, hc p.1 p.2]
  have hinj : Function.Injective (fun p : W × W => (i p.1, i p.2)) := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ hab
    simp only [Prod.mk.injEq] at hab ⊢
    exact ⟨hi hab.1, hi hab.2⟩
  have hsum : Summable (fun p : W × W => H'.gradSq g (i p.1, i p.2)) :=
    hg.comp_injective hinj
  have hle : ∑' p : W × W, H.gradSq (fun x => g (i x)) p
      ≤ ∑' q : W' × W', H'.gradSq g q := by
    rw [tsum_congr hpt]
    exact hsum.tsum_le_tsum_of_inj (fun p : W × W => (i p.1, i p.2)) hinj
      (fun c _ => H'.gradSq_nonneg g c) (fun _ => le_rfl) hg
  rw [H.tsum_gradSq_eq, H'.tsum_gradSq_eq] at hle
  linarith

/-! ### The energy of a restriction -/

/-- The Dirichlet energy of the restriction of `f` to the vertex set `S`, computed in the
restricted conductance graph. -/
noncomputable def restrictedEnergy (S : Set V) (f : V → ℝ) : ℝ :=
  (restrictGraph G S).Energy (fun x : S => f ↑x)

/-- Every function has finite energy on a finite level. -/
theorem hasFiniteEnergy_restrict_finset (K : Finset V) (f : V → ℝ) :
    (restrictGraph G (↑K : Set V)).HasFiniteEnergy (fun x : (↑K : Set V) => f ↑x) := by
  haveI := K.finite_toSet.to_subtype
  exact Summable.of_finite

/-- **Restricting to a smaller vertex set decreases the energy.** -/
theorem restrictedEnergy_mono_of_subset {S T : Set V} (hST : S ⊆ T) (f : V → ℝ)
    (hT : (restrictGraph G T).HasFiniteEnergy (fun x : T => f ↑x)) :
    restrictedEnergy G S f ≤ restrictedEnergy G T f := by
  have hinj : Function.Injective (fun x : S => (⟨(x : V), hST x.2⟩ : T)) := by
    intro a b hab
    have hval : (a : V) = (b : V) := congrArg (fun y : T => (y : V)) hab
    exact Subtype.ext hval
  exact energy_comp_injective_le (restrictGraph G S) (restrictGraph G T)
    (fun x : S => (⟨(x : V), hST x.2⟩ : T)) hinj (fun _ _ => rfl) hT

/-- **A restriction never has more energy than the full function.** -/
theorem restrictedEnergy_le_energy (S : Set V) {f : V → ℝ} (hf : G.HasFiniteEnergy f) :
    restrictedEnergy G S f ≤ G.Energy f :=
  energy_comp_injective_le (restrictGraph G S) G Subtype.val Subtype.coe_injective
    (fun _ _ => rfl) hf

/-- **A finite block of edges inside `S` is controlled by the restricted energy.** -/
theorem sum_gradSq_le_two_restrictedEnergy {S : Set V} (f : V → ℝ)
    (hS : (restrictGraph G S).HasFiniteEnergy (fun x : S => f ↑x))
    (t : Finset (V × V)) (ht : ∀ p ∈ t, p.1 ∈ S ∧ p.2 ∈ S) :
    ∑ p ∈ t, G.gradSq f p ≤ 2 * restrictedEnergy G S f := by
  classical
  set φ : {p : V × V // p ∈ t} → (↥S × ↥S) :=
    fun p => (⟨p.1.1, (ht p.1 p.2).1⟩, ⟨p.1.2, (ht p.1 p.2).2⟩) with hφ
  have hinj : ∀ a ∈ t.attach, ∀ b ∈ t.attach, φ a = φ b → a = b := by
    rintro ⟨⟨a1, a2⟩, ha⟩ - ⟨⟨b1, b2⟩, hb⟩ - hab
    simp only [hφ, Prod.mk.injEq, Subtype.mk.injEq] at hab
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    exact hab
  have hkey : ∑ q ∈ t.attach.image φ,
      (restrictGraph G S).gradSq (fun x : S => f ↑x) q = ∑ p ∈ t, G.gradSq f p := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_attach t (fun p => G.gradSq f p)
  rw [← hkey]
  unfold restrictedEnergy
  rw [← (restrictGraph G S).tsum_gradSq_eq]
  exact hS.sum_le_tsum _ (fun q _ => (restrictGraph G S).gradSq_nonneg _ q)

/-! ### Monotone exhausting families of finite levels -/

/-- A finite vertex set of a monotone exhausting family is contained in a single level. -/
theorem exists_level_superset {L : ℕ → Finset V} (hmono : Monotone L)
    (hcover : ∀ x : V, ∃ n, x ∈ L n) (K : Finset V) : ∃ m, K ⊆ L m := by
  classical
  refine Finset.induction_on K ⟨0, Finset.empty_subset _⟩ ?_
  intro a s _ ih
  obtain ⟨m, hm⟩ := ih
  obtain ⟨n, hn⟩ := hcover a
  refine ⟨max m n, ?_⟩
  intro x hx
  rcases Finset.mem_insert.1 hx with rfl | hxs
  · exact hmono (le_max_right m n) hn
  · exact hmono (le_max_left m n) (hm hxs)

/-! ### Level minimizers as globally defined functions -/

/-! ### Monotonicity and the elementary upper bound -/

section Levels

variable {A : Set V} {u : V → ℝ} {L : ℕ → Finset V} {F : ℕ → V → ℝ}

/-- **The level minimum energies increase.** The level-`m` minimizer competes against the
restriction of the level-`n` minimizer, which has the prescribed trace on the smaller level
and no more energy there than on the larger one. -/
theorem monotone_levelEnergy (hmono : Monotone L)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n)) (F n) ≤ restrictedEnergy G (↑(L n)) w) :
    Monotone (fun n => restrictedEnergy G (↑(L n)) (F n)) := by
  intro m n hmn
  have h1 : restrictedEnergy G (↑(L m)) (F m) ≤ restrictedEnergy G (↑(L m)) (F n) :=
    hmin m (F n) (fun a ha haL => htrace n a ha (hmono hmn haL))
  have h2 : restrictedEnergy G (↑(L m)) (F n) ≤ restrictedEnergy G (↑(L n)) (F n) :=
    restrictedEnergy_mono_of_subset G (Finset.coe_subset.2 (hmono hmn)) (F n)
      (hasFiniteEnergy_restrict_finset G (L n) (F n))
  exact h1.trans h2

/-- **The level minimum energies are bounded by every full competitor's energy.** -/
theorem levelEnergy_le_energy
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n)) (F n) ≤ restrictedEnergy G (↑(L n)) w)
    {w : V → ℝ} (hw : G.HasFiniteEnergy w) (hwtrace : ∀ a ∈ A, w a = u a) (n : ℕ) :
    restrictedEnergy G (↑(L n)) (F n) ≤ G.Energy w :=
  (hmin n w (fun a ha _ => hwtrace a ha)).trans (restrictedEnergy_le_energy G _ hw)

/-! ### The cluster point of the level minimizers -/

/-- **A pointwise limit of the level minimizers is a full anchored minimizer, and the level
minimum energies converge to its energy.**

The hypotheses are: an anchored boundary `A`, a finite-energy reference `u`, a monotone
exhausting family `L` of finite levels, extended level minimizers `F n` with the prescribed
trace on `A ∩ L n` and minimizing the restricted energy there, and an explicitly supplied
pointwise limit `g` of the `F n`. No compactness argument is performed here: the existence
of such a pointwise limit (after passing to a subsequence) is a separate statement, so this
is a conditional cluster-point theorem rather than an unconditional convergence theorem. -/
theorem tendsto_levelEnergy_of_tendsto_pointwise (hA : BoundaryAnchored G A)
    (hu : G.HasFiniteEnergy u) (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n)) (F n) ≤ restrictedEnergy G (↑(L n)) w)
    {g : V → ℝ} (hg : ∀ x : V, Tendsto (fun n => F n x) atTop (𝓝 (g x))) :
    G.HasFiniteEnergy g ∧ (∀ a ∈ A, g a = u a) ∧
      (∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
        G.Energy g ≤ G.Energy h) ∧
      Tendsto (fun n => restrictedEnergy G (↑(L n)) (F n)) atTop (𝓝 (G.Energy g)) := by
  classical
  obtain ⟨f₀, hf₀E, hf₀trace, -, hf₀min⟩ := exists_anchored_trace_minimizer G hA hu
  set E : ℕ → ℝ := fun n => restrictedEnergy G (↑(L n)) (F n) with hEdef
  have hEmono : Monotone E := monotone_levelEnergy G hmono htrace hmin
  have hEle : ∀ n, E n ≤ G.Energy f₀ := fun n =>
    levelEnergy_le_energy G hmin hf₀E hf₀trace n
  have hbdd : BddAbove (Set.range E) := by
    refine ⟨G.Energy f₀, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hEle n
  have hEtendsto : Tendsto E atTop (𝓝 (⨆ n, E n)) := tendsto_atTop_ciSup hEmono hbdd
  set M : ℝ := ⨆ n, E n with hMdef
  have hEleM : ∀ n, E n ≤ M := fun n => le_ciSup hbdd n
  have hMle : M ≤ G.Energy f₀ := ciSup_le hEle
  -- the limit carries the prescribed trace on the whole boundary
  have hgtrace : ∀ a ∈ A, g a = u a := by
    intro a ha
    obtain ⟨n₀, hn₀⟩ := hcover a
    refine tendsto_nhds_unique (hg a) (Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact (htrace n a ha (hmono hn hn₀)).symm
  -- each level block of the limit is controlled by the supremum of the level energies
  have hlevel_g : ∀ m : ℕ, restrictedEnergy G (↑(L m)) g ≤ M := by
    intro m
    haveI : Fintype (↑(L m) : Set V) := (L m).finite_toSet.fintype
    have hlim : Tendsto (fun n => restrictedEnergy G (↑(L m)) (F n)) atTop
        (𝓝 (restrictedEnergy G (↑(L m)) g)) := by
      simp only [restrictedEnergy, ReflectedWalk.ConductanceGraph.Energy, tsum_fintype,
        ReflectedWalk.ConductanceGraph.gradSq]
      refine Tendsto.div_const (tendsto_finset_sum _ fun q _ => ?_) 2
      exact (((hg ((q.2 : V))).sub (hg ((q.1 : V)))).pow 2).const_mul _
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have h1 : restrictedEnergy G (↑(L m)) (F n) ≤ E n :=
      restrictedEnergy_mono_of_subset G (Finset.coe_subset.2 (hmono hn)) (F n)
        (hasFiniteEnergy_restrict_finset G (L n) (F n))
    exact h1.trans (hEleM n)
  -- lower semicontinuity of the full energy along the levels
  have hgnonneg : ∀ p : V × V, 0 ≤ G.gradSq g p := fun p => G.gradSq_nonneg g p
  have hsum : ∀ t : Finset (V × V), ∑ p ∈ t, G.gradSq g p ≤ 2 * M := by
    intro t
    obtain ⟨m, hm⟩ :=
      exists_level_superset hmono hcover (t.image Prod.fst ∪ t.image Prod.snd)
    have ht : ∀ p ∈ t, p.1 ∈ (↑(L m) : Set V) ∧ p.2 ∈ (↑(L m) : Set V) := by
      intro p hp
      refine ⟨Finset.mem_coe.2 (hm (Finset.mem_union_left _ ?_)),
        Finset.mem_coe.2 (hm (Finset.mem_union_right _ ?_))⟩
      · exact Finset.mem_image_of_mem _ hp
      · exact Finset.mem_image_of_mem _ hp
    have h1 := sum_gradSq_le_two_restrictedEnergy G g
      (hasFiniteEnergy_restrict_finset G (L m) g) t ht
    have h2 : restrictedEnergy G (↑(L m)) g ≤ M := hlevel_g m
    linarith
  have hgE : G.HasFiniteEnergy g := summable_of_sum_le hgnonneg hsum
  have hgEnergy : G.Energy g ≤ M := by
    have hts := Real.tsum_le_of_sum_le hgnonneg hsum
    rw [G.tsum_gradSq_eq] at hts
    linarith
  have hminG : ∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
      G.Energy g ≤ G.Energy h := fun h hh hht =>
    hgEnergy.trans (hMle.trans (hf₀min h hh hht))
  have hMeq : M = G.Energy g :=
    le_antisymm (hMle.trans (hf₀min g hgE hgtrace)) hgEnergy
  refine ⟨hgE, hgtrace, hminG, ?_⟩
  rw [← hMeq]
  exact hEtendsto

/-- **The pointwise limit is the unique full anchored minimizer.** -/
theorem eq_anchored_trace_minimizer_of_tendsto_pointwise (hA : BoundaryAnchored G A)
    (hu : G.HasFiniteEnergy u) (hmono : Monotone L) (hcover : ∀ x : V, ∃ n, x ∈ L n)
    (htrace : ∀ n, ∀ a ∈ A, a ∈ L n → F n a = u a)
    (hmin : ∀ n, ∀ w : V → ℝ, (∀ a ∈ A, a ∈ L n → w a = u a) →
      restrictedEnergy G (↑(L n)) (F n) ≤ restrictedEnergy G (↑(L n)) w)
    {g : V → ℝ} (hg : ∀ x : V, Tendsto (fun n => F n x) atTop (𝓝 (g x)))
    {f : V → ℝ} (hfE : G.HasFiniteEnergy f) (hftrace : ∀ a ∈ A, f a = u a)
    (hfmin : ∀ h : V → ℝ, G.HasFiniteEnergy h → (∀ a ∈ A, h a = u a) →
      G.Energy f ≤ G.Energy h) :
    g = f := by
  obtain ⟨hgE, hgtrace, hgmin, -⟩ :=
    tendsto_levelEnergy_of_tendsto_pointwise G hA hu hmono hcover htrace hmin hg
  obtain ⟨f₁, -, huniq⟩ := existsUnique_anchored_trace_minimizer G hA hu
  exact (huniq g ⟨hgE, hgtrace, hgmin⟩).trans (huniq f ⟨hfE, hftrace, hfmin⟩).symm

end Levels

end FiniteDirichletEnergyLimit

end ReflectedGMS
