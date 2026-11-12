/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412cStep3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412cLC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bL414

/-!
# GM L4.15 Step 3 for boundary points (DEC-86 item (2))

GM L4.15 Step 3 (`literature/src/1905.00383/uniqueness-final.tex` l. 2157–2166) and the
assembly (l. 2242–2244) apply L4.14 to the L4.15 version of `𝒞_y` (l. 2107), which contains the
point `P(t_k) ∈ ∂𝓑^•_{t_k}` produced by L4.13 (l. 2075). DEC-86 keeps the L4.14 version
`dcSetC` and proves GM's (∗) for such boundary points:

* `p412c_cc_subset_dcSetC` — a bounded component `V` of `ℂ∖(X∪K)` with `y ∈ cl V` lies in
  `𝒞_y` (`dcSetC`), so `cl V ⊆ cl U` once `𝒞_y ⊆ cl U` (`GML4_14'`).
* `p412c_exit` — a path starting at `x ∈ cl U ∩ ∂K` (`U` a component of `ℂ∖(A∪K)`, (LC) at
  `x`), running in `ℂ∖K` afterwards and ending outside `U`, meets `cl A` (shadow lemma
  `p412c_shadow`).
* `p412c_step3` — the combination: L4.13′-type output at `P(a)` + `GML4_14'`'s conclusion ⇒
  `P` meets `cl B_{2r}(z)` for a point `z ∈ ∂K` depending only on `(K, c, r)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace LQGMetric.GM

/-- Every point of a bounded component `V` of `ℂ ∖ (X ∪ K)` with `y ∈ cl V` lies in `𝒞^ε_y`. -/
theorem p412c_cc_subset_dcSetC {K X : Set ℂ} {y v : ℂ} {ε : ℝ} (hX : X ⊆ Kᶜ)
    (hXc : IsConnected X) (hXd : Metric.ediam X ≤ ENNReal.ofReal ε) (hv : v ∉ X ∪ K)
    (hb : Bornology.IsBounded (connectedComponentIn (X ∪ K)ᶜ v))
    (hy : y ∈ closure (connectedComponentIn (X ∪ K)ᶜ v)) :
    connectedComponentIn (X ∪ K)ᶜ v ⊆ dcSetC K y ε := fun p hp =>
  ⟨fun hpK => connectedComponentIn_subset _ _ hp (Or.inr hpK), X, hX, hXc, hXd, v, hv, hb,
    subset_closure hp, hy⟩

/-- **Exit lemma**: a path from `x ∈ cl U` (`U` a component of `ℂ ∖ (A ∪ K)`, (LC) at `x`) that
runs in `ℂ ∖ K` after time `a` and ends outside `U` meets `cl A`. -/
theorem p412c_exit {K A : Set ℂ} {u : ℂ} {P : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hLC : LocConnAt K (P a)) (hxU : P a ∈ closure (connectedComponentIn (A ∪ K)ᶜ u))
    (hP : ContinuousOn P (Icc a b)) (hPK : ∀ t ∈ Ioc a b, P t ∉ K)
    (hPb : P b ∉ connectedComponentIn (A ∪ K)ᶜ u) : ∃ t ∈ Icc a b, P t ∈ closure A := by
  by_contra hno
  push_neg at hno
  have hxA : P a ∉ closure A := hno a (left_mem_Icc.2 hab.le)
  set S := P '' Ioc a b
  have hSc : IsPreconnected S :=
    isPreconnected_Ioc.image _ (hP.mono Ioc_subset_Icc_self)
  have hSAK : S ⊆ (A ∪ K)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩ h
    rcases h with h | h
    · exact hno t (Ioc_subset_Icc_self ht) (subset_closure h)
    · exact hPK t ht h
  have hbS : P b ∈ S := ⟨b, right_mem_Ioc.2 hab, rfl⟩
  have hSsub := hSc.subset_connectedComponentIn hbS hSAK
  have hxS : P a ∈ closure S := by
    have hcl : closure (Ioc a b) = Icc a b := closure_Ioc hab.ne
    have := (hcl ▸ hP).image_closure (s := Ioc a b)
    exact this ⟨a, by rw [hcl]; exact left_mem_Icc.2 hab.le, rfl⟩
  have hxW : P a ∈ closure (connectedComponentIn (A ∪ K)ᶜ (P b)) := closure_mono hSsub hxS
  have heq := p412c_shadow hLC hxA hxU hxW
  exact hPb (heq ▸ mem_connectedComponentIn (hSAK hbS))

end LQGMetric.GM
