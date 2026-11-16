import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import LatticeProb.Analysis.Elliptic.Domain
import LatticeProb.Analysis.Elliptic.HolderCompositionConvex

/-!
# Local graphs of defining functions

A regular boundary point has a local coordinate graph. The Hessian identity and local
Hölder estimates describe the regularity of this graph.
-/

open scoped Topology

namespace LatticeProb.Elliptic.HolderExtension

/-- At a regular point, a coordinate derivative of the defining function is nonzero. -/
theorem exists_partialDeriv_ne_zero {d : ℕ} {ρ : (Fin d → ℝ) → ℝ} {p : Fin d → ℝ}
    (h : fderiv ℝ ρ p ≠ 0) : ∃ i, partialDeriv i ρ p ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply h
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin d)).ext
  intro i
  simpa [partialDeriv, Pi.basisFun_apply] using hn i

/-- At each boundary point a defining function vanishes and has a nonzero coordinate derivative. -/
theorem exists_definingFunction_partialDeriv_ne_zero {d : ℕ} {σ : ℝ}
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    {p : Fin d → ℝ} (hp : p ∈ frontier U) :
    ∃ ρ : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 ρ ∧
      (∀ R : ℝ, c2HolderNorm σ {x | LatticeProb.Euclidean.Lattice.radius x < R} ρ < ⊤) ∧
      U = {x | ρ x < 0} ∧ ρ p = 0 ∧ ∃ i, partialDeriv i ρ p ≠ 0 := by
  obtain ⟨_, _, _, ρ, hρ, hnorm, heq, hreg⟩ := hU
  have hp0 : ρ p = 0 := by
    rw [frontier_eq_zero_of_definingFunction hρ heq hreg] at hp
    exact hp
  exact ⟨ρ, hρ, hnorm, heq, hp0, exists_partialDeriv_ne_zero (hreg p hp0)⟩

/-- Replacing one coordinate by a scalar is a smooth map. -/
theorem contDiff_update_pair {d : ℕ} (i : Fin d) :
    ContDiff ℝ 2 (fun z : (Fin d → ℝ) × ℝ => Function.update z.1 i z.2) := by
  classical
  apply contDiff_pi.mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa using (contDiff_snd : ContDiff ℝ 2 (fun z : (Fin d → ℝ) × ℝ => z.2))
  · simpa [Function.update, h, Function.comp_def] using
      ((contDiff_apply ℝ ℝ j).comp (contDiff_fst : ContDiff ℝ 2 (fun z : (Fin d → ℝ) × ℝ => z.1)))

private theorem real_linear_isInvertible (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) :
    L.IsInvertible := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (L 1) h)
  have he : L = (e : ℝ →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext_ring
    simp [e]
  rw [he]
  exact ContinuousLinearMap.isInvertible_equiv

/-- A regular coordinate gives a local implicit graph of a level set. -/
theorem exists_local_level_graph {d : ℕ} (ρ : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (p : Fin d → ℝ) (i : Fin d)
    (hi : partialDeriv i ρ p ≠ 0) :
    ∃ h : (Fin d → ℝ) → ℝ, ContDiffAt ℝ 2 h p ∧ h p = p i ∧
      ∀ᶠ z : (Fin d → ℝ) × ℝ in 𝓝 (p, p i),
        ρ (Function.update z.1 i z.2) = ρ p ↔ h z.1 = z.2 := by
  classical
  let F : (Fin d → ℝ) × ℝ → ℝ := fun z => ρ (Function.update z.1 i z.2)
  have hF : ContDiff ℝ 2 F := hρ.comp (contDiff_update_pair i)
  have hf : HasFDerivAt (fun t : ℝ => F (p, t))
      (fderiv ℝ F (p, p i) ∘L ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) (p i) := by
    convert ((hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp (p i)
      ((hasFDerivAt_const p (p i)).prodMk (hasFDerivAt_id (p i)))) using 1 <;>
        ext <;> simp
  have hg : HasFDerivAt (fun t : ℝ => F (p, t))
      (fderiv ℝ ρ p ∘L ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)))
      (p i) := by
    have hh := (hρ.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp (p i)
      (hasFDerivAt_update p (i := i) (p i))
    simpa [F, Function.comp_def] using hh
  have hv : (fderiv ℝ F (p, p i) ∘L ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) 1 =
      partialDeriv i ρ p := by
    have h := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) (hf.unique hg)
    have hs : (fun j => ((Pi.single i (ContinuousLinearMap.id ℝ ℝ) : Fin d → (ℝ →L[ℝ] ℝ)) j) 1) =
        Pi.single i (1 : ℝ) := by
      ext j
      by_cases hji : j = i <;> simp [hji]
    simpa [partialDeriv, hs] using h
  have hinv : (fderiv ℝ F (p, p i) ∘L
      ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ).IsInvertible :=
    real_linear_isInvertible _ (hv ▸ hi)
  let h := hF.contDiffAt.implicitFunction (by norm_num) hinv
  refine ⟨h, hF.contDiffAt.contDiffAt_implicitFunction (by norm_num) hinv,
    hF.contDiffAt.implicitFunction_apply_self (by norm_num) hinv, ?_⟩
  simpa [F] using hF.contDiffAt.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv

/-- A local implicit graph can be chosen independent of the solved coordinate. -/
theorem exists_local_level_graph_independent {d : ℕ} (ρ : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (p : Fin d → ℝ) (i : Fin d)
    (hi : partialDeriv i ρ p ≠ 0) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiffAt ℝ 2 g p ∧ g p = p i ∧
      (∀ x t, g (Function.update x i t) = g x) ∧
      ∀ᶠ x in 𝓝 p, ρ x = ρ p ↔ g x = x i := by
  classical
  obtain ⟨h, hh, hp, hz⟩ := exists_local_level_graph ρ hρ p i hi
  let P : (Fin d → ℝ) → (Fin d → ℝ) := fun x => Function.update x i (p i)
  let g : (Fin d → ℝ) → ℝ := fun x => h (P x)
  have hP : ContDiff ℝ 2 P := by
    have h := (contDiff_update_pair i).comp (contDiff_id.prodMk
      (contDiff_const : ContDiff ℝ 2 (fun _ : Fin d → ℝ => p i)))
    simpa [P, Function.comp_def] using h
  have hPp : P p = p := by simp [P]
  have hΦ : ContinuousAt (fun x : Fin d → ℝ => (P x, x i)) p :=
    hP.continuous.continuousAt.prodMk (continuous_apply i).continuousAt
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · have hhP : ContDiffAt ℝ 2 h (P p) := by simpa only [hPp] using hh
    simpa [g, Function.comp_def] using hhP.comp p hP.contDiffAt
  · simpa [g, hPp] using hp
  · intro x t
    simp [g, P]
  · have hz' := hΦ.tendsto.eventually (by simpa [hPp] using hz)
    filter_upwards [hz'] with x hx
    simpa [g, P] using hx

/-- A positive coordinate derivative makes a coordinate line strictly increasing. -/
theorem strictMonoOn_update_of_partialDeriv_pos {d : ℕ} (ρ : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (x : Fin d → ℝ) (i : Fin d) {a b : ℝ}
    (hpos : ∀ t ∈ Set.Ioo a b, 0 < partialDeriv i ρ (Function.update x i t)) :
    StrictMonoOn (ρ ∘ Function.update x i) (Set.Ioo a b) := by
  classical
  apply strictMonoOn_of_deriv_pos (convex_Ioo a b)
  · exact (hρ.continuous.comp (contDiff_update (𝕜 := ℝ) 2 x i).continuous).continuousOn
  · intro t ht
    have hd := (hρ.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_update x i t)
    have he : deriv (ρ ∘ Function.update x i) t = partialDeriv i ρ (Function.update x i t) := by
      simpa [partialDeriv, Function.comp_def] using hd.deriv
    rw [he]
    exact hpos t (interior_subset ht)

/-- A negative coordinate derivative makes a coordinate line strictly decreasing. -/
theorem strictAntiOn_update_of_partialDeriv_neg {d : ℕ} (ρ : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (x : Fin d → ℝ) (i : Fin d) {a b : ℝ}
    (hneg : ∀ t ∈ Set.Ioo a b, partialDeriv i ρ (Function.update x i t) < 0) :
    StrictAntiOn (ρ ∘ Function.update x i) (Set.Ioo a b) := by
  classical
  apply strictAntiOn_of_deriv_neg (convex_Ioo a b)
  · exact (hρ.continuous.comp (contDiff_update (𝕜 := ℝ) 2 x i).continuous).continuousOn
  · intro t ht
    have hd := (hρ.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_update x i t)
    have he : deriv (ρ ∘ Function.update x i) t = partialDeriv i ρ (Function.update x i t) := by
      simpa [partialDeriv, Function.comp_def] using hd.deriv
    rw [he]
    exact hneg t (interior_subset ht)

/-- A positive normal derivative orients the local implicit graph. -/
theorem exists_local_sublevel_graph_of_partialDeriv_pos_with_level {d : ℕ}
    (ρ : (Fin d → ℝ) → ℝ) (hρ : ContDiff ℝ 2 ρ) (p : Fin d → ℝ) (i : Fin d)
    (hi : 0 < partialDeriv i ρ p) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiffAt ℝ 2 g p ∧ g p = p i ∧
      (∀ x t, g (Function.update x i t) = g x) ∧
      (∀ᶠ x in 𝓝 p, ρ (Function.update x i (g x)) = ρ p) ∧
      ∀ᶠ x in 𝓝 p, ρ x < ρ p ↔ x i < g x := by
  classical
  obtain ⟨g, hg, hgp, hind, hlevel⟩ :=
    exists_local_level_graph_independent ρ hρ p i hi.ne'
  have hpcont : Continuous (partialDeriv i ρ) := by
    exact (hρ.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  have hsign : ∀ᶠ z : (Fin d → ℝ) × ℝ in 𝓝 (p, p i),
      0 < partialDeriv i ρ (Function.update z.1 i z.2) := by
    have hc := hpcont.comp (contDiff_update_pair i).continuous
    have hcp : (partialDeriv i ρ ∘ fun z : (Fin d → ℝ) × ℝ =>
        Function.update z.1 i z.2) (p, p i) ∈ Set.Ioi (0 : ℝ) := by
      simpa using hi
    have h := (hc.continuousAt : ContinuousAt _ (p, p i)).eventually
      (isOpen_Ioi.mem_nhds hcp)
    simpa using h
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hsign
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hv
  have hI : Set.Ioo a b ∈ 𝓝 (p i) := Ioo_mem_nhds ha hb
  have hxI : ∀ᶠ x : Fin d → ℝ in 𝓝 p, x i ∈ Set.Ioo a b :=
    (continuous_apply i).continuousAt.tendsto.eventually hI
  have hgI : ∀ᶠ x in 𝓝 p, g x ∈ Set.Ioo a b := by
    have hI' : Set.Ioo a b ∈ 𝓝 (g p) := by rw [hgp]; exact hI
    exact hg.continuousAt.tendsto.eventually hI'
  have hupdate : ContinuousAt (fun x => Function.update x i (g x)) p := by
    exact (contDiff_update_pair i).continuous.continuousAt.comp
      (continuousAt_id.prodMk hg.continuousAt)
  have hgraph : ∀ᶠ x in 𝓝 p, ρ (Function.update x i (g x)) = ρ p := by
    have h := hupdate.tendsto.eventually (by simpa [hgp] using hlevel)
    filter_upwards [h] with x hx
    exact hx.mpr (by simp [hind])
  refine ⟨g, hg, hgp, hind, hgraph, ?_⟩
  filter_upwards [hu, hxI, hgI, hgraph] with x hx hxi hgi hgraphx
  have hmono : StrictMonoOn (ρ ∘ Function.update x i) (Set.Ioo a b) := by
    apply strictMonoOn_update_of_partialDeriv_pos ρ hρ x i
    intro t ht
    exact huv (show (x, t) ∈ u ×ˢ v from ⟨hx, hab ht⟩)
  have hh := hmono.lt_iff_lt hxi hgi
  simpa [Function.comp_def, hgraphx] using hh

/-- A negative normal derivative orients the local implicit graph. -/
theorem exists_local_sublevel_graph_of_partialDeriv_neg_with_level {d : ℕ}
    (ρ : (Fin d → ℝ) → ℝ) (hρ : ContDiff ℝ 2 ρ) (p : Fin d → ℝ) (i : Fin d)
    (hi : partialDeriv i ρ p < 0) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiffAt ℝ 2 g p ∧ g p = p i ∧
      (∀ x t, g (Function.update x i t) = g x) ∧
      (∀ᶠ x in 𝓝 p, ρ (Function.update x i (g x)) = ρ p) ∧
      ∀ᶠ x in 𝓝 p, ρ x < ρ p ↔ g x < x i := by
  classical
  obtain ⟨g, hg, hgp, hind, hlevel⟩ :=
    exists_local_level_graph_independent ρ hρ p i hi.ne
  have hpcont : Continuous (partialDeriv i ρ) := by
    exact (hρ.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  have hsign : ∀ᶠ z : (Fin d → ℝ) × ℝ in 𝓝 (p, p i),
      partialDeriv i ρ (Function.update z.1 i z.2) < 0 := by
    have hc := hpcont.comp (contDiff_update_pair i).continuous
    have hcp : (partialDeriv i ρ ∘ fun z : (Fin d → ℝ) × ℝ =>
        Function.update z.1 i z.2) (p, p i) ∈ Set.Iio (0 : ℝ) := by
      simpa using hi
    have h := (hc.continuousAt : ContinuousAt _ (p, p i)).eventually
      (isOpen_Iio.mem_nhds hcp)
    simpa using h
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hsign
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hv
  have hI : Set.Ioo a b ∈ 𝓝 (p i) := Ioo_mem_nhds ha hb
  have hxI : ∀ᶠ x : Fin d → ℝ in 𝓝 p, x i ∈ Set.Ioo a b :=
    (continuous_apply i).continuousAt.tendsto.eventually hI
  have hgI : ∀ᶠ x in 𝓝 p, g x ∈ Set.Ioo a b := by
    have hI' : Set.Ioo a b ∈ 𝓝 (g p) := by rw [hgp]; exact hI
    exact hg.continuousAt.tendsto.eventually hI'
  have hupdate : ContinuousAt (fun x => Function.update x i (g x)) p := by
    exact (contDiff_update_pair i).continuous.continuousAt.comp
      (continuousAt_id.prodMk hg.continuousAt)
  have hgraph : ∀ᶠ x in 𝓝 p, ρ (Function.update x i (g x)) = ρ p := by
    have h := hupdate.tendsto.eventually (by simpa [hgp] using hlevel)
    filter_upwards [h] with x hx
    exact hx.mpr (by simp [hind])
  refine ⟨g, hg, hgp, hind, hgraph, ?_⟩
  filter_upwards [hu, hxI, hgI, hgraph] with x hx hxi hgi hgraphx
  have hmono : StrictAntiOn (ρ ∘ Function.update x i) (Set.Ioo a b) := by
    apply strictAntiOn_update_of_partialDeriv_neg ρ hρ x i
    intro t ht
    exact huv (show (x, t) ∈ u ×ˢ v from ⟨hx, hab ht⟩)
  have hh := hmono.lt_iff_gt hxi hgi
  simpa [Function.comp_def, hgraphx] using hh

/-- A positive normal derivative gives an oriented local graph. -/
theorem exists_local_sublevel_graph_of_partialDeriv_pos {d : ℕ}
    (ρ : (Fin d → ℝ) → ℝ) (hρ : ContDiff ℝ 2 ρ) (p : Fin d → ℝ) (i : Fin d)
    (hi : 0 < partialDeriv i ρ p) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiffAt ℝ 2 g p ∧ g p = p i ∧
      (∀ x t, g (Function.update x i t) = g x) ∧
      ∀ᶠ x in 𝓝 p, ρ x < ρ p ↔ x i < g x := by
  obtain ⟨g, hg, hp, hi, _, hs⟩ :=
    exists_local_sublevel_graph_of_partialDeriv_pos_with_level ρ hρ p i hi
  exact ⟨g, hg, hp, hi, hs⟩

/-- A negative normal derivative gives an oriented local graph. -/
theorem exists_local_sublevel_graph_of_partialDeriv_neg {d : ℕ}
    (ρ : (Fin d → ℝ) → ℝ) (hρ : ContDiff ℝ 2 ρ) (p : Fin d → ℝ) (i : Fin d)
    (hi : partialDeriv i ρ p < 0) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiffAt ℝ 2 g p ∧ g p = p i ∧
      (∀ x t, g (Function.update x i t) = g x) ∧
      ∀ᶠ x in 𝓝 p, ρ x < ρ p ↔ g x < x i := by
  obtain ⟨g, hg, hp, hi, _, hs⟩ :=
    exists_local_sublevel_graph_of_partialDeriv_neg_with_level ρ hρ p i hi
  exact ⟨g, hg, hp, hi, hs⟩

/-- A local graph retains the defining function and its level-set identity. -/
theorem definingFunction_local_graph_with_level {d : ℕ} {σ : ℝ}
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    {p : Fin d → ℝ} (hp : p ∈ frontier U) :
    ∃ (ρ : (Fin d → ℝ) → ℝ) (i : Fin d) (g : (Fin d → ℝ) → ℝ),
      ContDiff ℝ 2 ρ ∧
      (∀ R : ℝ, c2HolderNorm σ {x | LatticeProb.Euclidean.Lattice.radius x < R} ρ < ⊤) ∧
      U = {x | ρ x < 0} ∧ ρ p = 0 ∧ partialDeriv i ρ p ≠ 0 ∧
      ContDiffAt ℝ 2 g p ∧ g p = p i ∧
      (∀ x t, g (Function.update x i t) = g x) ∧
      (∀ᶠ x in 𝓝 p, ρ (Function.update x i (g x)) = 0) ∧
      ((∀ᶠ x in 𝓝 p, x ∈ U ↔ x i < g x) ∨
       (∀ᶠ x in 𝓝 p, x ∈ U ↔ g x < x i)) := by
  obtain ⟨ρ, hρ, hnorm, heq, hp0, i, hi⟩ :=
    exists_definingFunction_partialDeriv_ne_zero hU hp
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · obtain ⟨g, hg, hgp, hind, hlevel, hside⟩ :=
      exists_local_sublevel_graph_of_partialDeriv_neg_with_level ρ hρ p i hneg
    refine ⟨ρ, i, g, hρ, hnorm, heq, hp0, hi, hg, hgp, hind, ?_, Or.inr ?_⟩
    · simpa [hp0] using hlevel
    · filter_upwards [hside] with x hx
      simpa [heq, hp0] using hx
  · obtain ⟨g, hg, hgp, hind, hlevel, hside⟩ :=
      exists_local_sublevel_graph_of_partialDeriv_pos_with_level ρ hρ p i hpos
    refine ⟨ρ, i, g, hρ, hnorm, heq, hp0, hi, hg, hgp, hind, ?_, Or.inl ?_⟩
    · simpa [hp0] using hlevel
    · filter_upwards [hside] with x hx
      simpa [heq, hp0] using hx

/-- Near a boundary point the domain lies on one side of a local coordinate graph. -/
theorem definingFunction_local_graph_at {d : ℕ} {σ : ℝ} {U : Set (Fin d → ℝ)}
    (hU : IsC2HolderDomain σ U) {p : Fin d → ℝ} (hp : p ∈ frontier U) :
    ∃ (i : Fin d) (g : (Fin d → ℝ) → ℝ) (r : ℝ), 0 < r ∧
      ContDiffAt ℝ 2 g p ∧ (∀ x t, g (Function.update x i t) = g x) ∧ g p = p i ∧
      ((∀ x ∈ Metric.ball p r, x ∈ U ↔ x i < g x) ∨
       (∀ x ∈ Metric.ball p r, x ∈ U ↔ g x < x i)) := by
  obtain ⟨ρ, hρ, _, heq, hp0, i, hi⟩ :=
    exists_definingFunction_partialDeriv_ne_zero hU hp
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · obtain ⟨g, hg, hgp, hind, hlocal⟩ :=
      exists_local_sublevel_graph_of_partialDeriv_neg ρ hρ p i hneg
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hlocal
    refine ⟨i, g, r, hr, hg, hind, hgp, Or.inr ?_⟩
    intro x hx
    simpa [heq, hp0] using hball hx
  · obtain ⟨g, hg, hgp, hind, hlocal⟩ :=
      exists_local_sublevel_graph_of_partialDeriv_pos ρ hρ p i hpos
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hlocal
    refine ⟨i, g, r, hr, hg, hind, hgp, Or.inl ?_⟩
    intro x hx
    simpa [heq, hp0] using hball hx

/-- A locally twice differentiable function agrees locally with a global one. -/
theorem exists_contDiff_eq_near {d : ℕ} (f : (Fin d → ℝ) → ℝ) (p : Fin d → ℝ)
    (hf : ContDiffAt ℝ 2 f p) :
    ∃ F : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ F =ᶠ[𝓝 p] f := by
  classical
  have hnear := hf.eventually (by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let b : ContDiffBump p := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let F : (Fin d → ℝ) → ℝ := fun x => b x * f x
  have hF : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · have hxb : x ∈ Metric.ball p r := by
        rw [b.tsupport_eq] at hx
        simp only [Metric.mem_closedBall] at hx
        simp only [Metric.mem_ball]
        dsimp [b] at hx
        linarith
      exact b.contDiffAt.mul (hball hxb)
    · have hz : b =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have heq : F =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hz] with y hy
        simp [F, hy]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hFcompact : HasCompactSupport F := by
    exact b.hasCompactSupport.mul_right
  refine ⟨F, hF, hFcompact, ?_⟩
  have hb := b.eventuallyEq_one_of_mem_ball (Metric.mem_ball_self b.rIn_pos)
  filter_upwards [hb] with x hx
  simp [F, hx]

/-- A global graph agrees locally with the level set of its defining function. -/
theorem definingFunction_global_C2_graph_with_level {d : ℕ} {σ : ℝ}
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    {p : Fin d → ℝ} (hp : p ∈ frontier U) :
    ∃ (ρ : (Fin d → ℝ) → ℝ) (i : Fin d) (g : (Fin d → ℝ) → ℝ) (r : ℝ),
      0 < r ∧ ContDiff ℝ 2 ρ ∧
      (∀ R : ℝ, c2HolderNorm σ {x | LatticeProb.Euclidean.Lattice.radius x < R} ρ < ⊤) ∧
      U = {x | ρ x < 0} ∧ ρ p = 0 ∧ partialDeriv i ρ p ≠ 0 ∧
      ContDiff ℝ 2 g ∧ supNorm Set.univ g < ⊤ ∧
      (∀ x t, g (Function.update x i t) = g x) ∧ g p = p i ∧
      (∀ x ∈ Metric.ball p r, ρ (Function.update x i (g x)) = 0) ∧
      ((∀ x ∈ Metric.ball p r, x ∈ U ↔ x i < g x) ∨
       (∀ x ∈ Metric.ball p r, x ∈ U ↔ g x < x i)) := by
  classical
  obtain ⟨ρ, i, f, hρ, hnorm, heq, hp0, hi, hf, hfp, hind, hlevel, hside⟩ :=
    definingFunction_local_graph_with_level hU hp
  obtain ⟨F, hF, hFc, hFeq⟩ := exists_contDiff_eq_near f p hf
  let P : (Fin d → ℝ) → (Fin d → ℝ) := fun x => Function.update x i (p i)
  let g : (Fin d → ℝ) → ℝ := fun x => F (P x)
  have hP : ContDiff ℝ 2 P := by
    have h := (contDiff_update_pair i).comp (contDiff_id.prodMk
      (contDiff_const : ContDiff ℝ 2 (fun _ : Fin d → ℝ => p i)))
    simpa [P, Function.comp_def] using h
  have hPp : P p = p := by simp [P]
  have hfg : ∀ᶠ x in 𝓝 p, g x = f x := by
    have hFeqP : F =ᶠ[𝓝 (P p)] f := by rw [hPp]; exact hFeq
    have h := (hP.continuous.continuousAt : ContinuousAt P p).tendsto.eventually hFeqP
    filter_upwards [h] with x hx
    simpa [g, P, hind] using hx
  have hglobal : ContDiff ℝ 2 g := hF.comp hP
  have hbounded : supNorm Set.univ g < ⊤ := by
    obtain ⟨C, hC⟩ := hF.continuous.bounded_above_of_compact_support hFc
    apply supNorm_lt_top_of_bound C
    intro x _
    simpa [g, Real.norm_eq_abs] using hC (P x)
  have hind' : ∀ x t, g (Function.update x i t) = g x := by
    intro x t
    simp [g, P]
  have hgp : g p = p i := by simpa [hfp] using hfg.self_of_nhds
  have hlevel' : ∀ᶠ x in 𝓝 p, ρ (Function.update x i (g x)) = 0 := by
    filter_upwards [hfg, hlevel] with x hxf hx
    simpa [hxf] using hx
  rcases hside with hleft | hright
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hlevel'.and (hfg.and hleft))
    refine ⟨ρ, i, g, r, hr, hρ, hnorm, heq, hp0, hi, hglobal, hbounded, hind', hgp,
      fun x hx => (hball hx).1, Or.inl ?_⟩
    intro x hx
    obtain ⟨_, hxf, hs⟩ := hball hx
    simpa [hxf] using hs
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hlevel'.and (hfg.and hright))
    refine ⟨ρ, i, g, r, hr, hρ, hnorm, heq, hp0, hi, hglobal, hbounded, hind', hgp,
      fun x hx => (hball hx).1, Or.inr ?_⟩
    intro x hx
    obtain ⟨_, hxf, hs⟩ := hball hx
    simpa [hxf] using hs

/-- The local boundary graph extends to a global twice differentiable coordinate graph. -/
theorem definingFunction_global_C2_local_graph {d : ℕ} {σ : ℝ} {U : Set (Fin d → ℝ)}
    (hU : IsC2HolderDomain σ U) {p : Fin d → ℝ} (hp : p ∈ frontier U) :
    ∃ (i : Fin d) (g : (Fin d → ℝ) → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ 2 g ∧ supNorm Set.univ g < ⊤ ∧
      (∀ x t, g (Function.update x i t) = g x) ∧ g p = p i ∧
      ((∀ x ∈ Metric.ball p r, x ∈ U ↔ x i < g x) ∨
       (∀ x ∈ Metric.ball p r, x ∈ U ↔ g x < x i)) := by
  classical
  obtain ⟨i, f, r, hr, hf, hind, hfp, hside⟩ := definingFunction_local_graph_at hU hp
  obtain ⟨F, hF, hFc, hFeq⟩ := exists_contDiff_eq_near f p hf
  let P : (Fin d → ℝ) → (Fin d → ℝ) := fun x => Function.update x i (p i)
  let g : (Fin d → ℝ) → ℝ := fun x => F (P x)
  have hP : ContDiff ℝ 2 P := by
    have h := (contDiff_update_pair i).comp (contDiff_id.prodMk
      (contDiff_const : ContDiff ℝ 2 (fun _ : Fin d → ℝ => p i)))
    simpa [P, Function.comp_def] using h
  have hPp : P p = p := by simp [P]
  have hfg : ∀ᶠ x in 𝓝 p, g x = f x := by
    have hFeqP : F =ᶠ[𝓝 (P p)] f := by rw [hPp]; exact hFeq
    have h := (hP.continuous.continuousAt : ContinuousAt P p).tendsto.eventually hFeqP
    filter_upwards [h] with x hx
    simpa [g, P, hind] using hx
  have hevent : ∀ᶠ x in 𝓝 p, x ∈ Metric.ball p r ∧ g x = f x := by
    filter_upwards [Metric.ball_mem_nhds p hr, hfg] with x hx hfx
    exact ⟨hx, hfx⟩
  obtain ⟨r', hr', hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨i, g, r', hr', ?_, ?_, ?_, ?_, ?_⟩
  · exact hF.comp hP
  · obtain ⟨C, hC⟩ := hF.continuous.bounded_above_of_compact_support hFc
    apply supNorm_lt_top_of_bound C
    intro x _
    simpa [g, Real.norm_eq_abs] using hC (P x)
  · intro x t
    simp [g, P]
  · have h := hfg.self_of_nhds
    simpa [hfp] using h
  · rcases hside with hleft | hright
    · left
      intro x hx
      obtain ⟨hxr, hgfx⟩ := hball hx
      simpa [hgfx] using hleft x hxr
    · right
      intro x hx
      obtain ⟨hxr, hgfx⟩ := hball hx
      simpa [hgfx] using hright x hxr

/-- The boundary graph can be chosen Lipschitz on the local chart. -/
theorem definingFunction_local_lipschitz_graph {d : ℕ} {σ : ℝ} {U : Set (Fin d → ℝ)}
    (hU : IsC2HolderDomain σ U) {p : Fin d → ℝ} (hp : p ∈ frontier U) :
    ∃ (i : Fin d) (g : (Fin d → ℝ) → ℝ) (r : ℝ) (K : NNReal), 0 < r ∧
      ContDiff ℝ 2 g ∧ supNorm Set.univ g < ⊤ ∧
      LipschitzOnWith K g (Metric.ball p r) ∧
      (∀ x t, g (Function.update x i t) = g x) ∧ g p = p i ∧
      ((∀ x ∈ Metric.ball p r, x ∈ U ↔ x i < g x) ∨
       (∀ x ∈ Metric.ball p r, x ∈ U ↔ g x < x i)) := by
  obtain ⟨i, g, r, hr, hg, hbound, hind, hgp, hside⟩ :=
    definingFunction_global_C2_local_graph hU hp
  obtain ⟨K, s, hs, hLip⟩ := (hg.contDiffAt.of_le (by norm_num) :
    ContDiffAt ℝ 1 g p).exists_lipschitzOnWith
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨i, g, min r δ, K, lt_min hr hδ, hg, hbound,
    hLip.mono (fun x hx => hδs (Metric.ball_subset_ball (min_le_right _ _) hx)),
    hind, hgp, ?_⟩
  have hsub : Metric.ball p (min r δ) ⊆ Metric.ball p r :=
    Metric.ball_subset_ball (min_le_left _ _)
  rcases hside with hleft | hright
  · exact Or.inl (fun x hx => hleft x (hsub hx))
  · exact Or.inr (fun x hx => hright x (hsub hx))

/-- A nonzero coordinate derivative stays uniformly away from zero near the point. -/
theorem exists_partialDeriv_abs_lower_bound {d : ℕ} (ρ : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (p : Fin d → ℝ) (i : Fin d)
    (hi : partialDeriv i ρ p ≠ 0) :
    ∃ a r : ℝ, 0 < a ∧ 0 < r ∧
      ∀ x ∈ Metric.ball p r, a ≤ |partialDeriv i ρ x| := by
  have hpcont : Continuous (partialDeriv i ρ) := by
    exact (hρ.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  have hpos : 0 < |partialDeriv i ρ p| := abs_pos.mpr hi
  let a := |partialDeriv i ρ p| / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let V : Set (Fin d → ℝ) := {x | a < |partialDeriv i ρ x|}
  have hV : IsOpen V := isOpen_lt continuous_const hpcont.abs
  have hpV : p ∈ V := by dsimp [V, a]; linarith
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV p hpV
  exact ⟨a, r, ha, hr, fun x hx => (hrV hx).le⟩

/-- The second-order chain rule along a local zero graph. -/
theorem secondPartial_graph_identity {d : ℕ} (ρ g : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (hg : ContDiff ℝ 2 g) (i : Fin d)
    {x : Fin d → ℝ} (hzero : ∀ᶠ y in 𝓝 x, ρ (Function.update y i (g y)) = 0)
    (j k : Fin d) :
    ∑ l, ((∑ m, secondPartial m l ρ (Function.update x i (g x)) *
      partialDeriv j (fun y => Function.update y i (g y) m) x) *
      partialDeriv k (fun y => Function.update y i (g y) l) x +
      partialDeriv l ρ (Function.update x i (g x)) *
      secondPartial j k (fun y => Function.update y i (g y) l) x) = 0 := by
  let φ : (Fin d → ℝ) → (Fin d → ℝ) := fun y => Function.update y i (g y)
  have hφ : ContDiff ℝ 2 φ := by
    have h := (contDiff_update_pair i).comp (contDiff_id.prodMk hg)
    simpa [φ, Function.comp_def] using h
  have hz : (ρ ∘ φ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hzero] with y hy
    exact hy
  have hzd : fderiv ℝ (ρ ∘ φ) =ᶠ[𝓝 x] fderiv ℝ (fun _ => (0 : ℝ)) :=
    hz.eventuallyEq_nhds.mono fun _ h => h.fderiv_eq
  have hc : ContDiffOn ℝ 2 (ρ ∘ φ) Set.univ := (hρ.comp hφ).contDiffOn
  have hzdiff : DifferentiableAt ℝ (fderiv ℝ (ρ ∘ φ)) x :=
    ((hc.fderiv_of_isOpen (m := 1) isOpen_univ (by norm_num)).contDiffAt
      (isOpen_univ.mem_nhds (Set.mem_univ x))).differentiableAt (by norm_num)
  have hpartial : partialDeriv k (ρ ∘ φ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hzd] with y hy
    simp [partialDeriv, hy]
  have hz2 : secondPartial j k (ρ ∘ φ) x = 0 := by
    rw [← fderiv_partialDeriv_apply hzdiff k j, hpartial.fderiv_eq]
    simp
  have hchain := secondPartial_comp (S := Set.univ) (T := Set.univ)
    isOpen_univ isOpen_univ hφ.contDiffOn hρ.contDiffOn (Set.mapsTo_univ φ Set.univ)
    (Set.mem_univ x) k j
  simpa [φ, hz2] using hchain.symm

/-- Coordinate projections have vanishing second partial derivatives. -/
theorem secondPartial_coordinate {d : ℕ} (i j k : Fin d) (x : Fin d → ℝ) :
    secondPartial i j (fun y : Fin d → ℝ => y k) x = 0 := by
  let P : (Fin d → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y : Fin d → ℝ => y k)) x := by
    have he : fderiv ℝ (fun y : Fin d → ℝ => y k) =
        fun _ => P := by
      funext y
      exact P.hasFDerivAt.fderiv
    rw [he]
    exact differentiableAt_const _
  rw [← fderiv_partialDeriv_apply hd j i]
  have he : partialDeriv j (fun y : Fin d → ℝ => y k) =
      fun _ => (Pi.single j (1 : ℝ) : Fin d → ℝ) k := by
    funext y
    change (fderiv ℝ P y) (Pi.single j 1) = _
    rw [P.hasFDerivAt.fderiv]
    rfl
  rw [he]
  simp

/-- The normal derivative multiplies the Hessian of the implicit graph. -/
theorem secondPartial_graph_equation {d : ℕ} (ρ g : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (hg : ContDiff ℝ 2 g) (i : Fin d)
    {x : Fin d → ℝ} (hzero : ∀ᶠ y in 𝓝 x, ρ (Function.update y i (g y)) = 0)
    (j k : Fin d) :
    (∑ l, (∑ m, secondPartial m l ρ (Function.update x i (g x)) *
      partialDeriv j (fun y => Function.update y i (g y) m) x) *
      partialDeriv k (fun y => Function.update y i (g y) l) x) +
      partialDeriv i ρ (Function.update x i (g x)) * secondPartial j k g x = 0 := by
  classical
  have hs : (∑ l, partialDeriv l ρ (Function.update x i (g x)) *
      secondPartial j k (fun y => Function.update y i (g y) l) x) =
      partialDeriv i ρ (Function.update x i (g x)) * secondPartial j k g x := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro l _ hli
      have he : (fun y => Function.update y i (g y) l) = (fun y : Fin d → ℝ => y l) := by
        funext y
        simp [Function.update, hli]
      rw [he, secondPartial_coordinate, mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have h := secondPartial_graph_identity ρ g hρ hg i hzero j k
  rw [Finset.sum_add_distrib, hs] at h
  exact h

/-- The Hessian of a regular implicit graph is given by the defining function. -/
theorem secondPartial_graph_formula {d : ℕ} (ρ g : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (hg : ContDiff ℝ 2 g) (i : Fin d)
    {x : Fin d → ℝ} (hzero : ∀ᶠ y in 𝓝 x, ρ (Function.update y i (g y)) = 0)
    (hreg : partialDeriv i ρ (Function.update x i (g x)) ≠ 0) (j k : Fin d) :
    secondPartial j k g x =
      -(∑ l, (∑ m, secondPartial m l ρ (Function.update x i (g x)) *
        partialDeriv j (fun y => Function.update y i (g y) m) x) *
        partialDeriv k (fun y => Function.update y i (g y) l) x) /
      partialDeriv i ρ (Function.update x i (g x)) := by
  have h := secondPartial_graph_equation ρ g hρ hg i hzero j k
  apply (eq_div_iff hreg).2
  linarith

/-- The normal derivative is uniformly nonzero along a sufficiently small graph. -/
theorem exists_graph_partialDeriv_abs_lower_bound {d : ℕ} {p : Fin d → ℝ}
    (ρ g : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (hg : ContinuousAt g p) (i : Fin d)
    (hgp : g p = p i) (hi : partialDeriv i ρ p ≠ 0) :
    ∃ a r : ℝ, 0 < a ∧ 0 < r ∧
      ∀ x ∈ Metric.ball p r, a ≤ |partialDeriv i ρ (Function.update x i (g x))| := by
  obtain ⟨a, r, ha, hr, hbound⟩ := exists_partialDeriv_abs_lower_bound ρ hρ p i hi
  have hgraph : ContinuousAt (fun x => Function.update x i (g x)) p :=
    (contDiff_update_pair i).continuous.continuousAt.comp (continuousAt_id.prodMk hg)
  have hpgraph : Function.update p i (g p) = p := by simp [hgp]
  have hnear : ∀ᶠ x in 𝓝 p, Function.update x i (g x) ∈ Metric.ball p r := by
    apply hgraph.tendsto.eventually
    change Metric.ball p r ∈ 𝓝 (Function.update p i (g p))
    rw [hpgraph]
    exact Metric.ball_mem_nhds p hr
  obtain ⟨s, hs, hsbound⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨a, s, ha, hs, fun x hx => hbound _ (hsbound hx)⟩

/-- The derivative of a twice differentiable function is locally Lipschitz. -/
theorem exists_fderiv_lipschitzOn_ball {d : ℕ} (g : (Fin d → ℝ) → ℝ)
    (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) :
    ∃ (K : NNReal) (r : ℝ), 0 < r ∧ LipschitzOnWith K (fderiv ℝ g) (Metric.ball p r) := by
  have h := (show ContDiffAt ℝ 1 (fderiv ℝ g) p from
    (hg.fderiv_right (m := 1) (by norm_num)).contDiffAt).exists_lipschitzOnWith
  obtain ⟨K, s, hs, hLip⟩ := h
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  exact ⟨K, r, hr, hLip.mono hrs⟩

/-- The map parametrizing a regular graph is locally Lipschitz. -/
theorem exists_graph_map_lipschitzOn_ball {d : ℕ} (g : (Fin d → ℝ) → ℝ)
    (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) (i : Fin d) :
    ∃ (K : NNReal) (r : ℝ), 0 < r ∧
      LipschitzOnWith K (fun x => Function.update x i (g x)) (Metric.ball p r) := by
  have hφ : ContDiff ℝ 2 (fun x => Function.update x i (g x)) := by
    have h := (contDiff_update_pair i).comp (contDiff_id.prodMk hg)
    simpa [Function.comp_def] using h
  have h := (hφ.contDiffAt.of_le (by norm_num) :
    ContDiffAt ℝ 1 (fun x => Function.update x i (g x)) p).exists_lipschitzOnWith
  obtain ⟨K, s, hs, hLip⟩ := h
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  exact ⟨K, r, hr, hLip.mono hrs⟩

/-- Each coordinate partial of a twice differentiable function is locally Lipschitz. -/
theorem exists_partialDeriv_lipschitzOn_ball {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 f) (p : Fin d → ℝ) (j : Fin d) :
    ∃ (K : NNReal) (r : ℝ), 0 < r ∧
      LipschitzOnWith K (partialDeriv j f) (Metric.ball p r) := by
  obtain ⟨K, r, hr, hK⟩ := exists_fderiv_lipschitzOn_ball f hf p
  refine ⟨‖(Pi.single j (1 : ℝ) : Fin d → ℝ)‖₊ * K, r, hr, ?_⟩
  change LipschitzOnWith _ (fun x => fderiv ℝ f x (Pi.single j 1)) _
  have heval : LipschitzWith ‖(Pi.single j (1 : ℝ) : Fin d → ℝ)‖₊
      (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) :=
    ContinuousLinearMap.lipschitzWith_apply _
  exact heval.comp_lipschitzOnWith hK

/-- Each first coordinate derivative of the graph map is locally Lipschitz. -/
theorem exists_partialDeriv_graph_map_lipschitzOn_ball {d : ℕ}
    (g : (Fin d → ℝ) → ℝ) (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ)
    (i j k : Fin d) :
    ∃ (K : NNReal) (r : ℝ), 0 < r ∧
      LipschitzOnWith K (partialDeriv j (fun x => Function.update x i (g x) k))
        (Metric.ball p r) := by
  have hφ : ContDiff ℝ 2 (fun x : Fin d → ℝ => Function.update x i (g x) k) := by
    have h := (contDiff_update_pair i).comp (contDiff_id.prodMk hg)
    exact (contDiff_apply ℝ ℝ k).comp (by simpa [Function.comp_def] using h)
  exact exists_partialDeriv_lipschitzOn_ball _ hφ p j

/-- Inversion preserves an increment bound when both values stay away from zero. -/
theorem abs_inv_sub_inv_le_of_lower_bound {a b c H R : ℝ}
    (hc : 0 < c) (ha : c ≤ |a|) (hb : c ≤ |b|)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hab : |a - b| ≤ H * R) :
    |a⁻¹ - b⁻¹| ≤ (c⁻¹ * H * c⁻¹) * R := by
  have ha0 : a ≠ 0 := abs_pos.mp (lt_of_lt_of_le hc ha)
  have hb0 : b ≠ 0 := abs_pos.mp (lt_of_lt_of_le hc hb)
  have hia : |a⁻¹| ≤ c⁻¹ := by
    rw [abs_inv]
    exact (inv_le_inv₀ (lt_of_lt_of_le hc ha) hc).2 ha
  have hib : |b⁻¹| ≤ c⁻¹ := by
    rw [abs_inv]
    exact (inv_le_inv₀ (lt_of_lt_of_le hc hb) hc).2 hb
  rw [inv_sub_inv' ha0 hb0, abs_mul, abs_mul, abs_sub_comm b a]
  calc
    _ ≤ (c⁻¹ * (H * R)) * c⁻¹ := by gcongr
    _ = _ := by ring

/-- A Lipschitz increment is a Hölder increment at Euclidean distances at most one. -/
theorem abs_sub_le_rpow_of_lipschitzOnWith {d : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) {S : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} {K : NNReal} (hf : LipschitzOnWith K f S)
    {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : LatticeProb.Euclidean.Lattice.radius (x - y) ≤ 1) :
    |f x - f y| ≤ (K : ℝ) * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  have hnorm : ‖x - y‖ ≤ LatticeProb.Euclidean.Lattice.radius (x - y) :=
    pi_norm_le_radius _
  have hpow : LatticeProb.Euclidean.Lattice.radius (x - y) ≤
      LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge'
        (LatticeProb.Euclidean.Lattice.radius_nonneg _) hxy hσ hσ')
  have h := hf.dist_le_mul x hx y hy
  rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hnorm.trans hpow) K.coe_nonneg)

/-- A sufficiently small coordinate ball has Euclidean diameter less than one. -/
theorem exists_ball_radius_sub_lt_one {d : ℕ} (p : Fin d → ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
      LatticeProb.Euclidean.Lattice.radius (x - y) < 1 := by
  let q : (Fin d → ℝ) × (Fin d → ℝ) → ℝ :=
    fun z => LatticeProb.Euclidean.Lattice.radius (z.1 - z.2)
  have hq : Continuous q :=
    (LatticeProb.Euclidean.Lattice.radius_continuous d).comp (continuous_fst.sub continuous_snd)
  have hp : (p, p) ∈ {z | q z < 1} := by
    simp [q, LatticeProb.Euclidean.Lattice.radius]
  have hn : {z | q z < 1} ∈ 𝓝 (p, p) := (isOpen_lt hq continuous_const).mem_nhds hp
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨s, hs, hsv⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨min r s, lt_min hr hs, ?_⟩
  intro x hx y hy
  have hx₁ : x ∈ u := hru (Metric.ball_subset_ball (min_le_left r s) hx)
  have hy₁ : y ∈ v := hsv (Metric.ball_subset_ball (min_le_right r s) hy)
  exact huv (show (x, y) ∈ u ×ˢ v from ⟨hx₁, hy₁⟩)

/-- Local Lipschitz control gives a Hölder increment bound on a smaller ball. -/
theorem exists_holder_increment_on_ball_of_lipschitz {d : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) {f : (Fin d → ℝ) → ℝ}
    {p : Fin d → ℝ} {K : NNReal} {r : ℝ} (hr : 0 < r)
    (hf : LipschitzOnWith K f (Metric.ball p r)) :
    ∃ s : ℝ, 0 < s ∧ ∀ x ∈ Metric.ball p s, ∀ y ∈ Metric.ball p s,
      |f x - f y| ≤ (K : ℝ) * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  obtain ⟨t, ht, hsmall⟩ := exists_ball_radius_sub_lt_one p
  refine ⟨min r t, lt_min hr ht, ?_⟩
  intro x hx y hy
  exact abs_sub_le_rpow_of_lipschitzOnWith hσ hσ' hf
    (Metric.ball_subset_ball (min_le_left _ _) hx)
    (Metric.ball_subset_ball (min_le_left _ _) hy)
    (hsmall x (Metric.ball_subset_ball (min_le_right _ _) hx)
      y (Metric.ball_subset_ball (min_le_right _ _) hy)).le

/-- The first coordinate derivatives of a graph map have local Hölder increments. -/
theorem exists_holder_increment_partialDeriv_graph_map {d : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (g : (Fin d → ℝ) → ℝ)
    (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) (i j k : Fin d) :
    ∃ (K : ℝ) (r : ℝ), 0 ≤ K ∧ 0 < r ∧
      ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
        |partialDeriv j (fun z => Function.update z i (g z) k) x -
          partialDeriv j (fun z => Function.update z i (g z) k) y| ≤
            K * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  obtain ⟨K, r, hr, hK⟩ := exists_partialDeriv_graph_map_lipschitzOn_ball g hg p i j k
  obtain ⟨s, hs, hbound⟩ := exists_holder_increment_on_ball_of_lipschitz hσ hσ' hr hK
  exact ⟨K, s, K.coe_nonneg, hs, hbound⟩

/-- The reciprocal normal derivative along a regular graph has local Hölder increments. -/
theorem exists_holder_increment_inv_graph_partialDeriv {d : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (ρ g : (Fin d → ℝ) → ℝ)
    (hρ : ContDiff ℝ 2 ρ) (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) (i : Fin d)
    (hgp : g p = p i) (hi : partialDeriv i ρ p ≠ 0) :
    ∃ (K : ℝ) (r : ℝ), 0 ≤ K ∧ 0 < r ∧
      ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
        |(partialDeriv i ρ (Function.update x i (g x)))⁻¹ -
          (partialDeriv i ρ (Function.update y i (g y)))⁻¹| ≤
            K * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  let φ : (Fin d → ℝ) → (Fin d → ℝ) := fun x => Function.update x i (g x)
  have hφ2 : ContDiff ℝ 2 φ := by
    have h := (contDiff_update_pair i).comp (contDiff_id.prodMk hg)
    simpa [φ, Function.comp_def] using h
  have hφ : ContDiff ℝ 1 φ := hφ2.of_le (by norm_num)
  have hρi : ContDiff ℝ 1 (partialDeriv i ρ) := by
    exact (hρ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hc : ContDiff ℝ 1 (fun x => partialDeriv i ρ (φ x)) := hρi.comp hφ
  obtain ⟨K, S, hS, hK⟩ := hc.contDiffAt.exists_lipschitzOnWith (x := p)
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨s, hs, hinc⟩ := exists_holder_increment_on_ball_of_lipschitz hσ hσ' hr
    (hK.mono hrS)
  obtain ⟨a, t, ha, ht, hreg⟩ :=
    exists_graph_partialDeriv_abs_lower_bound ρ g hρ hg.continuous.continuousAt i hgp hi
  refine ⟨a⁻¹ * (K : ℝ) * a⁻¹, min s t, by positivity, lt_min hs ht, ?_⟩
  intro x hx y hy
  have hx₁ := Metric.ball_subset_ball (min_le_left s t) hx
  have hy₁ := Metric.ball_subset_ball (min_le_left s t) hy
  have hx₂ := Metric.ball_subset_ball (min_le_right s t) hx
  have hy₂ := Metric.ball_subset_ball (min_le_right s t) hy
  exact abs_inv_sub_inv_le_of_lower_bound ha (hreg x hx₂) (hreg y hy₂)
    K.coe_nonneg (Real.rpow_nonneg (LatticeProb.Euclidean.Lattice.radius_nonneg _) _)
    (hinc x hx₁ y hy₁)

/-- The Hessian of a defining function has Hölder increments along a local graph. -/
theorem exists_holder_increment_secondPartial_along_graph {d : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (ρ g : (Fin d → ℝ) → ℝ)
    (hρ : ∀ R : ℝ, c2HolderNorm σ
      {x | LatticeProb.Euclidean.Lattice.radius x < R} ρ < ⊤)
    (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) (i : Fin d) :
    ∃ (H : ℝ) (r : ℝ), 0 ≤ H ∧ 0 < r ∧ ∀ j k,
      ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
        |secondPartial j k ρ (Function.update x i (g x)) -
          secondPartial j k ρ (Function.update y i (g y))| ≤
            H * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  let φ : (Fin d → ℝ) → (Fin d → ℝ) := fun x => Function.update x i (g x)
  let R := LatticeProb.Euclidean.Lattice.radius (φ p) + 1
  let T : Set (Fin d → ℝ) := {x | LatticeProb.Euclidean.Lattice.radius x < R}
  have hφ : Continuous φ := by
    have h := (contDiff_update_pair i).comp (contDiff_id.prodMk hg)
    exact (by simpa [φ, Function.comp_def] using h : ContDiff ℝ 2 φ).continuous
  have hT : IsOpen T := isOpen_lt (LatticeProb.Euclidean.Lattice.radius_continuous d)
    continuous_const
  have hpT : φ p ∈ T := by simp [T, R]
  have hn : ∀ᶠ x in 𝓝 p, φ x ∈ T := hφ.continuousAt.tendsto.eventually (hT.mem_nhds hpT)
  obtain ⟨r, hr, hrmap⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨K, s, hs, hK⟩ := exists_graph_map_lipschitzOn_ball g hg p i
  let S := Metric.ball p (min r s)
  have hmap : Set.MapsTo φ S T := fun _ hx =>
    hrmap (Metric.ball_subset_ball (min_le_left r s) hx)
  have hLip : LipschitzOnWith K φ S := hK.mono
    (fun _ hx => Metric.ball_subset_ball (min_le_right r s) hx)
  have hnρ : c2HolderNorm σ T ρ < ⊤ := hρ R
  let H := (c2HolderNorm σ T ρ).toReal *
    (‖(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap‖ * K) ^ σ
  refine ⟨H, min r s, by dsimp [H]; positivity, lt_min hr hs, ?_⟩
  intro j k x hx y hy
  exact abs_sub_comp_le_of_holder_bound hσ ENNReal.toReal_nonneg
    (fun _ hz _ hw => abs_sub_secondPartial_le_c2HolderNorm_toReal hnρ j k hz hw)
    hmap hLip hx hy

/-- All first coordinate derivatives of a graph map share a local Hölder bound. -/
theorem exists_uniform_holder_increment_partialDeriv_graph_map {d : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (g : (Fin d → ℝ) → ℝ)
    (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) (i : Fin d) :
    ∃ (K : ℝ) (r : ℝ), 0 ≤ K ∧ 0 < r ∧ ∀ j k,
      ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
        |partialDeriv j (fun z => Function.update z i (g z) k) x -
          partialDeriv j (fun z => Function.update z i (g z) k) y| ≤
            K * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ := by
  classical
  choose K r hK hr hbound using fun j k : Fin d =>
    exists_holder_increment_partialDeriv_graph_map hσ hσ' g hg p i j k
  have hev (j k : Fin d) : ∀ᶠ z : (Fin d → ℝ) × (Fin d → ℝ) in 𝓝 (p, p),
      |partialDeriv j (fun x => Function.update x i (g x) k) z.1 -
        partialDeriv j (fun x => Function.update x i (g x) k) z.2| ≤
          K j k * LatticeProb.Euclidean.Lattice.radius (z.1 - z.2) ^ σ := by
    have hn : Metric.ball p (r j k) ×ˢ Metric.ball p (r j k) ∈ 𝓝 (p, p) :=
      prod_mem_nhds (Metric.ball_mem_nhds p (hr j k)) (Metric.ball_mem_nhds p (hr j k))
    filter_upwards [hn] with z hz
    exact hbound j k z.1 hz.1 z.2 hz.2
  have heall : ∀ᶠ z : (Fin d → ℝ) × (Fin d → ℝ) in 𝓝 (p, p), ∀ j k,
      |partialDeriv j (fun x => Function.update x i (g x) k) z.1 -
        partialDeriv j (fun x => Function.update x i (g x) k) z.2| ≤
          K j k * LatticeProb.Euclidean.Lattice.radius (z.1 - z.2) ^ σ :=
    Filter.eventually_all.2 fun j => Filter.eventually_all.2 (hev j)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp heall
  obtain ⟨a, ha, hau⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨b, hb, hbv⟩ := Metric.mem_nhds_iff.mp hv
  let M := ∑ j, ∑ k, K j k
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hK j k
  refine ⟨M, min a b, hM, lt_min ha hb, ?_⟩
  intro j k x hx y hy
  have hx₁ : x ∈ u := hau (Metric.ball_subset_ball (min_le_left a b) hx)
  have hy₁ : y ∈ v := hbv (Metric.ball_subset_ball (min_le_right a b) hy)
  have h := huv (show (x, y) ∈ u ×ˢ v from ⟨hx₁, hy₁⟩) j k
  have hkj : K j k ≤ ∑ l, K j l :=
    Finset.single_le_sum (fun l _ => hK j l) (Finset.mem_univ k)
  have hjM : (∑ l, K j l) ≤ M :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun m _ => hK l m) (Finset.mem_univ j)
  exact h.trans (mul_le_mul_of_nonneg_right (hkj.trans hjM)
    (Real.rpow_nonneg (LatticeProb.Euclidean.Lattice.radius_nonneg _) _))

/-- On a smaller ball the first graph derivatives have simultaneous uniform bounds. -/
theorem exists_uniform_bound_partialDeriv_graph_map {d : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (g : (Fin d → ℝ) → ℝ)
    (hg : ContDiff ℝ 2 g) (p : Fin d → ℝ) (i : Fin d) :
    ∃ (B H r : ℝ), 0 ≤ B ∧ 0 ≤ H ∧ 0 < r ∧ ∀ j k,
      (∀ x ∈ Metric.ball p r,
        |partialDeriv j (fun z => Function.update z i (g z) k) x| ≤ B) ∧
      (∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
        |partialDeriv j (fun z => Function.update z i (g z) k) x -
          partialDeriv j (fun z => Function.update z i (g z) k) y| ≤
            H * LatticeProb.Euclidean.Lattice.radius (x - y) ^ σ) := by
  obtain ⟨H, r, hH, hr, hinc⟩ :=
    exists_uniform_holder_increment_partialDeriv_graph_map hσ hσ' g hg p i
  obtain ⟨s, hs, hsmall⟩ := exists_ball_radius_sub_lt_one p
  let V : Fin d → Fin d → ℝ := fun j k =>
    |partialDeriv j (fun z => Function.update z i (g z) k) p|
  let B := H + ∑ j, ∑ k, V j k
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg hH (Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => abs_nonneg _)
  refine ⟨B, H, min r s, hB, hH, lt_min hr hs, ?_⟩
  intro j k
  constructor
  · intro x hx
    have hx₁ := Metric.ball_subset_ball (min_le_left r s) hx
    have hx₂ := Metric.ball_subset_ball (min_le_right r s) hx
    have hp₁ : p ∈ Metric.ball p r := Metric.mem_ball_self hr
    have hp₂ : p ∈ Metric.ball p s := Metric.mem_ball_self hs
    have hpw : LatticeProb.Euclidean.Lattice.radius (x - p) ^ σ ≤ 1 :=
      Real.rpow_le_one (LatticeProb.Euclidean.Lattice.radius_nonneg _)
        (hsmall x hx₂ p hp₂).le hσ
    have hHpow : H * LatticeProb.Euclidean.Lattice.radius (x - p) ^ σ ≤ H := by
      simpa using mul_le_mul_of_nonneg_left hpw hH
    have hvj : V j k ≤ ∑ l, V j l :=
      Finset.single_le_sum (fun l _ => abs_nonneg _) (Finset.mem_univ k)
    have hjB : (∑ l, V j l) ≤ ∑ l, ∑ m, V l m :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun m _ => abs_nonneg _)
        (Finset.mem_univ j)
    have htriangle := abs_add_le
      (partialDeriv j (fun z => Function.update z i (g z) k) x -
        partialDeriv j (fun z => Function.update z i (g z) k) p)
      (partialDeriv j (fun z => Function.update z i (g z) k) p)
    simp only [sub_add_cancel] at htriangle
    have hinc' := hinc j k x hx₁ p hp₁
    dsimp [B, V] at *
    linarith
  · intro x hx y hy
    exact hinc j k x (Metric.ball_subset_ball (min_le_left r s) hx)
      y (Metric.ball_subset_ball (min_le_left r s) hy)

end LatticeProb.Elliptic.HolderExtension
