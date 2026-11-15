/-
Ported from the Exploding-Sandpiles repository (Apache-2.0): `Exploding/Support/ExtMHCount.lean`,
declaration `xmh_starCount` (lines 294 to 403 of the source), and `Exploding/Support/ExtMHProof.lean`,
declarations `xmh_bitLaw_univ`, `xmh_bitLaw_false`, `xmh_site_closed_prob` and `xmh_peierls_union`.
Names and statements are kept; the namespace is `LatticeProb.Percolation.Peierls`, and the Bernoulli
laws are those of `LatticeProb.Percolation.LSS`.
-/
import LatticeProb.Prob.Percolation.Peierls.KingWalk
import LatticeProb.Prob.Percolation.LSS.Basic

/-!
# `*`-animals and closed sites under Bernoulli site percolation

Two counting and probability inputs of the Peierls estimate of Lemma 5.2 of Mathieu on the holes
of the infinite cluster of site percolation.

* The exponential count of `*`-connected sets: a connected finite set of sites is the support of a
  closed king walk of length at most twice its number of vertices, so the `*`-connected sets of
  `m` sites through a fixed point are at most `(3 ^ d) ^ (2 * (m - 1))` in number.
* The probability that a prescribed finite set of sites is entirely closed is `(1 - q)` to the
  power of its cardinality, and a finite family of sets of equal size is hit by a closed set with
  probability at most its size times `(1 - q)` to that size (the union bound).
-/

namespace LatticeProb.Percolation.Peierls

open LatticeProb MeasureTheory LatticeProb.Percolation.LSS SimpleGraph Relation

variable {d : ℕ}

/-! ### Exponential count of `*`-connected sets -/

/-- **Exponential count of `*`-connected sets.**  There is a constant `K` (depending only on
`d`) such that for every site `p` and size `m` the `*`-connected `m`-sets containing `p` lie
in a family of at most `K ^ m` sets. -/
theorem xmh_starCount (d : ℕ) : xmh_StarCount d := by
  classical
  refine ⟨(3 ^ d) ^ 2, fun p m => ?_⟩
  by_cases hm : m = 0
  · subst hm
    refine ⟨{∅}, by simp, fun F _ hFcard _ => ?_⟩
    rw [Finset.mem_singleton]
    exact Finset.card_eq_zero.mp hFcard
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    let L : ℕ := 2 * (m - 1)
    let T : Finset (Finset (Site d)) := Finset.univ.image (fun u : Fin L → xmh_KingDir d =>
      (xmh_posList p (List.ofFn u)).toFinset)
    have hTcard : T.card ≤ ((3 ^ d) ^ 2) ^ m := by
      refine (Finset.card_image_le.trans ?_)
      have hK : Fintype.card (xmh_KingDir d) = 3 ^ d := by
        change Fintype.card (Fin d → Fin 3) = 3 ^ d
        rw [Fintype.card_fun]
        simp
      rw [Finset.card_univ, Fintype.card_fun, hK, Fintype.card_fin]
      have hLm : L ≤ 2 * m := by simp only [L]; omega
      calc (3 ^ d) ^ L ≤ (3 ^ d) ^ (2 * m) :=
            pow_le_pow_right₀ (Nat.one_le_pow d 3 (by norm_num)) hLm
        _ = ((3 ^ d) ^ 2) ^ m := by rw [pow_mul]
    refine ⟨T, hTcard, fun F hFp hFcard hFconn => ?_⟩
    have hpre : ((xmh_kingGraph d).induce (F : Set (Site d))).Preconnected :=
      (xmh_SConn_iff_preconnected (F : Set (Site d))).mp hFconn
    have : Nonempty ↥(F : Set (Site d)) := ⟨(⟨p, by simpa using hFp⟩ : ↥(F : Set (Site d)))⟩
    have hGconn : ((xmh_kingGraph d).induce (F : Set (Site d))).Connected :=
      Connected.mk hpre
    have hcardF : Fintype.card ↥(F : Set (Site d)) = m :=
      (Fintype.card_ofFinset F (fun _ => Iff.rfl)).trans hFcard
    obtain ⟨w', hw'supp, hw'len⟩ :=
      xmh_conn_walk_aux (Fintype.card ↥(F : Set (Site d))) ↥(F : Set (Site d)) rfl
        ((xmh_kingGraph d).induce (F : Set (Site d))) ⟨p, by simpa using hFp⟩ hGconn
    let w : (xmh_kingGraph d).Walk p p :=
      w'.map (xmh_induceHom (xmh_kingGraph d) (F : Set (Site d)))
    let ds : List (xmh_KingDir d) := xmh_walkOffs p p w
    have hwsupp : xmh_posList p ds = w.support := xmh_posList_walkOffs w
    have hlen : ds.length ≤ L := by
      have h1 : ds.length = w'.length := by
        change (xmh_walkOffs p p w).length = w'.length
        rw [xmh_length_walkOffs]
        change (w'.map (xmh_induceHom (xmh_kingGraph d) (F : Set (Site d)))).length = w'.length
        exact Walk.length_map _ w'
      rw [h1]
      have h2 := hw'len
      rw [hcardF] at h2
      simp only [L]
      omega
    have hlast : p + xmh_lastOff ds = p := by
      have h := xmh_lastOff_walkOffs (p := p) (q := p) w
      rw [h]; abel
    let ds' : List (xmh_KingDir d) := ds ++ List.replicate (L - ds.length) (xmh_zeroDir d)
    have hds'len : ds'.length = L := by
      simp only [ds', List.length_append, List.length_replicate]
      omega
    have hds' : xmh_posList p ds' = xmh_posList p ds ++ List.replicate (L - ds.length) p := by
      simp only [ds', xmh_posList_append, hlast]
      rw [xmh_posList_replicate_zero]
      simp
    have hsuppF : w.support.toFinset = F := by
      have hws : w.support = (w'.support).map Subtype.val := by
        exact Walk.support_map (xmh_induceHom (xmh_kingGraph d) (F : Set (Site d))) w'
      ext x
      rw [List.mem_toFinset]
      constructor
      · intro hx
        rw [hws] at hx
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
        exact y.property
      · intro hx
        rw [hws]
        exact List.mem_map.mpr ⟨(⟨x, hx⟩ : ↥(F : Set (Site d))), hw'supp ⟨x, hx⟩, rfl⟩
    have hcover : F ∈ T := by
      refine Finset.mem_image.mpr ⟨fun i : Fin L => ds'.get (Fin.cast hds'len.symm i),
        Finset.mem_univ _, ?_⟩
      have hu : List.ofFn (fun i : Fin L => ds'.get (Fin.cast hds'len.symm i)) = ds' := by
        apply List.ext_get
        · rw [List.length_ofFn, hds'len]
        · intro n h1 h2
          simp only [List.get_ofFn]
          rfl
      rw [hu, hds', List.toFinset_append]
      have hp_mem : p ∈ (xmh_posList p ds).toFinset := by
        rw [List.mem_toFinset]
        cases ds with
        | nil => simp [xmh_posList]
        | cons d ds => simp [xmh_posList]
      have hrep : (List.replicate (L - ds.length) p).toFinset ⊆ (xmh_posList p ds).toFinset := by
        intro x hx
        rw [List.mem_toFinset] at hx
        obtain ⟨_, hxa⟩ := List.mem_replicate.mp hx
        rw [hxa]
        exact hp_mem
      rw [Finset.union_eq_left.mpr hrep, hwsupp, hsuppF]
    exact hcover

/-! ### Closed sites under Bernoulli site percolation -/

/-- The one-site Bernoulli law is a probability measure. -/
theorem xmh_bitLaw_univ {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : bitLaw q Set.univ = 1 := by
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

/-- The one-site Bernoulli law of a closed site. -/
theorem xmh_bitLaw_false (q : ℝ) : bitLaw q {false} = ENNReal.ofReal (1 - q) := by
  simp [bitLaw]

/-- **Finite-cluster expansion.**  The probability that a prescribed finite set of sites is
entirely closed is `(1 - q)` to the power of its cardinality. -/
theorem xmh_site_closed_prob {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (S : Finset (Site d)) :
    sitePercolation d q {ω | ∀ x ∈ S, ω x = false} = ENNReal.ofReal (1 - q) ^ S.card := by
  have : IsProbabilityMeasure (bitLaw q) := ⟨xmh_bitLaw_univ h0 h1⟩
  have hset : {ω : Site d → Bool | ∀ x ∈ S, ω x = false} =
      Set.pi (↑S : Set (Site d)) (fun _ => ({false} : Set Bool)) := by
    ext ω
    simp
  unfold sitePercolation
  rw [hset, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [xmh_bitLaw_false]

/-- **Peierls union bound.**  The probability that some member of a finite family of
`m`-element sets is entirely closed is at most the size of the family times `(1 - q)^m`. -/
theorem xmh_peierls_union {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (T : Finset (Finset (Site d))) (m : ℕ) (hm : ∀ F ∈ T, F.card = m) :
    sitePercolation d q {ω | ∃ F ∈ T, ∀ x ∈ F, ω x = false}
      ≤ T.card * ENNReal.ofReal (1 - q) ^ m := by
  classical
  have hunion : sitePercolation d q {ω | ∃ F ∈ T, ∀ x ∈ F, ω x = false}
      ≤ ∑ F ∈ T, sitePercolation d q {ω | ∀ x ∈ F, ω x = false} := by
    have heq : {ω : Site d → Bool | ∃ F ∈ T, ∀ x ∈ F, ω x = false}
        = ⋃ F ∈ T, {ω : Site d → Bool | ∀ x ∈ F, ω x = false} := by
      ext ω; simp
    rw [heq]
    exact measure_biUnion_finset_le T _
  calc sitePercolation d q {ω | ∃ F ∈ T, ∀ x ∈ F, ω x = false}
      ≤ ∑ F ∈ T, sitePercolation d q {ω | ∀ x ∈ F, ω x = false} := hunion
    _ = ∑ F ∈ T, ENNReal.ofReal (1 - q) ^ F.card := by
        exact Finset.sum_congr rfl fun F _ => xmh_site_closed_prob h0 h1 F
    _ = ∑ _F ∈ T, ENNReal.ofReal (1 - q) ^ m := by
        refine Finset.sum_congr rfl fun F hF => ?_
        rw [hm F hF]
    _ = T.card * ENNReal.ofReal (1 - q) ^ m := by
        rw [Finset.sum_const, nsmul_eq_mul]

end LatticeProb.Percolation.Peierls
