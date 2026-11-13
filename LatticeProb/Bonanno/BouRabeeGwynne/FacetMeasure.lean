/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.FacetMeasure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.PaperObjects
import Mathlib.Analysis.Convex.Intrinsic

open scoped ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

/-- A nonempty compact convex set has positive finite volume in its affine span. -/
lemma euclideanHausdorffMeasure_affineSpan_pos_lt_top {d : ℕ} {s : Set (Euc d)}
    (hs : IsCompact s) (hconv : Convex ℝ s) (hne : s.Nonempty) :
    0 < μHE[Module.finrank ℝ (affineSpan ℝ s).direction] s ∧
      μHE[Module.finrank ℝ (affineSpan ℝ s).direction] s < ∞ := by
  classical
  let A := affineSpan ℝ s
  obtain ⟨p, hp⟩ := hne
  let pA : A := ⟨p, subset_affineSpan ℝ s hp⟩
  let : Nonempty A := ⟨pA⟩
  let e : A.direction ≃ᵢ A := IsometryEquiv.vaddConst pA
  let f : A.direction → Euc d := fun a => (e a).val
  let u : Set A.direction := f ⁻¹' s
  have hf : Isometry f := isometry_subtype_coe.comp e.isometry
  have hu : IsCompact u := hf.isClosedEmbedding.isCompact_preimage hs
  have hrel : (interior (Subtype.val ⁻¹' s : Set A)).Nonempty := by
    have hi := Set.Nonempty.intrinsicInterior hconv ⟨p, hp⟩
    simpa only [intrinsicInterior, Set.image_nonempty] using hi
  have hint : (interior u).Nonempty := by
    obtain ⟨x, hx⟩ := hrel
    refine ⟨e.symm x, ?_⟩
    change e.toHomeomorph.symm x ∈
      interior (e.toHomeomorph ⁻¹' (Subtype.val ⁻¹' s : Set A))
    rw [← e.toHomeomorph.preimage_interior]
    simpa using hx
  have himage : f '' u = s := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      let xA : A := ⟨x, subset_affineSpan ℝ s hx⟩
      refine ⟨e.symm xA, ?_, ?_⟩
      · change (e (e.symm xA)).val ∈ s
        simpa using hx
      · change (e (e.symm xA)).val = x
        simp [xA]
  have hmeasure : μHE[Module.finrank ℝ A.direction] s = volume u := by
    calc
      μHE[Module.finrank ℝ A.direction] s =
          μHE[Module.finrank ℝ A.direction] (f '' u) := congrArg _ himage.symm
      _ = μHE[Module.finrank ℝ A.direction] u :=
        hf.euclideanHausdorffMeasure_image u
      _ = volume u := by rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  change 0 < μHE[Module.finrank ℝ A.direction] s ∧
    μHE[Module.finrank ℝ A.direction] s < ∞
  rw [hmeasure]
  exact ⟨Measure.measure_pos_of_nonempty_interior volume hint, hu.measure_lt_top⟩

namespace TilingData

variable {d : ℕ} (T : TilingData d)

lemma facet_compact (v w : T.V) : IsCompact (T.facet v w) :=
  (T.cell v).compact.inter_right (T.cell w).compact.isClosed

lemma facet_convex (v w : T.V) : Convex ℝ (T.facet v w) :=
  (T.cell v).convex.inter (T.cell w).convex

/-- Codimension-one convex contacts have strictly positive finite facet area. -/
lemma facetVolume_pos_lt_top {v w : T.V} (hvw : T.adj v w) :
    0 < T.facetVolume v w ∧ T.facetVolume v w < ∞ := by
  have h := euclideanHausdorffMeasure_affineSpan_pos_lt_top
    (T.facet_compact v w) (T.facet_convex v w) hvw.2.1
  have hdim : Module.finrank ℝ (affineSpan ℝ (T.facet v w)).direction = d - 1 :=
    hvw.2.2
  change 0 < μHE[d - 1] (T.facet v w) ∧ μHE[d - 1] (T.facet v w) < ∞
  rw [← hdim]
  exact h

lemma facetVolume_pos {v w : T.V} (hvw : T.adj v w) :
    0 < T.facetVolume v w :=
  (T.facetVolume_pos_lt_top hvw).1

lemma facetVolume_ne_top {v w : T.V} (hvw : T.adj v w) :
    T.facetVolume v w ≠ ∞ :=
  (T.facetVolume_pos_lt_top hvw).2.ne

lemma facetVolume_toReal_pos {v w : T.V} (hvw : T.adj v w) :
    0 < (T.facetVolume v w).toReal :=
  ENNReal.toReal_pos (T.facetVolume_pos hvw).ne' (T.facetVolume_ne_top hvw)

lemma edgeLength_ne_top (v w : T.V) : T.edgeLength v w ≠ ∞ :=
  ENNReal.ofReal_ne_top

lemma edgeLength_pos {v w : T.V} (hvw : T.adj v w) :
    0 < T.edgeLength v w := by
  apply ENNReal.ofReal_pos.mpr
  apply norm_pos_iff.mpr
  intro hzero
  exact hvw.1 (T.pos_injective (sub_eq_zero.mp hzero).symm)

lemma conductance_pos {v w : T.V} (hvw : T.adj v w) :
    0 < T.conductance v w :=
  ENNReal.div_pos (T.facetVolume_pos hvw).ne' (T.edgeLength_ne_top v w)

lemma conductance_ne_top {v w : T.V} (hvw : T.adj v w) :
    T.conductance v w ≠ ∞ :=
  ENNReal.div_ne_top (T.facetVolume_ne_top hvw) (T.edgeLength_pos hvw).ne'

end TilingData

end BouRabeeGwynne
