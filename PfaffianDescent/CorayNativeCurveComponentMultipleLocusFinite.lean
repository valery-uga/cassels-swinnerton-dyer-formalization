import PfaffianDescent.CorayIntegralCurveClosedSupportFinite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits

/-! Finite native multiple-component locus of an actual curve component
cover. No reducedness of the whole union, cycle or gluing rank is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option autoImplicit false

/-- Native integral curve components have a finite closed multiple-component
locus. The actual component-image equivalence, curve dimensions and structural
Noetherian hypotheses suffice; no finite bad-locus input is supplied. -/
theorem nativeIntegralCurveComponentCover_multipleLocus_finite001
    {ι : Type u} [Finite ι] (X : ι → Scheme.{u}) {T : Scheme.{u}}
    [∀ i, IsIntegral (X i)] [∀ i, NoetherianSpace (X i)]
    (j : ∀ i, X i ⟶ T) (hClosed : ∀ i, IsClosedImmersion (j i))
    (c : ι ≃ irreducibleComponents T) (hc : ∀ i, (c i).1 = Set.range (j i))
    (hDim : ∀ i, ∀ x : X i, Ring.DimensionLEOne ((X i).presheaf.stalk x)) :
    let S := fun i => j i ⁻¹' (⋃ k, ⋃ (_ : k ≠ i), Set.range (j k))
    let Bad := ⋃ i, j i '' S i
    IsClosed Bad ∧ Bad.Finite ∧
      ∀ x ∉ Bad, ∃! i, x ∈ (c i).1 := by
  classical
  letI (i : ι) : IsClosedImmersion (j i) := hClosed i
  let S := fun i => j i ⁻¹' (⋃ k, ⋃ (_ : k ≠ i), Set.range (j k))
  let Bad := ⋃ i, j i '' S i
  have hSClosed (i : ι) : IsClosed (S i) := by
    have hOther : IsClosed (⋃ k, ⋃ (_ : k ≠ i), Set.range (j k)) := by
      apply isClosed_iUnion_of_finite
      intro k
      apply isClosed_iUnion_of_finite
      intro _
      exact (j k).isClosedEmbedding.isClosed_range
    exact hOther.preimage (j i).continuous
  have hGeneric (i : ι) : genericPoint (X i) ∉ S i := by
    intro h
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
    obtain ⟨hne, hPoint⟩ := Set.mem_iUnion.mp hk
    have hPreClosed : IsClosed (j i ⁻¹' Set.range (j k)) :=
      (j k).isClosedEmbedding.isClosed_range.preimage (j i).continuous
    have hWhole : (Set.univ : Set (X i)) ⊆ j i ⁻¹' Set.range (j k) := by
      have hClosure : closure ({genericPoint (X i)} : Set (X i)) ⊆
          j i ⁻¹' Set.range (j k) :=
        closure_minimal (Set.singleton_subset_iff.mpr hPoint) hPreClosed
      simpa only [genericPoint_closure] using hClosure
    have hSubset : Set.range (j i) ⊆ Set.range (j k) := by
      rintro _ ⟨z, rfl⟩
      exact hWhole (Set.mem_univ z)
    have hiComp : Set.range (j i) ∈ irreducibleComponents T := by rw [← hc i]; exact (c i).2
    have hkComp : Set.range (j k) ∈ irreducibleComponents T := by rw [← hc k]; exact (c k).2
    have hReverse : Set.range (j k) ⊆ Set.range (j i) := hiComp.2 hkComp.1 hSubset
    have hEqual : (c k).1 = (c i).1 :=
      (hc k).trans ((Set.Subset.antisymm hSubset hReverse).symm.trans (hc i).symm)
    exact hne (c.injective (Subtype.ext hEqual))
  have hSFinite (i : ι) : (S i).Finite :=
    (integralCurve_closed_avoiding_generic_finite_and_closedPoints
      (X i) (hDim i) (S i) (hSClosed i) (hGeneric i)).1
  have hBadClosed : IsClosed Bad :=
    isClosed_iUnion_of_finite fun i =>
      (j i).isClosedEmbedding.isClosedMap _ (hSClosed i)
  have hBadFinite : Bad.Finite :=
    Set.finite_iUnion fun i => (hSFinite i).image (j i)
  refine ⟨hBadClosed, hBadFinite, ?_⟩
  intro x hx
  let z : irreducibleComponents T :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let i := c.symm z
  have hi : x ∈ (c i).1 := by
    change x ∈ (c (c.symm z)).1
    rw [c.apply_symm_apply]
    exact mem_irreducibleComponent
  refine ⟨i, hi, ?_⟩
  intro k hk
  by_contra hne
  have hxI : x ∈ Set.range (j i) := (hc i) ▸ hi
  obtain ⟨y, hy⟩ := hxI
  have hyS : y ∈ S i := by
    refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hne, ?_⟩⟩
    rw [hy]
    exact (hc k) ▸ hk
  exact hx (Set.mem_iUnion.mpr ⟨i, ⟨y, hyS, hy⟩⟩)

end PfaffianDescent.Coray
