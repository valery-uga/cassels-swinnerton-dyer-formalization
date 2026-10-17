import PfaffianDescent.CorayHomogeneousProjectiveComponentBijection
import PfaffianDescent.CorayHomogeneousPrimeComponentGeometry
import PfaffianDescent.CorayIntegralCurveClosedSupportFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! SOURCE ONLY / UNVERIFIED. The literal scheme-theoretic intersection of
DISTINCT actual integral curve components is finite over the ORIGINAL field.
No bounded Hilbert function, component degree or finite-intersection premise.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Distinct relevant minimal components with genuine native curve dimensions
have finite SCHEME-THEORETIC intersection. Its actual source is scheme(C ⊔ D),
including any nilpotents; no reduced point-set replacement occurs. -/
theorem homogeneousDistinctCurveComponents_sup_isFinite
    (I C D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hC : C.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hCrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C)
    (hD : D.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hDrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ D)
    (hne : C ≠ D)
    (hdim : ∀ x : scheme C, ringKrullDim ((scheme C).presheaf.stalk x) ≤ 1) :
    IsFinite (toBase (C ⊔ D)) := by
  classical
  let iC := schemeQuotientMap I C hC.1.2
  let iD := schemeQuotientMap I D hD.1.2
  letI : IsClosedImmersion iC := schemeQuotientMap_closedImmersion I C hC.1.2
  letI : IsClosedImmersion iD := schemeQuotientMap_closedImmersion I D hD.1.2
  have hCgeom := homogeneousMinimalPrime_projective_reducedComponent I C hC hCrel
  have hDgeom := homogeneousMinimalPrime_projective_reducedComponent I D hD hDrel
  letI : IsIntegral (scheme C) := hCgeom.2.1
  letI : IsLocallyNoetherian (scheme C) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase C)
  letI : CompactSpace (scheme C) :=
    QuasiCompact.compactSpace_of_compactSpace (toBase C)
  letI : IsNoetherian (scheme C) := ⟨⟩
  let S : Set (scheme C) := iC ⁻¹' Set.range iD
  have hSclosed : IsClosed S :=
    iD.isClosedEmbedding.isClosed_range.preimage iC.continuous
  have hgeneric : genericPoint (scheme C) ∉ S := by
    intro hg
    have hclosure : closure ({genericPoint (scheme C)} : Set (scheme C)) ⊆ S :=
      closure_minimal (Set.singleton_subset_iff.mpr hg) hSclosed
    have hfull : (Set.univ : Set (scheme C)) ⊆ S := by
      simpa only [genericPoint_closure] using hclosure
    have hsubset : Set.range iC ⊆ Set.range iD := by
      rintro _ ⟨x, rfl⟩
      exact hfull (Set.mem_univ x)
    have hreverse : Set.range iD ⊆ Set.range iC := hCgeom.1.2 hDgeom.1.1 hsubset
    have hrange : Set.range iC = Set.range iD := Set.Subset.antisymm hsubset hreverse
    let e := homogeneousRelevantMinimalPrimesEquivProjectiveComponents I
    have he : e ⟨C, hC, hCrel⟩ = e ⟨D, hD, hDrel⟩ := Subtype.ext hrange
    exact hne (congrArg Subtype.val (e.injective he))
  have hdimNative (x : scheme C) : Ring.DimensionLEOne ((scheme C).presheaf.stalk x) := by
    letI : Ring.KrullDimLE 1 ((scheme C).presheaf.stalk x) :=
      Ring.krullDimLE_iff.mpr (hdim x)
    exact ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  have hfinite : S.Finite :=
    (integralCurve_closed_avoiding_generic_finite_and_closedPoints
      (scheme C) hdimNative S hSclosed hgeneric).1
  let H := C ⊔ D
  have hCH : C.toIdeal ≤ H.toIdeal := by
    change C.toIdeal ≤ C.toIdeal ⊔ D.toIdeal
    exact le_sup_left
  have hDH : D.toIdeal ≤ H.toIdeal := by
    change D.toIdeal ≤ C.toIdeal ⊔ D.toIdeal
    exact le_sup_right
  let jC := schemeQuotientMap C H hCH
  let jD := schemeQuotientMap D H hDH
  letI : IsClosedImmersion jC := schemeQuotientMap_closedImmersion C H hCH
  letI : IsClosedImmersion jD := schemeQuotientMap_closedImmersion D H hDH
  have hcomm (z : scheme H) : iC (jC z) = iD (jD z) := by
    apply (quotientProjMap I).isClosedEmbedding.injective
    calc
      quotientProjMap I (iC (jC z)) = quotientProjMap C (jC z) :=
        congrArg (fun m : scheme C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) =>
          m (jC z)) (schemeQuotientMap_comp_quotientProjMap I C hC.1.2)
      _ = quotientProjMap H z :=
        congrArg (fun m : scheme H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) =>
          m z) (schemeQuotientMap_comp_quotientProjMap C H hCH)
      _ = quotientProjMap D (jD z) :=
        (congrArg (fun m : scheme H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) =>
          m z) (schemeQuotientMap_comp_quotientProjMap D H hDH)).symm
      _ = quotientProjMap I (iD (jD z)) :=
        (congrArg (fun m : scheme D ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) =>
          m (jD z)) (schemeQuotientMap_comp_quotientProjMap I D hD.1.2)).symm
  have hpoints (z : scheme H) : jC z ∈ S := ⟨jD z, (hcomm z).symm⟩
  have hfiniteSource : (Set.univ : Set (scheme H)).Finite :=
    (hfinite.preimage jC.isClosedEmbedding.injective.injOn).subset
      (fun z _ => hpoints z)
  letI : LocallyQuasiFinite (toBase H) :=
    LocallyQuasiFinite.of_finite_preimage_singleton (toBase H)
      (fun _ => hfiniteSource.subset (Set.subset_univ _))
  exact IsFinite.of_locallyQuasiFinite (toBase H)

/-- Primitive selected smooth-cubic/degree-n caller: ALL native component
curve dimensions are derived from the actual original p/q chart quotient.
Only distinct actual relevant minimal components are supplied. -/
theorem selectedProjectiveDistinctComponents_sup_isFinite
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hC : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hCrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ C)
    (hD : D.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hDrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ D)
    (hne : C ≠ D) : IsFinite (toBase (C ⊔ D)) := by
  exact homogeneousDistinctCurveComponents_sup_isFinite
    (projectiveIntersectionIdeal p q hp hq) C D hC hCrel hD hDrel hne
    (selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
      p q hp hp0 n hq hnot C hC.1.2)

end PfaffianDescent.Coray
