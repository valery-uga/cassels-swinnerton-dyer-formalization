import PfaffianDescent.FourCoordinateVertexActualSchemePresentation
import PfaffianDescent.FiniteClosedImmersionRank
import AllCharacteristics.DisjointClosedUnion
import AllCharacteristics.FiniteFlatCycle

/-! The canonical coproduct map into a SEPARATELY supplied whole length-eight
scheme is an isomorphism. This follows from the actual disjoint length-two
closed components and rank equality, without assuming a full-base comparison. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fourCoordinateVertex_wholeScheme_canonicalCoproduct_isIso
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z)
    [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2)
    (hWhole : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 8) :
    IsIso (Sigma.desc c) := by
  let t := i ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  let j := Sigma.desc c
  letI : ∀ r, IsClosedImmersion (c r ≫ i) := fun r => inferInstance
  letI : ∀ r, IsFinite ((c r ≫ i) ≫ toBase ⊥) := by
    intro r
    rw [Category.assoc]
    infer_instance
  letI : IsClosedImmersion j := AllCharacteristics.isClosedImmersion_sigmaDesc_of_disjoint c hDisjoint
  letI : IsFinite (j ≫ t) := inferInstance
  have hComponents' : ∀ r, AllCharacteristics.finiteSchemeRank ((c r ≫ i) ≫ toBase ⊥) = 2 := by
    intro r
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, Category.assoc,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hComponents r
  obtain ⟨U, e, hdiag, hrows, hModel⟩ :=
    fourCoordinateVertex_actual_scheme_presentation Y (fun r => c r ≫ i) hSupport hComponents'
  let q := QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
  have hSigma : Sigma.desc (fun r => (c r ≫ i) ≫ quotientProjMap ⊥) =
      j ≫ i ≫ quotientProjMap ⊥ := by
    apply Sigma.hom_ext
    intro r
    simp only [j, Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
  have hSquare : e.hom ≫ q = j ≫ i ≫ quotientProjMap ⊥ := hModel.trans hSigma
  have hqBase : q ≫ ambientToBase =
      Spec.map (CommRingCat.ofHom (algebraMap K (QuarticNet.FourTangentDualAlgebra K))) := by
    rw [Category.assoc, quotientProjMap_toBase]
    exact linearNormalizedPointAt_toBase _ _ _ _ _ _
  have hBase : e.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (QuarticNet.FourTangentDualAlgebra K))) = j ≫ t := by
    have h := congrArg (fun f => f ≫ ambientToBase (R := K)) hSquare
    simp only [Category.assoc, quotientProjMap_toBase] at h
    rw [hqBase] at h
    exact h
  letI : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap K (QuarticNet.FourTangentDualAlgebra K)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hSource : AllCharacteristics.finiteSchemeRank (j ≫ t) = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, ← hBase,
      Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    exact QuarticNet.fourTangentDualAlgebra_finrank (K := K)
  exact isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq j t (hSource.trans hWhole.symm)

end PfaffianDescent
