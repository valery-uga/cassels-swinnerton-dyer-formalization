import PfaffianDescent.CubicFieldPointChartSerreSections
import PfaffianDescent.CubicClosedDegreeElevenPointSerreExtension

/-! Actual Serre extension with exactly nine global sections at the SAME
closed degree-eleven point and its actual selected chart. -/

noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldPointChartSerre_exists_sequence_nine
    {F L : Type u} [Field F] [CharZero F] [Field L] [Algebra F L]
    [FiniteDimensional F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    (i : Spec (.of L) ⟶ hypersurface P hP) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (j : Fin 4) (g : ChartRing (equationIdeal P hP) j →+* L)
    (hbase : g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L)
    (hgi : Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal P hP) j = i)
    (hL : Module.finrank F L = 11)
    (hker : Module.finrank F (cubicHomogeneousChartRestriction (equationIdeal P hP)
      (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g).ker = 9) :
    let I := equationIdeal P hP
    let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
    let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
    letI : IsClosedImmersion iG := cubicFieldPoint_selectedChart_ambient_isClosedImmersion P hP i j g hgi
    letI : HasExt.{u} (hypersurface P hP).Modules := schemeModules_hasExt _
    letI : HasExt.{u} (Proj (grading I)).Modules := schemeModules_hasExt _
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits I 3
    ∃ e : SerreExtensionSequenceData (hypersurface P hP)
      (closedImmersionIdealTwist iG (positiveSheafOfModules (grading I) 3)),
      (closedImmersionIdealTwistSequence_shortExact iG
        (positiveSheafOfModules (grading I) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface P hP) _ e
          (schemeModules_hasExt _)) (show 1 + 1 = 2 by omega) ≠ 0 ∧
      Module.finrank F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
        (show (hypersurface P hP).Modules from e.E)) = 9 := by
  let I := equationIdeal P hP
  let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
  letI : Infinite F := CharZero.infinite F
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
    cubicFieldPoint_selectedChart_isClosedImmersion P hP i j g hgi
  letI : IsClosedImmersion iG := cubicFieldPoint_selectedChart_ambient_isClosedImmersion P hP i j g hgi
  letI : HasExt.{u} (hypersurface P hP).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (grading I)).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) F)).Modules := schemeModules_hasExt _
  letI : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface P hP).presheaf.stalk (iG default))) :=
    moduleCatStalk_hasExt _
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits I 3
  have hsame : iG = i := cubicFieldPoint_selectedChart_ambient_eq P hP i j g hgi
  have hiG : iG ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)) :=
    (congrArg (fun t => t ≫ hypersurfaceToBase P hP) hsame).trans hi
  obtain ⟨e, he, _⟩ := cubicClosedPointSerreLocalFree_exists_sequence F P hP hP0 iG hiG hL
  refine ⟨e, he, ?_⟩
  exact cubicFieldPointChartSerreSections_finrank_nine P hP hP0 ell g hbase hL hker e

end PfaffianDescent.ProjectiveNegativeTwist
