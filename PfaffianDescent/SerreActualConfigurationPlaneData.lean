import PfaffianDescent.SerreActualConfigurationRankChart
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeSerrePlane

/-! Literal plane incidence on an actual affine configuration chart. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def SerreActualConfigurationPlaneAtChart
    {F : Type u} [Field F] {X A : Scheme.{u}} [IsAffine A] {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (cfg : A ⟶ Spec (.of F)) (chart : Fin 3 → C.ι)
    (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (hmarked : ∀ i, (markedA i ≫ (C.U (chart i)).ι) ≫ base = cfg) : Prop :=
    let D := serreIncidenceRankTwoAffineCover e C
    letI := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base
      (show X.Modules from e.E)
    let I := serreThreePointSectionIncidenceIdeal cfg base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E))
      (fun i => markedA i ≫ (C.U (chart i)).ι) hmarked
      (D.projectiveSectionLocalZeroGluedToAmbient base (show X.Modules from e.E))
    ∃ q : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(A, ⊤))) ≅
        I.subscheme,
      q.hom ≫ I.subschemeι ≫ pullback.fst cfg
        (schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E)) =
        toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(A, ⊤))) ≫ A.isoSpec.inv ∧
      IsOpenMap (I.subschemeι ≫ pullback.fst cfg
        (schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E)))

def SerreActualConfigurationPlaneData
    {F : Type u} [Field F] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9) : Prop :=
    ∃ (A : Scheme.{u}) (a : A ⟶ (orderedFamilyConfigurationOver base 3).left)
      (chart : Fin 3 → C.ι) (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme)
      (hmarked : ∀ i, (markedA i ≫ (C.U (chart i)).ι) ≫ base =
        a ≫ (orderedFamilyConfigurationOver base 3).hom)
      (hAffine : IsAffine A),
      IsOpenImmersion a ∧ IsIntegral A ∧
      (∀ i, markedA i ≫ (C.U (chart i)).ι =
        (a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
          (orderedFamilyCoordinate base 3 i).left) ∧
      ∃ m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9,
      IsUnit (Matrix.det (Matrix.submatrix
        (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA) id m)) ∧
      letI := hAffine
      SerreActualConfigurationPlaneAtChart base e C
        (a ≫ (orderedFamilyConfigurationOver base 3).hom) chart markedA hmarked

end PfaffianDescent
