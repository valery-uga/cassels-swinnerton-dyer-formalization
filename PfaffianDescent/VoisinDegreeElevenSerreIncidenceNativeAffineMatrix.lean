import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeMatrix

/-! # The actual affine six-by-nine Serre evaluation matrix -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Affine configuration charts and their three marked factorizations are
constructed from the actual Serre cover at any actual configuration point. -/
theorem serreIncidenceNativeAffineChart_exists_at
    {X B : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (marked : Fin 3 → (B ⟶ X)) (b : B) :
    ∃ (A : Scheme.{u}) (a : A ⟶ B) (chart : Fin 3 → C.ι)
      (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme),
      IsAffine A ∧ IsOpenImmersion a ∧ b ∈ Set.range a ∧
      ∀ i, markedA i ≫ (C.U (chart i)).ι = a ≫ marked i :=
  serreThreePointTrivializingAffineChart_exists_at
    (serreIncidenceRankTwoAffineCover e C) marked b

/-- The nine global sections and six affine bundle coordinates give this
literal matrix over the actual affine configuration ring. -/
def serreIncidenceNativeAffineEvaluationMatrix
    {F : Type u} [Field F] {X A : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank F
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme) :
    Matrix (Fin 3 × ULift.{u} (Fin 2)) (Fin 9) Γ(A, ⊤) :=
  serreThreePointRelativeEvaluationMatrix
    (serreIncidenceRankTwoAffineCover e C) chart markedA
    (serreIncidenceNineGlobalSections base e h9)

/-- A field-valued configuration specializes each entry to the actual free
coordinate of the actual basis section at its actual marked point. -/
theorem serreIncidenceNativeAffineEvaluationMatrix_fieldPoint
    {F L : Type u} [Field F] [Field L] {X A : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of F)) (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank F
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (markedA : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (b : Spec (.of L) ⟶ A) (row : Fin 3 × ULift.{u} (Fin 2)) (col : Fin 9) :
    fieldPointΓevaluation b
      (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedA row col) =
    fieldPointΓevaluation (b ≫ markedA row.1)
      (BundleSectionZeroLocus.sectionCoordinateOfFreeIso (ULift.{u} (Fin 2))
        (BundleSectionZeroLocus.localFreeIsoOfOver (C.U (chart row.1))
          (ULift.{u} (Fin 2)) (C.trivialization (chart row.1)))
        (BundleSectionZeroLocus.restrictSectionToOpen (C.U (chart row.1))
          (serreIncidenceNineGlobalSections base e h9 col)) row.2) :=
  serreThreePointRelativeEvaluationMatrix_fieldPoint
    (serreIncidenceRankTwoAffineCover e C) chart markedA
    (serreIncidenceNineGlobalSections base e h9) b row col

end PfaffianDescent
