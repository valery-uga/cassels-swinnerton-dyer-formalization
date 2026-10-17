import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteRestriction
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationFiniteDimension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- For a genuine rank-three finite field datum, actual split point
surjectivity descends to actual restriction onto and native kernel dimension three. -/
theorem pointSplittingFiniteDatumSerre_restriction_surjective_kernel_three
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {X : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of F))
    (D : AllCharacteristics.FiniteSubschemeDatum base 3)
    (s : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover s)
    (hField : IsField Γ(D.val.subscheme, ⊤))
    (e : (∐ fun _ : ULift.{u} (Fin 3) ↦ Spec (.of E)) ≅
      pullback (D.val.subschemeι ≫ base) (Spec.map (CommRingCat.ofHom (algebraMap F E))))
    (he : e.hom ≫ pullback.snd (D.val.subschemeι ≫ base)
        (Spec.map (CommRingCat.ofHom (algebraMap F E))) =
      AllCharacteristics.constantCoverToBase (ULift.{u} (Fin 3)) (Spec (.of E)))
    (hglobal : Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base
        (fun k => pointSplittingFiniteComponentPoint (D.val.subschemeι ≫ base) 3 e (ULift.up k)
          ≫ D.val.subschemeι)
        (fun k => by
          letI : IsFinite (D.val.subschemeι ≫ base) := D.property.1
          simpa only [Category.assoc] using
            pointSplittingFiniteComponentPoint_toBase (D.val.subschemeι ≫ base) 3 e he (ULift.up k))
        (show X.Modules from s.E)))
    (hsource : Module.finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from s.E)) = 9) :
    Function.Surjective (cubicClosedPointSerreDegreeThreeEvaluationMap base D.val.subschemeι
      (show X.Modules from s.E)) ∧
    Module.finrank F (LinearMap.ker (cubicClosedPointSerreDegreeThreeEvaluationMap
      base D.val.subschemeι (show X.Modules from s.E))) = 3 := by
  let q := D.val.subschemeι ≫ base
  letI : IsFinite q := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom q
  letI : Module.Finite F (SchemeModuleGlobalSectionsOver base (show X.Modules from s.E)) :=
    Module.finite_of_finrank_pos (by rw [hsource]; decide)
  have hr := pointSplittingFiniteSerre_restriction_surjective
    base D.val.subschemeι s C hField e he hglobal
  refine ⟨hr, pointSplitting_restriction_kernel_finrank_three _ hsource ?_ hr⟩
  exact cubicClosedPointSerreDegreeThreeEvaluationFiniteDimension_finrank_eq_six base s C D hField

end PfaffianDescent
