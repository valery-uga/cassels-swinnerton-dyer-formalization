import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalChosenResidual
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoverYonedaNonzero
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
theorem cubicClosedPointSerreFiniteZeroResidual_original_chosen_parameter_residual_eight_of_rankTwoCover
    (K : Type u) [Field K] {E L₃ : Type u} [Field E] [Field L₃] [Algebra K E] [Algebra K L₃] [FiniteDimensional K L₃]
    {B : Scheme.{u}}
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (SheafOfModules.{u}
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 11)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (C : SerreExtensionRankTwoAffineCover e)
    (j₃ : Spec (.of L₃) ⟶ hypersurface p hp) [IsClosedImmersion j₃]
    (hj₃ : j₃ ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L₃)))
    (hL₃ : Module.finrank K L₃ = 3)
    (cfg : B ⟶ Spec (.of K))
    (marked : Fin 3 → (B ⟶ hypersurface p hp))
    (hm : ∀ n, marked n ≫ hypersurfaceToBase p hp = cfg) :
    let base := hypersurfaceToBase p hp
    let M : (hypersurface p hp).Modules := e.E
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let D := serreIncidenceRankTwoAffineCover e C
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
    let g := serreThreePointSectionIncidenceZeroFamily cfg base pp marked hm zero
    ∀ (t : Spec (.of K) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M),
      t ≫ pp = 𝟙 _ →
      ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base pp marked hm zero),
      s (IsLocalRing.closedPoint E) ∈
        cubicClosedPointSerreFiniteZeroResidual_goodOpen g ⊓
        cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg base pp marked hm zero →
      s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t →
      ∀ n : Fin 3,
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) ∉ Set.range i →
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) = j₃ (IsLocalRing.closedPoint L₃) →
      ∃ R : AllCharacteristics.FiniteSubschemeDatum base 8,
        Disjoint (Set.range R.val.subschemeι) (Set.range j₃) := by
  have hne := cubicClosedPointSerreFiniteZeroResidual_yoneda_nonzero_of_rankTwoCover
    K p hp hp0 i e C
  exact cubicClosedPointSerreFiniteZeroResidual_original_chosen_parameter_residual_eight
    K p hp hp0 i e hne hi hL C j₃ hj₃ hL₃ cfg marked hm

end PfaffianDescent.ProjectiveNegativeTwist
