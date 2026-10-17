import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualChosenQuotient
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceOriginalCanonicalKernel
import PfaffianDescent.VoisinCubicConstantFunctions

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_original_chosen_parameter_exists_seed
    (K : Type u) [Field K] {E : Type u} [Field E] [Algebra K E]
    {B : Scheme.{u}}
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (SheafOfModules.{u}
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e.toSequenceData hExt)
        (show 1 + 1 = 2 by omega) ≠ 0)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (C : SerreExtensionRankTwoAffineCover e)
    (cfg : B ⟶ Spec (.of K))
    (marked : Fin 3 → (B ⟶ hypersurface p hp))
    (hm : ∀ n, marked n ≫ hypersurfaceToBase p hp = cfg) :
    let base := hypersurfaceToBase p hp
    let M : (hypersurface p hp).Modules := e.E
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let D := serreIncidenceRankTwoAffineCover e C
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    ∀ (t : Spec (.of K) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M)
      (ht : t ≫ pp = 𝟙 _)
      (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base pp marked hm zero),
      s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t →
      ∀ n : Fin 3,
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) ∉ Set.range i →
      ∃ (seed : SerreExtensionPencilSeed e)
        (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
        (b : finiteDimensionalProjectiveChartRing K (SchemeModuleGlobalSectionsOver base M) j →+* K)
        (a : K),
        IsUnit a ∧
        b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K (SchemeModuleGlobalSectionsOver base M)) j) =
          RingHom.id K ∧
        serreIncidenceGroundSectionParameter base M j b = t ∧
        seed.lift = e.E.unitHomEquiv
          (cubicClosedPointSerreFiniteZeroResidual_chosenChartSection base M j b) ∧
        let z : SchemeModuleGlobalSectionsOver base M := e.E.unitHomEquiv.symm seed.lift
        ∀ k, b (chartCoordinate (finiteDimensionalProjectiveIdeal K (SchemeModuleGlobalSectionsOver base M)) j k) =
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr (a • z) k := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let D := serreIncidenceRankTwoAffineCover e C
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  dsimp only
  intro t ht s hsp n hout
  obtain ⟨j,b,hb,hbt,hne₀⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_chosenParameter_exists_section base M t ht
  let v₀ := cubicClosedPointSerreFiniteZeroResidual_chosenChartSection base M j b
  have hsp' : s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ serreIncidenceGroundSectionParameter base M j b := by
    rw [hbt]
    exact hsp
  have hlocal : ∀ k, localSectionZeroIdealOfOver (D.U k) (ULift.{u} (Fin 2))
      (D.trivialization k) e.canonicalSection = i.ker.comap (D.U k).ι := by
    intro k
    exact (cubicClosedPointSerreFiniteZeroResidual_canonical_chart_ideal_eq
      K p hp hp0 i e hne ⟨C.U k,C.affine k⟩ (C.trivialization k)).trans
      (cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel i (C.U k).ι)
  let lift := e.E.unitHomEquiv v₀
  let q := SheafOfModules.sectionsMap e.projection lift
  have hq : q ≠ zeroSection _ :=
    cubicClosedPointSerreFiniteZeroResidual_chosen_quotient_nonzero
      base e (p3_smoothCubicGlobalFunctions_surjective K p hp hp0)
      D i hlocal cfg marked hm j b hb s hsp' n hout
  let seed : SerreExtensionPencilSeed e :=
    ⟨q,hq,lift,rfl,fun u => e.inclusion_section_ne_lift_of_projection_eq_nonzero lift q hq rfl u⟩
  refine ⟨seed,j,b,1,isUnit_one,hb,hbt,rfl,?_⟩
  intro k
  simpa only [seed,lift,Equiv.symm_apply_apply,one_smul] using
    (cubicClosedPointSerreFiniteZeroResidual_chosenChartSection_coordinates base M j b k).symm

end PfaffianDescent.ProjectiveNegativeTwist
