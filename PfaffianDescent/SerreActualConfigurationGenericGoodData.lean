import PfaffianDescent.CubicClosedPointSerreRankNativeGenericGoodParameter
import PfaffianDescent.SerreActualConfigurationPlanePoint

/-! Native affine rank data retains both its actual plane and an actual
good, simple-zero parameter over the generic configuration. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def SerreActualConfigurationGenericGoodAtChart
    {F : Type u} [Field F] {X B : Scheme.{u}} [IsIntegral B] {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base] [IsProper base] (e : SerreExtensionData X N)
    (C : SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (cfg : B ⟶ Spec (.of F)) (chart : Fin 3 → C.ι)
    (marked : ∀ n, B ⟶ (C.U (chart n)).toScheme)
    (hm : ∀ n, (marked n ≫ (C.U (chart n)).ι) ≫ base = cfg) : Prop :=
    let M : X.Modules := e.E
    let D := serreIncidenceRankTwoAffineCover e C
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let marked' := fun n => marked n ≫ (C.U (chart n)).ι
    let I := serreThreePointSectionIncidence cfg base pp marked' hm zero
    let π := serreThreePointSectionIncidenceToConfiguration cfg base pp marked' hm zero
    let g := serreThreePointSectionIncidenceZeroFamily cfg base pp marked' hm zero
    ∃ s : Spec (B.residueField (genericPoint B)) ⟶ I,
      s ≫ π = B.fromSpecResidueField (genericPoint B) ∧
      s (IsLocalRing.closedPoint (B.residueField (genericPoint B))) ∈
        serreIncidenceGoodOpen g
          (cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg base pp marked' hm zero) ∧
      IsFinite (pullback.snd g s)

def SerreActualConfigurationGenericGoodData
    {F : Type u} [Field F] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base] [IsProper base]
    (e : SerreExtensionData X N) (C : SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank F (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9) : Prop :=
    ∃ (A : Scheme.{u}) (a : A ⟶ (orderedFamilyConfigurationOver base 3).left)
      (chart : Fin 3 → C.ι) (marked : ∀ n, A ⟶ (C.U (chart n)).toScheme)
      (hm : ∀ n, (marked n ≫ (C.U (chart n)).ι) ≫ base =
        a ≫ (orderedFamilyConfigurationOver base 3).hom)
      (hAffine : IsAffine A) (hIntegral : IsIntegral A),
      IsOpenImmersion a ∧
      (∀ n, marked n ≫ (C.U (chart n)).ι =
        (a ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
          (orderedFamilyCoordinate base 3 n).left) ∧
      ∃ m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9,
        IsUnit (Matrix.det (Matrix.submatrix
          (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked) id m)) ∧
        letI := hAffine
        letI := hIntegral
        SerreActualConfigurationPlaneAtChart base e C
          (a ≫ (orderedFamilyConfigurationOver base 3).hom) chart marked hm ∧
        SerreActualConfigurationGenericGoodAtChart base e C
          (a ≫ (orderedFamilyConfigurationOver base 3).hom) chart marked hm

theorem cubicClosedPointSerreGenericGoodData_of_retained_plane
    {K L E : Type u} [Field K] [CharZero K] [Field L] [Field E]
    [Algebra K L] [FiniteDimensional K L] [Algebra K E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E)) = 9)
    (α : Fin 3 → (L →ₐ[K] E))
    (hdata : SerreActualConfigurationPlaneDataAtPoint (hypersurfaceToBase p hp) e C h9
      (fun n => Spec.map (CommRingCat.ofHom (α n).toRingHom) ≫ i)) :
    SerreActualConfigurationGenericGoodData (hypersurfaceToBase p hp) e C h9 := by
  obtain ⟨A, a, chart, marked, c, hm, hAffine, hOpen, hIntegral, hmarked, hpoints,
    m, hminor, hplane⟩ := hdata
  letI : IsAffine A := hAffine
  letI : IsIntegral A := hIntegral
  letI : IsOpenImmersion a := hOpen
  refine ⟨A, a, chart, marked, hm, hAffine, hIntegral, hOpen, hmarked,
    m, hminor, hplane, ?_⟩
  exact cubicClosedPointSerreRank_exists_native_generic_good_parameter
    p hp hp0 i hi e C h9 a chart marked hmarked hm m hminor c α
    (fun n => (hpoints n).symm)

end PfaffianDescent
