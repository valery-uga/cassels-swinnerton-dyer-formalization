import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalCanonicalRankClosedSupportSeed
import PfaffianDescent.SerreActualConfigurationPlaneData
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGenericGoodMembership

/-! Native rank six and the SAME canonical support seed construct an actual
good, simple-zero parameter at the generic configuration. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreRank_exists_native_generic_good_parameter
    {K L E : Type u} [Field K] [CharZero K] [Field L] [Field E]
    [Algebra K L] [FiniteDimensional K L] [Algebra K E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E)) = 9)
    {B : Scheme.{u}} [IsAffine B] [IsIntegral B]
    (a : B ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion a]
    (chart : Fin 3 → C.ι) (marked : ∀ n, B ⟶ (C.U (chart n)).toScheme)
    (hmarked : ∀ n, marked n ≫ (C.U (chart n)).ι =
      (a ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
    (hm : ∀ n, (marked n ≫ (C.U (chart n)).ι) ≫ hypersurfaceToBase p hp =
      a ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom)
    (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hminor : IsUnit (Matrix.det (Matrix.submatrix
      (serreIncidenceNativeAffineEvaluationMatrix (hypersurfaceToBase p hp) e C h9 chart marked)
      id m)))
    (c : Spec (.of E) ⟶ B) (α : Fin 3 → (L →ₐ[K] E))
    (hsupport : ∀ n, Spec.map (CommRingCat.ofHom (α n).toRingHom) ≫ i =
      (c ≫ marked n) ≫ (C.U (chart n)).ι) :
    let base := hypersurfaceToBase p hp
    let M : (hypersurface p hp).Modules := e.E
    let D := serreIncidenceRankTwoAffineCover e C
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let cfg := a ≫ (orderedFamilyConfigurationOver base 3).hom
    let marked' := fun n => marked n ≫ (C.U (chart n)).ι
    let I := serreThreePointSectionIncidence cfg base pp marked' hm zero
    let π := serreThreePointSectionIncidenceToConfiguration cfg base pp marked' hm zero
    let g := serreThreePointSectionIncidenceZeroFamily cfg base pp marked' hm zero
    ∃ s : Spec (B.residueField (genericPoint B)) ⟶ I,
      s ≫ π = B.fromSpecResidueField (genericPoint B) ∧
      s (IsLocalRing.closedPoint (B.residueField (genericPoint B))) ∈
        serreIncidenceGoodOpen g
          (cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg base pp marked' hm zero) ∧
      IsFinite (pullback.snd g s) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let D := serreIncidenceRankTwoAffineCover e C
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let cfg := a ≫ (orderedFamilyConfigurationOver base 3).hom
  let marked' := fun n => marked n ≫ (C.U (chart n)).ι
  let g := serreThreePointSectionIncidenceZeroFamily cfg base pp marked' hm zero
  let π := serreThreePointSectionIncidenceToConfiguration cfg base pp marked' hm zero
  let W := cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg base pp marked' hm zero
  letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI : HasExt.{u + 1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default))) :=
    moduleCatStalk_hasExt _
  have hcanonical : ∀ n, marked' n = a ≫
      (orderedFamilyConfigurationι base 3).left ≫ (orderedFamilyCoordinate base 3 n).left := by
    intro n
    exact (hmarked n).trans (Category.assoc _ _ _)
  have hsupport' : ∀ n, Spec.map (CommRingCat.ofHom (α n).toRingHom) ≫ i = c ≫ marked' n := by
    intro n
    exact (hsupport n).trans (Category.assoc _ _ _)
  obtain ⟨t, ht, s, hsP, hsC, hgood, hf, he⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_original_rank_closed_support_exists_good_marked_canonical_seed
      K p hp hp0 i e C hi cfg marked' hm a rfl hcanonical c α hsupport'
  have hplane : SerreActualConfigurationPlaneAtChart base e C cfg chart marked hm :=
    serreIncidenceNativeSerre_exists_plane base e C h9 cfg chart marked hm m hminor
  obtain ⟨q, hq, hπ⟩ := hplane
  let F := B.residueField (genericPoint B)
  let f := B.fromSpecResidueField (genericPoint B) ≫ cfg
  let ρ : K →+* F := (Scheme.ΓSpecIso (.of F)).hom.hom.comp (affineFunctionHom f)
  letI : CharZero F := charZero_of_injective_ringHom ρ.injective
  letI : Infinite F := CharZero.infinite F
  letI : IsProper g := inferInstance
  letI : IsFinite (pullback.snd g s) := hf
  let y := s (IsLocalRing.closedPoint E)
  letI : Finite (g.fiber y) := cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_finite g s
  letI : Finite (g ⁻¹' {y} : Set _) := (g.fiberHomeo y).finite_iff.mp inferInstance
  exact serreIncidencePlane_exists_generic_good_open_parameter g W π q hq hπ y
    (Set.toFinite _) hgood.2

end PfaffianDescent
