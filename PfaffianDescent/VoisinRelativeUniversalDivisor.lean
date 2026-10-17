import PfaffianDescent.VoisinProjectiveNontrivialEquationOpen
import AllCharacteristics.UniversalProjectiveIncidenceProper
import AllCharacteristics.UniversalProjectiveIncidenceClosed
import PfaffianDescent.PullbackToProductClosedImmersion

/-!
# The relative universal equation on a fixed cubic surface

An equation parameter family determines a scheme-theoretic incidence family
on the fixed cubic surface: pull back the universal projective hypersurface
incidence along the map from the surface family to ambient space times
parameters. The present file constructs that family, identifies it as the
intersection with the constant cubic surface in the parameterized universal
incidence family, and proves it is a closed subscheme of the constant cubic
surface family with proper structure map. Cartier and flatness properties
require further work.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K]
  (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
  {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
  (h : E ⟶ projectiveParameters K (Fin 4) 3)

/-- The constant cubic surface over an equation-parameter scheme. -/
noncomputable def fixedCubicSurfaceFamily : Scheme.{u} :=
  pullback (hypersurfaceToBase a ha) k

/-- The field fibre of the constant cubic surface family is the actual
coefficient-changed cubic hypersurface. -/
noncomputable def fixedCubicSurfaceFamilyFieldFibreIso
    {S : Type u} [CommRing S] (b : K →+* S)
    (s : Spec (.of S) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b)) :
    pullback (pullback.snd (hypersurfaceToBase a ha) k) s ≅
      hypersurface (a.map b) (ha.map b) :=
  pullbackLeftPullbackSndIso (hypersurfaceToBase a ha) k s ≪≫
    pullback.congrHom rfl hs ≪≫
      (hypersurfaceBaseChangeIso b a ha).symm

/-- The constant cubic surface family is closed in the ordinary product of
the cubic surface and the equation-parameter scheme. -/
instance fixedCubicSurfaceFamilyToProduct_isClosedImmersion :
    IsClosedImmersion
      (prod.lift (pullback.fst (hypersurfaceToBase a ha) k)
        (pullback.snd (hypersurfaceToBase a ha) k)) := by
  infer_instance

/-- The fixed cubic surface family, embedded in ambient projective space
times the equation-parameter scheme. -/
noncomputable def fixedCubicSurfaceFamilyToAmbientProduct :
    fixedCubicSurfaceFamily a ha k ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯ E :=
  prod.lift
    (pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
    (pullback.snd (hypersurfaceToBase a ha) k)

/-- The constant cubic surface is an actual closed subscheme of ambient
projective space times the equation parameters. -/
instance fixedCubicSurfaceFamilyToAmbientProduct_isClosedImmersion :
    IsClosedImmersion (fixedCubicSurfaceFamilyToAmbientProduct a ha k) := by
  have heq : fixedCubicSurfaceFamilyToAmbientProduct a ha k =
      prod.lift (pullback.fst (hypersurfaceToBase a ha) k)
        (pullback.snd (hypersurfaceToBase a ha) k) ≫
      prod.map (hypersurfaceToAmbient a ha) (𝟙 E) := by
    apply prod.hom_ext <;>
      simp [fixedCubicSurfaceFamilyToAmbientProduct] <;> rfl
  rw [heq]
  exact @IsClosedImmersion.comp _ _ _
    (prod.lift (pullback.fst (hypersurfaceToBase a ha) k)
      (pullback.snd (hypersurfaceToBase a ha) k))
    (prod.map (hypersurfaceToAmbient a ha) (𝟙 E))
    (fixedCubicSurfaceFamilyToProduct_isClosedImmersion a ha k)
    (isClosedImmersion_prodMap_id (hypersurfaceToAmbient a ha))

/-- The surface point and equation parameter as one incidence parameter. -/
noncomputable def fixedCubicSurfaceEquationIncidenceMap :
    fixedCubicSurfaceFamily a ha k ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) ⨯
        projectiveParameters K (Fin 4) 3 :=
  prod.lift
    (pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
    (pullback.snd (hypersurfaceToBase a ha) k ≫ h)

/-- The incidence parameter map factors through the closed ambient-product
embedding of the fixed cubic surface family. -/
theorem fixedCubicSurfaceEquationIncidenceMap_eq :
    fixedCubicSurfaceEquationIncidenceMap a ha k h =
      fixedCubicSurfaceFamilyToAmbientProduct a ha k ≫
        prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))) h := by
  change prod.lift
      (pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
      (pullback.snd (hypersurfaceToBase a ha) k ≫ h) =
    prod.lift
      (pullback.fst (hypersurfaceToBase a ha) k ≫ hypersurfaceToAmbient a ha)
      (pullback.snd (hypersurfaceToBase a ha) k) ≫
        prod.map (𝟙 _) h
  rw [prod.lift_map]
  simp only [Category.comp_id]

/-- The universal equation's scheme-theoretic incidence locus on the fixed
cubic surface family. -/
noncomputable def fixedCubicSurfaceEquationZeroLocus : Scheme.{u} :=
  projectiveUniversalIncidenceBaseChange K (Fin 4) 3
    (fixedCubicSurfaceEquationIncidenceMap a ha k h)

/-- The universal equation incidence family after base change to the chosen
equation parameters, before restricting to the fixed cubic surface. -/
noncomputable def parameterizedUniversalIncidence : Scheme.{u} :=
  pullback
    (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))) h)
    (projectiveUniversalIncidence K (Fin 4) 3)

/-- The relative universal equation on a fixed cubic surface is the
scheme-theoretic intersection of the cubic surface family with the
parameterized universal incidence family. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusIntersectionIso :
    fixedCubicSurfaceEquationZeroLocus a ha k h ≅
      pullback (fixedCubicSurfaceFamilyToAmbientProduct a ha k)
        (pullback.fst
          (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))) h)
          (projectiveUniversalIncidence K (Fin 4) 3)) := by
  change pullback (fixedCubicSurfaceEquationIncidenceMap a ha k h)
      (projectiveUniversalIncidence K (Fin 4) 3) ≅ _
  exact pullback.congrHom
      (fixedCubicSurfaceEquationIncidenceMap_eq a ha k h) rfl ≪≫
    (pullbackRightPullbackFstIso
      (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))) h)
      (projectiveUniversalIncidence K (Fin 4) 3)
      (fixedCubicSurfaceFamilyToAmbientProduct a ha k)).symm

/-- The relative universal equation is closed in the parameterized universal
incidence family, since the fixed cubic surface is closed in ambient space. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusToParameterizedIncidence :
    fixedCubicSurfaceEquationZeroLocus a ha k h ⟶
      parameterizedUniversalIncidence h :=
  (fixedCubicSurfaceEquationZeroLocusIntersectionIso a ha k h).hom ≫
    pullback.snd (fixedCubicSurfaceFamilyToAmbientProduct a ha k)
      (pullback.fst
        (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))) h)
        (projectiveUniversalIncidence K (Fin 4) 3))

instance fixedCubicSurfaceEquationZeroLocusToParameterizedIncidence_isClosedImmersion :
    IsClosedImmersion
      (fixedCubicSurfaceEquationZeroLocusToParameterizedIncidence a ha k h) := by
  unfold fixedCubicSurfaceEquationZeroLocusToParameterizedIncidence
  exact @IsClosedImmersion.comp _ _ _
    (fixedCubicSurfaceEquationZeroLocusIntersectionIso a ha k h).hom
    (pullback.snd (fixedCubicSurfaceFamilyToAmbientProduct a ha k)
      (pullback.fst
        (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))) h)
        (projectiveUniversalIncidence K (Fin 4) 3)))
    (by infer_instance) (by infer_instance)

/-- The zero locus's canonical map to the fixed surface family. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusToSurface :
    fixedCubicSurfaceEquationZeroLocus a ha k h ⟶
      fixedCubicSurfaceFamily a ha k :=
  projectiveUniversalIncidenceBaseChangeToBase K (Fin 4) 3
    (fixedCubicSurfaceEquationIncidenceMap a ha k h)

/-- The universal equation cuts out an actual closed subscheme of the fixed
cubic surface family over arbitrary equation parameters. -/
instance fixedCubicSurfaceEquationZeroLocusToSurface_isClosedImmersion :
    IsClosedImmersion (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h) := by
  change IsClosedImmersion
    (pullback.fst (fixedCubicSurfaceEquationIncidenceMap a ha k h)
      (projectiveUniversalIncidence K (Fin 4) 3))
  letI : IsClosedImmersion (projectiveUniversalIncidence K (Fin 4) 3) :=
    projectiveUniversalIncidence_isClosedImmersion K (Fin 4) 3
  infer_instance

/-- The intersection presentation preserves the canonical projection to the
fixed cubic surface family. -/
theorem fixedCubicSurfaceEquationZeroLocusIntersectionIso_toSurface :
    (fixedCubicSurfaceEquationZeroLocusIntersectionIso a ha k h).hom ≫
      pullback.fst (fixedCubicSurfaceFamilyToAmbientProduct a ha k)
        (pullback.fst
          (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))) h)
          (projectiveUniversalIncidence K (Fin 4) 3)) =
      fixedCubicSurfaceEquationZeroLocusToSurface a ha k h := by
  change ((pullback.congrHom
        (fixedCubicSurfaceEquationIncidenceMap_eq a ha k h) rfl).hom ≫
      (pullbackRightPullbackFstIso
        (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))) h)
        (projectiveUniversalIncidence K (Fin 4) 3)
        (fixedCubicSurfaceFamilyToAmbientProduct a ha k)).inv) ≫
      pullback.fst (fixedCubicSurfaceFamilyToAmbientProduct a ha k)
        (pullback.fst
          (prod.map (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))) h)
          (projectiveUniversalIncidence K (Fin 4) 3)) =
      pullback.fst (fixedCubicSurfaceEquationIncidenceMap a ha k h)
        (projectiveUniversalIncidence K (Fin 4) 3)
  rw [Category.assoc, pullbackRightPullbackFstIso_inv_fst]
  simp [pullback.congrHom, pullback.map]
  exact pullback.lift_fst _ _ _

/-- The zero locus's structure map to the equation-parameter scheme. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusToParameters :
    fixedCubicSurfaceEquationZeroLocus a ha k h ⟶ E :=
  fixedCubicSurfaceEquationZeroLocusToSurface a ha k h ≫
    pullback.snd (hypersurfaceToBase a ha) k

/-- The closed immersion of the universal zero locus into the fixed
surface, after pulling both families back to a parameter scheme. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre
    {T : Scheme.{u}} (s : T ⟶ E) :
    pullback (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ⟶
      pullback (pullback.snd (hypersurfaceToBase a ha) k) s :=
  pullback.lift
    (pullback.fst (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≫
      fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)
    (pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s)
    (by
      change pullback.fst
          (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≫
          fixedCubicSurfaceEquationZeroLocusToParameters a ha k h =
        pullback.snd
          (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≫ s
      exact pullback.condition)

theorem fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre_fst
    {T : Scheme.{u}} (s : T ⟶ E) :
    fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s ≫
      pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s =
    pullback.fst (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≫
      fixedCubicSurfaceEquationZeroLocusToSurface a ha k h := by
  exact pullback.lift_fst _ _ _

theorem fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre_snd
    {T : Scheme.{u}} (s : T ⟶ E) :
    fixedCubicSurfaceEquationZeroLocusFibreToSurfaceFibre a ha k h s ≫
      pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s =
    pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s := by
  exact pullback.lift_snd _ _ _

/-- Forming the universal equation zero locus on the fixed surface commutes
with base change of the equation-parameter scheme. The right side first
base-changes the constant surface family, then cuts it by universal
incidence. -/
noncomputable def fixedCubicSurfaceEquationZeroLocusFibreIso
    {T : Scheme.{u}} (s : T ⟶ E) :
    pullback (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≅
      pullback
        (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
          fixedCubicSurfaceEquationIncidenceMap a ha k h)
        (projectiveUniversalIncidence K (Fin 4) 3) := by
  change pullback
      (pullback.fst (fixedCubicSurfaceEquationIncidenceMap a ha k h)
        (projectiveUniversalIncidence K (Fin 4) 3) ≫
          pullback.snd (hypersurfaceToBase a ha) k) s ≅ _
  exact independentPullbackIso
    (pullback.snd (hypersurfaceToBase a ha) k)
    (fixedCubicSurfaceEquationIncidenceMap a ha k h)
    (projectiveUniversalIncidence K (Fin 4) 3) s

/-- The base-change comparison retains the point of the original fixed
surface family. -/
theorem fixedCubicSurfaceEquationZeroLocusFibreIso_toSurface
    {T : Scheme.{u}} (s : T ⟶ E) :
    (fixedCubicSurfaceEquationZeroLocusFibreIso a ha k h s).hom ≫
      pullback.fst
        (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
          fixedCubicSurfaceEquationIncidenceMap a ha k h)
        (projectiveUniversalIncidence K (Fin 4) 3) ≫
          pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s =
      pullback.fst (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≫
        fixedCubicSurfaceEquationZeroLocusToSurface a ha k h := by
  exact independentPullbackIso_hom_toX
    (pullback.snd (hypersurfaceToBase a ha) k)
    (fixedCubicSurfaceEquationIncidenceMap a ha k h)
    (projectiveUniversalIncidence K (Fin 4) 3) s

/-- The fibre comparison preserves the universal-incidence point. -/
theorem fixedCubicSurfaceEquationZeroLocusFibreIso_toIncidence
    {T : Scheme.{u}} (s : T ⟶ E) :
    (fixedCubicSurfaceEquationZeroLocusFibreIso a ha k h s).hom ≫
      pullback.snd
        (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
          fixedCubicSurfaceEquationIncidenceMap a ha k h)
        (projectiveUniversalIncidence K (Fin 4) 3) =
      pullback.fst (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s ≫
        pullback.snd (fixedCubicSurfaceEquationIncidenceMap a ha k h)
          (projectiveUniversalIncidence K (Fin 4) 3) := by
  exact independentPullbackIso_hom_toU
    (pullback.snd (hypersurfaceToBase a ha) k)
    (fixedCubicSurfaceEquationIncidenceMap a ha k h)
    (projectiveUniversalIncidence K (Fin 4) 3) s

/-- The fibre comparison is over the chosen base-change scheme. -/
theorem fixedCubicSurfaceEquationZeroLocusFibreIso_toBaseChange
    {T : Scheme.{u}} (s : T ⟶ E) :
    (fixedCubicSurfaceEquationZeroLocusFibreIso a ha k h s).hom ≫
      pullback.fst
        (pullback.fst (pullback.snd (hypersurfaceToBase a ha) k) s ≫
          fixedCubicSurfaceEquationIncidenceMap a ha k h)
        (projectiveUniversalIncidence K (Fin 4) 3) ≫
          pullback.snd (pullback.snd (hypersurfaceToBase a ha) k) s =
      pullback.snd (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) s := by
  exact independentPullbackIso_hom_toT
    (pullback.snd (hypersurfaceToBase a ha) k)
    (fixedCubicSurfaceEquationIncidenceMap a ha k h)
    (projectiveUniversalIncidence K (Fin 4) 3) s

/-- The universal zero locus is proper over the fixed surface family. -/
instance fixedCubicSurfaceEquationZeroLocusToSurface_isProper :
    IsProper (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h) := by
  unfold fixedCubicSurfaceEquationZeroLocusToSurface
  exact isProper_projectiveUniversalIncidenceBaseChangeToBase K (Fin 4) 3 _

/-- The fixed cubic surface family is proper over the equation parameters. -/
instance fixedCubicSurfaceFamilyToParameters_isProper :
    IsProper (pullback.snd (hypersurfaceToBase a ha) k) := by
  letI : IsProper (hypersurfaceToBase a ha) := inferInstance
  infer_instance

/-- The universal zero locus is proper over the equation parameters. -/
instance fixedCubicSurfaceEquationZeroLocusToParameters_isProper :
    IsProper (fixedCubicSurfaceEquationZeroLocusToParameters a ha k h) := by
  change IsProper
    (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h ≫
      pullback.snd (hypersurfaceToBase a ha) k)
  exact MorphismProperty.IsStableUnderComposition.comp_mem
    (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)
    (pullback.snd (hypersurfaceToBase a ha) k)
    (fixedCubicSurfaceEquationZeroLocusToSurface_isProper a ha k h)
    (fixedCubicSurfaceFamilyToParameters_isProper a ha k)

/-- The support of the relative zero locus is closed in the surface family. -/
theorem fixedCubicSurfaceEquationZeroLocus_range_closed :
    IsClosed (Set.range (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h)) := by
  exact isClosed_range_projectiveUniversalIncidenceBaseChangeToBase K (Fin 4) 3
    (fixedCubicSurfaceEquationIncidenceMap a ha k h)

/-- A point of the surface family is in the support exactly when its
ambient point and equation parameter lie in the universal incidence. -/
theorem fixedCubicSurfaceEquationZeroLocus_range_eq_incidence_preimage :
    Set.range (fixedCubicSurfaceEquationZeroLocusToSurface a ha k h) =
      fixedCubicSurfaceEquationIncidenceMap a ha k h ⁻¹'
        Set.range (projectiveUniversalIncidence K (Fin 4) 3) := by
  exact range_projectiveUniversalIncidenceBaseChangeToBase K (Fin 4) 3
    (fixedCubicSurfaceEquationIncidenceMap a ha k h)

/-- The universal equation parameter carried by the actual relative open
of the flat graded model. -/
noncomputable def flatGradedNontrivialOpenToGlobalParameters
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (ha0 : a ≠ 0) :
    flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0 ⟶
      projectiveParameters K (Fin 4) 3 := by
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  exact pullback.snd
    (grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f)
    (nontrivialSurfaceEquationOpen a ha ha0).ι ≫
      (nontrivialSurfaceEquationOpen a ha ha0).ι

/-- The equation parameter and the flat model determine the same ground-field
structure map on the relative open. -/
theorem flatGradedNontrivialOpenToGlobalParameters_toBase
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (ha0 : a ≠ 0) :
    flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0 ≫
        projectiveParametersToBase K (Fin 4) 3 =
      flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  let p := grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
  let i := (nontrivialSurfaceEquationOpen a ha ha0).ι
  change (pullback.snd p i ≫ i) ≫ projectiveParametersToBase K (Fin 4) 3 =
    (pullback.fst p i ≫ grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R))
  have hpBase : p ≫ projectiveParametersToBase K (Fin 4) 3 =
      grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
    change (pullback.fst (grassmannianFrameProjectiveToGrassmannian K 3 e) f ≫
        grassmannianFrameProjectiveToGlobalParameters K 3 e) ≫
          projectiveParametersToBase K (Fin 4) 3 =
      pullback.snd (grassmannianFrameProjectiveToGrassmannian K 3 e) f ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R))
    calc
      _ = pullback.fst (grassmannianFrameProjectiveToGrassmannian K 3 e) f ≫
          (grassmannianFrameProjectiveToGlobalParameters K 3 e ≫
            projectiveParametersToBase K (Fin 4) 3) :=
        Category.assoc _ _ _
      _ = pullback.fst (grassmannianFrameProjectiveToGrassmannian K 3 e) f ≫
          (grassmannianFrameProjectiveToGrassmannian K 3 e ≫
            grassmannianToBase K r q) := by
        rw [grassmannianFrameProjectiveToGlobalParameters_toBase]
        rfl
      _ = (pullback.snd (grassmannianFrameProjectiveToGrassmannian K 3 e) f ≫ f) ≫
          grassmannianToBase K r q := by
        rw [← Category.assoc, pullback.condition]
      _ = pullback.snd (grassmannianFrameProjectiveToGrassmannian K 3 e) f ≫
          Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
        rw [Category.assoc, grassmannianQuotientMorphism_toBase]
  calc
    (pullback.snd p i ≫ i) ≫ projectiveParametersToBase K (Fin 4) 3 =
        (pullback.fst p i ≫ p) ≫ projectiveParametersToBase K (Fin 4) 3 := by
          rw [pullback.condition]
    _ = pullback.fst p i ≫
        (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f ≫
          Spec.map (CommRingCat.ofHom (algebraMap K R))) := by
          rw [Category.assoc, hpBase]
    _ = (pullback.fst p i ≫ grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R)) := by rw [Category.assoc]

/-- The scheme-theoretic universal equation zero locus on the fixed cubic
surface over the nontrivial open of the actual flat projective family. -/
noncomputable def flatGradedNontrivialRelativeZeroLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (ha0 : a ≠ 0) : Scheme.{u} :=
  fixedCubicSurfaceEquationZeroLocus a ha
    (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R)))
    (flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0)

/-- The relative universal zero locus has a canonical structure map to
the nontrivial equation family. -/
noncomputable def flatGradedNontrivialRelativeZeroLocusToParameters
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (ha0 : a ≠ 0) :
    flatGradedNontrivialRelativeZeroLocus a ha J r q e hRank ha0 ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0 :=
  fixedCubicSurfaceEquationZeroLocusToParameters a ha
    (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R)))
    (flatGradedNontrivialOpenToGlobalParameters a ha J r q e hRank ha0)

/-- The actual relative zero locus is proper over the nontrivial equation
family. -/
instance flatGradedNontrivialRelativeZeroLocusToParameters_isProper
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (ha0 : a ≠ 0) :
    IsProper (flatGradedNontrivialRelativeZeroLocusToParameters
      a ha J r q e hRank ha0) := by
  unfold flatGradedNontrivialRelativeZeroLocusToParameters
  exact fixedCubicSurfaceEquationZeroLocusToParameters_isProper a ha _ _

end PfaffianDescent
