import PfaffianDescent.VoisinFlatGradedFibreProjectiveIncidence
import PfaffianDescent.IndependentPullbackIso
import PfaffianDescent.ProjectiveIdealCancellation
import AllCharacteristics.ProjectiveClassifyingFieldChange

/-!
# The open locus of equations nontrivial on a fixed cubic surface

A ground-field cubic equation determines a rational point of the
projective coefficient space. Because projective coefficient space is
separated over the ground field, this rational point has closed image.
Its complement is the parameter locus on which the represented equation
cannot be a scalar multiple of the surface equation.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K]

/-- The projective coefficient point of a nonzero ground-field cubic is a
closed point, expressed without choosing a normalized coefficient chart. -/
theorem isClosed_range_projectiveClassifyingMap
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    IsClosed (Set.range (projectiveClassifyingMap a ha ha0 (RingHom.id K))) := by
  let f := projectiveClassifyingMap a ha ha0 (RingHom.id K)
  have hf : f ≫ projectiveParametersToBase K (Fin 4) 3 = 𝟙 _ := by
    calc
      f ≫ projectiveParametersToBase K (Fin 4) 3 =
        Spec.map (CommRingCat.ofHom (RingHom.id K)) :=
          projectiveClassifyingMap_toBase a ha ha0 (RingHom.id K)
      _ = 𝟙 _ := by simp
  haveI : IsProper (f ≫ projectiveParametersToBase K (Fin 4) 3) := by
    rw [hf]
    infer_instance
  haveI : IsProper f := IsProper.of_comp f (projectiveParametersToBase K (Fin 4) 3)
  exact f.isClosedMap.isClosed_range

/-- Parameters other than the projective class of the fixed cubic form an
open subset of projective equation space. -/
noncomputable def nontrivialSurfaceEquationOpen
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    (projectiveParameters K (Fin 4) 3).Opens :=
  ⟨(Set.range (projectiveClassifyingMap a ha ha0 (RingHom.id K)))ᶜ,
    (isClosed_range_projectiveClassifyingMap a ha ha0).isOpen_compl⟩

/-- A field-valued parameter landing in the complementary open is
different from the base-changed class of the fixed surface equation. -/
theorem ne_baseChanged_projectiveClassifyingMap_of_mem_nontrivialOpen
    {S : Type u} [Field S] (b : K →+* S)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    (s : Spec (.of S) ⟶ projectiveParameters K (Fin 4) 3)
    (hs : s (IsLocalRing.closedPoint S) ∈
      nontrivialSurfaceEquationOpen a ha ha0) :
    s ≠ Spec.map (CommRingCat.ofHom b) ≫
      projectiveClassifyingMap a ha ha0 (RingHom.id K) := by
  intro heq
  have hmem : s (IsLocalRing.closedPoint S) ∈
      Set.range (projectiveClassifyingMap a ha ha0 (RingHom.id K)) := by
    refine ⟨(Spec.map (CommRingCat.ofHom b)) (IsLocalRing.closedPoint S), ?_⟩
    rw [heq]
    rfl
  exact hs hmem

/-- The projective class of a fixed ground-field equation agrees with the
class of its coefficient extension after restricting parameters back to
the ground field. -/
theorem projectiveClassifyingMap_mapped_ground
    {S : Type u} [Field S] (b : K →+* S)
    (a : MvPolynomial (Fin 4) K) {d : ℕ}
    (ha : a.IsHomogeneous d) (ha0 : a ≠ 0) :
    let haS := ha.map b
    let haS0 : a.map b ≠ 0 := by
      intro h
      exact ha0 (MvPolynomial.map_injective b (RingHom.injective b)
        (by simpa only [map_zero] using h))
    projectiveClassifyingMap (a.map b) haS haS0 (RingHom.id S) ≫
      projectiveParametersCoefficientMap d b =
      Spec.map (CommRingCat.ofHom b) ≫
        projectiveClassifyingMap a ha ha0 (RingHom.id K) := by
  let haS := ha.map b
  let haS0 : a.map b ≠ 0 := by
    intro h
    exact ha0 (MvPolynomial.map_injective b (RingHom.injective b)
      (by simpa only [map_zero] using h))
  calc
    projectiveClassifyingMap (a.map b) haS haS0 (RingHom.id S) ≫
        projectiveParametersCoefficientMap d b =
      projectiveClassifyingMap (a.map b) haS haS0 b :=
        projectiveClassifyingMap_comp_projectiveParametersCoefficientMap
          d b (a.map b) haS haS0
    _ = Spec.map (CommRingCat.ofHom b) ≫
        projectiveClassifyingMap a ha ha0 (RingHom.id K) := by
      simpa only [RingHom.comp_id] using
        (projectiveClassifyingMap_fieldChange
          (RingHom.id K) b a ha ha0 haS0).symm

/-- Restrict any family of cubic equations to the open parameter locus
different from the chosen ground-field surface equation. -/
noncomputable def nontrivialEquationFamily
    {X : Scheme.{u}} (h : X ⟶ projectiveParameters K (Fin 4) 3)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    Scheme.{u} :=
  pullback h (nontrivialSurfaceEquationOpen a ha ha0).ι

/-- The nontrivial-equation family is an actual open subscheme of the
original equation family. -/
theorem nontrivialEquationFamily_toFamily_isOpenImmersion
    {X : Scheme.{u}} (h : X ⟶ projectiveParameters K (Fin 4) 3)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    IsOpenImmersion (pullback.fst h (nontrivialSurfaceEquationOpen a ha ha0).ι) := by
  infer_instance

/-- Every field-valued point of the restricted family has an ambient
equation parameter in the nontrivial open. -/
theorem nontrivialEquationFamily_fieldPoint_mem
    {S : Type u} [Field S] {X : Scheme.{u}}
    (h : X ⟶ projectiveParameters K (Fin 4) 3)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    (s : Spec (.of S) ⟶ nontrivialEquationFamily h a ha ha0) :
    (s ≫ pullback.fst h (nontrivialSurfaceEquationOpen a ha ha0).ι ≫ h)
        (IsLocalRing.closedPoint S) ∈
      nontrivialSurfaceEquationOpen a ha ha0 := by
  let U := nontrivialSurfaceEquationOpen a ha ha0
  have hcond : pullback.fst h U.ι ≫ h = pullback.snd h U.ι ≫ U.ι :=
    pullback.condition
  have heq : (s ≫ pullback.fst h U.ι) ≫ h =
      (s ≫ pullback.snd h U.ι) ≫ U.ι := by
    calc
      _ = s ≫ (pullback.fst h U.ι ≫ h) := Category.assoc _ _ _
      _ = s ≫ (pullback.snd h U.ι ≫ U.ι) := congrArg (fun f => s ≫ f) hcond
      _ = _ := (Category.assoc _ _ _).symm
  change ((s ≫ pullback.fst h U.ι) ≫ h) (IsLocalRing.closedPoint S) ∈ U
  rw [heq]
  change U.ι ((s ≫ pullback.snd h U.ι) (IsLocalRing.closedPoint S)) ∈ U
  exact ((s ≫ pullback.snd h U.ι) (IsLocalRing.closedPoint S)).property

set_option backward.isDefEq.respectTransparency false

/-- On the open set of equations different from the ground cubic, every
field-valued point of a flat projective equation family gives a regular
surface equation. The chosen curve fibre is a closed subscheme of its
represented hypersurface. -/
theorem flatGradedProjectiveFamily_fibrePoint_regular_on_nontrivialOpen
    {R S : Type u} [CommRing R] [IsNoetherianRing R] [Algebra K R]
    [Field S] [Algebra R S] [Algebra K S] [IsScalarTower K R S]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase (a.map (algebraMap K S))
      (ha.map (algebraMap K S)))]
    (t : let W := flatGradedGrassmannian J 3 r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      Spec (.of S) ⟶ pullback
        (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g)
    (ht : let W := flatGradedGrassmannian J 3 r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      t ≫ pullback.snd
        (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g = 𝟙 _)
    (hopen : let W := flatGradedGrassmannian J 3 r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      (t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f)
        (IsLocalRing.closedPoint S) ∈
        nontrivialSurfaceEquationOpen a ha ha0) :
    let W := flatGradedGrassmannian J 3 r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let aS := a.map (algebraMap K S)
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
      (j : scheme C ⟶ hypersurface p hp),
      p ∈ C.toIdeal ∧
      IsClosedImmersion j ∧
      (∀ x : MvPolynomial (Fin 4) S,
        p * x ∈ Ideal.span ({aS} : Set (MvPolynomial (Fin 4) S)) →
        x ∈ Ideal.span ({aS} : Set (MvPolynomial (Fin 4) S))) ∧
      j ≫ hypersurfaceToAmbient p hp = quotientProjMap C ∧
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f =
        projectiveClassifyingMap p hp hp0 (RingHom.id S) ≫
          projectiveParametersCoefficientMap 3 (algebraMap K S) := by
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let aS := a.map (algebraMap K S)
  have haS0 : aS ≠ 0 := by
    intro h
    exact ha0 (MvPolynomial.map_injective (algebraMap K S)
      (RingHom.injective (algebraMap K S))
      (by simpa only [map_zero] using h))
  have hnontrivial :
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f ≠
        projectiveClassifyingMap aS (ha.map (algebraMap K S)) haS0
          (RingHom.id S) ≫
          projectiveParametersCoefficientMap 3 (algebraMap K S) := by
    rw [projectiveClassifyingMap_mapped_ground (algebraMap K S) a ha ha0]
    exact ne_baseChanged_projectiveClassifyingMap_of_mem_nontrivialOpen
      (algebraMap K S) a ha ha0 _ hopen
  have hprime : (Ideal.span ({aS} : Set (MvPolynomial (Fin 4) S))).IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic aS
      (ha.map (algebraMap K S)) haS0
  obtain ⟨p, hp, hp0, hpC, hregular, hparam⟩ :=
    flatGradedProjectiveFamily_fibrePoint_regular_of_parameter_ne_surface
      (K := K) J 3 r q e hRank C hmap aS
      (ha.map (algebraMap K S)) haS0 hprime t ht hnontrivial
  let j := homogeneousFixedCurveToHypersurface p hp C hpC
  exact ⟨p, hp, hp0, j, hpC,
    homogeneousFixedCurveToHypersurface_closedImmersion p hp C hpC,
    hregular,
    homogeneousFixedCurveToHypersurface_comp_hypersurfaceToAmbient p hp C hpC,
    hparam⟩

/-- The actual generic or special field fibre of a flat projective
equation family, restricted to members nontrivial on the fixed cubic. -/
noncomputable def flatGradedProjectiveFibreNontrivialOpen
    {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R] [Field S] [Algebra R S]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    Scheme.{u} := by
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  exact nontrivialEquationFamily
    (pullback.fst (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
      grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f)
    a ha ha0

/-- The nontrivial-equation locus in the relative projective family. -/
noncomputable def flatGradedProjectiveFamilyNontrivialOpen
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    Scheme.{u} := by
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  exact nontrivialEquationFamily
    (grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f)
    a ha ha0

/-- The relative nontrivial-equation family is an open subscheme of the
flat projective equation family. -/
theorem flatGradedProjectiveFamilyNontrivialOpen_isOpenImmersion
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    IsOpenImmersion
      (pullback.fst
        (grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e
          (grassmannianQuotientMorphism K
            (flatGradedGrassmannian J 3 r q e hRank)))
        (nontrivialSurfaceEquationOpen a ha ha0).ι) := by
  exact nontrivialEquationFamily_toFamily_isOpenImmersion _ a ha ha0

/-- The structure map of the relative nontrivial-equation locus. -/
noncomputable def flatGradedProjectiveFamilyNontrivialOpenToBase
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0 ⟶ Spec (.of R) := by
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  exact pullback.fst _ _ ≫
    grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f

/-- Formation of the nontrivial-equation open commutes with a field base change. -/
noncomputable def flatGradedProjectiveFamilyNontrivialOpen_baseChangeIso
    {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R] [Field S] [Algebra R S]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    pullback (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
        flatGradedProjectiveFibreNontrivialOpen (S := S) J r q e hRank a ha ha0 := by
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  exact independentPullbackIso
    (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f)
    (grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f)
    (nontrivialSurfaceEquationOpen a ha ha0).ι
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Restricting the field fibre to nontrivial equations is an open
immersion into the original field fibre. -/
theorem flatGradedProjectiveFibreNontrivialOpen_isOpenImmersion
    {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R] [Field S] [Algebra R S]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0) :
    let W := flatGradedGrassmannian J 3 r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let P := pullback.fst
      (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
      grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
    IsOpenImmersion (pullback.fst P (nontrivialSurfaceEquationOpen a ha ha0).ι) := by
  exact nontrivialEquationFamily_toFamily_isOpenImmersion _ a ha ha0

/-- Every field-valued point over the identity of the actual nontrivial
open fibre represents a nonzero equation of the chosen curve that is
regular modulo the smooth cubic surface equation. -/
theorem flatGradedProjectiveFibreNontrivialOpen_fieldPoint_regular
    {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R] [Field S] [Algebra R S] [Algebra K S]
    [IsScalarTower K R S]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase (a.map (algebraMap K S))
      (ha.map (algebraMap K S)))]
    (s : Spec (.of S) ⟶
      flatGradedProjectiveFibreNontrivialOpen J r q e hRank a ha ha0)
    (hs : let W := flatGradedGrassmannian J 3 r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      let P := pullback.fst
        (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
      (s ≫ pullback.fst P (nontrivialSurfaceEquationOpen a ha ha0).ι) ≫
        pullback.snd
          (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g = 𝟙 _) :
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      (∀ x : MvPolynomial (Fin 4) S,
        p * x ∈ Ideal.span
          ({a.map (algebraMap K S)} : Set (MvPolynomial (Fin 4) S)) →
        x ∈ Ideal.span
          ({a.map (algebraMap K S)} : Set (MvPolynomial (Fin 4) S))) ∧
      IsRegular (Ideal.Quotient.mk
        (Ideal.span ({a.map (algebraMap K S)} : Set (MvPolynomial (Fin 4) S))) p) := by
  let W := flatGradedGrassmannian J 3 r q e hRank
  let f := grassmannianQuotientMorphism K W
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let P := pullback.fst
    (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
    grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
  let t := s ≫ pullback.fst P (nontrivialSurfaceEquationOpen a ha ha0).ι
  have hopen : (t ≫ P) (IsLocalRing.closedPoint S) ∈
      nontrivialSurfaceEquationOpen a ha ha0 := by
    exact nontrivialEquationFamily_fieldPoint_mem P a ha ha0 s
  obtain ⟨p, hp, hp0, j, hpC, -, hregular, -, -⟩ :=
    flatGradedProjectiveFamily_fibrePoint_regular_on_nontrivialOpen
      J r q e hRank C hmap a ha ha0 t hs hopen
  refine ⟨p, hp, hp0, hpC, hregular, ?_⟩
  exact isRegular_iff_mem_nonZeroDivisors.mpr
    (quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal _ p hregular)

/-- A field point of the base-changed relative open represents an equation
of the actual fibre that is regular modulo the smooth cubic surface. -/
theorem flatGradedProjectiveFamilyNontrivialOpen_baseChange_fieldPoint_regular
    {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra K R] [Field S] [Algebra R S] [Algebra K S]
    [IsScalarTower K R S]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase (a.map (algebraMap K S))
      (ha.map (algebraMap K S)))]
    (s : Spec (.of S) ⟶
      pullback (flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hs : s ≫ pullback.snd
      (flatGradedProjectiveFamilyNontrivialOpenToBase J r q e hRank a ha ha0)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) = 𝟙 _) :
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      (∀ x : MvPolynomial (Fin 4) S,
        p * x ∈ Ideal.span
          ({a.map (algebraMap K S)} : Set (MvPolynomial (Fin 4) S)) →
        x ∈ Ideal.span
          ({a.map (algebraMap K S)} : Set (MvPolynomial (Fin 4) S))) ∧
      IsRegular (Ideal.Quotient.mk
        (Ideal.span ({a.map (algebraMap K S)} : Set (MvPolynomial (Fin 4) S))) p) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let φ := flatGradedProjectiveFamilyNontrivialOpen_baseChangeIso
    (S := S) J r q e hRank a ha ha0
  let t : Spec (.of S) ⟶
      flatGradedProjectiveFibreNontrivialOpen J r q e hRank a ha ha0 :=
    s ≫ φ.hom
  have ht : let W := flatGradedGrassmannian J 3 r q e hRank
      let f := grassmannianQuotientMorphism K W
      let P := pullback.fst
        (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e f
      (t ≫ pullback.fst P (nontrivialSurfaceEquationOpen a ha ha0).ι) ≫
        pullback.snd
          (grassmannianFrameProjectiveFamilyPullbackToBase K 3 e f) g = 𝟙 _ := by
    dsimp only [t, φ, flatGradedProjectiveFamilyNontrivialOpen_baseChangeIso]
    rw [Category.assoc, Category.assoc]
    rw [independentPullbackIso_hom_toT]
    exact hs
  exact flatGradedProjectiveFibreNontrivialOpen_fieldPoint_regular
    J r q e hRank C hmap a ha ha0 t ht

end PfaffianDescent
