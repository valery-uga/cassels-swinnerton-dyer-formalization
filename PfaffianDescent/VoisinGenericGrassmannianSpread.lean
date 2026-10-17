import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.LinearAlgebra.Pi
import AllCharacteristics.VoisinGenericCubicConfiguration
import PfaffianDescent.GrassmannianFiniteType
import PfaffianDescent.GrassmannianProper
import PfaffianDescent.GrassmannianQuotientMorphism
import PfaffianDescent.HomogeneousIdealPieces
import PfaffianDescent.HomogeneousProjection
import PfaffianDescent.GrassmannianHomogeneousFrame
import PfaffianDescent.GrassmannianFrameProjectiveProper
import PfaffianDescent.GrassmannianFrameProjectiveFieldPoint

/-!
# Spreading a generic linear system to the configuration base

Voisin's fixed-component argument starts with a linear system over the
function field of the configuration space and then varies it on a nonempty
open part of that space.  This file supplies that passage for the quotient
Grassmannian used in this project.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Over a field, a subspace of the standard ambient module defines a point
of the quotient Grassmannian as soon as the dimension of its quotient is
specified.  This is the elementary linear-algebra bridge used to turn the
generic quadratic system into a scheme-valued point. -/
noncomputable def fieldSubmoduleGrassmannian
    (F : Type u) [Field F] {m n : ℕ}
    (W : Submodule F ((Fin m → F) × (Fin n → F)))
    (hW : Module.finrank F
      (((Fin m → F) × (Fin n → F)) ⧸ W) = n) :
    Module.Grassmannian F ((Fin m → F) × (Fin n → F)) n where
  toSubmodule := W
  finite_quotient := Module.Finite.of_surjective W.mkQ W.mkQ_surjective
  projective_quotient := inferInstance
  rankAtStalk_eq q :=
    (congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := F) (M := ((Fin m → F) × (Fin n → F)) ⧸ W)) q).trans hW

/-- Coordinates on the ten-dimensional space of quadrics in four variables,
split into a block of size `r` and its complementary block. -/
theorem quadraticMonomials_card_for_grassmannian :
    Fintype.card (Monomials (Fin 4) 2) = 10 := by
  have hdim : Module.finrank ℚ
      (MvPolynomial.homogeneousSubmodule (Fin 4) ℚ 2) =
      Fintype.card (Monomials (Fin 4) 2) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact Module.finrank_eq_card_basis
      (MvPolynomial.basisRestrictSupport ℚ {a | a.degree = 2})
  rw [← hdim, four_variable_homogeneous_finrank]
  decide

/-- The monomial enumeration used to split the ten quadratic coordinates
into a system of rank `r` and its complementary block. -/
noncomputable def quadraticGrassmannianMonomialEquiv
    (r : ℕ) (hr : r ≤ 10) :
    Fin (r + (10 - r)) ≃ Monomials (Fin 4) 2 :=
  (finCongr (Nat.add_sub_of_le hr)).trans
    ((finCongr quadraticMonomials_card_for_grassmannian.symm).trans
      (Fintype.equivFin _).symm)

/-- Coordinates on the ten-dimensional space of quadrics in four variables,
split into a block of size `r` and its complementary block.  These are the
same monomial coordinates used by the projective Grassmannian-frame family. -/
noncomputable def quadraticCoordinateEquiv
    (F : Type u) [Field F] (r : ℕ) (hr : r ≤ 10) :
    MvPolynomial.homogeneousSubmodule (Fin 4) F 2 ≃ₗ[F]
      (Fin r → F) × (Fin (10 - r) → F) := by
  exact (grassmannianChartHomogeneousCoordinateEquiv
    (R := F) 2 (quadraticGrassmannianMonomialEquiv r hr)).symm

theorem quadraticSubmodule_finrank_le_ten
    (F : Type u) [Field F]
    (W : Submodule F (MvPolynomial.homogeneousSubmodule (Fin 4) F 2)) :
    Module.finrank F W ≤ 10 := by
  apply W.finrank_le.trans_eq
  rw [four_variable_homogeneous_finrank]
  decide

/-- The coordinate image of a quadratic subspace in the standard ambient
module used by the Grassmannian construction. -/
noncomputable def quadraticCoordinateSubmodule
    (F : Type u) [Field F]
    (W : Submodule F (MvPolynomial.homogeneousSubmodule (Fin 4) F 2)) :
    Submodule F
      ((Fin (Module.finrank F W) → F) ×
        (Fin (10 - Module.finrank F W) → F)) :=
  W.map (quadraticCoordinateEquiv F (Module.finrank F W)
    (quadraticSubmodule_finrank_le_ten F W)).toLinearMap

theorem quadraticCoordinateSubmodule_quotient_finrank
    (F : Type u) [Field F]
    (W : Submodule F (MvPolynomial.homogeneousSubmodule (Fin 4) F 2)) :
    Module.finrank F
      (((Fin (Module.finrank F W) → F) ×
          (Fin (10 - Module.finrank F W) → F)) ⧸
        quadraticCoordinateSubmodule F W) =
      10 - Module.finrank F W := by
  rw [Submodule.finrank_quotient]
  change Module.finrank F
      ((Fin (Module.finrank F W) → F) ×
        (Fin (10 - Module.finrank F W) → F)) -
      Module.finrank F
        (W.map (quadraticCoordinateEquiv F (Module.finrank F W)
          (quadraticSubmodule_finrank_le_ten F W)).toLinearMap) = _
  rw [LinearEquiv.finrank_map_eq]
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
  omega

/-- A quadratic subspace as an actual point of the quotient Grassmannian.
Its underlying Grassmannian submodule is the coordinate image of the given
system, and its quotient has the complementary dimension. -/
noncomputable def quadraticSubspaceGrassmannian
    (F : Type u) [Field F]
    (W : Submodule F (MvPolynomial.homogeneousSubmodule (Fin 4) F 2)) :
    Module.Grassmannian F
      ((Fin (Module.finrank F W) → F) ×
        (Fin (10 - Module.finrank F W) → F))
      (10 - Module.finrank F W) :=
  fieldSubmoduleGrassmannian F (quadraticCoordinateSubmodule F W)
    (quadraticCoordinateSubmodule_quotient_finrank F W)

/-- The degree-two piece of a homogeneous ideal, represented as a point of
the Grassmannian of subspaces of the ten-dimensional quadratic space. -/
noncomputable def fixedCurveQuadraticGrassmannian
    (F : Type u) [Field F]
    (C : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) F)) :
    Module.Grassmannian F
      ((Fin (Module.finrank F (homogeneousIdealPiece C 2)) → F) ×
        (Fin (10 - Module.finrank F (homogeneousIdealPiece C 2)) → F))
      (10 - Module.finrank F (homogeneousIdealPiece C 2)) :=
  quadraticSubspaceGrassmannian F (homogeneousIdealPiece C 2)

@[simp]
theorem fixedCurveQuadraticGrassmannian_toSubmodule
    (F : Type u) [Field F]
    (C : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) F)) :
    (fixedCurveQuadraticGrassmannian F C).toSubmodule =
      quadraticCoordinateSubmodule F (homogeneousIdealPiece C 2) := rfl

/-- Every nonzero quadratic equation containing the fixed curve gives an
actual point of the projective family over the function-field Grassmannian
point.  Its image in the ambient quadratic parameter space represents a
nonzero scalar multiple of the chosen equation. -/
theorem exists_fixedCurveQuadraticGrassmannian_projective_point
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (C : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) F))
    (q : MvPolynomial (Fin 4) F) (hq : q.IsHomogeneous 2)
    (hqC : q ∈ C.toIdeal) (hq0 : q ≠ 0) :
    let r := Module.finrank F (homogeneousIdealPiece C 2)
    let hr : r ≤ 10 := quadraticSubmodule_finrank_le_ten F
      (homogeneousIdealPiece C 2)
    let e := quadraticGrassmannianMonomialEquiv r hr
    ∃ (t : Spec (.of F) ⟶
        grassmannianFrameProjectiveFamilyPullback K 2 e
          (grassmannianQuotientMorphism (A := F) K
            (fixedCurveQuadraticGrassmannian F C)))
      (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 2) (hp0 : p ≠ 0)
      (alpha : F),
      alpha ≠ 0 ∧ p = MvPolynomial.C alpha * q ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToBase K 2 e
          (grassmannianQuotientMorphism (A := F) K
            (fixedCurveQuadraticGrassmannian F C)) = 𝟙 _ ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 2 e
          (grassmannianQuotientMorphism (A := F) K
            (fixedCurveQuadraticGrassmannian F C)) =
        projectiveClassifyingMap p hp hp0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap 2 (algebraMap K F) := by
  dsimp only
  let qh : homogeneousSubmodule (Fin 4) F 2 := ⟨q, hq⟩
  have hqPiece : qh ∈ homogeneousIdealPiece C 2 :=
    (mem_homogeneousIdealPiece_iff C 2 qh).mpr hqC
  apply exists_grassmannianFrameProjectiveFamilyPullback_point_of_mem
    (K := K) (F := F) (quadraticGrassmannianMonomialEquiv
      (Module.finrank F (homogeneousIdealPiece C 2))
      (quadraticSubmodule_finrank_le_ten F (homogeneousIdealPiece C 2)))
    (fixedCurveQuadraticGrassmannian F C) qh
  · exact ⟨qh, hqPiece, rfl⟩
  · intro hzero
    exact hq0 (congrArg Subtype.val hzero)

/-- A finite-dimensional quotient over the function field of an integral
scheme extends, after shrinking around the generic point, to a
Grassmannian-valued family over the original base.  The first equality says
that the extended family has exactly the prescribed generic fibre; the
second says that it remains a family over `Spec K`. -/
theorem exists_open_grassmannian_spread
    {K : Type u} [CommRing K]
    {B : Scheme.{u}} [IsIntegral B]
    [Algebra K B.functionField]
    (sB : B ⟶ Spec (.of K))
    {m n : ℕ}
    (ha : Spec.map (CommRingCat.ofHom (algebraMap K B.functionField)) =
      B.fromSpecStalk (genericPoint B) ≫ sB)
    (W : Module.Grassmannian B.functionField
      ((Fin m → B.functionField) × (Fin n → B.functionField)) n) :
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K m n),
      grassmannianQuotientMorphism (A := B.functionField) K W =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K m n = U.ι ≫ sB := by
  apply spread_out_of_isGermInjective' sB (grassmannianToBase K m n)
    (grassmannianQuotientMorphism (A := B.functionField) K W)
  rw [grassmannianQuotientMorphism_toBase]
  exact ha

/-- The spread in the preceding theorem takes values in a proper parameter
scheme when the coefficient ring is a field.  This is the form needed by the
finite-incidence genericity theorem: after restricting to a nonempty open of
the configuration base, the generic quadratic system is represented by a
point of a proper Grassmannian family. -/
theorem exists_open_grassmannian_spread_with_proper_target
    {K : Type u} [Field K]
    {B : Scheme.{u}} [IsIntegral B]
    [Algebra K B.functionField]
    (sB : B ⟶ Spec (.of K))
    {m n : ℕ}
    (ha : Spec.map (CommRingCat.ofHom (algebraMap K B.functionField)) =
      B.fromSpecStalk (genericPoint B) ≫ sB)
    (W : Module.Grassmannian B.functionField
      ((Fin m → B.functionField) × (Fin n → B.functionField)) n) :
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K m n),
      grassmannianQuotientMorphism (A := B.functionField) K W =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K m n = U.ι ≫ sB ∧
        IsProper (grassmannianToBase K m n) := by
  obtain ⟨U, hηU, f, hf, hbase⟩ :=
    exists_open_grassmannian_spread sB ha W
  exact ⟨U, hηU, f, hf, hbase, inferInstance⟩

/-- The preceding spreading result on the configuration space used in
Voisin's degree-eight argument.  Supplying the coefficient homomorphism of
the generic cubic installs the same `K`-algebra structure that appears in the
Grassmannian generic point. -/
theorem exists_open_cubicConfiguration_grassmannian_spread
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (configLength : ℕ)
    [IsIntegral (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength)]
    {m r : ℕ}
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)
    (ha : Spec.map a =
      AllCharacteristics.HomogeneousProjective.cubicConfigurationGenericBaseMap
          p hp configLength ≫
        AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
          p hp configLength)
    (W : Module.Grassmannian
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField
      ((Fin m → (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
          p hp configLength).functionField) ×
        (Fin r → (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
          p hp configLength).functionField)) r) :
    let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K m r),
      grassmannianQuotientMorphism (A := B.functionField) K W =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K m r =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  letI : Algebra K B.functionField := a.hom.toAlgebra
  apply exists_open_grassmannian_spread
    (AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
      p hp configLength)
    (W := W)
  change Spec.map a =
    AllCharacteristics.HomogeneousProjective.cubicConfigurationGenericBaseMap
        p hp configLength ≫
      AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
        p hp configLength
  exact ha

/-- The quadratic system containing a generic fixed curve spreads to an
actual family of quadratic subspaces on an open neighborhood of the generic
configuration.  This is the family object required by Voisin's moving-divisor
argument. -/
theorem exists_open_fixedCurveQuadraticSystem_spread
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (configLength : ℕ)
    [IsIntegral (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)
    (ha : Spec.map a =
      AllCharacteristics.HomogeneousProjective.cubicConfigurationGenericBaseMap
          p hp configLength ≫
        AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
          p hp configLength)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4)
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)) :
    let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength
    let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (10 - r)),
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveQuadraticGrassmannian B.functionField C) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (10 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
  letI : Algebra K B.functionField := a.hom.toAlgebra
  exact exists_open_cubicConfiguration_grassmannian_spread
    p hp configLength a ha (fixedCurveQuadraticGrassmannian B.functionField C)

/-- The fixed-curve spread carries the actual projective family of its
quadratic members.  The last clause is the Cartesian square identifying this
family as the pullback of the global projective Grassmannian-frame family. -/
theorem exists_open_fixedCurveQuadraticSystem_projectiveFamily
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (configLength : ℕ)
    [IsIntegral (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)
    (ha : Spec.map a =
      AllCharacteristics.HomogeneousProjective.cubicConfigurationGenericBaseMap
          p hp configLength ≫
        AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
          p hp configLength)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4)
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)) :
    let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength
    let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
    let hr : r ≤ 10 := quadraticSubmodule_finrank_le_ten
      B.functionField (homogeneousIdealPiece C 2)
    let e := quadraticGrassmannianMonomialEquiv r hr
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (10 - r)),
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveQuadraticGrassmannian B.functionField C) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (10 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength ∧
        IsPullback
          (pullback.fst (grassmannianFrameProjectiveToGrassmannian K 2 e) f)
          (grassmannianFrameProjectiveFamilyPullbackToBase K 2 e f)
          (grassmannianFrameProjectiveToGrassmannian K 2 e) f := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
  let hr : r ≤ 10 := quadraticSubmodule_finrank_le_ten
    B.functionField (homogeneousIdealPiece C 2)
  let e := quadraticGrassmannianMonomialEquiv r hr
  letI : Algebra K B.functionField := a.hom.toAlgebra
  obtain ⟨U, hηU, f, hgeneric, hbase⟩ :=
    exists_open_fixedCurveQuadraticSystem_spread
      p hp configLength a ha C
  exact ⟨U, hηU, f, hgeneric, hbase,
    isPullback_grassmannianFrameProjectiveFamily K 2 e f⟩

/-- The generic fibre of a spread fixed-curve system is canonically the
projective family classified by the original function-field Grassmannian
point. -/
noncomputable def fixedCurveQuadraticSystem_projectiveFamily_genericFiberIso
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (C : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) F))
    {X : Scheme.{u}}
    (η : Spec (.of F) ⟶ X)
    (f : X ⟶ grassmannianScheme K
      (Module.finrank F (homogeneousIdealPiece C 2))
      (10 - Module.finrank F (homogeneousIdealPiece C 2)))
    (hgeneric :
      grassmannianQuotientMorphism (A := F) K
          (fixedCurveQuadraticGrassmannian F C) = η ≫ f) :
    let r := Module.finrank F (homogeneousIdealPiece C 2)
    let hr : r ≤ 10 := quadraticSubmodule_finrank_le_ten F
      (homogeneousIdealPiece C 2)
    let e := quadraticGrassmannianMonomialEquiv r hr
    pullback (grassmannianFrameProjectiveFamilyPullbackToBase K 2 e f) η ≅
      grassmannianFrameProjectiveFamilyPullback K 2 e
        (grassmannianQuotientMorphism (A := F) K
          (fixedCurveQuadraticGrassmannian F C)) := by
  dsimp only
  rw [hgeneric]
  exact grassmannianFrameProjectiveFamilyPullback_baseChangeIso K 2 _ f η

/-- The spread fixed-curve system has a proper projective parameter family
over the scheme-theoretic closure of its Grassmannian image.  Its generic
fibre is the original function-field quadratic system. -/
theorem exists_open_fixedCurveQuadraticSystem_properImageFamily
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (configLength : ℕ)
    [IsIntegral (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)
    (ha : Spec.map a =
      AllCharacteristics.HomogeneousProjective.cubicConfigurationGenericBaseMap
          p hp configLength ≫
        AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
          p hp configLength)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4)
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)) :
    let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength
    let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
    let hr : r ≤ 10 := quadraticSubmodule_finrank_le_ten
      B.functionField (homogeneousIdealPiece C 2)
    let e := quadraticGrassmannianMonomialEquiv r hr
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (10 - r)),
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveQuadraticGrassmannian B.functionField C) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (10 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength ∧
        IsProper (grassmannianFrameProjectiveImageFamilyToBase K 2 e f) ∧
        grassmannianQuotientMorphism (A := B.functionField) K
            (fixedCurveQuadraticGrassmannian B.functionField C) =
          (U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage) ≫ f.imageι ∧
        Nonempty
          (pullback (grassmannianFrameProjectiveImageFamilyToImage K 2 e f)
              (U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage) ≅
            grassmannianFrameProjectiveFamilyPullback K 2 e
              (grassmannianQuotientMorphism (A := B.functionField) K
                (fixedCurveQuadraticGrassmannian B.functionField C))) := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
  let hr : r ≤ 10 := quadraticSubmodule_finrank_le_ten
    B.functionField (homogeneousIdealPiece C 2)
  let e := quadraticGrassmannianMonomialEquiv r hr
  letI : Algebra K B.functionField := a.hom.toAlgebra
  obtain ⟨U, hηU, f, hgeneric, hbase, -⟩ :=
    exists_open_fixedCurveQuadraticSystem_projectiveFamily
      p hp configLength a ha C
  refine ⟨U, hηU, f, hgeneric, hbase, inferInstance, ?_, ?_⟩
  · calc
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveQuadraticGrassmannian B.functionField C) =
        U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f := hgeneric
      _ = (U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage) ≫
          f.imageι := by simp only [Category.assoc, f.toImage_imageι]
  · exact ⟨grassmannianFrameProjectiveImageFamily_baseChangeIso
      K 2 e f (U.fromSpecStalkOfMem (genericPoint B) hηU) ≪≫
        eqToIso (by rw [hgeneric])⟩

/-- A chosen nonzero fixed-curve quadric extends to an actual field-valued
point of the proper projective family over the scheme-theoretic image of a
spread.  Both its point of the image base and its ambient quadratic
parameter are retained exactly. -/
theorem exists_open_fixedCurveQuadraticSystem_properImageFamily_point
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (configLength : ℕ)
    [IsIntegral (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)
    (ha : Spec.map a =
      AllCharacteristics.HomogeneousProjective.cubicConfigurationGenericBaseMap
          p hp configLength ≫
        AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
          p hp configLength)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4)
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField))
    (q : MvPolynomial (Fin 4)
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)
    (hq : q.IsHomogeneous 2) (hqC : q ∈ C.toIdeal) (hq0 : q ≠ 0) :
    let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength
    let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
    let hr : r ≤ 10 := quadraticSubmodule_finrank_le_ten
      B.functionField (homogeneousIdealPiece C 2)
    let e := quadraticGrassmannianMonomialEquiv r hr
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (10 - r))
      (t : Spec (.of B.functionField) ⟶
        grassmannianFrameProjectiveImageFamily K 2 e f)
      (q' : MvPolynomial (Fin 4) B.functionField)
      (hq' : q'.IsHomogeneous 2) (hq'0 : q' ≠ 0) (alpha : B.functionField),
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveQuadraticGrassmannian B.functionField C) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (10 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength ∧
        IsProper (grassmannianFrameProjectiveImageFamilyToBase K 2 e f) ∧
        alpha ≠ 0 ∧ q' = MvPolynomial.C alpha * q ∧
        t ≫ grassmannianFrameProjectiveImageFamilyToImage K 2 e f =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage ∧
        t ≫ grassmannianFrameProjectiveImageFamilyToGlobalParameters K 2 e f =
          projectiveClassifyingMap q' hq' hq'0 (RingHom.id B.functionField) ≫
            projectiveParametersCoefficientMap 2 (algebraMap K B.functionField) := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
  let hr : r ≤ 10 := quadraticSubmodule_finrank_le_ten
    B.functionField (homogeneousIdealPiece C 2)
  let e := quadraticGrassmannianMonomialEquiv r hr
  letI : Algebra K B.functionField := a.hom.toAlgebra
  obtain ⟨U, hηU, f, hgeneric, hbase, -, -, -⟩ :=
    exists_open_fixedCurveQuadraticSystem_properImageFamily
      p hp configLength a ha C
  let eta : Spec (.of B.functionField) ⟶ U.toScheme :=
    U.fromSpecStalkOfMem (genericPoint B) hηU
  have hgeneric' :
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveQuadraticGrassmannian B.functionField C) = eta ≫ f :=
    hgeneric
  obtain ⟨s, q', hq', hq'0, alpha, halpha, hqscale, hsbase, hsparam⟩ :=
    exists_fixedCurveQuadraticGrassmannian_projective_point
      (K := K) C q hq hqC hq0
  have hRaw :
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveQuadraticGrassmannian B.functionField C) =
        (eta ≫ f.toImage) ≫ f.imageι := by
    calc
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveQuadraticGrassmannian B.functionField C) = eta ≫ f :=
        hgeneric'
      _ = (eta ≫ f.toImage) ≫ f.imageι := by
        rw [Category.assoc, f.toImage_imageι]
  let sRaw : Spec (.of B.functionField) ⟶
      grassmannianFrameProjectiveFamilyPullback K 2 e
        ((eta ≫ f.toImage) ≫ f.imageι) :=
    grassmannianFrameProjectiveFamilyPullbackPointCast K 2 e hRaw s
  have hsRawBase : sRaw ≫
      grassmannianFrameProjectiveFamilyPullbackToBase K 2 e
        ((eta ≫ f.toImage) ≫ f.imageι) = 𝟙 _ := by
    rw [show sRaw = grassmannianFrameProjectiveFamilyPullbackPointCast
      K 2 e hRaw s from rfl]
    rw [grassmannianFrameProjectiveFamilyPullbackPointCast_toBase]
    exact hsbase
  have hsRawParam : sRaw ≫
      grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 2 e
        ((eta ≫ f.toImage) ≫ f.imageι) =
      projectiveClassifyingMap q' hq' hq'0 (RingHom.id B.functionField) ≫
        projectiveParametersCoefficientMap 2 (algebraMap K B.functionField) := by
    rw [show sRaw = grassmannianFrameProjectiveFamilyPullbackPointCast
      K 2 e hRaw s from rfl]
    rw [grassmannianFrameProjectiveFamilyPullbackPointCast_toGlobalParameters]
    exact hsparam
  let t : Spec (.of B.functionField) ⟶
      grassmannianFrameProjectiveImageFamily K 2 e f :=
    grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint K 2 e f eta sRaw
  refine ⟨U, hηU, f, t, q', hq', hq'0, alpha, hgeneric, hbase,
    inferInstance, halpha, hqscale, ?_, ?_⟩
  · exact grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint_toImage
      K 2 e f eta sRaw hsRawBase
  · rw [grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint_toGlobalParameters]
    exact hsRawParam

/-- The field-valued member of the proper image family constructed above is
over the original coefficient-field point represented by the generic
configuration. -/
theorem fixedCurveQuadraticSystem_properImageFamily_point_toBase
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d configLength : ℕ}
    (hp : p.IsHomogeneous d)
    [IsIntegral (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)
    (ha : Spec.map a =
      AllCharacteristics.HomogeneousProjective.cubicConfigurationGenericBaseMap
          p hp configLength ≫
        AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
          p hp configLength)
    {r : ℕ} (hr : r ≤ 10) (e := quadraticGrassmannianMonomialEquiv r hr)
    (U : (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength).Opens)
    (hηU : genericPoint
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength) ∈ U)
    (f : U.toScheme ⟶ grassmannianScheme K r (10 - r))
    (t : Spec (.of
        (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
          p hp configLength).functionField) ⟶
      grassmannianFrameProjectiveImageFamily K 2 e f)
    (hfbase : f ≫ grassmannianToBase K r (10 - r) =
      U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
        p hp configLength)
    (htimage : t ≫ grassmannianFrameProjectiveImageFamilyToImage K 2 e f =
      U.fromSpecStalkOfMem
          (genericPoint (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
            p hp configLength)) hηU ≫ f.toImage) :
    t ≫ grassmannianFrameProjectiveImageFamilyToBase K 2 e f = Spec.map a := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let eta : Spec (.of B.functionField) ⟶ U.toScheme :=
    U.fromSpecStalkOfMem (genericPoint B) hηU
  calc
    t ≫ grassmannianFrameProjectiveImageFamilyToBase K 2 e f =
        (t ≫ grassmannianFrameProjectiveImageFamilyToImage K 2 e f) ≫
          f.imageι ≫ grassmannianToBase K r (10 - r) := by
      rfl
    _ = (eta ≫ f.toImage) ≫ f.imageι ≫
          grassmannianToBase K r (10 - r) := by rw [htimage]
    _ = eta ≫ f ≫ grassmannianToBase K r (10 - r) := by
      simpa only [← Category.assoc] using
        congrArg (fun k => eta ≫ k ≫ grassmannianToBase K r (10 - r))
          f.toImage_imageι
    _ = eta ≫ U.ι ≫
          AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength := by rw [hfbase]
    _ = B.fromSpecStalk (genericPoint B) ≫
          AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength := by
      simpa only [eta, ← Category.assoc] using
        congrArg (fun k => k ≫
          AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength)
          (Scheme.Opens.fromSpecStalkOfMem_ι U (genericPoint B) hηU)
    _ = Spec.map a := ha.symm

/-- The fixed-curve quadratic system has a spread whose Grassmannian target
is proper over the original coefficient field.  It is the parameter-family
form of the fixed system required for the final generic-incidence argument. -/
theorem exists_open_fixedCurveQuadraticSystem_spread_with_proper_target
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) {d : ℕ} (hp : p.IsHomogeneous d)
    (configLength : ℕ)
    [IsIntegral (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)
    (ha : Spec.map a =
      AllCharacteristics.HomogeneousProjective.cubicConfigurationGenericBaseMap
          p hp configLength ≫
        AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
          p hp configLength)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4)
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField)) :
    let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength
    let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (10 - r)),
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveQuadraticGrassmannian B.functionField C) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (10 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength ∧
        IsProper (grassmannianToBase K r (10 - r)) := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField (homogeneousIdealPiece C 2)
  letI : Algebra K B.functionField := a.hom.toAlgebra
  exact exists_open_grassmannian_spread_with_proper_target
    (AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
      p hp configLength) ha
      (fixedCurveQuadraticGrassmannian B.functionField C)

end PfaffianDescent
