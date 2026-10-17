import PfaffianDescent.VoisinGenericGrassmannianSpread

/-!
# Cubic systems as Grassmannian families

The cubic fixed-curve argument must track a system over the function field
of the configuration base, rather than a single ground-field frame. This
file places a cubic subspace in the quotient Grassmannian and spreads its
function-field point to a family near the generic configuration.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- There are twenty degree-three monomials in four variables. -/
theorem cubicMonomials_card_for_grassmannian :
    Fintype.card (Monomials (Fin 4) 3) = 20 := by
  have hdim : Module.finrank ℚ
      (MvPolynomial.homogeneousSubmodule (Fin 4) ℚ 3) =
      Fintype.card (Monomials (Fin 4) 3) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact Module.finrank_eq_card_basis
      (MvPolynomial.basisRestrictSupport ℚ {a | a.degree = 3})
  rw [← hdim, four_variable_homogeneous_finrank]
  decide

/-- Cubic monomial coordinates split into a rank-`r` system and a
complementary block. -/
noncomputable def cubicGrassmannianMonomialEquiv
    (r : ℕ) (hr : r ≤ 20) :
    Fin (r + (20 - r)) ≃ Monomials (Fin 4) 3 :=
  (finCongr (Nat.add_sub_of_le hr)).trans
    ((finCongr cubicMonomials_card_for_grassmannian.symm).trans
      (Fintype.equivFin _).symm)

/-- Coordinates on the twenty-dimensional homogeneous cubic space. -/
noncomputable def cubicCoordinateEquiv
    (F : Type u) [Field F] (r : ℕ) (hr : r ≤ 20) :
    MvPolynomial.homogeneousSubmodule (Fin 4) F 3 ≃ₗ[F]
      (Fin r → F) × (Fin (20 - r) → F) := by
  exact (grassmannianChartHomogeneousCoordinateEquiv
    (R := F) 3 (cubicGrassmannianMonomialEquiv r hr)).symm

theorem cubicSubmodule_finrank_le_twenty
    (F : Type u) [Field F]
    (W : Submodule F (MvPolynomial.homogeneousSubmodule (Fin 4) F 3)) :
    Module.finrank F W ≤ 20 := by
  apply W.finrank_le.trans_eq
  rw [four_variable_homogeneous_finrank]
  decide

/-- The coordinate image of a cubic subspace in the standard Grassmannian
module. -/
noncomputable def cubicCoordinateSubmodule
    (F : Type u) [Field F]
    (W : Submodule F (MvPolynomial.homogeneousSubmodule (Fin 4) F 3)) :
    Submodule F
      ((Fin (Module.finrank F W) → F) ×
        (Fin (20 - Module.finrank F W) → F)) :=
  W.map (cubicCoordinateEquiv F (Module.finrank F W)
    (cubicSubmodule_finrank_le_twenty F W)).toLinearMap

theorem cubicCoordinateSubmodule_quotient_finrank
    (F : Type u) [Field F]
    (W : Submodule F (MvPolynomial.homogeneousSubmodule (Fin 4) F 3)) :
    Module.finrank F
      (((Fin (Module.finrank F W) → F) ×
          (Fin (20 - Module.finrank F W) → F)) ⧸
        cubicCoordinateSubmodule F W) =
      20 - Module.finrank F W := by
  rw [Submodule.finrank_quotient]
  change Module.finrank F
      ((Fin (Module.finrank F W) → F) ×
        (Fin (20 - Module.finrank F W) → F)) -
      Module.finrank F
        (W.map (cubicCoordinateEquiv F (Module.finrank F W)
          (cubicSubmodule_finrank_le_twenty F W)).toLinearMap) = _
  rw [LinearEquiv.finrank_map_eq]
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
  omega

/-- A cubic subspace as a point of the quotient Grassmannian. -/
noncomputable def cubicSubspaceGrassmannian
    (F : Type u) [Field F]
    (W : Submodule F (MvPolynomial.homogeneousSubmodule (Fin 4) F 3)) :
    Module.Grassmannian F
      ((Fin (Module.finrank F W) → F) ×
        (Fin (20 - Module.finrank F W) → F))
      (20 - Module.finrank F W) :=
  fieldSubmoduleGrassmannian F (cubicCoordinateSubmodule F W)
    (cubicCoordinateSubmodule_quotient_finrank F W)

/-- The cubic piece of a homogeneous fixed-curve ideal as a Grassmannian
point over its coefficient field. -/
noncomputable def fixedCurveCubicGrassmannian
    (F : Type u) [Field F]
    (C : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) F)) :
    Module.Grassmannian F
      ((Fin (Module.finrank F (homogeneousIdealPiece C 3)) → F) ×
        (Fin (20 - Module.finrank F (homogeneousIdealPiece C 3)) → F))
      (20 - Module.finrank F (homogeneousIdealPiece C 3)) :=
  cubicSubspaceGrassmannian F (homogeneousIdealPiece C 3)

@[simp]
theorem fixedCurveCubicGrassmannian_toSubmodule
    (F : Type u) [Field F]
    (C : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) F)) :
    (fixedCurveCubicGrassmannian F C).toSubmodule =
      cubicCoordinateSubmodule F (homogeneousIdealPiece C 3) := rfl

/-- A member of an arbitrary cubic subspace is an actual point of its
projective Grassmannian-frame family. This permits choosing a complement to
the defining cubic before constructing the incidence parameter. -/
theorem exists_cubicSubspaceGrassmannian_projective_point
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (W : Submodule F (homogeneousSubmodule (Fin 4) F 3))
    (q : homogeneousSubmodule (Fin 4) F 3)
    (hqW : q ∈ W) (hq0 : q ≠ 0) :
    let r := Module.finrank F W
    let hr : r ≤ 20 := cubicSubmodule_finrank_le_twenty F W
    let e := cubicGrassmannianMonomialEquiv r hr
    ∃ (t : Spec (.of F) ⟶
        grassmannianFrameProjectiveFamilyPullback K 3 e
          (grassmannianQuotientMorphism (A := F) K
            (cubicSubspaceGrassmannian F W)))
      (q' : MvPolynomial (Fin 4) F) (hq' : q'.IsHomogeneous 3)
      (hq'0 : q' ≠ 0) (alpha : F),
      alpha ≠ 0 ∧ q' = MvPolynomial.C alpha * q.1 ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToBase K 3 e
          (grassmannianQuotientMorphism (A := F) K
            (cubicSubspaceGrassmannian F W)) = 𝟙 _ ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e
          (grassmannianQuotientMorphism (A := F) K
            (cubicSubspaceGrassmannian F W)) =
        projectiveClassifyingMap q' hq' hq'0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap 3 (algebraMap K F) := by
  dsimp only
  apply exists_grassmannianFrameProjectiveFamilyPullback_point_of_mem
    (K := K) (F := F)
    (cubicGrassmannianMonomialEquiv (Module.finrank F W)
      (cubicSubmodule_finrank_le_twenty F W))
    (cubicSubspaceGrassmannian F W) q
  · exact ⟨q, hqW, rfl⟩
  · exact hq0

/-- Any cubic function-field subspace, including one chosen complementary
to the surface equation, spreads to a Grassmannian family near the generic
configuration. -/
theorem exists_open_cubicSubspace_spread
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
    (W : Submodule
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField
      (homogeneousSubmodule (Fin 4)
        (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
          p hp configLength).functionField 3)) :
    let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength
    let r := Module.finrank B.functionField W
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (20 - r)),
      grassmannianQuotientMorphism (A := B.functionField) K
          (cubicSubspaceGrassmannian B.functionField W) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (20 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField W
  letI : Algebra K B.functionField := a.hom.toAlgebra
  exact exists_open_cubicConfiguration_grassmannian_spread
    p hp configLength a ha (cubicSubspaceGrassmannian B.functionField W)

/-- An arbitrary function-field cubic subspace has a proper projective
member family over the closure of its Grassmannian spread. In particular
this applies to a subspace selected to be independent modulo the defining
surface equation. -/
theorem exists_open_cubicSubspace_properImageFamily
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
    (W : Submodule
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField
      (homogeneousSubmodule (Fin 4)
        (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
          p hp configLength).functionField 3)) :
    let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength
    let r := Module.finrank B.functionField W
    let hr : r ≤ 20 := cubicSubmodule_finrank_le_twenty B.functionField W
    let e := cubicGrassmannianMonomialEquiv r hr
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (20 - r)),
      grassmannianQuotientMorphism (A := B.functionField) K
          (cubicSubspaceGrassmannian B.functionField W) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (20 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength ∧
        IsProper (grassmannianFrameProjectiveImageFamilyToBase K 3 e f) ∧
        grassmannianQuotientMorphism (A := B.functionField) K
            (cubicSubspaceGrassmannian B.functionField W) =
          (U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage) ≫ f.imageι ∧
        Nonempty
          (pullback (grassmannianFrameProjectiveImageFamilyToImage K 3 e f)
              (U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage) ≅
            grassmannianFrameProjectiveFamilyPullback K 3 e
              (grassmannianQuotientMorphism (A := B.functionField) K
                (cubicSubspaceGrassmannian B.functionField W))) := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField W
  let hr : r ≤ 20 := cubicSubmodule_finrank_le_twenty B.functionField W
  let e := cubicGrassmannianMonomialEquiv r hr
  letI : Algebra K B.functionField := a.hom.toAlgebra
  obtain ⟨U, hηU, f, hgeneric, hbase⟩ :=
    exists_open_cubicSubspace_spread p hp configLength a ha W
  refine ⟨U, hηU, f, hgeneric, hbase, inferInstance, ?_, ?_⟩
  · calc
      grassmannianQuotientMorphism (A := B.functionField) K
          (cubicSubspaceGrassmannian B.functionField W) =
        U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f := hgeneric
      _ = (U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage) ≫
          f.imageι := by simp only [Category.assoc, f.toImage_imageι]
  · exact ⟨grassmannianFrameProjectiveImageFamily_baseChangeIso
      K 3 e f (U.fromSpecStalkOfMem (genericPoint B) hηU) ≪≫
        eqToIso (by rw [hgeneric])⟩

/-- A nonzero cubic member of a variable function-field subspace extends to
an actual field-valued member of the proper projective family of its
Grassmannian spread. -/
theorem exists_open_cubicSubspace_properImageFamily_point
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
    (W : Submodule
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField
      (homogeneousSubmodule (Fin 4)
        (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
          p hp configLength).functionField 3))
    (q : homogeneousSubmodule (Fin 4)
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength).functionField 3)
    (hqW : q ∈ W) (hq0 : q ≠ 0) :
    let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength
    let r := Module.finrank B.functionField W
    let hr : r ≤ 20 := cubicSubmodule_finrank_le_twenty B.functionField W
    let e := cubicGrassmannianMonomialEquiv r hr
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (20 - r))
      (t : Spec (.of B.functionField) ⟶
        grassmannianFrameProjectiveImageFamily K 3 e f)
      (q' : MvPolynomial (Fin 4) B.functionField)
      (hq' : q'.IsHomogeneous 3) (hq'0 : q' ≠ 0) (alpha : B.functionField),
      grassmannianQuotientMorphism (A := B.functionField) K
          (cubicSubspaceGrassmannian B.functionField W) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (20 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength ∧
        IsProper (grassmannianFrameProjectiveImageFamilyToBase K 3 e f) ∧
        alpha ≠ 0 ∧ q' = MvPolynomial.C alpha * q.1 ∧
        t ≫ grassmannianFrameProjectiveImageFamilyToImage K 3 e f =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage ∧
        t ≫ grassmannianFrameProjectiveImageFamilyToGlobalParameters K 3 e f =
          projectiveClassifyingMap q' hq' hq'0 (RingHom.id B.functionField) ≫
            projectiveParametersCoefficientMap 3 (algebraMap K B.functionField) := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField W
  let hr : r ≤ 20 := cubicSubmodule_finrank_le_twenty B.functionField W
  let e := cubicGrassmannianMonomialEquiv r hr
  letI : Algebra K B.functionField := a.hom.toAlgebra
  obtain ⟨U, hηU, f, hgeneric, hbase, -, -, -⟩ :=
    exists_open_cubicSubspace_properImageFamily p hp configLength a ha W
  let eta : Spec (.of B.functionField) ⟶ U.toScheme :=
    U.fromSpecStalkOfMem (genericPoint B) hηU
  have hgeneric' :
      grassmannianQuotientMorphism (A := B.functionField) K
          (cubicSubspaceGrassmannian B.functionField W) = eta ≫ f :=
    hgeneric
  obtain ⟨s, q', hq', hq'0, alpha, halpha, hqscale, hsbase, hsparam⟩ :=
    exists_cubicSubspaceGrassmannian_projective_point
      (K := K) W q hqW hq0
  have hRaw :
      grassmannianQuotientMorphism (A := B.functionField) K
          (cubicSubspaceGrassmannian B.functionField W) =
        (eta ≫ f.toImage) ≫ f.imageι := by
    calc
      grassmannianQuotientMorphism (A := B.functionField) K
          (cubicSubspaceGrassmannian B.functionField W) = eta ≫ f :=
        hgeneric'
      _ = (eta ≫ f.toImage) ≫ f.imageι := by
        rw [Category.assoc, f.toImage_imageι]
  let sRaw : Spec (.of B.functionField) ⟶
      grassmannianFrameProjectiveFamilyPullback K 3 e
        ((eta ≫ f.toImage) ≫ f.imageι) :=
    grassmannianFrameProjectiveFamilyPullbackPointCast K 3 e hRaw s
  have hsRawBase : sRaw ≫
      grassmannianFrameProjectiveFamilyPullbackToBase K 3 e
        ((eta ≫ f.toImage) ≫ f.imageι) = 𝟙 _ := by
    rw [show sRaw = grassmannianFrameProjectiveFamilyPullbackPointCast
      K 3 e hRaw s from rfl]
    rw [grassmannianFrameProjectiveFamilyPullbackPointCast_toBase]
    exact hsbase
  have hsRawParam : sRaw ≫
      grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e
        ((eta ≫ f.toImage) ≫ f.imageι) =
      projectiveClassifyingMap q' hq' hq'0 (RingHom.id B.functionField) ≫
        projectiveParametersCoefficientMap 3 (algebraMap K B.functionField) := by
    rw [show sRaw = grassmannianFrameProjectiveFamilyPullbackPointCast
      K 3 e hRaw s from rfl]
    rw [grassmannianFrameProjectiveFamilyPullbackPointCast_toGlobalParameters]
    exact hsparam
  let t : Spec (.of B.functionField) ⟶
      grassmannianFrameProjectiveImageFamily K 3 e f :=
    grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint K 3 e f eta sRaw
  refine ⟨U, hηU, f, t, q', hq', hq'0, alpha, hgeneric, hbase,
    inferInstance, halpha, hqscale, ?_, ?_⟩
  · exact grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint_toImage
      K 3 e f eta sRaw hsRawBase
  · rw [grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint_toGlobalParameters]
    exact hsRawParam

/-- The proper-family member lies over the original coefficient-field point
of the generic configuration. -/
theorem cubicSubspace_properImageFamily_point_toBase
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
    {r : ℕ} (hr : r ≤ 20) (e := cubicGrassmannianMonomialEquiv r hr)
    (U : (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
      p hp configLength).Opens)
    (hηU : genericPoint
      (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
        p hp configLength) ∈ U)
    (f : U.toScheme ⟶ grassmannianScheme K r (20 - r))
    (t : Spec (.of
        (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
          p hp configLength).functionField) ⟶
      grassmannianFrameProjectiveImageFamily K 3 e f)
    (hfbase : f ≫ grassmannianToBase K r (20 - r) =
      U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
        p hp configLength)
    (htimage : t ≫ grassmannianFrameProjectiveImageFamilyToImage K 3 e f =
      U.fromSpecStalkOfMem
          (genericPoint (AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
            p hp configLength)) hηU ≫ f.toImage) :
    t ≫ grassmannianFrameProjectiveImageFamilyToBase K 3 e f = Spec.map a := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let eta : Spec (.of B.functionField) ⟶ U.toScheme :=
    U.fromSpecStalkOfMem (genericPoint B) hηU
  calc
    t ≫ grassmannianFrameProjectiveImageFamilyToBase K 3 e f =
        (t ≫ grassmannianFrameProjectiveImageFamilyToImage K 3 e f) ≫
          f.imageι ≫ grassmannianToBase K r (20 - r) := by
      rfl
    _ = (eta ≫ f.toImage) ≫ f.imageι ≫
          grassmannianToBase K r (20 - r) := by rw [htimage]
    _ = eta ≫ f ≫ grassmannianToBase K r (20 - r) := by
      simpa only [← Category.assoc] using
        congrArg (fun k => eta ≫ k ≫ grassmannianToBase K r (20 - r))
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

/-- A nonzero cubic equation of a function-field fixed curve is a point of
the projective family over its cubic Grassmannian point. Its ambient
parameter represents a nonzero scalar multiple of that equation. -/
theorem exists_fixedCurveCubicGrassmannian_projective_point
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (C : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin 4) F))
    (q : MvPolynomial (Fin 4) F) (hq : q.IsHomogeneous 3)
    (hqC : q ∈ C.toIdeal) (hq0 : q ≠ 0) :
    let r := Module.finrank F (homogeneousIdealPiece C 3)
    let hr : r ≤ 20 := cubicSubmodule_finrank_le_twenty F
      (homogeneousIdealPiece C 3)
    let e := cubicGrassmannianMonomialEquiv r hr
    ∃ (t : Spec (.of F) ⟶
        grassmannianFrameProjectiveFamilyPullback K 3 e
          (grassmannianQuotientMorphism (A := F) K
            (fixedCurveCubicGrassmannian F C)))
      (q' : MvPolynomial (Fin 4) F) (hq' : q'.IsHomogeneous 3)
      (hq'0 : q' ≠ 0) (alpha : F),
      alpha ≠ 0 ∧ q' = MvPolynomial.C alpha * q ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToBase K 3 e
          (grassmannianQuotientMorphism (A := F) K
            (fixedCurveCubicGrassmannian F C)) = 𝟙 _ ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 3 e
          (grassmannianQuotientMorphism (A := F) K
            (fixedCurveCubicGrassmannian F C)) =
        projectiveClassifyingMap q' hq' hq'0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap 3 (algebraMap K F) := by
  dsimp only
  let qh : homogeneousSubmodule (Fin 4) F 3 := ⟨q, hq⟩
  have hqPiece : qh ∈ homogeneousIdealPiece C 3 :=
    (mem_homogeneousIdealPiece_iff C 3 qh).mpr hqC
  apply exists_grassmannianFrameProjectiveFamilyPullback_point_of_mem
    (K := K) (F := F) (cubicGrassmannianMonomialEquiv
      (Module.finrank F (homogeneousIdealPiece C 3))
      (cubicSubmodule_finrank_le_twenty F (homogeneousIdealPiece C 3)))
    (fixedCurveCubicGrassmannian F C) qh
  · exact ⟨qh, hqPiece, rfl⟩
  · intro hzero
    exact hq0 (congrArg Subtype.val hzero)

/-- The generic cubic system of a fixed curve spreads to an actual family
of cubic subspaces over an open neighborhood of the generic configuration. -/
theorem exists_open_fixedCurveCubicSystem_spread
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
    let r := Module.finrank B.functionField (homogeneousIdealPiece C 3)
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (20 - r)),
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveCubicGrassmannian B.functionField C) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (20 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField (homogeneousIdealPiece C 3)
  letI : Algebra K B.functionField := a.hom.toAlgebra
  exact exists_open_cubicConfiguration_grassmannian_spread
    p hp configLength a ha (fixedCurveCubicGrassmannian B.functionField C)

/-- The cubic Grassmannian spread carries a proper projective parameter
family over the closure of its image. Its generic fibre is the projective
system classified by the original function-field subspace. -/
theorem exists_open_fixedCurveCubicSystem_properImageFamily
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
    let r := Module.finrank B.functionField (homogeneousIdealPiece C 3)
    let hr : r ≤ 20 := cubicSubmodule_finrank_le_twenty B.functionField
      (homogeneousIdealPiece C 3)
    let e := cubicGrassmannianMonomialEquiv r hr
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K r (20 - r)),
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveCubicGrassmannian B.functionField C) =
          U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
        f ≫ grassmannianToBase K r (20 - r) =
          U.ι ≫ AllCharacteristics.HomogeneousProjective.cubicConfigurationToBase
            p hp configLength ∧
        IsProper (grassmannianFrameProjectiveImageFamilyToBase K 3 e f) ∧
        grassmannianQuotientMorphism (A := B.functionField) K
            (fixedCurveCubicGrassmannian B.functionField C) =
          (U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage) ≫ f.imageι ∧
        Nonempty
          (pullback (grassmannianFrameProjectiveImageFamilyToImage K 3 e f)
              (U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage) ≅
            grassmannianFrameProjectiveFamilyPullback K 3 e
              (grassmannianQuotientMorphism (A := B.functionField) K
                (fixedCurveCubicGrassmannian B.functionField C))) := by
  let B := AllCharacteristics.HomogeneousProjective.cubicConfigurationBase
    p hp configLength
  let r := Module.finrank B.functionField (homogeneousIdealPiece C 3)
  let hr : r ≤ 20 := cubicSubmodule_finrank_le_twenty B.functionField
    (homogeneousIdealPiece C 3)
  let e := cubicGrassmannianMonomialEquiv r hr
  letI : Algebra K B.functionField := a.hom.toAlgebra
  obtain ⟨U, hηU, f, hgeneric, hbase⟩ :=
    exists_open_fixedCurveCubicSystem_spread p hp configLength a ha C
  refine ⟨U, hηU, f, hgeneric, hbase, inferInstance, ?_, ?_⟩
  · calc
      grassmannianQuotientMorphism (A := B.functionField) K
          (fixedCurveCubicGrassmannian B.functionField C) =
        U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f := hgeneric
      _ = (U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage) ≫
          f.imageι := by simp only [Category.assoc, f.toImage_imageι]
  · exact ⟨grassmannianFrameProjectiveImageFamily_baseChangeIso
      K 3 e f (U.fromSpecStalkOfMem (genericPoint B) hηU) ≪≫
        eqToIso (by rw [hgeneric])⟩

end PfaffianDescent
