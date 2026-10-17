import PfaffianDescent.VoisinGenericSixteenSeparatedCubicRankThree
import PfaffianDescent.VoisinFixedCurveSeparatedCubicSpread

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The fixed-curve system has a proper spread with a polynomial presentation
of rank at most three over the generic configuration function field. -/
theorem exists_genericSixteen_fixedCurve_separatedCubicProperFamily_rank_le_three
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 16).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    [Infinite (cubicConfigurationBase p hp 16).functionField]
    {m : ℕ} (e₀ : Fin m ≃ Monomials (Fin 4) 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase p hp 16).functionField))
    (hCp : p.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      p hp 16 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (p.map a.hom) (hp.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        p hp 16 a ha).val.subschemeι)
    (q : MvPolynomial (Fin 4)
      (cubicConfigurationBase p hp 16).functionField)
    (hq : q.IsHomogeneous 3) (hqC : q ∈ C.toIdeal)
    (hqnonrelation : q ∉ Ideal.span ({p.map a.hom} : Set
      (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField))) :
    let B := cubicConfigurationBase p hp 16
    letI : Algebra K B.functionField := a.hom.toAlgebra
    ∃ (W : Submodule B.functionField
        (homogeneousSubmodule (Fin 4) B.functionField 3))
      (w : homogeneousSubmodule (Fin 4) B.functionField 3),
      W ≤ homogeneousIdealPiece C 3 ∧
      (∀ z ∈ W,
        z.1 ∈ Ideal.span ({p.map a.hom} : Set
          (MvPolynomial (Fin 4) B.functionField)) → z = 0) ∧
      finrank B.functionField W ≤ 3 ∧
      w ∈ W ∧ w ≠ 0 ∧
      cubicSurfaceHomogeneousCoordinateProjection
        (p.map a.hom) (hp.map a.hom) 3 w =
        cubicSurfaceHomogeneousCoordinateProjection
          (p.map a.hom) (hp.map a.hom) 3 ⟨q, hq⟩ ∧
      let r := finrank B.functionField W
      let hr : r ≤ 20 := cubicSubmodule_finrank_le_twenty B.functionField W
      let e := cubicGrassmannianMonomialEquiv r hr
      ∃ (U : B.Opens) (hηU : genericPoint B ∈ U)
        (f : U.toScheme ⟶ grassmannianScheme K r (20 - r))
        (t : Spec (.of B.functionField) ⟶
          grassmannianFrameProjectiveImageFamily K 3 e f)
        (q' : MvPolynomial (Fin 4) B.functionField)
        (hq' : q'.IsHomogeneous 3) (hq'0 : q' ≠ 0)
        (alpha : B.functionField),
        grassmannianQuotientMorphism (A := B.functionField) K
            (cubicSubspaceGrassmannian B.functionField W) =
            U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f ∧
          f ≫ grassmannianToBase K r (20 - r) =
            U.ι ≫ cubicConfigurationToBase p hp 16 ∧
          IsProper (grassmannianFrameProjectiveImageFamilyToBase K 3 e f) ∧
          alpha ≠ 0 ∧ q' = alpha • w.1 ∧ q' ∈ C.toIdeal ∧
          t ≫ grassmannianFrameProjectiveImageFamilyToImage K 3 e f =
            U.fromSpecStalkOfMem (genericPoint B) hηU ≫ f.toImage ∧
          t ≫ grassmannianFrameProjectiveImageFamilyToGlobalParameters K 3 e f =
            projectiveClassifyingMap q' hq' hq'0
                (RingHom.id B.functionField) ≫
              projectiveParametersCoefficientMap 3
                (algebraMap K B.functionField) := by
  dsimp only
  let B := cubicConfigurationBase p hp 16
  letI : Algebra K B.functionField := a.hom.toAlgebra
  have hthree :=
    cubicConfigurationGenericSixteen_fixedCurve_cubicSurfaceSystem_finrank_le_three
      p hp hp0 hprime a ha e₀ C hCp h hfac
  obtain ⟨W, w, hWC, hsep, -, hdim, hwW, hw0, hwproj⟩ :=
    exists_fixedCurveCubicSystem_separated_lift_member_of_system_finrank_le
      (p.map a.hom) (hp.map a.hom) C 3 hthree
      q hq hqC hqnonrelation
  refine ⟨W, w, hWC, hsep, hdim, hwW, hw0, hwproj, ?_⟩
  obtain ⟨U, hηU, f, t, q', hq', hq'0, alpha,
      hgeneric, hbase, hproper, halpha, hscale, htbase, htparam⟩ :=
    exists_open_cubicSubspace_properImageFamily_point
      p hp 16 a ha W w hwW hw0
  have hwC : w.1 ∈ C.toIdeal := hWC hwW
  have hq'C : q' ∈ C.toIdeal := by
    rw [hscale]
    exact C.toIdeal.mul_mem_left (MvPolynomial.C alpha) hwC
  exact ⟨U, hηU, f, t, q', hq', hq'0, alpha,
    hgeneric, hbase, hproper, halpha,
    by simpa only [MvPolynomial.smul_eq_C_mul] using hscale,
    hq'C, htbase,
    htparam⟩


end PfaffianDescent
