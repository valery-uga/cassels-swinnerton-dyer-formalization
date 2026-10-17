import PfaffianDescent.VoisinGenericSixteenFixedCurveCubicIdealRank
import PfaffianDescent.VoisinFixedCurveThreePoints
import PfaffianDescent.VoisinCubicProjectionKernelOne

/-!
# Three-dimensional fixed-curve cubic system on the surface
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Four cubic equations of a curve, including a nonzero surface equation,
give at most three cubic sections on the surface. -/
theorem fixedCurveCubicSurfaceSystem_finrank_le_three_of_idealPiece_le_four
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hne : p ≠ 0)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (hfour : finrank K (homogeneousIdealPiece C 3) ≤ 4) :
    finrank K (fixedCurveCubicSurfaceSystem p hp C) ≤ 3 := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) K 3)
  letI : FiniteDimensional K (homogeneousIdealPiece C 3) := inferInstance
  letI : AddCommGroup (homogeneousIdealPiece C 3) := inferInstance
  letI : AddCommGroup (grading (equationIdeal p hp) 3) := inferInstance
  let f : homogeneousIdealPiece C 3 →ₗ[K] grading (equationIdeal p hp) 3 :=
    (cubicSurfaceHomogeneousCoordinateProjection p hp 3).comp
      (homogeneousIdealPiece C 3).subtype
  have hrange : LinearMap.range f = fixedCurveCubicSurfaceSystem p hp C := by
    simp only [f, fixedCurveCubicSurfaceSystem, LinearMap.range_comp,
      Submodule.range_subtype]
  have hdim := f.finrank_range_add_finrank_ker
  rw [hrange] at hdim
  have hker : 0 < finrank K (LinearMap.ker f) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    let q : homogeneousIdealPiece C 3 := ⟨⟨p, hp⟩, hCp⟩
    refine ⟨⟨q, ?_⟩, ?_⟩
    · apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change Ideal.Quotient.mk (equationIdeal p hp).toIdeal p = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton p))
    · intro hq
      apply hne
      exact congrArg (fun z : homogeneousIdealPiece C 3 => z.1.1)
        (congrArg Subtype.val hq)
  omega

/-- Under the common-component hypothesis, the three cubic sections on the
surface are linearly independent as well as spanning the fixed-curve system. -/
theorem fixedCurveCubicSurfaceSystem_finrank_eq_three_of_common_component
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hne : p ≠ 0)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hC : ∀ q ∈ C.toIdeal, q.eval₂ (algebraMap K A) x = 0)
    (hcommon : ∀ q : homogeneousSubmodule (Fin 4) K 3,
      q.val.eval₂ (algebraMap K A) x = 0 → q.val ∈ C.toIdeal)
    (hrank : cubicVanishingSectionsModuloEquationFinrank p hp x hpx = 3) :
    finrank K (fixedCurveCubicSurfaceSystem p hp C) = 3 := by
  letI : FiniteDimensional K (homogeneousSubmodule (Fin 4) K 3) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) K 3)
  letI : FiniteDimensional K (homogeneousIdealPiece C 3) := inferInstance
  letI : AddCommGroup (homogeneousIdealPiece C 3) := inferInstance
  letI : AddCommGroup (grading (equationIdeal p hp) 3) := inferInstance
  let projection := cubicSurfaceHomogeneousCoordinateProjection p hp 3
  let f : homogeneousIdealPiece C 3 →ₗ[K] grading (equationIdeal p hp) 3 :=
    projection.comp (homogeneousIdealPiece C 3).subtype
  have hrange : LinearMap.range f = fixedCurveCubicSurfaceSystem p hp C := by
    simp only [f, projection, fixedCurveCubicSurfaceSystem,
      LinearMap.range_comp, Submodule.range_subtype]
  have hmaple : (LinearMap.ker f).map (homogeneousIdealPiece C 3).subtype ≤
      LinearMap.ker projection := by
    rintro q ⟨v, hv, rfl⟩
    exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp hv)
  have hkerle : finrank K (LinearMap.ker f) ≤ 1 := by
    calc
      finrank K (LinearMap.ker f) =
          finrank K ((LinearMap.ker f).map (homogeneousIdealPiece C 3).subtype) :=
        (Submodule.finrank_map_subtype_eq
          (homogeneousIdealPiece C 3) (LinearMap.ker f)).symm
      _ ≤ finrank K (LinearMap.ker projection) := Submodule.finrank_mono hmaple
      _ = 1 := cubicSurfaceHomogeneousCoordinateProjection_kernel_finrank_one
        p hp hne
  have hfour : finrank K (homogeneousIdealPiece C 3) = 4 :=
    fixedCurveCubicIdealPiece_finrank_eq_four_of_common_component
      p hp C x hpx hC hcommon hrank
  have hdim := f.finrank_range_add_finrank_ker
  rw [hrange, hfour] at hdim
  have hle : finrank K (fixedCurveCubicSurfaceSystem p hp C) ≤ 3 :=
    fixedCurveCubicSurfaceSystem_finrank_le_three_of_idealPiece_le_four
      p hp hne C hCp (by omega)
  omega

/-- A fixed curve through the actual generic sixteen-point scheme carries
at most three independent cubic sections on the cubic surface. -/
theorem cubicConfigurationGenericSixteen_fixedCurve_cubicSurfaceSystem_finrank_le_three
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι) :
    let Q := cubicConfigurationBase cubic hcubic 16
    finrank Q.functionField
      (fixedCurveCubicSurfaceSystem (cubic.map a.hom) (hcubic.map a.hom) C) ≤ 3 := by
  dsimp only
  have hfour :=
    cubicConfigurationGenericSixteen_fixedCurve_cubicIdealPiece_finrank_le_four
      cubic hcubic hcubic_ne hcubic_prime a ha e C hCp h hfac
  have hneη : cubic.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero cubic hcubic 16 a hcubic_ne
  exact fixedCurveCubicSurfaceSystem_finrank_le_three_of_idealPiece_le_four
    (cubic.map a.hom) (hcubic.map a.hom) hneη C hCp hfour

end PfaffianDescent
