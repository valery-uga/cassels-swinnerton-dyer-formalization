import PfaffianDescent.PointGlobalTraceP3BasisUnitStalk
import PfaffianDescent.CubicPointQuadraticRestrictionPointFiber

/-! # Actual basis augmentation at a native closed field point of projective space

The native augmentation kernel is constructed for every closed field point.
The actual basis Koszul augmentation is exact there once its normalized
coefficients are proved to generate that point's native maximal ideal.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

local instance pointGlobalTraceP3Basis_augmentationPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

/-- The actual augmentation vanishes precisely on the native homogeneous
maximal ideal, without a supplied restriction compatibility square. -/
theorem pointGlobalTraceP3BasisAugmentation_stalk_eq_zero_iff
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ Proj PS) [IsClosedImmersion i]
    (k : Spec (.of L))
    (z : (schemeModuleStalkFunctor (Proj PS) (i k)).obj
      (SheafOfModules.unit (Proj PS).ringCatSheaf)) :
    (schemeModuleStalkFunctor (Proj PS) (i k)).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) z = 0 ↔
      ambientPointKoszul_unitStalkCoordinate K (i k) z ∈
        IsLocalRing.maximalIdeal (AtPrime PS
          (pointIdeal PS (i k))) := by
  let x := i k
  letI : IsLocalRing ((Proj PS).presheaf.stalk x) := inferInstance
  letI : IsLocalRing ((ProjectiveSpectrum.Proj.structureSheaf PS).presheaf.stalk x) :=
    show IsLocalRing ((Proj PS).presheaf.stalk x) from inferInstance
  let e := cubicPointQuadraticRestrictionPushforwardResidueIso
    (i) k
  have hres := cubicPointQuadraticRestrictionPushforwardResidueIso_unit
    (i) k z
  have hzero : (schemeModuleStalkFunctor (Proj PS) x).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) z = 0 ↔
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal ((Proj PS).presheaf.stalk x))
        ((schemeModuleUnitStalkIso (Proj PS) x).hom z) = 0 := by
    constructor
    · intro h
      rw [← hres]
      change e.hom ((schemeModuleStalkFunctor (Proj PS) x).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) z) = 0
      rw [h, map_zero]
    · intro h
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      change e.hom ((schemeModuleStalkFunctor (Proj PS) x).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) z) = e.hom 0
      rw [map_zero]
      exact hres.trans h
  rw [Ideal.Quotient.eq_zero_iff_mem] at hzero
  have hmem : Proj.stalkIso' PS x ((schemeModuleUnitStalkIso (Proj PS) x).hom z) ∈
      IsLocalRing.maximalIdeal (AtPrime PS (pointIdeal PS x)) ↔
      (schemeModuleUnitStalkIso (Proj PS) x).hom z ∈
        IsLocalRing.maximalIdeal ((Proj PS).presheaf.stalk x) := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal (Proj.stalkIso' PS x)]
    exact Ideal.apply_mem_of_equiv_iff
  exact hzero.trans hmem.symm


/-- The original basis differential and original closed-point restriction
are exact at the point when the actual normalized coefficients generate
the native maximal ideal. No restriction square is assumed. -/
theorem pointGlobalTraceP3BasisAugmentation_last_stalk_exact_at_point
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ Proj PS) [IsClosedImmersion i]
    (f : Fin 4 → homogeneousSubmodule (Fin 4) K 1) (j : Fin 4)
    (k : Spec (.of L))
    (hx : (f j).val ∈ (pointIdeal PS (i k)).primeCompl)
    (hspan : Ideal.span {pointGlobalTraceP3Basis_stalkParameter K f 1 j (i k) hx,
      pointGlobalTraceP3Basis_stalkParameter K f 2 j (i k) hx,
      pointGlobalTraceP3Basis_stalkParameter K f 3 j (i k) hx} =
        IsLocalRing.maximalIdeal (AtPrime PS (pointIdeal PS (i k)))) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) (i k)).map
        (pointGlobalTraceP3BasisKoszulLast K f))
      ((schemeModuleStalkFunctor (Proj PS) (i k)).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) := by
  let x := i k
  intro z
  rw [pointGlobalTraceP3BasisAugmentation_stalk_eq_zero_iff K i k z,
    ← hspan,
    ← threeGeneratorLast_range]
  change ambientPointKoszul_unitStalkCoordinate K x z ∈
      LinearMap.range (threeGeneratorLast
        (pointGlobalTraceP3Basis_stalkParameter K f 1 j x hx)
        (pointGlobalTraceP3Basis_stalkParameter K f 2 j x hx)
        (pointGlobalTraceP3Basis_stalkParameter K f 3 j x hx)) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(pointGlobalTraceP3Basis_stalkTripleCoordinate K f j x hx 1).symm a, ?_⟩
    apply (ambientPointKoszul_unitStalkCoordinate K x).injective
    rw [pointGlobalTraceP3Basis_last_unit_stalk_coordinates,
      AddEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨w, rfl⟩
    exact ⟨pointGlobalTraceP3Basis_stalkTripleCoordinate K f j x hx 1 w,
      (pointGlobalTraceP3Basis_last_unit_stalk_coordinates K f j x hx w).symm⟩

#check pointGlobalTraceP3BasisAugmentation_stalk_eq_zero_iff
#check pointGlobalTraceP3BasisAugmentation_last_stalk_exact_at_point
end PfaffianDescent.ProjectiveNegativeTwist
