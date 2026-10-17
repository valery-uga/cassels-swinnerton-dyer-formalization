import PfaffianDescent.CubicElevenPointGroundKernelInterpolation
import PfaffianDescent.CubicFieldPointScaledComponentCoordinates
import PfaffianDescent.CubicElevenPointGroundRestrictionSurjective
import PfaffianDescent.CubicPolynomialJetEquation

/-! A smooth cubic over the original field constructs the actual canonical
degree-eleven chart restriction kernel and its six derivative directions.
No interpolation, rank, or component-coordinate certificate is an input. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

local instance {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hO : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left] :
    IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left := hO

theorem exists_cubicElevenPoint_groundChartKernel
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (hO : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (hB : IsIntegral (cubicConfigurationBase p hp 11)),
    letI := hO
    letI := hB
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 11).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 11 ≫
        cubicConfigurationToBase p hp 11),
    CubicElevenPointGroundChartKernelFor p hp a ha := by
  classical
  obtain ⟨hO, hB⟩ := cubicSurfaceElevenPoint_native_configuration_integral p hp hp0
  letI : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left := hO
  letI : IsIntegral (cubicConfigurationBase p hp 11) := hB
  refine ⟨hO, hB, ?_⟩
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 11
  refine ⟨a, ha, ?_⟩
  obtain ⟨U, hUa, hUint, c, i, t, b, x, anchor, pivot, m, hd, _, _,
    hi, hb, hx, ht, hdata⟩ := exists_cubicSurfaceElevenPoint_native_generic_interpolation p hp hp0
  letI : IsAffine U := hUa
  letI : IsIntegral U := hUint
  let S := Localization.Away (cubicCoordinateDenominator x anchor)
  letI : _root_.IsDomain S := Localization.Away.isDomain hd
  let E := FractionRing S
  let f : S →+* E := algebraMap S E
  let h : Γ(U, ⊤) →+* E := f.comp (algebraMap Γ(U, ⊤) S)
  let y : Fin 11 → Fin 4 → E := fun k r => f (cubicCoordinateLocalizedVector x anchor k r)
  rcases hdata with ⟨_, _, _, ⟨β, hβ⟩, hy, _, hpy, hfull⟩
  exact cubicElevenPointGroundChartKernel_of_interpolation p hp a ha U i c t ht
    b hb x hx h β hβ anchor pivot y
    (fun k => ((cubicCoordinateDenominator_isUnit_each x anchor k).map f).ne_zero)
    hy hpy hfull

end PfaffianDescent
