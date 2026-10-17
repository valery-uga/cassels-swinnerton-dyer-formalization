import PfaffianDescent.CubicElevenPointLocalizedJetWitness
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericBasePoint

/-! The actual localized configuration fraction point has full interpolation
and lies over the actual unordered generic configuration. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicPolynomialJetMinorDet_interpolation_of_injective_fieldMap
    {R : Type u} [CommRing R] {F : Type v} [Field F]
    (p : MvPolynomial (Fin 4) R) (x : Fin 11 → Fin 4 → R)
    (anchor : Fin 3 → Fin 4) (pivot : Fin 3 → Fin 3)
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3)
    (f : R →+* F) (hf : Function.Injective f)
    (hm : cubicPolynomialJetMinorDet p x anchor pivot m ≠ 0) :
    Function.Surjective (cubicElevenPointFullJetRestriction (fun i j => f (x i j))
      (cubicFullJetCoordinates (fun i j => f (x i j))
        (cubicPolynomialSurfaceTangentRows (p.map f) (fun i j => f (x i j))
          anchor pivot))) := by
  have hunit : IsUnit (cubicPolynomialJetMinorDet (p.map f)
      (fun i j => f (x i j)) anchor pivot m) := by
    rw [← cubicPolynomialJetMinorDet_map]
    exact isUnit_iff_ne_zero.mpr (fun hz => hm (hf (hz.trans (map_zero f).symm)))
  exact cubicFullJetCoordinates_interpolation_of_unitMinor _ _ m hunit

theorem cubicElevenPoint_localizedFractionPoint_fullInterpolation
    {U O B : Scheme.{u}} [IsAffine U] [IsIntegral U] [IsIntegral O] [IsIntegral B]
    (i : U ⟶ O) [IsOpenImmersion i] (π : O ⟶ B) [Surjective π]
    (p : MvPolynomial (Fin 4) Γ(U, ⊤)) (x : Fin 11 → Fin 4 → Γ(U, ⊤))
    (anchor : Fin 11 → Fin 4) (pivot : Fin 3 → Fin 3)
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) 3)
    (hd : cubicCoordinateDenominator x anchor ≠ 0)
    (hm : cubicPolynomialJetMinorDet
      (p.map (algebraMap Γ(U, ⊤)
        (Localization.Away (cubicCoordinateDenominator x anchor))))
      (cubicCoordinateLocalizedVector x anchor)
      (fun k => anchor (k.castAdd 8)) pivot m ≠ 0) :
    let S := Localization.Away (cubicCoordinateDenominator x anchor)
    letI : _root_.IsDomain S := Localization.Away.isDomain hd
    let E := FractionRing S
    let f : S →+* E := algebraMap S E
    let h := f.comp (algebraMap Γ(U, ⊤) S)
    let a := voisinDegreeTenSelectedAvoidance_affineFieldPoint h
    voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a = h ∧
      a (IsLocalRing.closedPoint E) = genericPoint U ∧
      (a ≫ i) (IsLocalRing.closedPoint E) = genericPoint O ∧
      (∃ b : B.functionField →+* E,
        Spec.map (CommRingCat.ofHom b) ≫ B.fromSpecStalk (genericPoint B) =
          (a ≫ i) ≫ π) ∧
      Function.Surjective (cubicElevenPointFullJetRestriction
        (fun k j => f (cubicCoordinateLocalizedVector x anchor k j))
        (cubicFullJetCoordinates
          (fun k j => f (cubicCoordinateLocalizedVector x anchor k j))
          (cubicPolynomialSurfaceTangentRows (p.map h)
            (fun k j => f (cubicCoordinateLocalizedVector x anchor k j))
            (fun k => anchor (k.castAdd 8)) pivot))) := by
  dsimp only
  let S := Localization.Away (cubicCoordinateDenominator x anchor)
  letI : _root_.IsDomain S := Localization.Away.isDomain hd
  let E := FractionRing S
  let f : S →+* E := algebraMap S E
  let h : Γ(U, ⊤) →+* E := f.comp (algebraMap Γ(U, ⊤) S)
  obtain ⟨ha, hgU, hgO, hb⟩ :=
    voisinDegreeTenSelectedAvoidance_localizedFractionPoint_over_genericQuotient
      i π (cubicCoordinateDenominator x anchor) hd
  refine ⟨ha, hgU, hgO, hb, ?_⟩
  have hfull := cubicPolynomialJetMinorDet_interpolation_of_injective_fieldMap
    (p.map (algebraMap Γ(U, ⊤) S)) (cubicCoordinateLocalizedVector x anchor)
    (fun k => anchor (k.castAdd 8)) pivot m f (IsFractionRing.injective S E) hm
  rw [MvPolynomial.map_map] at hfull
  exact hfull

theorem cubicSurfaceElevenPoint_native_configuration_integral
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left ∧
      IsIntegral (cubicConfigurationBase p hp 11) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hO, hB, _, _⟩ :=
    exists_cubicSurfaceElevenPoint_ground_configuration_jet_witness
      (L := AlgebraicClosure K) p hp hp0
  exact ⟨hO, hB⟩

end PfaffianDescent
