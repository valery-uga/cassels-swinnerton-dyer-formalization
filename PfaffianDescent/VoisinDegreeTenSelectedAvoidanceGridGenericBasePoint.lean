import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridFractionPoint
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericField
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridCoordinateValues

/-! The actual determinant-open fraction-field point lies over the native
unordered generic configuration, with the literal function-field factorization. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_localizedFractionPoint_over_genericQuotient
    {U O B : Scheme.{u}} [IsAffine U] [IsIntegral U] [IsIntegral O] [IsIntegral B]
    (i : U ⟶ O) [IsOpenImmersion i] (π : O ⟶ B) [Surjective π]
    (s : Γ(U, ⊤)) (hs : s ≠ 0) :
    let S := Localization.Away s
    letI : IsDomain S := Localization.Away.isDomain hs
    let E := FractionRing S
    let h := (algebraMap S E).comp (algebraMap Γ(U, ⊤) S)
    let a := voisinDegreeTenSelectedAvoidance_affineFieldPoint h
    voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a = h ∧
      a (IsLocalRing.closedPoint E) = genericPoint U ∧
      (a ≫ i) (IsLocalRing.closedPoint E) = genericPoint O ∧
      ∃ b : B.functionField →+* E,
        Spec.map (CommRingCat.ofHom b) ≫ B.fromSpecStalk (genericPoint B) =
          (a ≫ i) ≫ π := by
  dsimp only
  let S := Localization.Away s
  letI : IsDomain S := Localization.Away.isDomain hs
  let E := FractionRing S
  let h : Γ(U, ⊤) →+* E := (algebraMap S E).comp (algebraMap Γ(U, ⊤) S)
  let a := voisinDegreeTenSelectedAvoidance_affineFieldPoint h
  have hloc : Function.Injective (algebraMap Γ(U, ⊤) S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hhinj : Function.Injective h := (IsFractionRing.injective S E).comp hloc
  have ha : a (IsLocalRing.closedPoint E) = genericPoint U :=
    voisinDegreeTenSelectedAvoidance_affineFieldPoint_generic h hhinj
  have hao : (a ≫ i) (IsLocalRing.closedPoint E) = genericPoint O := by
    change i (a (IsLocalRing.closedPoint E)) = _
    rw [ha]
    exact genericPoint_eq_of_isOpenImmersion i
  have hB : ((a ≫ i) ≫ π) (IsLocalRing.closedPoint E) = genericPoint B := by
    change π ((a ≫ i) (IsLocalRing.closedPoint E)) = _
    rw [hao]
    exact AllCharacteristics.genericPoint_map_of_surjective π
  refine ⟨voisinDegreeTenSelectedAvoidance_affineFieldPoint_specialization h, ha, hao,
    B.genericFieldPointRingHom ((a ≫ i) ≫ π) hB, ?_⟩
  exact B.genericFieldPointRingHom_spec ((a ≫ i) ≫ π) hB

end PfaffianDescent
