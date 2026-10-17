import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridAffineCoordinates
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGenericFiniteFibre

/-! An injective map from the actual affine chart ring gives the literal
field point at its generic point, retaining the exact global-section map. -/

noncomputable section
open AlgebraicGeometry CategoryTheory AllCharacteristics
namespace PfaffianDescent
universe u

noncomputable def voisinDegreeTenSelectedAvoidance_affineFieldPoint
    {U : Scheme.{u}} [IsAffine U] {F : Type u} [Field F]
    (g : Γ(U, ⊤) →+* F) : Spec (.of F) ⟶ U :=
  Spec.map (CommRingCat.ofHom g) ≫ U.isoSpec.inv

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_affineFieldPoint_specialization
    {U : Scheme.{u}} [IsAffine U] {F : Type u} [Field F]
    (g : Γ(U, ⊤) →+* F) :
    voisinDegreeTenSelectedAvoidance_fieldPointSpecialization
      (voisinDegreeTenSelectedAvoidance_affineFieldPoint g) = g := by
  let a := voisinDegreeTenSelectedAvoidance_affineFieldPoint g
  have ha : a ≫ U.toSpecΓ = Spec.map (CommRingCat.ofHom g) := by
    change (Spec.map (CommRingCat.ofHom g) ≫ U.isoSpec.inv) ≫ U.toSpecΓ = _
    rw [Category.assoc, U.isoSpec_inv_toSpecΓ]
    exact Category.comp_id (Spec.map (CommRingCat.ofHom g))
  ext s
  have hsec := congrArg (fun f : Spec (.of F) ⟶ Spec Γ(U, ⊤) =>
    f.appTop.hom ((Scheme.ΓSpecIso Γ(U, ⊤)).inv.hom s)) ha
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at hsec
  change a.appTop.hom ((Scheme.ΓSpecIso Γ(U, ⊤)).hom.hom
    ((Scheme.ΓSpecIso Γ(U, ⊤)).inv.hom s)) = _ at hsec
  rw [(Scheme.ΓSpecIso Γ(U, ⊤)).inv_hom_id_apply] at hsec
  change (Scheme.ΓSpecIso (.of F)).hom.hom (a.appTop.hom s) = g s
  have hm : (Spec.map (CommRingCat.ofHom g)).appTop.hom
      ((Scheme.ΓSpecIso Γ(U, ⊤)).inv.hom s) =
      (Scheme.ΓSpecIso (.of F)).inv.hom (g s) :=
    specMap_appTop_globalSectionsIso_apply g s
  exact (congrArg (Scheme.ΓSpecIso (.of F)).hom.hom (hsec.trans hm)).trans
    ((Scheme.ΓSpecIso (.of F)).inv_hom_id_apply _)

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_affineFieldPoint_generic
    {U : Scheme.{u}} [IsAffine U] [IsIntegral U] {F : Type u} [Field F]
    (g : Γ(U, ⊤) →+* F) (hg : Function.Injective g) :
    voisinDegreeTenSelectedAvoidance_affineFieldPoint g (IsLocalRing.closedPoint F) =
      genericPoint U := by
  change U.isoSpec.inv (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint F)) = _
  rw [specFieldMap_closedPoint_eq_genericPoint_of_injective g hg]
  exact genericPoint_eq_of_isOpenImmersion U.isoSpec.inv

end PfaffianDescent
