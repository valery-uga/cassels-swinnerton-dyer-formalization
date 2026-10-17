import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridFractionPoint

/-! Native chart coordinates and their literal values at the constructed
fraction-field point. -/
noncomputable section
open AlgebraicGeometry CategoryTheory AllCharacteristics
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_fieldPointSpecialization_affineFunctionHom
    {U : Scheme.{u}} {F R : Type u} [Field F] [CommRing R]
    (a : Spec (.of F) ⟶ U) (t : U ⟶ Spec (.of R)) (z : R) :
    voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a (affineFunctionHom t z) =
      (Spec.preimage (a ≫ t)).hom z := by
  let β := (Spec.preimage (a ≫ t)).hom
  have hmap : Spec.map (CommRingCat.ofHom β) = a ≫ t := Spec.map_preimage (a ≫ t)
  have heq : affineFunctionHom (a ≫ t) z =
      (Scheme.ΓSpecIso (.of F)).inv.hom (β z) := by
    calc
      affineFunctionHom (a ≫ t) z = affineFunctionHom (Spec.map (CommRingCat.ofHom β)) z :=
        congrArg (fun f => affineFunctionHom f z) hmap.symm
      _ = (Scheme.ΓSpecIso (.of F)).inv.hom (β z) :=
        specMap_appTop_globalSectionsIso_apply β z
  have hcomp : a.appTop.hom (affineFunctionHom t z) =
      affineFunctionHom (a ≫ t) z :=
    (congrArg (fun h : R →+* Γ(Spec (.of F), ⊤) => h z)
      (affineFunctionHom_comp a t)).symm
  change (Scheme.ΓSpecIso (.of F)).hom.hom (a.appTop.hom (affineFunctionHom t z)) = β z
  exact (congrArg (Scheme.ΓSpecIso (.of F)).hom.hom (hcomp.trans heq)).trans
    ((Scheme.ΓSpecIso (.of F)).inv_hom_id_apply _)

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_affineFieldPoint_coordinate_value
    {U : Scheme.{u}} [IsAffine U] {F R : Type u} [Field F] [CommRing R]
    (g : Γ(U, ⊤) →+* F) (t : U ⟶ Spec (.of R)) (z : R) :
    (Spec.preimage (voisinDegreeTenSelectedAvoidance_affineFieldPoint g ≫ t)).hom z =
      g (affineFunctionHom t z) := by
  have h := voisinDegreeTenSelectedAvoidance_fieldPointSpecialization_affineFunctionHom
    (voisinDegreeTenSelectedAvoidance_affineFieldPoint g) t z
  rw [voisinDegreeTenSelectedAvoidance_affineFieldPoint_specialization] at h
  exact h.symm

end PfaffianDescent
