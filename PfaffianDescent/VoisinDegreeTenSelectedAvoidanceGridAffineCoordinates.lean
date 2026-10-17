import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridAffineChart

/-! # Literal coefficient and specialization ring maps on the grid chart -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The native coefficient map on actual global sections of a scheme over
the ground field. -/
def voisinDegreeTenSelectedAvoidance_affineBaseRingMap
    {K : Type u} [Field K] (U : Scheme.{u}) (s : U ⟶ Spec (.of K)) :
    K →+* Γ(U, ⊤) :=
  s.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom

/-- Literal evaluation of global sections at an actual extension-field point. -/
def voisinDegreeTenSelectedAvoidance_fieldPointSpecialization
    {L : Type u} [Field L] {U : Scheme.{u}} (a : Spec (.of L) ⟶ U) :
    Γ(U, ⊤) →+* L :=
  (Scheme.ΓSpecIso (.of L)).hom.hom.comp a.appTop.hom

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_fieldPointSpecialization_base
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (U : Scheme.{u}) (s : U ⟶ Spec (.of K)) (a : Spec (.of L) ⟶ U)
    (ha : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    (voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a).comp
      (voisinDegreeTenSelectedAvoidance_affineBaseRingMap U s) = algebraMap K L := by
  ext c
  change (Scheme.ΓSpecIso (.of L)).hom.hom
    (a.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom c))) = algebraMap K L c
  have hsec := congrArg (fun f : Spec (.of L) ⟶ Spec (.of K) =>
    f.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom c)) ha
  change a.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom c)) = _ at hsec
  rw [hsec, specMap_appTop_globalSectionsIso_apply]
  exact (Scheme.ΓSpecIso (.of L)).inv_hom_id_apply _

set_option backward.isDefEq.respectTransparency false in
/-- The actual chart specialization sends each native pulled coordinate to
the original selected vector coordinate. -/
theorem voisinDegreeTenSelectedAvoidance_fieldPointSpecialization_coordinate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (v : Fin 4 → L) (hpv : p.eval₂ (algebraMap K L) v = 0) (hv0 : v 0 = 1)
    (U : Scheme.{u}) (a : Spec (.of L) ⟶ U)
    (t : U ⟶ Spec (.of (Away (grading (equationIdeal p hp)) (coordinate (equationIdeal p hp) 0))))
    (hpoint : (a ≫ t) ≫ Proj.awayι (grading (equationIdeal p hp))
      (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
      (by decide : 0 < 1) =
      voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver p hp v hpv hv0)
    (j : Fin 4) :
    voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a
      (pulledLinearChartCoordinate (equationIdeal p hp)
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) U t j) = v j := by
  change (Scheme.ΓSpecIso (.of L)).hom.hom (a.appTop.hom _) = v j
  rw [voisinDegreeTenSelectedAvoidance_normalizedCubicPointOver_pulled_coordinate
    p hp v hpv hv0 U a t hpoint j]
  exact (Scheme.ΓSpecIso (.of L)).inv_hom_id_apply _

end PfaffianDescent
