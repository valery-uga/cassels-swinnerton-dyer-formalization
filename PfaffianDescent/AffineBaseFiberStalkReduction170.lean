import PfaffianDescent.ActualSmoothFamilyAmbientStalk169
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineFibreQuotient

/-! SOURCE ONLY / UNVERIFIED170. Actual affine base-change fiber stalk
reduction and its entire kernel, under the original canonical base action.
No flatness, smoothness, regularity or kernel certificate is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical family coefficient map for Spec(g) is exactly the
original g followed by the native coefficient map into the target stalk. -/
lemma familyBaseToStalk169_specMap170
    {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A)
    (x : PrimeSpectrum A) :
    letI : Algebra A ((Spec (.of A)).presheaf.stalk x) :=
      StructureSheaf.stalkAlgebra A x
    familyBaseToStalk169 (Spec.map (CommRingCat.ofHom g)) x =
      (algebraMap A ((Spec (.of A)).presheaf.stalk x)).comp g := by
  change (StructureSheaf.toStalk R (PrimeSpectrum.comap g x) ≫
      (Spec.sheafedSpaceMap (CommRingCat.ofHom g)).hom.stalkMap x).hom =
    (CommRingCat.ofHom g ≫ StructureSheaf.toStalk A x).hom
  exact congrArg (fun a => a.hom) (AlgebraicGeometry.stalkMap_toStalk (CommRingCat.ofHom g) x)

/-- The actual stalk reduction: the stalk map of the ACTUAL first
projection of Spec(A) ×_Spec(R) Spec(R/I), without a chosen ring quotient. -/
def affineBaseFiberStalkReduction170
    {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A) (I : Ideal R)
    (z : ↥(pullback (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    let i := pullback.fst (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (Spec (.of A)).presheaf.stalk (i z) →+*
      (pullback (Spec.map (CommRingCat.ofHom g))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).presheaf.stalk z :=
  (Scheme.Hom.stalkMap (pullback.fst (Spec.map (CommRingCat.ofHom g))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z).hom

/-- The actual base-fiber closed immersion has a surjective stalk map. -/
lemma affineBaseFiberStalkReduction170_surjective
    {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A) (I : Ideal R)
    (z : ↥(pullback (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    Function.Surjective (affineBaseFiberStalkReduction170 g I z) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact (pullback.fst (Spec.map (CommRingCat.ofHom g))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).stalkMap_surjective z

/-- The entire actual reduction kernel is the extension of the ORIGINAL
base ideal under the EXACT canonical coefficient map. No principal-ideal
restriction, flatness premise or quotient/kernel identification hypothesis. -/
lemma affineBaseFiberStalkReduction170_ker
    {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A) (I : Ideal R)
    (z : ↥(pullback (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    let i := pullback.fst (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    RingHom.ker (affineBaseFiberStalkReduction170 g I z) =
      I.map (familyBaseToStalk169 (Spec.map (CommRingCat.ofHom g)) (i z)) := by
  let i := pullback.fst (Spec.map (CommRingCat.ofHom g))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let x : PrimeSpectrum A := i z
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : Algebra A ((Spec (.of A)).presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra A x
  let e := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  have hgerm : ((Spec (.of A)).presheaf.germ ⊤ x (by trivial)).hom.comp
      (Scheme.ΓSpecIso (.of A)).inv.hom =
      algebraMap A ((Spec (.of A)).presheaf.stalk x) := rfl
  change RingHom.ker (i.stalkMap z).hom = _
  calc
    RingHom.ker (i.stalkMap z).hom =
        ((I.map g).comap (Scheme.ΓSpecIso (.of A)).hom.hom).map
          ((Spec (.of A)).presheaf.germ ⊤ x (by trivial)).hom := by
      rw [← cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel
        i ⟨⊤, isAffineOpen_top _⟩ z (by trivial),
        cubicClosedPointSerreFiniteZeroResidual_affineFibre_kernel_top]
    _ = ((I.map g).map (Scheme.ΓSpecIso (.of A)).inv.hom).map
          ((Spec (.of A)).presheaf.germ ⊤ x (by trivial)).hom := by
      exact congrArg (fun J : Ideal Γ(Spec (.of A), ⊤) =>
        J.map ((Spec (.of A)).presheaf.germ ⊤ x (by trivial)).hom)
        (Ideal.map_symm (I := I.map g) e).symm
    _ = (I.map g).map (algebraMap A ((Spec (.of A)).presheaf.stalk x)) := by
      rw [Ideal.map_map, hgerm]
    _ = I.map (familyBaseToStalk169 (Spec.map (CommRingCat.ofHom g)) x) := by
      rw [Ideal.map_map, familyBaseToStalk169_specMap170]

/-- The actual fiber stalk is the quotient by precisely the extended
original base ideal, retaining the actual reduction map. -/
def affineBaseFiberStalkQuotientEquiv170
    {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A) (I : Ideal R)
    (z : ↥(pullback (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    let i := pullback.fst (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    ((Spec (.of A)).presheaf.stalk (i z) ⧸
      I.map (familyBaseToStalk169 (Spec.map (CommRingCat.ofHom g)) (i z))) ≃+*
      (pullback (Spec.map (CommRingCat.ofHom g))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).presheaf.stalk z :=
  (Ideal.quotEquivOfEq (affineBaseFiberStalkReduction170_ker g I z).symm).trans
    ((affineBaseFiberStalkReduction170 g I z).quotientKerEquivOfSurjective
      (affineBaseFiberStalkReduction170_surjective g I z))

/-- The quotient equivalence commutes with the ORIGINAL native stalk map,
so it does not merely identify an unrelated abstract quotient ring. -/
lemma affineBaseFiberStalkQuotientEquiv170_mk
    {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A) (I : Ideal R)
    (z : ↥(pullback (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u}))
    (a : (Spec (.of A)).presheaf.stalk
      ((pullback.fst (Spec.map (CommRingCat.ofHom g))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z)) :
    affineBaseFiberStalkQuotientEquiv170 g I z (Ideal.Quotient.mk _ a) =
      affineBaseFiberStalkReduction170 g I z a := by
  simp only [affineBaseFiberStalkQuotientEquiv170, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ a

end PfaffianDescent
