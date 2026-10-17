import PfaffianDescent.CorayQuotientNativeConormalSheaf

/-! Actual OWN affine source, quotient presentation constructed from rho.
SOURCE ONLY / UNVERIFIED. No field or supplied quotient/sheaf identification. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- The actual quotient presentation preserves ORIGINAL ground constants
through A. Neither B's coefficient action nor the quotient is replaced. -/
theorem surjectiveAffineQuotientPresentation_groundConstants
    {K A B : Type u} [Field K] [CommRing A] [CommRing B] [Algebra K A]
    (rho : A →+* B) (hrho : Function.Surjective rho) (c : K) :
    rho.quotientKerEquivOfSurjective hrho
      (algebraMap K (A ⧸ RingHom.ker rho) c) = rho (algebraMap K A c) := by
  change rho.quotientKerEquivOfSurjective hrho
    (Ideal.Quotient.mk (RingHom.ker rho) (algebraMap K A c)) = _
  exact RingHom.quotientKerEquivOfSurjective_apply_mk hrho (algebraMap K A c)

/-- The SAME source Spec B carries the actual conormal sheaf to the native
kernel cotangent sheaf by its actual quotientKer scheme isomorphism.
The action on Spec B is the ACTUAL scheme pullback, not linear-equivalence
transport. All rings may have nilpotents and B need not be a field. -/
def surjectiveAffineNativeConormalQuotientTildeIso
    {A B : Type u} [CommRing A] [CommRing B]
    (rho : A →+* B) (hrho : Function.Surjective rho) :
    let I := RingHom.ker rho
    let eRing := rho.quotientKerEquivOfSurjective hrho
    actualClosedImmersionConormalModule (Spec.map (CommRingCat.ofHom rho)) ≅
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom eRing.toRingHom))).obj
        ((tilde.functor (CommRingCat.of (A ⧸ I))).obj
          (ModuleCat.of (A ⧸ I) I.Cotangent)) := by
  let I := RingHom.ker rho
  let eRing := rho.quotientKerEquivOfSurjective hrho
  let e : Spec (.of B) ≅ Spec (.of (A ⧸ I)) :=
    Scheme.Spec.mapIso eRing.toCommRingCatIso.op
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let i := Spec.map (CommRingCat.ofHom rho)
  have he : e.hom ≫ j = i := by
    change Spec.map (CommRingCat.ofHom eRing.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = _
    rw [← Spec.map_comp]
    congr 1
  let eI : IdealSheafDataModule.closedImmersionModule i ≅
      IdealSheafDataModule.closedImmersionModule j :=
    eqToIso (congrArg IdealSheafDataModule.closedImmersionModule he.symm) ≪≫
      closedImmersionModuleSourceIso e j
  exact (Scheme.Modules.pullback i).mapIso eI ≪≫
    (Scheme.Modules.pullbackCongr he.symm).app
      (IdealSheafDataModule.closedImmersionModule j) ≪≫
    ((Scheme.Modules.pullbackComp e.hom j).app
      (IdealSheafDataModule.closedImmersionModule j)).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso (affineQuotientNativeConormalTildeIso I)

end PfaffianDescent
