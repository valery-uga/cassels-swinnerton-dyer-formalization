import PfaffianDescent.ActualAffineDifferentialPresheafBasicOpen

/- SOURCE ONLY / UNVERIFIED. The actual presheaf localization comparison
retains the genuine universal derivation on the SAME original functions. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/- Equality of the ACTUAL coefficient-ring maps transports its universal d.
   Auxiliary equality input is discharged internally in the public theorem. -/
private lemma actualCommRingDifferential_eqToIso_d
    {A B : CommRingCat.{u}} (s t : A ⟶ B) (h : s = t) (b : B) :
    (eqToIso (congrArg (fun f : A ⟶ B => CommRingCat.KaehlerDifferential f) h)).toLinearEquiv
        (CommRingCat.KaehlerDifferential.d (f := s) b) =
      CommRingCat.KaehlerDifferential.d (f := t) b := by
  cases h
  rfl


/-- Inferred proof of the canonical comparison on original differentials.
Its coefficient map equality is derived internally on the same actual open. -/
def actualAffineDifferentialPresheafBasicOpenEquiv_d (f r : R) :=
  let A := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen f)
  letI : Algebra R A := inferInstanceAs
    (Algebra R ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen f))))
  let s : CommRingCat.of k ⟶ CommRingCat.of A :=
    (schemeBaseScalarPresheafMap
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))).app
        (op (PrimeSpectrum.basicOpen f))
  let t : CommRingCat.of k ⟶ CommRingCat.of A :=
    CommRingCat.ofHom ((algebraMap R A).comp (algebraMap k R))
  let h : s = t := affineSchemeBaseScalarPresheafMap_app (k := k) (R := R)
    (PrimeSpectrum.basicOpen f)
  let hd := actualCommRingDifferential_eqToIso_d s t h (algebraMap R A r)
  (congrArg (fun z => affineKaehlerBasicOpenEquiv (k := k) f z) hd).trans
    (affineKaehlerBasicOpenEquiv_D (k := k) f r)

end PfaffianDescent
