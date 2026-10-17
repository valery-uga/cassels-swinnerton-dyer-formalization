import PfaffianDescent.ActualForgottenDifferentialInitialRestrictionLocalization
import PfaffianDescent.ActualAffineDifferentialPresheafOverBase

/- SOURCE ONLY / UNVERIFIED. The final input is a primitive affine scheme
and one basic open. Coefficient-ring localization is DERIVED here.
No differential-map localization, QC, Iso, or chart comparison is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- Change only the COEFFICIENT-RING algebra along its proved ring-map equality.
This lemma does not transport or replace any module scalar action. -/
private lemma coefficientRingLocalization_of_map_eq
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A] (g : R →+* A)
    (h : g = algebraMap R A) :
    letI : Algebra R A := g.toAlgebra
    IsLocalization S A := by
  have ha : g.toAlgebra = (inferInstance : Algebra R A) :=
    (congrArg (fun t : R →+* A => t.toAlgebra) h).trans toAlgebra_algebraMap
  exact (congrArg (fun a : Algebra R A => @IsLocalization R _ S A _ a) ha).mpr
    (inferInstance : IsLocalization S A)

/-- The SAME actual forgotten differential-presheaf restriction top -> D(f)
is a localization for the original R action. The proof is inferred to avoid
re-elaborating the full actual module dictionary in an expected annotation. -/
noncomputable def actualAffineForgottenDifferentialRestriction_localized
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] (f : R) :=
  let X := Spec (CommRingCat.of R)
  let U : X.Opens := PrimeSpectrum.basicOpen f
  let A := X.presheaf.obj (op U)
  let h₀ : CategoryTheory.Limits.IsInitial (op (⊤ : X.Opens)) :=
    CategoryTheory.Limits.initialOpOfTerminal CategoryTheory.Limits.isTerminalTop
  let e : CommRingCat.of R ≅ X.presheaf.obj (op ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm
  let sigma := schemeBaseScalarPresheafMap
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let gamma : CommRingCat.of R ⟶ A := e.hom ≫ X.presheaf.map (h₀.to (op U))
  letI : Algebra R A := StructureSheaf.openAlgebra R (op U)
  letI : IsLocalization (Submonoid.powers f) A :=
    StructureSheaf.IsLocalization.to_basicOpen R f
  have hi : h₀.to (op U) = U.leTop.op := Subsingleton.elim _ _
  have hgamma : gamma = CommRingCat.ofHom (algebraMap R A) :=
    (congrArg (fun a => e.hom ≫ X.presheaf.map a) hi).trans
      (Scheme.toOpen_eq (CommRingCat.of R) U).symm
  have hLoc : letI : Algebra R A := gamma.hom.toAlgebra
      IsLocalization (Submonoid.powers f) A :=
    coefficientRingLocalization_of_map_eq (Submonoid.powers f) gamma.hom
      (congrArg CommRingCat.Hom.hom hgamma)
  have h := actualForgottenDifferentialInitialRestriction_localized
    X.presheaf sigma (op ⊤) h₀ e (op U) f hLoc
  let F := actualAffineDifferentialPresheafOverBase (k := k) (R := R)
  (congrArg (fun a : op (⊤ : X.Opens) ⟶ op U =>
    IsLocalizedModule (Submonoid.powers f) ((F.map a).hom)) hi).mp h

end PfaffianDescent
