import PfaffianDescent.ActualAffineLocalizedModulePresheafSheafIso
import PfaffianDescent.ActualAffineForgottenDifferentialRestrictionLocalization

/- SOURCE ONLY / UNVERIFIED. Unconditional actual affine specialization.
All basic-open localization inputs are derived from primitive k/R/f.
The original genuine differential sheaf and unit are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

noncomputable def actualAffineDifferentialPresheafSheafIso
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] :=
  let P := schemeRelativeDifferentialsPresheaf
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  have hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom) :=
    fun f => actualAffineForgottenDifferentialRestriction_localized
      (k := k) (R := R) f
  actualAffineLocalizedModulePresheafSheafIso P hLoc

noncomputable def actualAffineDifferentialPresheafUnit_top_bijective
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] :=
  let P := schemeRelativeDifferentialsPresheaf
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  have hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom) :=
    fun f => actualAffineForgottenDifferentialRestriction_localized
      (k := k) (R := R) f
  actualAffineLocalizedModulePresheafUnit_top_bijective P hLoc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual genuine Omega sheaf is localizing. No QC or comparison
input remains: the required Iso is the actual derived sheafification Iso. -/
noncomputable def actualAffineGenuineDifferentialSheaf_localizing
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] :=
  let P := schemeRelativeDifferentialsPresheaf
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let e := actualAffineDifferentialPresheafSheafIso (k := k) (R := R)
  let M : ModuleCat R := (actualAffineModulePresheafOverBase P).obj (op ⊤)
  have hM : IsLocalizing
      ((modulesSpecToSheaf (R := CommRingCat.of R)).obj
        (tilde (R := CommRingCat.of R) M)) :=
    isLocalizing_tilde (R := CommRingCat.of R) M
  isLocalizing_of_iso
    ((modulesSpecToSheaf (R := CommRingCat.of R)).mapIso e.symm) hM

end PfaffianDescent
