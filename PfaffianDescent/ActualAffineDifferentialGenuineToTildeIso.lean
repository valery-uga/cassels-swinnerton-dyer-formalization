import PfaffianDescent.ActualAffineDifferentialTildeToGenuineSheafIso

/- SOURCE ONLY / UNVERIFIED. The inverse of the SAME genuine tilde
adjoint195, with exact native unit and point actions derived internally.
This is not an equality assertion about the old unverified affine Iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

/-- Actual genuine Omega -> native tilde, using the internally derived
Iso property of SAME195. No comparison or invertibility premise. -/
def actualAffineDifferentialGenuineToTildeIso :
    schemeRelativeDifferentials
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≅
      (tilde.functor (CommRingCat.of R)).obj
        (ModuleCat.of R (KaehlerDifferential k R)) := by
  let A := actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)
  letI : IsIso A := actualAffineDifferentialTildeToGenuineSheaf_isIso
    (k := k) (R := R)
  exact (asIso A).symm

private lemma actualGenuineNativeIso_inv_hom_apply
    {S : Type u} [CommRing S] {M N : ModuleCat S}
    (e : M ≅ N) (x : M) : e.inv (e.hom x) = x :=
  ConcreteCategory.congr_hom e.hom_inv_id x

/-- The genuine-to-tilde comparison sends the SAME193 top universal
section of every native differential to the SAME native tilde unit. -/
lemma actualAffineDifferentialGenuineToTildeIso_nativeTop (x : KaehlerDifferential k R) :
    (moduleSpecΓFunctor (R := CommRingCat.of R)).map
      (actualAffineDifferentialGenuineToTildeIso (k := k) (R := R)).hom
      (actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R) x) =
    ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).app
      (ModuleCat.of R (KaehlerDifferential k R))).hom x := by
  let M := ModuleCat.of R (KaehlerDifferential k R)
  let A := actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)
  letI : IsIso A := actualAffineDifferentialTildeToGenuineSheaf_isIso
    (k := k) (R := R)
  let G := moduleSpecΓFunctor (R := CommRingCat.of R)
  let e := G.mapIso (asIso A)
  let u := ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).app M).hom x
  have hUnit := actualAffineDifferentialTildeToGenuineSheaf_unit
    (k := k) (R := R) x
  change e.inv (actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R) x) = u
  exact (congrArg (fun y => e.inv y) hUnit.symm).trans
    (actualGenuineNativeIso_inv_hom_apply e u)

/-- At every actual point, the SAME genuine universal section class maps
to the true native tilde point class. CommRing L is retained. -/
lemma actualAffineDifferentialGenuineToTildeIso_nativePoint
    {L : Type u} [CommRing L] (rho : R →+* L) (x : KaehlerDifferential k R) :
    (moduleSpecΓFunctor (R := CommRingCat.of L)).map
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).map
        (actualAffineDifferentialGenuineToTildeIso (k := k) (R := R)).hom)
      (actualAffineSheafPointClass (CommRingCat.ofHom rho)
        (schemeRelativeDifferentials
          (Spec.map (CommRingCat.ofHom (algebraMap k R))))
        (actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R) x)) =
    affineTildeActualPointClass (CommRingCat.ofHom rho)
      (ModuleCat.of R (KaehlerDifferential k R)) x := by
  let phi := CommRingCat.ofHom rho
  let M := ModuleCat.of R (KaehlerDifferential k R)
  let T := (tilde.functor (CommRingCat.of R)).obj M
  let O := schemeRelativeDifferentials
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let B := actualAffineDifferentialGenuineToTildeIso (k := k) (R := R)
  let u := ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).app M).hom x
  let v := actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R) x
  have hN := actualAffineSheafPointClass_natural phi B.hom v
  have hTop := actualAffineDifferentialGenuineToTildeIso_nativeTop
    (k := k) (R := R) x
  have hClass := affineTildeActualPointClass_eq_actualSheafPointClass phi M x
  exact hN.symm.trans
    ((congrArg (fun y => actualAffineSheafPointClass phi T y) hTop).trans hClass.symm)

end PfaffianDescent
