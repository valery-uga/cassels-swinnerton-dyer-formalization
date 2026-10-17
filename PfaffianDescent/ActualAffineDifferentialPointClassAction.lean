import PfaffianDescent.AffineTildeActualPointClass
import PfaffianDescent.ActualAffineSchemeDifferentialPointFiber

/- SOURCE ONLY / UNVERIFIED. Original point-class contract, using the
same genuine forward195 map and revised142 inverse point equivalence.
No old unverified actualAffineDifferentialSheafIso/derivation-action path. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [CommRing L] [Algebra k R]

def actualAffineDifferentialPointClass (ρ : R →+* L) (r : R) :
    (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ρ))).obj
        (schemeRelativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap k R))))) :=
  (moduleSpecΓFunctor (R := CommRingCat.of L)).map
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom ρ))).map
      (actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)))
    (affineTildeActualPointClass (CommRingCat.ofHom ρ)
      (ModuleCat.of R (KaehlerDifferential k R)) (KaehlerDifferential.D k R r))

lemma actualAffineDifferentialPointFiberEquiv_pointClass (ρ : R →+* L) (r : R) :
    letI : Algebra R L := ρ.toAlgebra
    actualAffineSchemeDifferentialPointFiberEquiv (k := k) ρ
      (actualAffineDifferentialPointClass (k := k) ρ r) =
        (1 : L) ⊗ₜ[R] KaehlerDifferential.D k R r := by
  letI : Algebra R L := ρ.toAlgebra
  let f := Spec.map (CommRingCat.ofHom ρ)
  let A := actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)
  letI : IsIso A := actualAffineDifferentialTildeToGenuineSheaf_isIso (k := k) (R := R)
  let M := ModuleCat.of R (KaehlerDifferential k R)
  let H := moduleSpecΓFunctor (R := CommRingCat.of L)
  let P := Scheme.Modules.pullback f
  let e := H.mapIso (P.mapIso (asIso A))
  let x := affineTildeActualPointClass (CommRingCat.ofHom ρ) M
    (KaehlerDifferential.D k R r)
  let E := affineTildeActualPointFiberEquiv (CommRingCat.ofHom ρ) M
  have hc : e.inv (e.hom x) = x :=
    ConcreteCategory.congr_hom e.hom_inv_id x
  change E (e.inv (e.hom x)) = _
  exact (congrArg (fun z => E z) hc).trans
    (affineTildeActualPointFiberEquiv_pointClass (CommRingCat.ofHom ρ) M
      (KaehlerDifferential.D k R r))

end PfaffianDescent
