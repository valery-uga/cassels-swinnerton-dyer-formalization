import PfaffianDescent.AffineQuotientPushforwardTilde
import PfaffianDescent.AffineGammaPushforward
import PfaffianDescent.NativeCanonicalIdealInclusionFactory013
import PfaffianDescent.NativeClosedSourceChainDiagram030

/- SOURCE ONLY / UNVERIFIED. Tilde of the actual kernel of ANY surjective
ring map equals the SAME actual closed-immersion ideal module. The source
Iso and literal scheme-map equality are constructed from the first
isomorphism theorem, not assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Capture the original quotient inclusion law at the abstract ideal,
before the kernel of a concrete surjective ring map is inserted. -/
private def affineSourceIdealQuotientLaw021
    {R : Type u} [CommRing R] (I : Ideal R) :=
  affineQuotientIdealTildeClosedImmersionModuleIso_hom_toUnit I

/-- Capture the checked source inverse law independently of chain construction. -/
private def affineSourceIdealInverseLaw021
    {R : Type u} [CommRing R] (I : Ideal R)
    {Z : Scheme.{u}} (e : Z ≅ Spec (.of (R ⧸ I))) :=
  nativeClosedImmersionSourceInverseOwnSquare013 e
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- Capture the literal final equality-transport inclusion law independently. -/
private def affineSourceIdealEqualityLaw021
    {R : Type u} [CommRing R] (I : Ideal R)
    {Z : Scheme.{u}} (e : Z ≅ Spec (.of (R ⧸ I)))
    (f : Z ⟶ Spec (.of R))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = f) :=
  nativeClosedImmersionEqualityOwnSquare013
    (e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) f he

/-- The exact original right-associated chain as a value, without any diagram proof. -/
private def affineSourceIdealChainValue021
    {R : Type u} [CommRing R] (I : Ideal R)
    {Z : Scheme.{u}} (e : Z ≅ Spec (.of (R ⧸ I)))
    (f : Z ⟶ Spec (.of R))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = f) :=
  affineQuotientIdealTildeClosedImmersionModuleIso I ≪≫
    (closedImmersionModuleSourceIso e
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).symm ≪≫
    eqToIso (congrArg IdealSheafDataModule.closedImmersionModule he)

/-- Pin the quotient Scheme map's source from the CommRing quotient BEFORE
any ideal-module objects or SourceIso projections are elaborated. -/
private def affineSourceIdealQuotientMap027
    {R : Type u} [CommRing R] (I : Ideal R) :
    Spec (.of (R ⧸ I)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The typed quotient Scheme map is the ORIGINAL quotient Scheme map. -/
private theorem affineSourceIdealQuotientMap_original027
    {R : Type u} [CommRing R] (I : Ideal R) :
    affineSourceIdealQuotientMap027 I =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := rfl

/-- Specialize the WHOLE original three-arrow Scheme diagram once, after it
has been constructed without any quotient/Spec/tilde dictionary expressions.
The first-leg law is the original proved quotient law, never an endpoint premise. -/
private def affineSourceIdealInclusionData021
    {R : Type u} [CommRing R] (I : Ideal R)
    {Z : Scheme.{u}} (e : Z ≅ Spec (.of (R ⧸ I)))
    (f : Z ⟶ Spec (.of R))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = f) :=
  nativeClosedSourceChainDiagramData030 (X := Spec (.of R))
    (M := (tilde.functor (.of R)).obj (ModuleCat.of R I))
    e (affineSourceIdealQuotientMap027 I) f he
    (affineQuotientIdealTildeClosedImmersionModuleIso I)
    ((tilde.functor (.of R)).map (ModuleCat.ofHom I.subtype) ≫
      (affineGlobalSectionsUnitTildeIso (A := R)).hom)
    (affineSourceIdealQuotientLaw021 I)

/-- Specialize the proved abstract ORIGINAL chain identity with the exact
arguments of the passed quotient diagram; do not unfold its map/law proof. -/
private def affineSourceIdealInclusionData_value021
    {R : Type u} [CommRing R] (I : Ideal R)
    {Z : Scheme.{u}} (e : Z ≅ Spec (.of (R ⧸ I)))
    (f : Z ⟶ Spec (.of R))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = f) :=
  @nativeClosedSourceChainDiagramData_original030
    (Spec (.of R)) Z (Spec (.of (R ⧸ I)))
    ((tilde.functor (.of R)).obj (ModuleCat.of R I))
    e (affineSourceIdealQuotientMap027 I) f he
    (affineQuotientIdealTildeClosedImmersionModuleIso I)
    ((tilde.functor (.of R)).map (ModuleCat.ofHom I.subtype) ≫
      (affineGlobalSectionsUnitTildeIso (A := R)).hom)
    (affineSourceIdealQuotientLaw021 I)

/-- Specialize the already formed native map/law data ONCE to the original kernel,
original first-isomorphism source Iso, and its proved literal scheme-map equality. -/
private def surjectiveAffineActualIdealTildeData013
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :=
  let I := RingHom.ker rho
  let eRing := rho.quotientKerEquivOfSurjective hrho
  let e : Spec (.of L) ≅ Spec (.of (R ⧸ I)) :=
    Scheme.Spec.mapIso eRing.toCommRingCatIso.op
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let he : e.hom ≫ i = Spec.map (CommRingCat.ofHom rho) := by
    change Spec.map (CommRingCat.ofHom eRing.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = _
    rw [← Spec.map_comp]
    congr 1
  affineSourceIdealInclusionData021 (R := R) I e
    (Spec.map (CommRingCat.ofHom rho)) he

def surjectiveAffineActualIdealTildeIso
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    (tilde.functor (.of R)).obj (ModuleCat.of R (RingHom.ker rho)) ≅
      IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom rho)) := by
  exact (surjectiveAffineActualIdealTildeData013 rho hrho).val

/-- The upstream canonical map's own inclusion law is returned by the same data. -/
def surjectiveAffineActualIdealTildeData_hom_toUnit013
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :=
  (surjectiveAffineActualIdealTildeData013 rho hrho).property

/-- Name the EXACT original quotient chain proposition under its dependent
local source-Iso/map-equality bindings. This is a result type, not an assumption. -/
private def surjectiveAffineActualIdealTildeOriginalChainStatement038
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) : Prop :=
  let I := RingHom.ker rho
  let eRing := rho.quotientKerEquivOfSurjective hrho
  let e : Spec (.of L) ≅ Spec (.of (R ⧸ I)) :=
    Scheme.Spec.mapIso eRing.toCommRingCatIso.op
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let he : e.hom ≫ i = Spec.map (CommRingCat.ofHom rho) := by
    change Spec.map (CommRingCat.ofHom eRing.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = _
    rw [← Spec.map_comp]
    congr 1
  (affineSourceIdealInclusionData021 (R := R) I e
    (Spec.map (CommRingCat.ofHom rho)) he).val =
    affineSourceIdealChainValue021 (R := R) I e
      (Spec.map (CommRingCat.ofHom rho)) he

/-- Capture the original-kernel/source-Iso/map-equality specialization of the
proved quotient chain identity independently of the public original-chain header. -/
private def surjectiveAffineActualIdealTildeOriginalChainLaw037
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    surjectiveAffineActualIdealTildeOriginalChainStatement038 rho hrho :=
  let I := RingHom.ker rho
  let eRing := rho.quotientKerEquivOfSurjective hrho
  let e : Spec (.of L) ≅ Spec (.of (R ⧸ I)) :=
    Scheme.Spec.mapIso eRing.toCommRingCatIso.op
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let he : e.hom ≫ i = Spec.map (CommRingCat.ofHom rho) := by
    change Spec.map (CommRingCat.ofHom eRing.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = _
    rw [← Spec.map_comp]
    congr 1
  affineSourceIdealInclusionData_value021 (R := R) I e
    (Spec.map (CommRingCat.ofHom rho)) he

lemma surjectiveAffineActualIdealTildeIso_originalChain013
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :
  let I := RingHom.ker rho
  let eRing := rho.quotientKerEquivOfSurjective hrho
  let e : Spec (.of L) ≅ Spec (.of (R ⧸ I)) :=
    Scheme.Spec.mapIso eRing.toCommRingCatIso.op
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let he : e.hom ≫ i = Spec.map (CommRingCat.ofHom rho) := by
    change Spec.map (CommRingCat.ofHom eRing.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = _
    rw [← Spec.map_comp]
    congr 1
  surjectiveAffineActualIdealTildeIso rho hrho =
    affineQuotientIdealTildeClosedImmersionModuleIso I ≪≫
      (closedImmersionModuleSourceIso e i).symm ≪≫
      eqToIso (congrArg IdealSheafDataModule.closedImmersionModule he) := by
  exact surjectiveAffineActualIdealTildeOriginalChainLaw037 rho hrho

end PfaffianDescent
