import PfaffianDescent.FieldPointExtResiduePresentation
import PfaffianDescent.CanonicalQuotientStalkCoordinate
import Mathlib.RingTheory.Ideal.Colon

/-! # The actual point quotient determines its maximal ideal

An isomorphism with the unit-twisted closed-point stalk forces the parameter
ideal to be the maximal ideal. No extra span hypothesis is needed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u

/-- A module isomorphism between ring quotients determines their defining
ideals, through invariance of the module annihilator. -/
theorem moduleCatQuotientIdeal_eq_of_iso {R : Type u} [CommRing R]
    (I J : Ideal R) (q : ModuleCat.of R (R ⧸ I) ≅ ModuleCat.of R (R ⧸ J)) : I = J := by
  simpa only [Ideal.annihilator_quotient] using q.toLinearEquiv.annihilator_eq

set_option backward.isDefEq.respectTransparency false in
/-- The regular-parameter quotient of an actual unit-twisted closed point
has exactly the maximal ideal as its defining ideal. -/
theorem fieldPointUnitTwistStalkQuotient_span_eq_maximalIdeal
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    (f g : X.presheaf.stalk (i x))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _))) :
    Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)) := by
  let P : X.Modules := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  letI := schemeModuleStalkModule P (i x)
  let qP := (quotientStalkLinearEquivOfSurjectiveAndKernelEq
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (closedImmersionPushforwardStalkFromRingLinearMap i (i x))
    (closedImmersionPushforwardStalkFromRingLinearMap_surjective i (i x))
    (closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal i x)).toModuleIso
  exact moduleCatQuotientIdeal_eq_of_iso _ _
    (qM.symm ≪≫ (schemeModuleStalkModuleFunctor X (i x)).mapIso
      (closedImmersionIdealTwistSequenceUnitTargetIso i) ≪≫ qP.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The retained residue presentation of a unit-twisted point already
contains enough data to prove that its parameters span the maximal ideal. -/
theorem FieldPointExtResiduePresentation.span_eq_maximalIdeal_of_unit_source
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (Y : X.Modules)
    (e : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2 ≃+ L)
    (d : FieldPointExtResiduePresentation i x
      (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ Y e) :
    Ideal.span ({d.f, d.g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)) :=
  fieldPointUnitTwistStalkQuotient_span_eq_maximalIdeal i x d.f d.g d.qM

end PfaffianDescent
