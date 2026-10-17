import PfaffianDescent.CubicPointTraceFieldBaseChangeExtendedSupport
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! SOURCE ONLY198. The original parameter remains a parameter at the actual
separable scalar-extension stalk. No local Ext/nonzero trace assertion is made. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Unramified local finite-type geometry preserves the ORIGINAL principal
maximal ideal under the actual scheme stalk map. The target ideal equality
is derived, never supplied as a parameter/base-change certificate. -/
theorem actualUnramifiedStalk_parameter198
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f] (x : X) (t : Y.presheaf.stalk (f x))
    (hspan : maximalIdeal (Y.presheaf.stalk (f x)) =
      Ideal.span ({t} : Set (Y.presheaf.stalk (f x)))) :
    maximalIdeal (X.presheaf.stalk x) =
      Ideal.span ({(f.stalkMap x).hom t} : Set (X.presheaf.stalk x)) := by
  algebraize [(f.stalkMap x).hom]
  haveI : IsLocalHom
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  haveI : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  haveI : Algebra.FormallyUnramified
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  have h := Algebra.FormallyUnramified.map_maximalIdeal
    (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x)
  rw [RingHom.algebraMap_toAlgebra, hspan, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

/-- The SAME actual field-base-change projection is étale, derived solely
from the finite separable residue extension. No étale projection input. -/
theorem actualFiniteSeparableBaseChangeProjection_etale198
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) :
    Etale (cubicPointTraceFieldBaseChangeProjection K L p) := by
  letI : Module.FinitePresentation K L := Module.finitePresentation_of_finite K L
  letI : Algebra.Etale K L := {
    formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
    finitePresentation := Algebra.FinitePresentation.of_finitePresentation K L }
  letI : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  change Etale (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))))
  infer_instance

/-- At EVERY actual residue-extension point, including the constructed
rational diagonal point, the SAME mapped original parameter generates the
actual maximal ideal. No diagonal decomposition or target frame is assumed. -/
theorem actualFiniteSeparableBaseChangeStalk_parameter198
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (x : schemeBaseChangeToField (L := L) X p)
    (t : X.presheaf.stalk (cubicPointTraceFieldBaseChangeProjection K L p x))
    (hspan : maximalIdeal
      (X.presheaf.stalk (cubicPointTraceFieldBaseChangeProjection K L p x)) =
      Ideal.span ({t} : Set
        (X.presheaf.stalk (cubicPointTraceFieldBaseChangeProjection K L p x)))) :
    maximalIdeal ((schemeBaseChangeToField (L := L) X p).presheaf.stalk x) =
      Ideal.span ({((cubicPointTraceFieldBaseChangeProjection K L p).stalkMap x).hom t} :
        Set ((schemeBaseChangeToField (L := L) X p).presheaf.stalk x)) := by
  letI : Etale (cubicPointTraceFieldBaseChangeProjection K L p) :=
    actualFiniteSeparableBaseChangeProjection_etale198 K L p
  exact actualUnramifiedStalk_parameter198
    (cubicPointTraceFieldBaseChangeProjection K L p) x t hspan

end PfaffianDescent
