import PfaffianDescent.CorayPerfectFiniteTypeNormalization
import PfaffianDescent.CorayFiniteSchemeGenericNormalization

/-! SOURCE ONLY / UNVERIFIED. PerfectField K native generic normalization
is finite using internally derived canonical chart closure finiteness.
SAME generic-point map/normalization, actual original chart coefficient
map and literal fraction/section equivalences; no finite glue certificate.
Source092 is PENDING until root accepts it. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u

/-- Actual generic normalization over ORIGINAL perfect K is finite, derived
from the actual original affine chart maps and native relative normalization.
No CharZero, separability or normalization-finiteness premise. -/
theorem perfectField_integralScheme_genericNormalization_isFinite
    {K : Type u} [Field K] [PerfectField K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hnonempty : Nonempty U
  · letI : Nonempty U := hnonempty
    let beta : K →+* Γ(X, U) :=
      (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    letI : Algebra K Γ(X, U) := beta.toAlgebra
    have hbeta : beta.FiniteType := RingHom.FiniteType.comp
      (pi.finiteType_appLE (isAffineOpen_top _) hU (by simp))
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
    letI : Algebra.FiniteType K Γ(X, U) := hbeta
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : Module.Finite Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U))) :=
      finiteNormalization_of_finiteType_perfectField K Γ(X, U)
    let fracEquiv := FractionRing.algEquiv (A := Γ(X, U)) X.functionField
    letI : Module.Finite Γ(X, U) (integralClosure Γ(X, U) X.functionField) :=
      Module.Finite.equiv fracEquiv.mapIntegralClosure.toLinearEquiv
    letI : Algebra Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    let sectionEquiv : Γ(Spec X.functionField, f ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField :=
      AlgEquiv.ofBijective
        { toRingHom := (integralGenericPointPreimageSectionsIso X U).hom.hom
          commutes' := fun r => by
            exact ConcreteCategory.congr_hom (integralGenericPointPreimageSectionsIso_comp_app X U) r }
        (ConcreteCategory.bijective_of_isIso (integralGenericPointPreimageSectionsIso X U).hom)
    letI : Module.Finite Γ(X, U)
        (integralClosure Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U)) :=
      Module.Finite.equiv sectionEquiv.symm.mapIntegralClosure.toLinearEquiv
    rw [Scheme.Hom.fromNormalization_app f hU, CommRingCat.hom_comp]
    exact RingHom.Finite.comp
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
      (RingHom.finite_algebraMap.mpr inferInstance)
  · have hpreempty : f.fromNormalization ⁻¹ᵁ U = ⊥ := by
      ext y
      change f.fromNormalization y ∈ U ↔ False
      exact iff_false_intro (fun hy => hnonempty ⟨⟨f.fromNormalization y, hy⟩⟩)
    haveI : Subsingleton Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) := by
      rw [hpreempty]
      infer_instance
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)


end PfaffianDescent.Coray
