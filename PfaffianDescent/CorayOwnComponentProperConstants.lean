import PfaffianDescent.CorayHomogeneousPrimeComponentGeometry
import PfaffianDescent.CorayGeometricallyIntegralNormalizationConstants
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.LinearAlgebra.Dimension.Free

/-! SOURCE ONLY / UNVERIFIED. Properness derives the actual OWN integral
component's finite field of global functions. Its actual point map gives
the original-K constant-field tower, not a stabilizer-field or normalization
constant-field embedding. No H0 finiteness or degree-divisibility premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem integralProper_originalGlobalRing_finite
    {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] :
    letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
    Module.Finite K Γ(X, ⊤) := by
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  have hf : (affineFunctionHom pi).Finite := by
    apply RingHom.finite_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv)
    exact finite_appTop_of_universallyClosed K pi
  have heq : schemeOpenBaseRingHom pi ⊤ = affineFunctionHom pi := by
    ext c
    exact schemeOpenBaseRingHom_top_apply pi c
  change (schemeOpenBaseRingHom pi ⊤).Finite
  rw [heq]
  exact hf

/-- Native properness supplies a field of global functions and finite OWN
unit sections for the SAME original structural map. The finite dimension
is derived, including for a singular integral curve. -/
theorem integralProper_originalGlobalFunctions_field_and_unitSectionsFinite
    {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] :
    IsField Γ(X, ⊤) ∧
      Module.Finite K (SchemeModuleOpenSectionsOver pi
        (SheafOfModules.unit X.ringCatSheaf) ⊤) := by
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI : Module.Finite K Γ(X, ⊤) := integralProper_originalGlobalRing_finite pi
  refine ⟨isField_of_universallyClosed K pi, ?_⟩
  exact Module.Finite.equiv (schemeModuleUnitTopOriginalRingLinearEquiv pi).symm

private def originalGlobalFunctionsToPointAlgHom
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (x : X) :
    letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
    letI := pointAlgebra pi x
    Γ(X, ⊤) →ₐ[K] X.residueField x := by
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI := pointAlgebra pi x
  let a : CommRingCat.of K ⟶ X.residueField x :=
    Spec.preimage (X.fromSpecResidueField x ≫ pi)
  let t := X.fromSpecResidueField x
  let F := X.residueField x
  have hbase : t ≫ pi = Spec.map a := (Spec.map_preimage _).symm
  refine
    { toRingHom := (t.appTop ≫ (Scheme.ΓSpecIso F).hom).hom
      commutes' := ?_ }
  intro c
  change (Scheme.ΓSpecIso F).hom
    (t.appTop (schemeOpenBaseRingHom pi ⊤ c)) = a.hom c
  rw [schemeOpenBaseRingHom_top_apply]
  have ht : t.appTop (affineFunctionHom pi c) =
      affineFunctionHom (Spec.map a) c := by
    change (t.appTop.hom.comp (affineFunctionHom pi)) c = _
    rw [← affineFunctionHom_comp, hbase]
  rw [ht]
  have hv := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality a) c
  change (Scheme.ΓSpecIso F).inv (a.hom c) =
    affineFunctionHom (Spec.map a) c at hv
  rw [← hv]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso F).inv_hom_id (a.hom c)

/-- The actual global-functions field maps into the actual point residue
field through fromSpecResidueField. Its original-K tower derives division
of the FULL original residue degree by OWN unit H0 rank. This holds without
regularity at the point; it makes no normalization-constant assertion. -/
theorem integralProper_originalUnitSections_finrank_dvd_residueDegree
    {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] (P : closedPoints X) :
    Module.finrank K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) ∣ pi.residueDegree P.1 := by
  let A := Γ(X, ⊤)
  let L := X.residueField P.1
  letI : Algebra K A := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI : Field A := (isField_of_universallyClosed K pi).toField
  letI : Algebra K L := pointAlgebra pi P.1
  let i : A →ₐ[K] L := originalGlobalFunctionsToPointAlgHom pi P.1
  letI : Algebra A L := i.toRingHom.toAlgebra
  letI : IsScalarTower K A L :=
    IsScalarTower.of_algebraMap_eq (fun c => (i.commutes c).symm)
  have hdiv : Module.finrank K A ∣ Module.finrank K L :=
    Module.finrank_dvd_finrank_right K A L
  have hunit : Module.finrank K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) = Module.finrank K A :=
    (schemeModuleUnitTopOriginalRingLinearEquiv pi).finrank_eq
  have hpoint : Module.finrank K L = pi.residueDegree P.1 :=
    closedPoint_finrank_eq_residueDegree pi P
  exact hunit.symm ▸ (hpoint ▸ hdiv)

/-- An actual original coprime closed point constructs an actual integral
minimal component through that SAME point. Native properness derives the
OWN finite H0 field and its actual residue tower derives the coprime H0
rank. The point's immersion, residue isomorphism and original degree are
retained. The selected-curve endpoint supplies I/Q directly. -/
theorem homogeneousProjective_originalCoprimePoint_exists_minimalComponent_finiteConstants
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (P : closedPoints (scheme I))
    (hPcop : Nat.Coprime ((toBase I).residueDegree P.1) 3) :
    ∃ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hIC : I.toIdeal ≤ C.toIdeal),
      C.toIdeal ∈ I.toIdeal.minimalPrimes ∧ C.toIdeal.IsPrime ∧
      IsIntegral (scheme C) ∧
      ∃ Q : closedPoints (scheme C),
        schemeQuotientMap I C hIC Q.1 = P.1 ∧
        IsIso ((schemeQuotientMap I C hIC).residueFieldMap Q.1) ∧
        (toBase C).residueDegree Q.1 = (toBase I).residueDegree P.1 ∧
        IsField Γ(scheme C, ⊤) ∧
        Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
          (SheafOfModules.unit (scheme C).ringCatSheaf) ⊤) ∧
        Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
          (SheafOfModules.unit (scheme C).ringCatSheaf) ⊤) ∣
            (toBase I).residueDegree P.1 ∧
        Nat.Coprime (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
          (SheafOfModules.unit (scheme C).ringCatSheaf) ⊤)) 3 := by
  obtain ⟨C, hIC, hCmin, hCprime, hCint, Q, hpoint, hresidue, hdegree⟩ :=
    homogeneousProjective_originalClosedPoint_exists_integralMinimalComponent I P
  letI : IsIntegral (scheme C) := hCint
  letI : IsProper (toBase C) := isProper_toBase C
  obtain ⟨hfield, hfinite⟩ :=
    integralProper_originalGlobalFunctions_field_and_unitSectionsFinite (toBase C)
  have hdiv : Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
      (SheafOfModules.unit (scheme C).ringCatSheaf) ⊤) ∣
        (toBase I).residueDegree P.1 := by
    rw [← hdegree]
    exact integralProper_originalUnitSections_finrank_dvd_residueDegree (toBase C) Q
  exact ⟨C, hIC, hCmin, hCprime, hCint, Q, hpoint, hresidue, hdegree,
    hfield, hfinite, hdiv, hPcop.coprime_dvd_left hdiv⟩

end PfaffianDescent.Coray
