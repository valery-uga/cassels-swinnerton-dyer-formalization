import AllCharacteristics.AffineSchemeActionQuotient
import AllCharacteristics.InvariantRationalPointResidue

/-!
# Residue extensions over rational affine-scheme quotient points

This file states the rational-section residue theorem directly for an affine
scheme carrying a finite group action.  It hides the induced action and
algebra structures on global sections, so it can be applied to the affine
common-open charts of the projective tuple quotient.
-/

open AlgebraicGeometry CategoryTheory
open scoped Pointwise

namespace AllCharacteristics

universe u v

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [IsAffine X]
variable (G : Type v) [Finite G] [Group G]
variable (rho : G → (X ⟶ X)) (hOne : rho 1 = 𝟙 X)
variable (hMul : ∀ g h : G, rho (g * h) = rho g ≫ rho h)
variable (f : X ⟶ Spec (.of K))
variable (hf : ∀ g : G, rho g ≫ f = f)

/-- The quotient prime beneath a prime of an affine scheme, for the action
induced on global sections. -/
noncomputable abbrev affineSchemeSectionQuotientPrime
    (q : PrimeSpectrum Γ(X, ⊤)) :=
  letI := schemeGlobalSectionAction G rho hOne hMul
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G rho hOne hMul f hf
  invariantQuotientPrime Γ(Spec (.of K), ⊤) Γ(X, ⊤) G q

/-- The ground-field algebra structure on the upstairs residue field above a
rational section of an affine scheme quotient. -/
@[instance_reducible]
noncomputable def affineSchemeSectionPointResidueAlgebra
    (c : Spec (.of K) ⟶
      affineSchemeActionQuotient G rho hOne hMul f hf)
    (hc : c ≫ affineSchemeActionQuotientToBase
      G rho hOne hMul f hf = 𝟙 _)
    (q : PrimeSpectrum Γ(X, ⊤))
    (hq : affineSchemeSectionQuotientPrime G rho hOne hMul f hf q =
      c (IsLocalRing.closedPoint K)) :
    Algebra K q.asIdeal.ResidueField := by
  letI := schemeGlobalSectionAction G rho hOne hMul
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G rho hOne hMul f hf
  exact invariantSectionPointResidueAlgebra
    Γ(Spec (.of K), ⊤) Γ(X, ⊤) G
      (affineSchemeActionQuotientToBase G rho hOne hMul f hf)
      c hc q hq

/-- In characteristic zero, the upstairs residue field is finite over the
ground field. -/
theorem affineSchemeSectionPointResidue_moduleFinite
    [CharZero K]
    (c : Spec (.of K) ⟶
      affineSchemeActionQuotient G rho hOne hMul f hf)
    (hc : c ≫ affineSchemeActionQuotientToBase
      G rho hOne hMul f hf = 𝟙 _)
    (q : PrimeSpectrum Γ(X, ⊤))
    (hq : affineSchemeSectionQuotientPrime G rho hOne hMul f hf q =
      c (IsLocalRing.closedPoint K)) :
    @Module.Finite K q.asIdeal.ResidueField _ _
      (affineSchemeSectionPointResidueAlgebra
        G rho hOne hMul f hf c hc q hq).toModule := by
  letI := schemeGlobalSectionAction G rho hOne hMul
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G rho hOne hMul f hf
  exact invariantSectionPointResidue_moduleFinite
    Γ(Spec (.of K), ⊤) Γ(X, ⊤) G
      (affineSchemeActionQuotientToBase G rho hOne hMul f hf)
      c hc q hq

/-- In characteristic zero, the upstairs residue field is Galois over the
ground field. -/
theorem affineSchemeSectionPointResidue_isGalois
    [CharZero K]
    (c : Spec (.of K) ⟶
      affineSchemeActionQuotient G rho hOne hMul f hf)
    (hc : c ≫ affineSchemeActionQuotientToBase
      G rho hOne hMul f hf = 𝟙 _)
    (q : PrimeSpectrum Γ(X, ⊤))
    (hq : affineSchemeSectionQuotientPrime G rho hOne hMul f hf q =
      c (IsLocalRing.closedPoint K)) :
    @IsGalois K _ q.asIdeal.ResidueField _
      (affineSchemeSectionPointResidueAlgebra
        G rho hOne hMul f hf c hc q hq) := by
  letI := schemeGlobalSectionAction G rho hOne hMul
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G rho hOne hMul f hf
  exact invariantSectionPointResidue_isGalois
    Γ(Spec (.of K), ⊤) Γ(X, ⊤) G
      (affineSchemeActionQuotientToBase G rho hOne hMul f hf)
      c hc q hq

end AllCharacteristics
