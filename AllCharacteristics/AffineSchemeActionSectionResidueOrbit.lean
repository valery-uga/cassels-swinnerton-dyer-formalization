import AllCharacteristics.AffineSchemeActionResidueOrbit
import AllCharacteristics.AffineSchemeActionSectionResidue

/-!
# Galois orbits above rational affine quotient points

The invariant-ring residue theorem first describes automorphisms over the
residue field of the quotient prime.  A rational section identifies that
base field with the original field.  This file transports an automorphism
over the original field back across that identification and applies the
affine scheme orbit theorem.
-/

open AlgebraicGeometry CategoryTheory
open scoped Pointwise

namespace AllCharacteristics

universe u v

variable {K : Type u} [Field K] [CharZero K]
variable {X : Scheme.{u}} [IsAffine X]
variable (G : Type v) [Finite G] [Group G]
variable (rho : G → (X ⟶ X)) (hOne : rho 1 = 𝟙 X)
variable (hMul : ∀ g h : G, rho (g * h) = rho g ≫ rho h)
variable (f : X ⟶ Spec (.of K))
variable (hf : ∀ g : G, rho g ≫ f = f)

/-- The canonical residue point above a rational quotient section is a point
over the original ground field for the transported residue-field algebra. -/
theorem affineSchemeSectionPointResidue_toBase
    (c : Spec (.of K) ⟶
      affineSchemeActionQuotient G rho hOne hMul f hf)
    (hc : c ≫ affineSchemeActionQuotientToBase
      G rho hOne hMul f hf = 𝟙 _)
    (q : PrimeSpectrum Γ(X, ⊤))
    (hq : affineSchemeSectionQuotientPrime G rho hOne hMul f hf q =
      c (IsLocalRing.closedPoint K)) :
    letI := affineSchemeSectionPointResidueAlgebra
      G rho hOne hMul f hf c hc q hq
    Spec.map (CommRingCat.ofHom
        (algebraMap K q.asIdeal.ResidueField)) =
      affinePrimeResiduePoint q ≫ f := by
  unfold affineSchemeActionQuotient at c hc hq
  letI := schemeGlobalSectionAction G rho hOne hMul
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G rho hOne hMul f hf
  letI : Algebra K q.asIdeal.ResidueField :=
    affineSchemeSectionPointResidueAlgebra
      G rho hOne hMul f hf c hc q hq
  let m : Spec Γ(X, ⊤) ⟶ Spec (.of K) :=
    affineInvariantQuotientMap Γ(Spec (.of K), ⊤) Γ(X, ⊤) G ≫
      affineSchemeActionQuotientToBase G rho hOne hMul f hf
  have hbase := invariantSectionPointResidue_specMap_toBase
    Γ(Spec (.of K), ⊤) Γ(X, ⊤) G
      (affineSchemeActionQuotientToBase G rho hOne hMul f hf)
      c hc q hq
  change Spec.map (CommRingCat.ofHom
      (algebraMap K q.asIdeal.ResidueField)) =
    Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) q.asIdeal.ResidueField)) ≫ m at hbase
  rw [hbase]
  have hft := affineSchemeActionQuotientMap_toBase
    G rho hOne hMul f hf
  change (X.isoSpec.hom ≫
      affineInvariantQuotientMap Γ(Spec (.of K), ⊤) Γ(X, ⊤) G) ≫
      affineSchemeActionQuotientToBase G rho hOne hMul f hf = f at hft
  have hft' : X.isoSpec.hom ≫ m = f := by
    change X.isoSpec.hom ≫
      (affineInvariantQuotientMap Γ(Spec (.of K), ⊤) Γ(X, ⊤) G ≫
        affineSchemeActionQuotientToBase G rho hOne hMul f hf) = f
    exact (Category.assoc X.isoSpec.hom
      (affineInvariantQuotientMap Γ(Spec (.of K), ⊤) Γ(X, ⊤) G)
      (affineSchemeActionQuotientToBase G rho hOne hMul f hf)).symm.trans hft
  unfold affinePrimeResiduePoint
  calc
    Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, ⊤) q.asIdeal.ResidueField)) ≫ m =
      (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, ⊤) q.asIdeal.ResidueField)) ≫
        X.isoSpec.inv) ≫ (X.isoSpec.hom ≫ m) := by
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, ⊤) q.asIdeal.ResidueField)) ≫
        X.isoSpec.inv) ≫ f := congrArg _ hft'

/-- Every ground-field automorphism of the canonical residue extension above
a rational quotient point acts on the canonical residue point through an
element of the original finite group. -/
theorem affineSchemeSectionPointResidue_galoisOrbit
    (c : Spec (.of K) ⟶
      affineSchemeActionQuotient G rho hOne hMul f hf)
    (hc : c ≫ affineSchemeActionQuotientToBase
      G rho hOne hMul f hf = 𝟙 _)
    (q : PrimeSpectrum Γ(X, ⊤))
    (hq : affineSchemeSectionQuotientPrime G rho hOne hMul f hf q =
      c (IsLocalRing.closedPoint K))
    (g : @AlgEquiv K q.asIdeal.ResidueField q.asIdeal.ResidueField _ _ _
      (affineSchemeSectionPointResidueAlgebra
        G rho hOne hMul f hf c hc q hq)
      (affineSchemeSectionPointResidueAlgebra
        G rho hOne hMul f hf c hc q hq)) :
    ∃ s : affineSchemePrimeStabilizer G rho hOne hMul q,
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          affinePrimeResiduePoint q =
        affinePrimeResiduePoint q ≫ rho s.val := by
  letI := schemeGlobalSectionAction G rho hOne hMul
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G rho hOne hMul f hf
  letI : Algebra K q.asIdeal.ResidueField :=
    affineSchemeSectionPointResidueAlgebra
      G rho hOne hMul f hf c hc q hq
  let p := invariantQuotientPrime Γ(Spec (.of K), ⊤) Γ(X, ⊤) G q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra Γ(Spec (.of K), ⊤) Γ(X, ⊤) G)
        Γ(X, ⊤)) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  let e : p.asIdeal.ResidueField ≃+* K :=
    invariantSectionPointResidueBaseIso
      Γ(Spec (.of K), ⊤) Γ(X, ⊤) G
      (affineSchemeActionQuotientToBase G rho hOne hMul f hf)
      c hc q hq
  let g' : q.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField]
      q.asIdeal.ResidueField :=
    algEquivOfBaseRingEquiv p.asIdeal.ResidueField K
      q.asIdeal.ResidueField e g
  obtain ⟨s, hs⟩ := affineSchemePrimeResidue_galoisOrbit
    G rho hOne hMul f hf q g'
  refine ⟨s, ?_⟩
  change Spec.map (CommRingCat.ofHom g'.toRingHom) ≫
      affinePrimeResiduePoint q =
    affinePrimeResiduePoint q ≫ rho s.val at hs
  have hg : g'.toRingEquiv = g.toRingEquiv := by rfl
  rw [hg] at hs
  exact hs

end AllCharacteristics
