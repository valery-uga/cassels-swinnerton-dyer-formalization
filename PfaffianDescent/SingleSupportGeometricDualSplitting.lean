import PfaffianDescent.SingleClosedPointFiniteSchemeAlgebra
import PfaffianDescent.QuarticGeometricSplitting

/-! The geometric algebra of the GIVEN rank-eight singleton-support scheme
splits into four dual-number algebras. The actual global algebra is retained;
no constructed replacement scheme or decomposition certificate is assumed. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct
universe u
variable {k K : Type u} [Field k] [PerfectField k] [Field K]
  [IsAlgClosed K] [Algebra k K] {X Z : Scheme.{u}}

/-- Scalar extension of the actual Gamma(Z) is a product of four dual-number
algebras. Locality and its actual residue quotient are derived from the given
closed immersion and support equality. -/
theorem singleClosedSupport_geometric_globalAlgebra_splits
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsFinite (i ≫ f)]
    (P : closedPoints X) (hSupport : Set.range i = {P.1})
    (hP : f.residueDegree P.1 = 4)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = 8) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ f)
    ∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
      Nonempty ((K ⊗[k] Γ(Z, ⊤)) ≃ₐ[K] (J → DualNumber K)) := by
  classical
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  letI := AllCharacteristics.pointAlgebra f P.1
  letI := AllCharacteristics.closedPoint_moduleFinite f P
  obtain ⟨e⟩ := singleClosedSupport_rankEight_dualAlgebra i f P hSupport hP hZ
  have hL : finrank k (X.residueField P.1) = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree f P).trans hP
  obtain ⟨J, hJ, hcard, ⟨eSplit⟩⟩ :=
    QuarticNet.degree_four_dualPoint_splits k K (X.residueField P.1) hL
  letI := hJ
  exact ⟨J, hJ, hcard, ⟨(Algebra.TensorProduct.congr
    (AlgEquiv.refl : K ≃ₐ[K] K) e.symm).trans eSplit⟩⟩

/-- The spectrum of the actual geometric global algebra is the disjoint
union of the four actual length-two factors from the preceding theorem. -/
theorem singleClosedSupport_geometric_globalSpec_splits
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsFinite (i ≫ f)]
    (P : closedPoints X) (hSupport : Set.range i = {P.1})
    (hP : f.residueDegree P.1 = 4)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = 8) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ f)
    ∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
      Nonempty (Spec (.of (K ⊗[k] Γ(Z, ⊤))) ≅
        CategoryTheory.Limits.sigmaObj (fun _ : J => Spec (.of (DualNumber K)))) := by
  classical
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  obtain ⟨J, hJ, hcard, ⟨e⟩⟩ :=
    singleClosedSupport_geometric_globalAlgebra_splits (K := K) i f P hSupport hP hZ
  letI := hJ
  exact ⟨J, hJ, hcard, ⟨Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op ≪≫
    (asIso (sigmaSpec (fun _ : J => CommRingCat.of (DualNumber K)))).symm⟩⟩

end PfaffianDescent
