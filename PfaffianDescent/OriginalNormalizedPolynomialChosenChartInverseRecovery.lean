import PfaffianDescent.OriginalNormalizedPolynomialGlobalHilbertChartIso

/-! Exact inverse classifier recovery in the ORIGINAL coordinate chart.
The literal317 classifier and both actual whole-family transports are retained.
No support/reduction substitution or classifier outcome is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u v w
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem normalizedOriginalYonedaClassifier_inverse001
    {C : Type v} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type w} {H J : C}
    (eta : F ≅ yoneda.obj H) (comparison : F ≅ G) (theta : G ≅ yoneda.obj J)
    (T : C) (c : T ⟶ H) :
    theta.inv.app (.op T)
        (c ≫ (Yoneda.fullyFaithful.preimageIso (eta.symm ≪≫ comparison ≪≫ theta)).hom) =
      comparison.hom.app (.op T) (eta.inv.app (.op T) c) := by
  have hComponent :
      (yoneda.map (Yoneda.fullyFaithful.preimageIso
        (eta.symm ≪≫ comparison ≪≫ theta)).hom).app (.op T) =
      (eta.symm ≪≫ comparison ≪≫ theta).hom.app (.op T) :=
    congrArg (fun alpha => alpha.app (.op T))
      (Yoneda.fullyFaithful.map_preimage (eta.symm ≪≫ comparison ≪≫ theta).hom)
  have hAction := ConcreteCategory.congr_hom (C := Type w) hComponent c
  change c ≫ (Yoneda.fullyFaithful.preimageIso (eta.symm ≪≫ comparison ≪≫ theta)).hom =
    theta.hom.app (.op T) (comparison.hom.app (.op T) (eta.inv.app (.op T) c)) at hAction
  have hCancel : theta.inv.app (.op T)
      (theta.hom.app (.op T) (comparison.hom.app (.op T) (eta.inv.app (.op T) c))) =
        comparison.hom.app (.op T) (eta.inv.app (.op T) c) := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (theta.hom_inv_id_app (.op T))
        (comparison.hom.app (.op T) (eta.inv.app (.op T) c))
  exact (congrArg (fun x => theta.inv.app (.op T) x) hAction).trans hCancel

private theorem normalizedOriginalYonedaClassifier_physicalRecovery001
    {C : Type v} [Category.{w} C] {F G : Cᵒᵖ ⥤ Type w} {H J : C}
    (eta : F ≅ yoneda.obj H) (comparison : F ≅ G) (theta : G ≅ yoneda.obj J)
    (T : C) {P : Type*} (E : P ≃ F.obj (.op T)) (Q : P) :
    E.symm (comparison.inv.app (.op T) (theta.inv.app (.op T)
      (eta.hom.app (.op T) (E Q) ≫
        (Yoneda.fullyFaithful.preimageIso (eta.symm ≪≫ comparison ≪≫ theta)).hom))) = Q := by
  have h := normalizedOriginalYonedaClassifier_inverse001 eta comparison theta T
    (eta.hom.app (.op T) (E Q))
  have hEta : eta.inv.app (.op T) (eta.hom.app (.op T) (E Q)) = E Q := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (eta.hom_inv_id_app (.op T)) (E Q)
  have hComparison : comparison.inv.app (.op T) (comparison.hom.app (.op T) (E Q)) = E Q := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (comparison.hom_inv_id_app (.op T)) (E Q)
  rw [hEta] at h
  exact (congrArg (fun x => E.symm (comparison.inv.app (.op T) x)) h).trans
    ((congrArg E.symm hComparison).trans (E.symm_apply_apply Q))

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d)
variable (j : Fin 4) (n : ℕ) (hn : 0 < n)

/-- Inverse of the SAME chosen chart classifier recovers the actual transported
whole polynomial family of ANY original-base classifier map. -/
theorem originalNormalizedPolynomialChosenChart_inverseClassifier001
    (T : Over (Spec (.of R)))
    (c : T ⟶ monomialPolynomialContainmentRepresentingObject312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j)) :
    (originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal p hp) n hn
        (originalNormalizedCoordinateChartIndex001 p hp j)).inv.app (.op T)
      (c ≫ (originalNormalizedPolynomialChosenChartOverIso001 p hp j n hn).hom) =
    (originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n).hom.app (.op T)
      ((polynomialHypersurfaceHilbertRepresentingIso312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) hn).inv.app (.op T) c) := by
  exact normalizedOriginalYonedaClassifier_inverse001
    (polynomialHypersurfaceHilbertRepresentingIso312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) hn)
    (originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal p hp) n hn
      (originalNormalizedCoordinateChartIndex001 p hp j)) T c

/-- Starting with the actual physical317 whole family, its literal317
classifier followed by the actual slice iso recovers EXACTLY that family
through the two constructed inverse native ambient transports. -/
theorem originalNormalizedPolynomialChosenChart_recoversPhysicalPoint001
    (B : Type u) [CommRing B] [Algebra R B]
    (Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 (p.map (algebraMap R B)) j)))) n) :
    (originalNormalizedAffineTestPointEquiv317 R p hp j B n).symm
      ((originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n).inv.app
        (.op (originalNormalizedAffineTest317 R B))
        ((originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal p hp) n hn
            (originalNormalizedCoordinateChartIndex001 p hp j)).inv.app
          (.op (originalNormalizedAffineTest317 R B))
          (originalNormalizedAffineClassifyingMap317 R p hp j B n hn Q ≫
            (originalNormalizedPolynomialChosenChartOverIso001 p hp j n hn).hom))) = Q := by
  exact normalizedOriginalYonedaClassifier_physicalRecovery001
    (polynomialHypersurfaceHilbertRepresentingIso312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) hn)
    (originalNormalizedPolynomialBasicOpenHilbertFunctorIso001 p hp j n)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal p hp) n hn
      (originalNormalizedCoordinateChartIndex001 p hp j))
    (originalNormalizedAffineTest317 R B)
    (originalNormalizedAffineTestPointEquiv317 R p hp j B n) Q

end PfaffianDescent
end
