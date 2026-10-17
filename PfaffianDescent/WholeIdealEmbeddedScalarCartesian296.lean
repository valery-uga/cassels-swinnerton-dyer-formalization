import PfaffianDescent.TensorEquivalenceNativeCartesian296
import PfaffianDescent.PolynomialWholeIdealScalarExtension286
import PfaffianDescent.MonomialWholeIdealChartOverlap290
import PfaffianDescent.NativeAffineUniversalWholeFamily289
import AllCharacteristics.ResidueSpecialFiber

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {C S : Type u} [CommRing C] [CommRing S] [Algebra C S] {m : ℕ}
variable (I : Ideal (MvPolynomial (Fin m) C))

/-- The canonical map of entire quotient rings from the proved tensor/quotient equivalence. -/
def wholeIdealScalarQuotientRingMap296 :
    (MvPolynomial (Fin m) C ⧸ I) →+*
      (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map (algebraMap C S))) :=
  tensorEquivalenceRightRingMap296 (polynomialWholeIdealScalarExtension286 S I)

lemma wholeIdealScalarQuotientRingMap_mk296 (p : MvPolynomial (Fin m) C) :
    wholeIdealScalarQuotientRingMap296 (S := S) I (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap C S)))
        (MvPolynomial.map (algebraMap C S) p) := by
  change polynomialWholeIdealScalarExtension286 S I (1 ⊗ₜ[C] Ideal.Quotient.mk I p) = _
  simpa only [one_smul] using polynomialWholeIdealScalarExtension_tmul286 S I 1 p

lemma wholeIdealScalarQuotientRingMap_eq_nativeQuotientMap296 :
    wholeIdealScalarQuotientRingMap296 (S := S) I =
      Ideal.quotientMap (I.map (MvPolynomial.map (algebraMap C S)))
        (MvPolynomial.map (algebraMap C S)) Ideal.le_comap_map := by
  apply RingHom.ext
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [wholeIdealScalarQuotientRingMap_mk296, Ideal.quotientMap_mk]

lemma wholeIdealScalarQuotient_isCartesian296 :
    IsPullback (Spec.map (CommRingCat.ofHom (wholeIdealScalarQuotientRingMap296 (S := S) I)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map (algebraMap C S))))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (MvPolynomial (Fin m) C ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap C S))) :=
  tensorEquivalenceNativeSpecCartesian296 (polynomialWholeIdealScalarExtension286 S I)

lemma ambientPolynomialScalar_isCartesian296 :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap C S))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (MvPolynomial (Fin m) S))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (MvPolynomial (Fin m) C))))
      (Spec.map (CommRingCat.ofHom (algebraMap C S))) := by
  have hm : tensorEquivalenceRightRingMap296
      (MvPolynomial.algebraTensorAlgEquiv C S :
        S ⊗[C] MvPolynomial (Fin m) C ≃ₐ[S] MvPolynomial (Fin m) S) =
      MvPolynomial.map (σ := Fin m) (algebraMap C S) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.algebraTensorAlgEquiv C S (1 ⊗ₜ[C] p) = _
    simpa only [one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul C S 1 p
  exact hm ▸ tensorEquivalenceNativeSpecCartesian296
    (MvPolynomial.algebraTensorAlgEquiv C S : S ⊗[C] MvPolynomial (Fin m) C ≃ₐ[S] MvPolynomial (Fin m) S)

/-- The two quotient embeddings themselves form a Cartesian square over the native ambient map. -/
lemma wholeIdealEmbeddedScalar_isCartesian296 :
    IsPullback (Spec.map (CommRingCat.ofHom (wholeIdealScalarQuotientRingMap296 (S := S) I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap C S))))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap C S)))) := by
  have hc : (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap C S)))).comp
      (MvPolynomial.map (algebraMap C S)) =
      (wholeIdealScalarQuotientRingMap296 (S := S) I).comp (Ideal.Quotient.mk I) := by
    apply RingHom.ext
    intro p
    exact (wholeIdealScalarQuotientRingMap_mk296 (S := S) I p).symm
  have hk : RingHom.ker (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap C S)))) =
      (RingHom.ker (Ideal.Quotient.mk I)).map (MvPolynomial.map (algebraMap C S)) := by
    rw [Ideal.mk_ker, Ideal.mk_ker]
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (AllCharacteristics.isPushout_of_surjective_of_ker_map
      (MvPolynomial.map (algebraMap C S)) (Ideal.Quotient.mk I)
      (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap C S))))
      (wholeIdealScalarQuotientRingMap296 (S := S) I)
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective hc hk)).flip

/-- The literal original ideal sheaf pulls back to the literal extended ideal's embedding kernel. -/
lemma wholeIdealEmbeddedScalar_kernel_comap296 :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
        (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap C S)))) =
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap C S)))))).ker := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective
  exact wholeIdeal_comap_eq_of_isPullback195
    (Spec.map (CommRingCat.ofHom (wholeIdealScalarQuotientRingMap296 (S := S) I)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap C S))))))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap C S))))
    (wholeIdealEmbeddedScalar_isCartesian296 (S := S) I)

/-- Actual finite-flat Hilbert point base change equals the point of the same extended whole quotient. -/
lemma affineWholeQuotientHilbertPoint_baseChange296 {n : ℕ}
    (b : Module.Basis (Fin n) C (MvPolynomial (Fin m) C ⧸ I)) :
    finiteFlatHilbertBaseChange195
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap C S))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (MvPolynomial (Fin m) S))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (MvPolynomial (Fin m) C))))
      (Spec.map (CommRingCat.ofHom (algebraMap C S)))
      (ambientPolynomialScalar_isCartesian296 (C := C) (S := S) (m := m)) n
      (affineWholeQuotientHilbertPoint289 I b) =
    affineWholeQuotientHilbertPoint289
      (I.map (MvPolynomial.map (algebraMap C S))) (wholeIdealScalarBasis290 S I b) := by
  apply Subtype.ext
  exact wholeIdealEmbeddedScalar_kernel_comap296 (S := S) I

end PfaffianDescent
