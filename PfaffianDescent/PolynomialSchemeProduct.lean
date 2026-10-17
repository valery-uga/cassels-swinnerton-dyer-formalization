import PfaffianDescent.PolynomialSumPushout

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] (ι σ : Type)

/-- Affine spaces with disjoint coordinate sets form the actual product over the coefficient base. -/
lemma polynomialSum_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) (Sum.inl : ι → ι ⊕ σ)).toRingHom))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) (Sum.inr : σ → ι ⊕ σ)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (polynomialSum_isPushout K ι σ)

noncomputable def polynomialSumProductIso : Spec (.of (MvPolynomial (ι ⊕ σ) K)) ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K)))) :=
  (polynomialSum_isPullback K ι σ).isoPullback

end
end PfaffianDescent
