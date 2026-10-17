import PfaffianDescent.MonomialOverlapSchemeTransition298

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u

/-- The SAME monomial quotient basis gives the identity coordinate matrix on the diagonal. -/
lemma monomialWholeIdealChartTransitionDet_self300
    {A : Type u} [CommRing A] {m n : ℕ}
    (B : Fin n → (Fin m →₀ ℕ)) (x : MonomialWholeIdealChart287 (A := A) B) :
    monomialWholeIdealChartTransitionDet290 B B x = 1 := by
  classical
  have hv : (fun j => Ideal.Quotient.mk x.val (MvPolynomial.monomial (B j) 1)) =
      (monomialWholeIdealChartBasis287 B x : Fin n → _) :=
    funext (fun j => (monomialWholeIdealChartBasis_apply287 B x j).symm)
  change ((monomialWholeIdealChartBasis287 B x).toMatrix
    (fun j => Ideal.Quotient.mk x.val (MvPolynomial.monomial (B j) 1))).det = 1
  rw [hv, Basis.toMatrix_self, Matrix.det_one]

variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) (hk : B k = 0)

/-- The diagonal determinant in the ORIGINAL universal coefficient chart is exactly one. -/
lemma universalMonomialOverlapDet_self300 :
    universalMonomialOverlapDet292 R m n B B k hk = 1 :=
  monomialWholeIdealChartTransitionDet_self300 B
    (universalMonomialWholeIdealChart292 R m n B k hk)

/-- Self reversal preserves the actual whole-ideal chart datum exactly. -/
lemma monomialWholeIdealOverlapFlip_self300
    {A : Type u} [CommRing A] (x : MonomialWholeIdealChartOverlap290 (A := A) B B) :
    monomialWholeIdealOverlapFlip293 B B x = x := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The SAME293 original coefficient self transition is identity, derived by classification. -/
lemma monomialOverlapForwardCoefficientMap_self300 :
    monomialOverlapForwardCoefficientMap293 R m n B B k k hk hk =
      AlgHom.id R (MonomialOverlapCoefficientAlgebra292 R m n B B k hk) := by
  apply (monomialOverlapLocalizationAlgHomEquiv292 R m n B B k hk
    (MonomialOverlapCoefficientAlgebra292 R m n B B k hk)).injective
  rw [monomialOverlapForwardCoefficientMap_classifies293,
    monomialWholeIdealOverlapFlip_self300]

/-- The SAME298 actual affine self transition is identity. -/
lemma monomialOverlapAffineSchemeIso_self_hom300 :
    (monomialOverlapAffineSchemeIso298 R m n B B k k hk hk).hom =
      𝟙 (Spec (.of (MonomialOverlapCoefficientAlgebra292 R m n B B k hk))) := by
  rw [monomialOverlapAffineSchemeIso_hom298, monomialOverlapForwardCoefficientMap_self300]
  change Spec.map (𝟙 (CommRingCat.of
    (MonomialOverlapCoefficientAlgebra292 R m n B B k hk))) = _
  exact Spec.map_id _

/-- The SAME298 ORIGINAL determinant-principal-open self transition is identity. -/
lemma monomialOverlapPrincipalSchemeIso_self_hom300 :
    (monomialOverlapPrincipalSchemeIso298 R m n B B k k hk hk).hom =
      𝟙 (monomialOverlapPrincipalScheme298 R m n B B k hk) := by
  rw [monomialOverlapPrincipalSchemeIso_hom298, monomialOverlapAffineSchemeIso_self_hom300]
  simp only [Category.id_comp, Iso.inv_hom_id]

end PfaffianDescent
