import AllCharacteristics.KollarGenericTargetCone
import AllCharacteristics.PolynomialFieldExtensionIdealContraction

/-! Relations of the actual generic target descend from
the larger algebraically closed coefficient field to the original field. -/

noncomputable section
namespace AllCharacteristics
open MvPolynomial
universe u

theorem cubicGenericTarget_original_relation_detection
    {k K : Type u} [Field k] [Field K] (f : k →+* K)
    (F : MvPolynomial (Fin 4) k)
    [(Ideal.span ({F.map f} : Set (MvPolynomial (Fin 4) K))).IsPrime]
    (G : MvPolynomial (Fin 4) k)
    (hzero : G.eval₂ ((cubicGenericTargetCoefficientMap (F.map f)).comp f)
      (cubicGenericTargetCoordinates (F.map f)) = 0) :
    G ∈ Ideal.span ({F} : Set (MvPolynomial (Fin 4) k)) := by
  have hmapzero : (G.map f).eval₂ (cubicGenericTargetCoefficientMap (F.map f))
      (cubicGenericTargetCoordinates (F.map f)) = 0 := by
    rw [MvPolynomial.eval₂_map]
    exact hzero
  have hmem := (cubicGenericTarget_relation_iff (F.map f) (G.map f)).mp hmapzero
  exact polynomial_mem_principal_of_map_mem_field_extension f F G hmem

end AllCharacteristics
