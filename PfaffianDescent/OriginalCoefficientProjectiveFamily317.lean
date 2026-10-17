import PfaffianDescent.OriginalCoefficientChartTestFamily317
import PfaffianDescent.OriginalNormalizedAffinePointToProjective317

/-! Coefficient algebra tests give actual projective whole families, with
exact reduction law over the original ground ring. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (n : ℕ)
  {B S : Type u} [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
  (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
  (j : Fin 4) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
  (q : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
    (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] B)

def originalCoefficientTestProjectiveFamily317 :
    FiniteFlatHilbertPoint195
      (hypersurfaceToBase (r.map (algebraMap R B)) (hr.map (algebraMap R B))) n :=
  originalNormalizedAffinePointToProjective317 (r.map (algebraMap R B))
    (hr.map (algebraMap R B)) j n
    (originalCoefficientTestPhysicalFamily317 R n r hr j hn i q)

lemma originalCoefficientTestProjectiveFamily_wholeIdeal317 :
    (originalCoefficientTestProjectiveFamily317 R n r hr j hn i q).val =
      (originalCoefficientTestPhysicalFamily317 R n r hr j hn i q).val.map
        (originalNormalizedHypersurfaceChartEmbedding312
          (r.map (algebraMap R B)) (hr.map (algebraMap R B)) j) :=
  originalNormalizedAffinePointToProjective_wholeIdeal317 (r.map (algebraMap R B))
    (hr.map (algebraMap R B)) j n
    (originalCoefficientTestPhysicalFamily317 R n r hr j hn i q)

lemma originalCoefficientTestProjectiveFamily_range317 :
    Set.range (originalCoefficientTestProjectiveFamily317 R n r hr j hn i q).val.subschemeι ⊆
      Set.range (originalNormalizedHypersurfaceChartEmbedding312
        (r.map (algebraMap R B)) (hr.map (algebraMap R B)) j) :=
  originalNormalizedAffinePointToProjective_range317 (r.map (algebraMap R B))
    (hr.map (algebraMap R B)) j n
    (originalCoefficientTestPhysicalFamily317 R n r hr j hn i q)

lemma originalCoefficientTestProjectiveFamily_reductionWholeIdeal317 (pi : B →ₐ[R] S) :
    (originalCoefficientTestProjectiveFamily317 R n r hr j hn i q).val.comap
      (hypersurfaceReductionMap pi.toRingHom
        (r.map (algebraMap R B)) (hr.map (algebraMap R B))
        (r.map (algebraMap R S)) (hr.map (algebraMap R S))
        (originalNormalizedTestEquation317 R pi r)) =
      (originalCoefficientTestProjectiveFamily317 R n r hr j hn i (pi.comp q)).val := by
  have h := originalNormalizedAffinePointToProjective_reductionWholeIdeal317
    (r.map (algebraMap R B)) (hr.map (algebraMap R B)) j n
    (originalCoefficientTestPhysicalFamily317 R n r hr j hn i q)
    pi.toRingHom (r.map (algebraMap R S)) (hr.map (algebraMap R S))
    (originalNormalizedTestEquation317 R pi r)
  exact h.symm.trans
    (congrArg
      (fun Q => (originalNormalizedAffinePointToProjective317
        (r.map (algebraMap R S)) (hr.map (algebraMap R S)) j n Q).val)
      (originalCoefficientTestPhysicalFamily_natural317 R n r hr j hn i pi q))

end PfaffianDescent
end
