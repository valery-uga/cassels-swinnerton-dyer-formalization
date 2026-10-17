import PfaffianDescent.VoisinFlatGradedGrassmannian

/-!
# Equations of every fibre of a flat homogeneous system

The Grassmannian family defined by a flat model consists of actual model
equations after every coefficient extension.  This gives the algebraic
incidence direction needed to relate its projective parameter family to
the corresponding base-changed projective curve.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R S : Type u} [CommRing R] [IsNoetherianRing R]
  [CommRing S] [Algebra R S]
  (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
  [Module.Flat R (CoordinateRing J)]
  (d r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) d)
  (hRank : ∀ p : PrimeSpectrum R,
    Module.rankAtStalk (grading J d) p = q)

/-- After any coefficient extension, the Grassmannian equation space is
exactly the span of the coefficient extensions of the model's degree-`d`
equations.  This is an equality of actual submodules, with no flatness
assumption on the new coefficient ring. -/
theorem flatGradedGrassmannian_baseChange_equationSpan :
    (grassmannianSubmoduleBaseChange (algebraMap R S)
      (flatGradedGrassmannian J d r q e hRank).toSubmodule).map
        (grassmannianChartHomogeneousCoordinateEquiv (R := S) d e).toLinearMap =
      Submodule.span S
        (homogeneousSubmoduleBaseChange d (algebraMap R S) ''
          (homogeneousModelIdealPiece J d :
            Set (homogeneousSubmodule (Fin 4) R d))) := by
  let ER := grassmannianChartHomogeneousCoordinateEquiv (R := R) d e
  let ES := grassmannianChartHomogeneousCoordinateEquiv (R := S) d e
  let W := flatGradedGrassmannian J d r q e hRank
  have hW : W.toSubmodule =
      (homogeneousModelIdealPiece J d).comap ER.toLinearMap :=
    flatGradedGrassmannian_toSubmodule J d r q e hRank
  rw [grassmannianSubmoduleBaseChange, Submodule.map_span]
  change Submodule.span S
    (ES '' (graphCoefficientMap (algebraMap R S) ''
      (W.toSubmodule : Set ((Fin r → R) × (Fin q → R))))) = _
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hwJ : ER w ∈ homogeneousModelIdealPiece J d := by
      rw [hW] at hw
      exact hw
    refine ⟨ER w, hwJ, ?_⟩
    exact grassmannianChartHomogeneousCoordinateEquiv_baseChange
      (R := R) d (algebraMap R S) e w
  · rintro ⟨v, hv, rfl⟩
    let w := ER.symm v
    have hw : w ∈ W.toSubmodule := by
      rw [hW]
      change ER w ∈ (homogeneousModelIdealPiece J d :
        Set (homogeneousSubmodule (Fin 4) R d))
      simpa only [w, ER.apply_symm_apply] using hv
    refine ⟨graphCoefficientMap (algebraMap R S) w,
      ⟨w, hw, rfl⟩, ?_⟩
    rw [← grassmannianChartHomogeneousCoordinateEquiv_baseChange
      (R := R) d (algebraMap R S) e w]
    exact congrArg (homogeneousSubmoduleBaseChange d (algebraMap R S))
      (ER.apply_symm_apply v)

/-- Membership in the specialized Grassmannian system is equivalent to
being a linear combination of the specialized model equations. -/
theorem flatGradedGrassmannian_baseChange_mem_iff_equationSpan
    (v : homogeneousSubmodule (Fin 4) S d) :
    (grassmannianChartHomogeneousCoordinateEquiv (R := S) d e).symm v ∈
      grassmannianSubmoduleBaseChange (algebraMap R S)
        (flatGradedGrassmannian J d r q e hRank).toSubmodule ↔
      v ∈ Submodule.span S
        (homogeneousSubmoduleBaseChange d (algebraMap R S) ''
          (homogeneousModelIdealPiece J d :
            Set (homogeneousSubmodule (Fin 4) R d))) := by
  rw [← flatGradedGrassmannian_baseChange_equationSpan J d r q e hRank]
  rw [Submodule.mem_map_equiv]

/-- Every vector in the base-changed flat Grassmannian system gives a
homogeneous polynomial belonging to the coefficient extension of the
model's ideal.  No flatness assumption on the new coefficient ring is
needed. -/
theorem flatGradedGrassmannian_baseChange_mem_extendedIdeal
    (x : (Fin r → S) × (Fin q → S))
    (hx : x ∈ grassmannianSubmoduleBaseChange (algebraMap R S)
      (flatGradedGrassmannian J d r q e hRank).toSubmodule) :
    (grassmannianChartHomogeneousCoordinateEquiv (R := S) d e x).1 ∈
      Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal := by
  let ER := grassmannianChartHomogeneousCoordinateEquiv (R := R) d e
  let ES := grassmannianChartHomogeneousCoordinateEquiv (R := S) d e
  let W := flatGradedGrassmannian J d r q e hRank
  have hW : W.toSubmodule =
      (homogeneousModelIdealPiece J d).comap ER.toLinearMap :=
    flatGradedGrassmannian_toSubmodule J d r q e hRank
  change x ∈ Submodule.span S
    (graphCoefficientMap (algebraMap R S) ''
      (W.toSubmodule : Set ((Fin r → R) × (Fin q → R)))) at hx
  refine Submodule.span_induction (p := fun y _ =>
    (ES y).1 ∈ Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨z, hz, rfl⟩
    have hzJ : ER z ∈ homogeneousModelIdealPiece J d := by
      rw [hW] at hz
      exact hz
    have hzPoly : (ER z).1 ∈ J.toIdeal :=
      (mem_homogeneousModelIdealPiece_iff J d (ER z)).mp hzJ
    have he := grassmannianChartHomogeneousCoordinateEquiv_baseChange
      (R := R) d (algebraMap R S) e z
    change (ES (graphCoefficientMap (algebraMap R S) z)).1 ∈ _
    rw [← he]
    exact Ideal.mem_map_of_mem _ hzPoly
  · simpa only [map_zero, Submodule.coe_zero] using
      (Ideal.zero_mem (Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal))
  · intro a b _ _ ha hb
    simpa only [map_add, Submodule.coe_add] using
      (Ideal.add_mem _ ha hb)
  · intro c a _ ha
    change (ES (c • a)).1 ∈ _
    rw [map_smul]
    change c • (ES a).1 ∈ _
    rw [smul_eq_C_mul]
    exact (Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal).mul_mem_left _ ha

/-- The same incidence statement for the actual base-changed Grassmannian
point, rather than its underlying submodule. -/
theorem flatGradedGrassmannian_quotientMap_mem_extendedIdeal
    (x : (Fin r → S) × (Fin q → S))
    (hx : x ∈
      (grassmannianQuotientMap (algebraMap R S)
        (flatGradedGrassmannian J d r q e hRank)).toSubmodule) :
    (grassmannianChartHomogeneousCoordinateEquiv (R := S) d e x).1 ∈
      Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal := by
  rw [grassmannianQuotientMap_submodule] at hx
  exact flatGradedGrassmannian_baseChange_mem_extendedIdeal
    J d r q e hRank x hx

/-- When the specialized curve is given by the extended model ideal, every
member of the specialized Grassmannian system is literally an equation of
that curve in the chosen degree. -/
theorem flatGradedGrassmannian_quotientMap_mem_fibreIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (x : (Fin r → S) × (Fin q → S))
    (hx : x ∈
      (grassmannianQuotientMap (algebraMap R S)
        (flatGradedGrassmannian J d r q e hRank)).toSubmodule) :
    grassmannianChartHomogeneousCoordinateEquiv (R := S) d e x ∈
      homogeneousModelIdealPiece C d := by
  apply (mem_homogeneousModelIdealPiece_iff C d _).mpr
  rw [← hmap]
  exact flatGradedGrassmannian_quotientMap_mem_extendedIdeal
    J d r q e hRank x hx

end PfaffianDescent
