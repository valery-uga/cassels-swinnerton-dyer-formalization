import AllCharacteristics.TangentHyperplaneGeneric

/-!
# Smooth cubic points under a Galois conjugation

A cubic defined over the fixed field has conjugate smooth coordinate points.
This is the smoothness transfer used to choose a tangent direction at one
root of a quadratic residual line and transport it to the other root.
-/

namespace AllCharacteristics

open PfaffianDescent

universe u

/-- Evaluating a polynomial fixed by an algebra automorphism commutes with
applying that automorphism to all coordinates. -/
theorem MvPolynomial.eval_apply_algEquiv_of_map_eq
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Fin 4 → L) (P : MvPolynomial (Fin 4) L)
    (hP : P.map σ.toRingHom = P) :
    P.eval (fun i => σ (x i)) = σ (P.eval x) := by
  calc
    P.eval (fun i => σ (x i)) = (P.map σ.toRingHom).eval
        (fun i => σ (x i)) :=
          congrArg (fun Q => Q.eval (fun i => σ (x i))) hP.symm
    _ = MvPolynomial.eval₂ σ.toRingHom (fun i => σ (x i)) P := by
        rw [MvPolynomial.eval_map]
    _ = σ (P.eval x) := by
      change MvPolynomial.eval₂ σ.toRingHom (fun i => σ (x i)) P =
        σ (MvPolynomial.eval₂ (RingHom.id L) x P)
      have h : MvPolynomial.eval₂Hom σ.toRingHom (fun i => σ (x i)) =
          σ.toRingHom.comp (MvPolynomial.eval₂Hom (RingHom.id L) x) := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
        · intro i
          simp
      exact DFunLike.congr_fun h P

/-- A smooth coordinate point of a cubic remains smooth after a fixed-field
algebra automorphism is applied to its homogeneous coordinates. -/
theorem isSmoothCubicCoordinatePoint_apply_algEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (c : Cubic K 4) (σ : L ≃ₐ[K] L) (x : Fin 4 → L)
    (hs : IsSmoothCubicCoordinatePoint
      ((c.map (algebraMap K L)).toMvPolynomial) x) :
    IsSmoothCubicCoordinatePoint
      ((c.map (algebraMap K L)).toMvPolynomial) (fun i => σ (x i)) := by
  let cL := c.map (algebraMap K L)
  have hfix : cL.map σ.toRingHom = cL := by
    funext t
    change σ (algebraMap K L (c t)) = algebraMap K L (c t)
    exact σ.commutes (c t)
  have hpoly : cL.toMvPolynomial.map σ.toRingHom = cL.toMvPolynomial := by
    rw [← Cubic.toMvPolynomial_map, hfix]
  have hderiv (i : Fin 4) :
      (MvPolynomial.pderiv i cL.toMvPolynomial).map σ.toRingHom =
        MvPolynomial.pderiv i cL.toMvPolynomial := by
    rw [← MvPolynomial.pderiv_map, hpoly]
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    apply hs.1
    funext i
    apply σ.injective
    have h := congrFun hzero i
    simpa using h
  · have he := MvPolynomial.eval_apply_algEquiv_of_map_eq σ x cL.toMvPolynomial hpoly
    rw [he, hs.2.1, map_zero]
  · obtain ⟨i, hi⟩ := hs.2.2
    refine ⟨i, ?_⟩
    rw [MvPolynomial.eval_apply_algEquiv_of_map_eq σ x
      (MvPolynomial.pderiv i cL.toMvPolynomial) (hderiv i)]
    exact (map_ne_zero σ.toRingHom).mpr hi

end AllCharacteristics
