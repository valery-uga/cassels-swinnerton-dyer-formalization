import PfaffianDescent.GrassmannianHomogeneousFrame
import PfaffianDescent.CubicLineFiniteSubscheme
import PfaffianDescent.CorayLiteralOriginalPairPolynomial

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem actualBlockCoordinates_sumLabel_apply002
    {R : Type u} [CommRing R] (x : (Fin 2 → R) × (Fin 2 → R)) (s : Fin 2 ⊕ Fin 2) :
    finiteProductCoordinateEquiv (R := R) 2 2 x (finSumFinEquiv s) = Sum.elim x.1 x.2 s := by
  rcases x with ⟨x₁, x₂⟩
  cases s <;>
    simp [finiteProductCoordinateEquiv, LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft', LinearEquiv.sumArrowLequivProdArrow,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr]

private theorem actualGraphAdjoinRootVector_firstPivot_eq_root001
    {K : Type u} [Field K] (F : Polynomial K)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (T : Matrix (Fin 2) (Fin 2) K) :
    let a := finiteProductCoordinateEquiv (R := K) 2 2 (grassmannianChartColumn K rho T 0)
    let b := finiteProductCoordinateEquiv (R := K) 2 2 (grassmannianChartColumn K rho T 1)
    let B := AdjoinRoot F
    let x := AdjoinRoot.root F • (fun k => algebraMap K B (a k)) +
      (fun k => algebraMap K B (b k))
    x (finSumFinEquiv (rho (Sum.inl (0 : Fin 2)))) = AdjoinRoot.root F := by
  intro a b B x
  have hColumn (k : Fin 2) :
      finiteProductCoordinateEquiv (R := K) 2 2 (grassmannianChartColumn K rho T k)
        (finSumFinEquiv (rho (Sum.inl (0 : Fin 2)))) = if (0 : Fin 2) = k then 1 else 0 := by
    rw [actualBlockCoordinates_sumLabel_apply002]
    dsimp only [grassmannianChartColumn]
    have hPerm (s : Fin 2 ⊕ Fin 2) (v : (Fin 2 → K) × (Fin 2 → K)) :
        Sum.elim (graphCoordinatePermutation K rho.symm v).1
          (graphCoordinatePermutation K rho.symm v).2 s = Sum.elim v.1 v.2 (rho.symm s) := by
      cases s <;> rfl
    rw [hPerm, rho.symm_apply_apply]
    simp [Pi.single_apply]
  simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  dsimp only [a, b]
  rw [hColumn 0, hColumn 1]
  simp

private theorem chartMap_surjective_of_originalCoordinateEvaluation_surjective001
    {K R B : Type u} [Field K] [CommRing R] [CommRing B]
    [Algebra K R] [Algebra K B] (g : R →ₐ[K] B)
    (z : Fin 4 → R) (x : Fin 4 → B) (hCoords : ∀ k, g (z k) = x k)
    (hEval : Function.Surjective (eval₂Hom (algebraMap K B) x)) :
    Function.Surjective g := by
  intro v
  obtain ⟨q, hq⟩ := hEval v
  refine ⟨q.eval₂ (algebraMap K R) z, ?_⟩
  have hCoeff : g.toRingHom.comp (algebraMap K R) = algebraMap K B := RingHom.ext g.commutes
  have h := MvPolynomial.hom_eval₂ q (algebraMap K R) g.toRingHom z
  rw [hCoeff] at h
  change g (q.eval₂ (algebraMap K R) z) =
    q.eval₂ (algebraMap K B) (fun k => g (z k)) at h
  have hCoordsFun : (fun k => g (z k)) = x := funext hCoords
  rw [hCoordsFun] at h
  exact h.trans hq

/-- The actual original coordinate map onto the literal graph-cut AdjoinRoot
algebra is SURJECTIVE. First-pivot=root is derived from original canonical
columns; no field-product decomposition, independent point or surjectivity
outcome is supplied. -/
theorem originalFixedGraphAdjoinRoot_chartMap_surjective001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (F : Polynomial K) (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (T : Matrix (Fin 2) (Fin 2) K) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let a := finiteProductCoordinateEquiv (R := K) 2 2 (grassmannianChartColumn K rho T 0)
    let b := finiteProductCoordinateEquiv (R := K) 2 2 (grassmannianChartColumn K rho T 1)
    let B := AdjoinRoot F
    let x := AdjoinRoot.root F • (fun k => algebraMap K B (a k)) +
      (fun k => algebraMap K B (b k))
    ∀ g : R →ₐ[K] B,
      (∀ k, g (chartCoordinate (equationIdeal p hp) j k) = x k) → Function.Surjective g := by
  intro R
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  intro a b B x g hCoords
  have hRoot := actualGraphAdjoinRootVector_firstPivot_eq_root001 F rho T
  have hEval : Function.Surjective (eval₂Hom (algebraMap K B) x) :=
    PfaffianDescent.eval₂_line_coordinate_surjective F
      (finSumFinEquiv (rho (Sum.inl (0 : Fin 2)))) x hRoot
  exact chartMap_surjective_of_originalCoordinateEvaluation_surjective001
    g (chartCoordinate (equationIdeal p hp) j) x hCoords hEval

end PfaffianDescent.Coray
