import PfaffianDescent.CorayOriginalCubicChartFunctionGraphGuard
import PfaffianDescent.CorayOriginalGrassmannFinitePolynomialKMatrixChoice

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- ACTUAL finitely many original nonzero chart functions give an ORIGINAL-K
matrix avoiding all their zeros at EVERY scalar-valued point of that SAME
graph. An additional honest nonzero original graph polynomial can include
the separately constructed badpair kernel equation; no such equation is
constructed or assumed geometrically proper by this finite selector. -/
theorem cubicOriginalChartFunctions_exists_originalKMatrix_sameGraph_all_nonzero001
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (hPivot : finSumFinEquiv (m := 2) (n := 2) (rho (Sum.inl (1 : Fin 2))) = j)
    {ι : Type u} [Finite ι] :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ∀ h : ι → R, (∀ i, h i ≠ 0) →
    ∀ Q : GrassmannianChartRing K 2 2, Q ≠ 0 →
    ∃ T : Matrix (Fin 2) (Fin 2) K,
      MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) Q ≠ 0 ∧
      ∀ (M : Type u) [CommRing M] [Nontrivial M] [Algebra K M] (f : R →ₐ[K] M),
        graphCoefficientMap f.toRingHom
          ((fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i))),
           (fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)))) ∈
          grassmannianChartSubmodule M rho (T.map (algebraMap K M)) →
        ∀ i, f (h i) ≠ 0 := by
  intro R
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  intro h hh Q hQ
  classical
  have hGuard (i : ι) :=
    cubicOriginalChartFunction_exists_nonzeroOriginalGraphPolynomial_forcing_sameGraph_nonzero001
      p hp hp0 j rho hPivot (h i) (hh i)
  choose q hq0 hq using hGuard
  let qs : Option ι → GrassmannianChartRing K 2 2 := Option.elim' Q q
  have hqs : ∀ i, qs i ≠ 0 := by
    intro i
    cases i with
    | none => exact hQ
    | some i => exact hq0 i
  obtain ⟨T, hT⟩ :=
    originalGrassmannChart_exists_KMatrix_avoiding_finite_nonzero_polynomials001 qs hqs
  refine ⟨T, hT none, ?_⟩
  intro M _ _ _ f hx i
  apply hq i M f (T.map (algebraMap K M)) hx
  have hKi := hT (some i)
  have hMapped :
      (aeval (R := K) (fun ij : Fin 2 × Fin 2 => (T.map (algebraMap K M)) ij.1 ij.2)) (q i) =
        algebraMap K M (MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) (q i)) := by
    have h := MvPolynomial.hom_eval₂ (q i) (RingHom.id K) (algebraMap K M)
      (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)
    rw [MvPolynomial.aeval_def]
    change (q i).eval₂ (algebraMap K M)
      (fun ij : Fin 2 × Fin 2 => algebraMap K M (T ij.1 ij.2)) =
        algebraMap K M ((q i).eval₂ (RingHom.id K)
          (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2))
    rw [RingHom.comp_id] at h
    exact h.symm
  rw [hMapped]
  intro hZero
  apply hKi
  apply (algebraMap K M).injective
  exact hZero.trans (map_zero _).symm

end PfaffianDescent.Coray
