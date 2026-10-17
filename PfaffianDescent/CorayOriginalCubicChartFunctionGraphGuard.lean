import PfaffianDescent.CorayOriginalChartFunctionGraphGuard
import PfaffianDescent.CorayOriginalPairChartDimension
import AllCharacteristics.NormalizedChartGeneration

/-! SOURCE ONLY. An ACTUAL nonzero original cubic chart function produces
an original-K graph guard; chart normalization, finite type, integrality and
dimension are derived on the SAME original chart. This does not itself
produce the tangent-good function or establish the surface branch. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- A genuine original nonzero chart function constructs a nonzero SAME
fixed-graph polynomial that excludes all its zeros from the chosen graph.
The whole scalar-valued condition applies also to the actual degree-three
AdjoinRoot field and to every scalar extension, with no avoidance premise. -/
theorem cubicOriginalChartFunction_exists_nonzeroOriginalGraphPolynomial_forcing_sameGraph_nonzero001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (hypersurface p hp)]
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (hPivot : finSumFinEquiv (m := 2) (n := 2) (rho (Sum.inl (1 : Fin 2))) = j) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ∀ h : R, h ≠ 0 →
    ∃ q : GrassmannianChartRing K 2 2, q ≠ 0 ∧
      ∀ (M : Type u) [CommRing M] [Algebra K M]
        (f : R →ₐ[K] M) (T : Matrix (Fin 2) (Fin 2) M),
        graphCoefficientMap f.toRingHom
          ((fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i))),
           (fun i => chartCoordinate (equationIdeal p hp) j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i)))) ∈
          grassmannianChartSubmodule M rho T →
        (aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)) q ≠ 0 → f h ≠ 0 := by
  intro R
  let I := equationIdeal p hp
  letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  intro h hh
  let g : R →+* (hypersurface p hp).functionField := @affineChartGenericEvaluation
    R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
  have hg : Function.Injective g := @affineChartGenericEvaluation_injective
    R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
  letI : IsDomain R := hg.isDomain g
  let e : MvPolynomial (Fin 4) K →ₐ[K] R := aeval (chartCoordinate I j)
  have he : Function.Surjective e := eval₂_chartCoordinate_surjective I j
  letI : Algebra.FiniteType K R := Algebra.FiniteType.of_surjective e he
  obtain ⟨_, hDim⟩ := cubicOriginalChart_noetherian_and_ringKrullDim_le_two001 p hp hp0 j
  let x : (Fin 2 → R) × (Fin 2 → R) :=
    ((fun i => chartCoordinate I j (finSumFinEquiv (m := 2) (n := 2) (Sum.inl i))),
     (fun i => chartCoordinate I j (finSumFinEquiv (m := 2) (n := 2) (Sum.inr i))))
  have hx1 : (graphCoordinatePermutation R rho x).1 1 = 1 := by
    rw [graphCoordinatePermutation_fst]
    change Sum.elim x.1 x.2 (rho (Sum.inl (1 : Fin 2))) = 1
    have hx (s : Fin 2 ⊕ Fin 2) : Sum.elim x.1 x.2 s = chartCoordinate I j (finSumFinEquiv s) := by
      cases s <;> rfl
    rw [hx, hPivot, chartCoordinate_self]
  exact chartFunction_exists_nonzeroOriginalGraphPolynomial_forcing_sameGraph_nonzero001
    (K := K) hDim h hh rho x hx1

end PfaffianDescent.Coray
