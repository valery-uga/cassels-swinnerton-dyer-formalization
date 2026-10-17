import PfaffianDescent.CorayOriginalGeometricPointEvaluationInjective
import PfaffianDescent.CorayLiteralOriginalPairPolynomial

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Actual surjectivity of the SAME original normalized chart map proves
that ALL actual auxiliary geometric points have distinct ORIGINAL normalized
coordinate vectors. Whole chart generation and literal K squares prove
this; distinct vector/projective point outcomes are not premises. -/
theorem cubicOriginalAuxiliaryGeometricPoint_normalizedCoordinates_injective001
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ∀ hA : R →ₐ[K] A, Function.Surjective hA →
      Function.Injective (fun x : PrimeSpectrum (M ⊗[K] A) => fun i : Fin 4 =>
        originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) x
          (hA (chartCoordinate (equationIdeal p hp) j i))) := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  dsimp only
  intro hA hSurj x y hCoordinates
  let sx := originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) x
  let sy := originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) y
  let fx : R →ₐ[K] M := sx.comp hA
  let fy : R →ₐ[K] M := sy.comp hA
  let ev : MvPolynomial (Fin 4) K →ₐ[K] R := aeval (chartCoordinate (equationIdeal p hp) j)
  have hEv : Function.Surjective ev := by
    intro r
    obtain ⟨q, hq⟩ := eval₂_chartCoordinate_surjective (equationIdeal p hp) j r
    exact ⟨q, hq⟩
  have hComp : fx.comp ev = fy.comp ev := by
    apply MvPolynomial.algHom_ext
    intro i
    change fx ((MvPolynomial.aeval (chartCoordinate (equationIdeal p hp) j)) (X i)) =
      fy ((MvPolynomial.aeval (chartCoordinate (equationIdeal p hp) j)) (X i))
    simp only [MvPolynomial.aeval_X]
    exact congrFun hCoordinates i
  have hChart : fx = fy := by
    apply AlgHom.ext
    intro r
    obtain ⟨q, hq⟩ := hEv r
    have h := AlgHom.congr_fun hComp q
    simpa only [AlgHom.comp_apply, hq] using h
  have hPoint : sx = sy := by
    apply AlgHom.ext
    intro a
    obtain ⟨r, hr⟩ := hSurj a
    have h := AlgHom.congr_fun hChart r
    change sx (hA r) = sy (hA r) at h
    rw [hr] at h
    exact h
  exact originalFiniteEtaleGeometricPoint_injective001 hPoint

end PfaffianDescent.Coray
