import PfaffianDescent.IntrinsicQuadraticIdealPiece
import PfaffianDescent.NormalizedFiniteEquationPoint
import PfaffianDescent.HomogeneousVanishingLinearSystem

/-! Evaluation on a normalized finite coordinate algebra implies intrinsic
scheme-theoretic vanishing on every ambient chart. Square-zero directions
remain in the evaluation kernel. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

instance intrinsicFullQuadraticSystem_finiteDimensional
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) :
    FiniteDimensional K (intrinsicFullQuadraticSystem i) := by
  let f : intrinsicFullQuadraticSystem i →ₗ[K] homogeneousSubmodule (Fin 4) K 2 :=
    { toFun p := ⟨p.val, p.property.1⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact FiniteDimensional.of_injective f (by
    intro p q h
    have hpoly : p.val = q.val := congrArg
      (fun r : homogeneousSubmodule (Fin 4) K 2 => r.val) h
    exact Subtype.ext hpoly)

set_option backward.isDefEq.respectTransparency false in
theorem normalizedFiniteEquationPoint_evaluationQuadrics_le_intrinsic
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0) :
    homogeneousVanishingPolynomialSubmodule x 2 ≤ intrinsicFullQuadraticSystem
      (normalizedFiniteEquationPoint I x ell hell hOne he ≫ quotientProjMap I) := by
  intro p hp
  obtain ⟨hhom, hzero⟩ := (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 p).mp hp
  let J := equationIdeal p hhom
  have heJ : ∀ q ∈ J.toIdeal, q.eval₂ (algebraMap K A) x = 0 := by
    have hle : J.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K A) x) := by
      apply Ideal.span_le.mpr
      rintro q hq
      obtain rfl := Set.mem_singleton_iff.mp hq
      exact hzero
    exact fun q hq => hle hq
  let r := normalizedFiniteEquationPoint J x ell hell hOne heJ
  have hdiag : r ≫ quotientProjMap J =
      normalizedFiniteEquationPoint I x ell hell hOne he ≫ quotientProjMap I :=
    (normalizedFiniteEquationPoint_toAmbient J x ell hell hOne heJ).trans
      (normalizedFiniteEquationPoint_toAmbient I x ell hell hOne he).symm
  refine ⟨hhom, ?_⟩
  apply (Submodule.mem_iInf _).mpr
  intro j
  rw [← hdiag]
  have hmem := quotientProjMap_mem_intrinsicQuadraticChartIdeal
    J j p (Ideal.subset_span (Set.mem_singleton p))
  change Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)
      (ambientChartEvaluation j p) ∈ (quotientProjMap J).ker.ideal
      (intrinsicQuadraticAmbientOpen j) at hmem
  change Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)
      (ambientChartEvaluation j p) ∈ (r ≫ quotientProjMap J).ker.ideal
      (intrinsicQuadraticAmbientOpen j)
  exact (Scheme.Hom.le_ker_comp r (quotientProjMap J)) _ hmem

theorem normalizedFiniteEquationPoint_intrinsicQuadrics_finrank_ge
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0) :
    finrank K (homogeneousVanishingPolynomialSubmodule (K := K) x 2) ≤ finrank K
      (intrinsicFullQuadraticSystem
        (normalizedFiniteEquationPoint I x ell hell hOne he ≫ quotientProjMap I)) := by
  let f := Submodule.inclusion
    (normalizedFiniteEquationPoint_evaluationQuadrics_le_intrinsic I x ell hell hOne he)
  exact LinearMap.finrank_le_finrank_of_injective
    (show Function.Injective f from Submodule.inclusion_injective _)

end PfaffianDescent
