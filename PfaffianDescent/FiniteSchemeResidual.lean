import PfaffianDescent.FiniteSchemeAlgebra
import PfaffianDescent.ResidualAffineScheme
import PfaffianDescent.FrobeniusResidualLength

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
section
variable {K : Type u} [Field K] {X Z : Scheme.{u}}

/-- Frobenius functionals on finite coefficient algebras transport along an
equality of finite structure morphisms.  This lets residual constructions use
the composite through a closed ambient immersion while complete-intersection
calculations state the same input using their canonical structure map. -/
theorem finiteScheme_exists_frobeniusFunctional_congr
    (f g : X ⟶ Spec (.of K)) [IsFinite f] [IsFinite g]
    (hfg : f = g)
    (hfrob : letI := finiteSchemeCoefficientAlgebra f
      ∃ ell : Module.Dual K Γ(X, ⊤), IsFrobeniusFunctional ell) :
    letI := finiteSchemeCoefficientAlgebra g
    ∃ ell : Module.Dual K Γ(X, ⊤), IsFrobeniusFunctional ell := by
  subst g
  exact hfrob

/-- The residual of a closed subscheme of a finite scheme, using its actual
ideal of global equations and the annihilator (colon) ideal. -/
noncomputable def finiteClosedResidualι (i : Z ⟶ X) (f : X ⟶ Spec (.of K)) [IsFinite f] :
    Spec (.of (Γ(X, ⊤) ⧸ residualAlgebraIdeal (RingHom.ker i.appTop.hom))) ⟶ X :=
  letI : IsAffine X := isAffine_of_isAffineHom f
  residualAffineι (RingHom.ker i.appTop.hom) ≫ X.isoSpec.inv

instance finiteClosedResidualι_isClosedImmersion (i : Z ⟶ X)
    (f : X ⟶ Spec (.of K)) [IsFinite f] : IsClosedImmersion (finiteClosedResidualι i f) := by
  unfold finiteClosedResidualι
  infer_instance

instance finiteClosedResidual_toBase_isFinite (i : Z ⟶ X)
    (f : X ⟶ Spec (.of K)) [IsFinite f] : IsFinite (finiteClosedResidualι i f ≫ f) := by
  infer_instance

/-- In a finite Frobenius scheme, the annihilator residual to a closed
subscheme has the complementary scheme-theoretic rank.  This is the general
length calculation needed for Voisin's complete-intersection residuals. -/
theorem finite_scheme_residual_rank_complement (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f] (N d : ℕ)
    (hX : AllCharacteristics.finiteSchemeRank f = N)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = d)
    (hfrob : letI := finiteSchemeCoefficientAlgebra f
      ∃ ell : Module.Dual K Γ(X, ⊤), IsFrobeniusFunctional ell) :
    AllCharacteristics.finiteSchemeRank (finiteClosedResidualι i f ≫ f) = N - d := by
  letI := finiteSchemeCoefficientAlgebra f
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  have := finiteSchemeCoefficient_finite f
  have := finiteSchemeCoefficient_finite (i ≫ f)
  have : IsAffine X := isAffine_of_isAffineHom f
  obtain ⟨ell, hell⟩ := hfrob
  let P := RingHom.ker i.appTop.hom
  have hA : finrank K Γ(X, ⊤) = N := (finiteSchemeCoefficient_finrank f).trans hX
  have hP : finrank K (Γ(X, ⊤) ⧸ P) = d := by
    have hg := (Ideal.quotientKerAlgEquivOfSurjective
      (finiteSchemeClosedMap_surjective i f)).toLinearEquiv.finrank_eq
    exact hg.trans ((finiteSchemeCoefficient_finrank (i ≫ f)).trans hZ)
  have hcomp : finiteClosedResidualι i f ≫ f =
      residualAffineι P ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) := by
    rw [finiteSchemeCoefficient_spec f]
    exact Category.assoc _ _ _
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hcomp, residualAffineι_toBase,
    Scheme.Hom.finrank_SpecMap_algebraMap]
  exact (congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := K) (M := Γ(X, ⊤) ⧸ residualAlgebraIdeal P)) _).trans
      (residual_quotient_finrank_complement ell hell P N d hA hP)

/-- A codimension-one closed subscheme of a finite scheme has a rank-one
annihilator residual.  Unlike the general complementary-rank statement,
this uses only the rank calculation and does not require the ambient finite
scheme to carry a Frobenius functional. -/
theorem finite_scheme_residual_length_one_of_codimension_one
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f] (n : ℕ)
    (hX : AllCharacteristics.finiteSchemeRank f = n + 1)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = n) :
    AllCharacteristics.finiteSchemeRank (finiteClosedResidualι i f ≫ f) = 1 := by
  letI := finiteSchemeCoefficientAlgebra f
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  have := finiteSchemeCoefficient_finite f
  have := finiteSchemeCoefficient_finite (i ≫ f)
  have : IsAffine X := isAffine_of_isAffineHom f
  let P := RingHom.ker i.appTop.hom
  have hA : finrank K Γ(X, ⊤) = n + 1 :=
    (finiteSchemeCoefficient_finrank f).trans hX
  have hP : finrank K (Γ(X, ⊤) ⧸ P) = n := by
    have hg := (Ideal.quotientKerAlgEquivOfSurjective
      (finiteSchemeClosedMap_surjective i f)).toLinearEquiv.finrank_eq
    exact hg.trans ((finiteSchemeCoefficient_finrank (i ≫ f)).trans hZ)
  have hcomp : finiteClosedResidualι i f ≫ f =
      residualAffineι P ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) := by
    rw [finiteSchemeCoefficient_spec f]
    exact Category.assoc _ _ _
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hcomp, residualAffineι_toBase,
    Scheme.Hom.finrank_SpecMap_algebraMap]
  exact (congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := K) (M := Γ(X, ⊤) ⧸ residualAlgebraIdeal P)) _).trans
      (residual_algebra_rank_one_of_codimension_one P n hA hP)

/-- The rank-one residual of a codimension-one finite subscheme supplies a
rational section of the ambient finite scheme. -/
theorem finite_scheme_residual_section_of_codimension_one
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f] (n : ℕ)
    (hX : AllCharacteristics.finiteSchemeRank f = n + 1)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = n) :
    ∃ s : Spec (.of K) ⟶
        Spec (.of (Γ(X, ⊤) ⧸ residualAlgebraIdeal (RingHom.ker i.appTop.hom))),
      s ≫ finiteClosedResidualι i f ≫ f = 𝟙 _ := by
  obtain ⟨z, hz⟩ := AllCharacteristics.exists_effectiveZeroCycle_degree_finiteSchemeRank
    (finiteClosedResidualι i f ≫ f)
  exact section_of_effective_cycle_degree_one _ z
    (hz.trans (finite_scheme_residual_length_one_of_codimension_one i f n hX hZ))

/-- An actual length-five closed subscheme of a length-six finite scheme
has an actual residual closed subscheme of length one. -/
theorem finite_scheme_residual_length_one (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    (hX : AllCharacteristics.finiteSchemeRank f = 6)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = 5) :
    AllCharacteristics.finiteSchemeRank (finiteClosedResidualι i f ≫ f) = 1 := by
  simpa using finite_scheme_residual_length_one_of_codimension_one i f 5 hX hZ

/-- The residual construction gives a rational section factoring through the
actual residual closed subscheme. -/
theorem finite_scheme_residual_section (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    (hX : AllCharacteristics.finiteSchemeRank f = 6)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = 5) :
    ∃ s : Spec (.of K) ⟶
        Spec (.of (Γ(X, ⊤) ⧸ residualAlgebraIdeal (RingHom.ker i.appTop.hom))),
      s ≫ finiteClosedResidualι i f ≫ f = 𝟙 _ := by
  simpa using finite_scheme_residual_section_of_codimension_one i f 5 hX hZ

end
end PfaffianDescent
