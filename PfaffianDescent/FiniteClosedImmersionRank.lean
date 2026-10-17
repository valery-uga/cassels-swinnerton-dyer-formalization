import PfaffianDescent.FiniteSchemeAlgebra

/-!
# Equal-length finite closed immersions

A closed immersion between finite schemes over a field is an isomorphism as
soon as source and target have the same scheme-theoretic rank.  This is the
scheme-theoretic equality step used by the degree-eight net of quadrics.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory Module

universe u

section

variable {K : Type u} [Field K] {X Z : Scheme.{u}}

/-- A finite closed immersion of equal rank is an isomorphism. -/
theorem isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    (hrank : AllCharacteristics.finiteSchemeRank (i ≫ f) =
      AllCharacteristics.finiteSchemeRank f) :
    IsIso i := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ : IsAffine Z := isAffine_of_isAffineHom (i ≫ f)
  let _ := finiteSchemeCoefficientAlgebra f
  let _ := finiteSchemeCoefficientAlgebra (i ≫ f)
  let _ := finiteSchemeCoefficient_finite f
  let _ := finiteSchemeCoefficient_finite (i ≫ f)
  let j := finiteSchemeClosedMap i f
  have hsurj : Function.Surjective j := finiteSchemeClosedMap_surjective i f
  have hdimX : finrank K Γ(X, ⊤) = AllCharacteristics.finiteSchemeRank f :=
    finiteSchemeCoefficient_finrank f
  have hdimZ : finrank K Γ(Z, ⊤) =
      AllCharacteristics.finiteSchemeRank (i ≫ f) :=
    finiteSchemeCoefficient_finrank (i ≫ f)
  have hdim : finrank K Γ(X, ⊤) = finrank K Γ(Z, ⊤) :=
    hdimX.trans (hrank.symm.trans hdimZ.symm)
  have hrange : LinearMap.range j.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hsum := j.toLinearMap.finrank_range_add_finrank_ker
  have hkerfin : finrank K (LinearMap.ker j.toLinearMap) = 0 := by
    rw [hrange, finrank_top] at hsum
    omega
  have hker : LinearMap.ker j.toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.mp hkerfin
  have hinj : Function.Injective j.toLinearMap :=
    LinearMap.ker_eq_bot.mp hker
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  intro a b hab
  exact hinj hab

end

end PfaffianDescent
