import PfaffianDescent.FiniteSchemeGeometricPoints
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
section
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A finite scheme of positive rank has an actual point over a field extension
whose degree is at most that rank. -/
theorem finiteScheme_small_field_point (f : X ⟶ Spec (.of K)) [IsFinite f]
    {n : ℕ} (hn : 0 < n) (hr : f.finrank (IsLocalRing.closedPoint K) = n) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (p : Spec (.of L) ⟶ X),
      finrank K L ≤ n ∧ p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  haveI : Module.Finite K Γ(X, ⊤) := finiteSchemeCoefficient_finite f
  have hdim : finrank K Γ(X, ⊤) = n :=
    (finiteSchemeCoefficient_finrank f).trans ((AllCharacteristics.finiteSchemeRank_eq_finrank f).trans hr)
  haveI : Nontrivial Γ(X, ⊤) := Module.nontrivial_of_finrank_pos (hdim.symm ▸ hn)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := Γ(X, ⊤))
  letI : m.IsMaximal := hm
  let L := Γ(X, ⊤) ⧸ m
  letI : Field L := Ideal.Quotient.field m
  let ev : Γ(X, ⊤) →ₐ[K] L := Ideal.Quotient.mkₐ K m
  have hev : Function.Surjective ev := Ideal.Quotient.mk_surjective
  refine ⟨L, inferInstance, inferInstance, inferInstance, finiteSchemeGeometricPoint f ev, ?_,
    finiteSchemeGeometricPoint_over_base f ev⟩
  exact (LinearMap.finrank_le_finrank_of_surjective (f := ev.toLinearMap) hev).trans_eq hdim

end
end PfaffianDescent
