import PfaffianDescent.FiniteSchemeSmallFieldPoint
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u
section
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

/-- A two-dimensional algebra either has a rational evaluation or is a quadratic field. -/
theorem degreeTwoAlgebra_dichotomy (hdim : finrank K A = 2) :
    Nonempty (A →ₐ[K] K) ∨
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L),
        finrank K L = 2 ∧ Nonempty (A ≃ₐ[K] L) := by
  haveI : Nontrivial A := Module.nontrivial_of_finrank_pos (hdim.symm ▸ (by decide : 0 < 2))
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := A)
  letI : m.IsMaximal := hm
  let L := A ⧸ m
  letI : Field L := Ideal.Quotient.field m
  let ev : A →ₐ[K] L := Ideal.Quotient.mkₐ K m
  have hev : Function.Surjective ev := Ideal.Quotient.mk_surjective
  have hle : finrank K L ≤ 2 :=
    (LinearMap.finrank_le_finrank_of_surjective (f := ev.toLinearMap) hev).trans_eq hdim
  have hpos : 0 < finrank K L := Module.finrank_pos
  by_cases h1 : finrank K L = 1
  · obtain ⟨e⟩ := (nonempty_algEquiv_iff_finrank_eq_one (R := K) (S := L)).mpr h1
    exact Or.inl ⟨e.symm.toAlgHom.comp ev⟩
  · have h2 : finrank K L = 2 := by omega
    have hi : Function.Injective ev :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdim.trans h2.symm)
        (f := ev.toLinearMap)).mpr hev
    exact Or.inr ⟨L, inferInstance, inferInstance, inferInstance, h2, ⟨AlgEquiv.ofBijective ev ⟨hi, hev⟩⟩⟩

end
section
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A finite degree-two scheme over a field has a rational point or is the
spectrum of a quadratic field extension. This includes the finite étale case. -/
theorem degreeTwoScheme_dichotomy (f : X ⟶ Spec (.of K)) [IsFinite f]
    (hr : f.finrank (IsLocalRing.closedPoint K) = 2) :
    (∃ p : Spec (.of K) ⟶ X, p ≫ f = 𝟙 _) ∨
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
        (e : Spec (.of L) ≅ X),
        finrank K L = 2 ∧ e.hom ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  haveI : Module.Finite K Γ(X, ⊤) := finiteSchemeCoefficient_finite f
  have hdim : finrank K Γ(X, ⊤) = 2 :=
    (finiteSchemeCoefficient_finrank f).trans ((AllCharacteristics.finiteSchemeRank_eq_finrank f).trans hr)
  rcases degreeTwoAlgebra_dichotomy hdim with hev | he
  · obtain ⟨ev⟩ := hev
    refine Or.inl ⟨finiteSchemeGeometricPoint f ev, ?_⟩
    exact (finiteSchemeGeometricPoint_over_base f ev).trans (Spec.map_id _)
  · obtain ⟨L, hL, aL, hfin, hdimL, ⟨e⟩⟩ := he
    letI := hL
    letI := aL
    letI := hfin
    let p := finiteSchemeGeometricPoint f e.toAlgHom
    haveI : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
      isIso_SpecMap_iff.mpr e.bijective
    haveI : IsIso p := by
      change IsIso (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.isoSpec.inv)
      infer_instance
    exact Or.inr ⟨L, hL, aL, hfin, asIso p, hdimL, finiteSchemeGeometricPoint_over_base f e.toAlgHom⟩

end
end PfaffianDescent
