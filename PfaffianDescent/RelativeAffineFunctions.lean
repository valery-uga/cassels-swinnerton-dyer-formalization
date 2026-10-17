import PfaffianDescent.SchemeAffineFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (R : Type u) [CommRing R] (ι : Type)

/-- Affine space over a ring, with its actual structure morphism. -/
noncomputable def relativeAffineProjection :
    Spec (.of (MvPolynomial ι R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom MvPolynomial.C)

variable {X : Scheme.{u}} (g : X ⟶ Spec (.of R))

/-- A tuple of regular functions gives a morphism to relative affine space over a fixed base map. -/
noncomputable def relativeAffineMorphismOfFunctions (c : ι → Γ(X, ⊤)) :
    X ⟶ Spec (.of (MvPolynomial ι R)) :=
  morphismFromAffineFunctions X (MvPolynomial.eval₂Hom (affineFunctionHom g) c)

lemma relativeAffineMorphismOfFunctions_projection (c : ι → Γ(X, ⊤)) :
    relativeAffineMorphismOfFunctions R ι g c ≫ relativeAffineProjection R ι = g := by
  apply affineFunctionHom_injective
  change affineFunctionHom (relativeAffineMorphismOfFunctions R ι g c ≫
    Spec.map (CommRingCat.ofHom MvPolynomial.C)) = _
  rw [affineFunctionHom_comp_Spec, relativeAffineMorphismOfFunctions, affineFunctionHom_from]
  ext r
  exact MvPolynomial.eval₂_C _ _ _

lemma relativeAffineMorphismOfFunctions_coordinate (c : ι → Γ(X, ⊤)) (i : ι) :
    affineFunctionHom (relativeAffineMorphismOfFunctions R ι g c) (MvPolynomial.X i) = c i := by
  rw [relativeAffineMorphismOfFunctions, affineFunctionHom_from]
  exact MvPolynomial.eval₂_X _ _ _

/-- Relative affine space represents arbitrary tuples of regular functions on every test scheme. -/
noncomputable def relativeAffineFunctionsEquiv :
    {f : X ⟶ Spec (.of (MvPolynomial ι R)) // f ≫ relativeAffineProjection R ι = g} ≃ (ι → Γ(X, ⊤)) where
  toFun f i := affineFunctionHom f.1 (MvPolynomial.X i)
  invFun c := ⟨relativeAffineMorphismOfFunctions R ι g c, relativeAffineMorphismOfFunctions_projection R ι g c⟩
  left_inv f := by
    apply Subtype.ext
    apply affineFunctionHom_injective
    change affineFunctionHom (relativeAffineMorphismOfFunctions R ι g
      (fun i => affineFunctionHom f.1 (MvPolynomial.X i))) = affineFunctionHom f.1
    rw [relativeAffineMorphismOfFunctions, affineFunctionHom_from]
    apply MvPolynomial.ringHom_ext
    · intro r
      have h := congrArg affineFunctionHom f.2
      have hc : (affineFunctionHom f.1).comp MvPolynomial.C = affineFunctionHom g :=
        (affineFunctionHom_comp_Spec f.1 MvPolynomial.C).symm.trans h
      exact (MvPolynomial.eval₂_C _ _ _).trans (RingHom.congr_fun hc r).symm
    · intro i
      exact MvPolynomial.eval₂_X _ _ _
  right_inv c := by
    funext i
    exact relativeAffineMorphismOfFunctions_coordinate R ι g c i

end
end PfaffianDescent
