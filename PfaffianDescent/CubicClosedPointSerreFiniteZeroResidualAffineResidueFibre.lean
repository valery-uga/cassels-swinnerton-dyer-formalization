import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineFibreQuotient

/-! # Actual affine residue-field fibres use the same extended kernel -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_affineSurjectiveFibre_kernel_top
    {A B F : Type u} [CommRing A] [CommRing B] [CommRing F]
    (g : A →+* B) (q : A →+* F) (hq : Function.Surjective q) :
    (pullback.fst (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom q))).ker.ideal
        (⟨⊤, isAffineOpen_top (Spec (.of B))⟩ : (Spec (.of B)).affineOpens) =
      ((RingHom.ker q).map g).comap (Scheme.ΓSpecIso (.of B)).hom.hom := by
  let I := RingHom.ker q
  let r : (A ⧸ I) ≃+* F := q.quotientKerEquivOfSurjective hq
  let e : Spec (.of F) ≅ Spec (.of (A ⧸ I)) :=
    Scheme.Spec.mapIso r.toCommRingCatIso.op
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      Spec.map (CommRingCat.ofHom q) := by
    change Spec.map (CommRingCat.ofHom r.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = _
    rw [← Spec.map_comp]
    congr 1
  let c := pullback.map (Spec.map (CommRingCat.ofHom g)) (Spec.map (CommRingCat.ofHom q))
    (Spec.map (CommRingCat.ofHom g)) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (𝟙 _) e.hom (𝟙 _) (by simp) (by simpa using he.symm)
  letI : IsIso c := by dsimp [c]; infer_instance
  have hc : c ≫ pullback.fst (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      pullback.fst (Spec.map (CommRingCat.ofHom g)) (Spec.map (CommRingCat.ofHom q)) := by
    simp [c]
  rw [← hc, Scheme.Hom.ker_comp_of_isIso]
  exact cubicClosedPointSerreFiniteZeroResidual_affineFibre_kernel_top g I

end PfaffianDescent
