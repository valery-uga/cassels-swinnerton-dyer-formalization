import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineResidueFibre
import Mathlib.AlgebraicGeometry.Fiber

/-! # Literal stalk quotient for actual closed fibres on affine spectra -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_nativeAffineFibre_kernel_top
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (y : Spec (.of A)) [y.asIdeal.IsMaximal] :
    ((Spec.map (CommRingCat.ofHom g)).fiberι y).ker.ideal
        (⟨⊤, isAffineOpen_top (Spec (.of B))⟩ : (Spec (.of B)).affineOpens) =
      (y.asIdeal.map g).comap (Scheme.ΓSpecIso (.of B)).hom.hom := by
  let f := Spec.map (CommRingCat.ofHom g)
  let q := Spec.map (CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField))
  let e := Spec.map (Scheme.Spec.residueFieldIso (.of A) y).inv
  have he : e ≫ q = (Spec (.of A)).fromSpecResidueField y :=
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of A) y
  let c := pullback.map f ((Spec (.of A)).fromSpecResidueField y) f q
    (𝟙 _) e (𝟙 _) (by simp) (by simpa using he.symm)
  letI : IsIso c := by dsimp [c, e]; infer_instance
  have hc : c ≫ pullback.fst f q = f.fiberι y := by
    simp [c, Scheme.Hom.fiberι]
  rw [← hc, Scheme.Hom.ker_comp_of_isIso]
  have h := cubicClosedPointSerreFiniteZeroResidual_affineSurjectiveFibre_kernel_top
    g (algebraMap A y.asIdeal.ResidueField) y.asIdeal.algebraMap_residueField_surjective
  simpa only [Ideal.ker_algebraMap_residueField] using h

/-- The actual closed scheme fibre stalk is the ambient stalk modulo the
actual extended closed-point ideal germ. -/
def cubicClosedPointSerreFiniteZeroResidual_nativeAffineFibre_stalkRingEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (y : Spec (.of A)) [y.asIdeal.IsMaximal]
    (z : (Spec.map (CommRingCat.ofHom g)).fiber y) :
    let i := (Spec.map (CommRingCat.ofHom g)).fiberι y
    ((Spec (.of B)).presheaf.stalk (i z) ⧸
      ((y.asIdeal.map g).comap (Scheme.ΓSpecIso (.of B)).hom.hom).map
        ((Spec (.of B)).presheaf.germ ⊤ (i z) (by trivial)).hom) ≃+*
      ((Spec.map (CommRingCat.ofHom g)).fiber y).presheaf.stalk z := by
  let i := (Spec.map (CommRingCat.ofHom g)).fiberι y
  letI : IsClosedImmersion ((Spec (.of A)).fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr inferInstance)
  letI : IsClosedImmersion i := by change IsClosedImmersion (pullback.fst _ _); infer_instance
  let e := cubicClosedPointSerreFiniteZeroResidual_affineIdeal_quotientStalkRingEquiv
    i ⟨⊤, isAffineOpen_top _⟩ z (by trivial)
  exact (Ideal.quotEquivOfEq
    (congrArg (fun J : Ideal Γ(Spec (.of B), ⊤) =>
      J.map ((Spec (.of B)).presheaf.germ ⊤ (i z) (by trivial)).hom)
      (cubicClosedPointSerreFiniteZeroResidual_nativeAffineFibre_kernel_top g y)).symm).trans e

end PfaffianDescent
