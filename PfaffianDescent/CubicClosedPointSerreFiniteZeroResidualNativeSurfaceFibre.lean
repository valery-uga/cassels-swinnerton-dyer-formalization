import AllCharacteristics.HypersurfaceCoefficientNaturality
import AllCharacteristics.ProjectiveHypersurfaceClosedDimension
import AllCharacteristics.SmoothSchemeRegularity
import Mathlib.AlgebraicGeometry.Fiber

/-! # Native regular surface stalks on actual constant-cubic fibres -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

def cubicClosedPointSerreFiniteZeroResidual_surfaceFieldFibreIso
    {K S : Type u} [Field K] [CommRing S]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (b : K →+* S) (s : Spec (.of S) ⟶ E)
    (hs : s ≫ k = Spec.map (CommRingCat.ofHom b)) :
    pullback (pullback.snd (hypersurfaceToBase p hp) k) s ≅
      hypersurface (p.map b) (hp.map b) :=
  pullbackLeftPullbackSndIso (hypersurfaceToBase p hp) k s ≪≫
    pullback.congrHom rfl hs ≪≫ (hypersurfaceBaseChangeIso b p hp).symm

/-- At every closed point of an actual constant-cubic fibre, the native
ambient stalk is regular of dimension two.  The fibre identification is
constructed from the actual residue-field point and the Cartesian square. -/
theorem cubicClosedPointSerreFiniteZeroResidual_surface_fibre_stalk_regular_dim_two
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {E : Scheme.{u}} (k : E ⟶ Spec (.of K)) (y : E)
    (x : (pullback.snd (hypersurfaceToBase p hp) k).fiber y)
    (hx : IsClosed ({x} : Set ((pullback.snd (hypersurfaceToBase p hp) k).fiber y))) :
    IsRegularLocalRing (((pullback.snd (hypersurfaceToBase p hp) k).fiber y).presheaf.stalk x) ∧
      ringKrullDim (((pullback.snd (hypersurfaceToBase p hp) k).fiber y).presheaf.stalk x) = 2 := by
  let g := pullback.snd (hypersurfaceToBase p hp) k
  letI : Smooth g := by dsimp [g]; infer_instance
  letI : Smooth (g.fiberToSpecResidueField y) := by
    change Smooth (pullback.snd g (E.fromSpecResidueField y))
    infer_instance
  let S := E.residueField y
  obtain ⟨b, hb⟩ := Spec.map_surjective (E.fromSpecResidueField y ≫ k)
  let e : g.fiber y ≅ hypersurface (p.map b.hom) (hp.map b.hom) :=
    cubicClosedPointSerreFiniteZeroResidual_surfaceFieldFibreIso p hp k b.hom
      (E.fromSpecResidueField y) hb.symm
  have hmap : p.map b.hom ≠ 0 := by
    intro hzero
    apply hp0
    apply (MvPolynomial.map_injective b.hom b.hom.injective)
    simpa using hzero
  have hx' : IsClosed ({e.hom x} : Set (hypersurface (p.map b.hom) (hp.map b.hom))) := by
    simpa only [Set.image_singleton, Scheme.Hom.homeomorph_apply] using
      e.hom.homeomorph.isClosedMap _ hx
  constructor
  · letI : IsRegularRing Γ(Spec S, ⊤) :=
      IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.symm
    exact AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine
      (g.fiberToSpecResidueField y) x
  · rw [← ringKrullDim_eq_of_ringEquiv
      (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv]
    exact ringKrullDim_stalk_projective_hypersurface_eq_two
      (p.map b.hom) (hp.map b.hom) hmap (e.hom x) hx'

end PfaffianDescent
