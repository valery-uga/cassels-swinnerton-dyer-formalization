import PfaffianDescent.OriginalCubicPhysicalArtinianLifts
import PfaffianDescent.OriginalCubicRelativeSurfaceDimension

/-!
Global Hilbert-scheme smoothness for a homogeneous lift of a nonzero smooth
cubic over the residue field of a Noetherian local base. Ambient smoothness,
the surface conditions on field-valued Artin tests, physical lifting, and
smoothness and flatness of the original global Hilbert object are derived
from these original inputs.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

theorem originalLiftedCubicGlobalHilbert_smooth_flat001
    {R k : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) R) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) (he : q.map b = p)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) :
    Smooth (originalNormalizedPolynomialGlobalHilbertObject001 q hq n hn).hom ∧
      Flat (originalNormalizedPolynomialGlobalHilbertObject001 q hq n hn).hom := by
  letI : SmoothOfRelativeDimension 2 (hypersurfaceToBase q hq) :=
    originalLocalCubic_smoothOfRelativeDimension_two_of_reduction001 b hb q hq p hp hp0 he
  letI : Smooth (hypersurfaceToBase q hq) :=
    SmoothOfRelativeDimension.smooth 2 (hypersurfaceToBase q hq)
  have hq0 : q.map b ≠ 0 := by rw [he]; exact hp0
  have hres : q.map (IsLocalRing.residue R) ≠ 0 :=
    polynomial_map_ne_zero_every_field_of_nonzero_residue001 b hb q hq0
      (IsLocalRing.residue R)
  exact originalNormalizedPolynomialGlobalHilbert_smooth_flat_primitive_smooth_cubic001
    q hq hres n hn

end PfaffianDescent
end
