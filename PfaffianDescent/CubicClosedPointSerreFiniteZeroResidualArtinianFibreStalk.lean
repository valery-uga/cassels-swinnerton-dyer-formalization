import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Literal stalk rings on finite fibres are Artinian -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u

/-- Local Artinianness on affine charts passes to the actual native stalk. -/
theorem cubicClosedPointSerreFiniteZeroResidual_isArtinianRing_stalk
    (X : Scheme.{u}) [IsLocallyArtinian X] (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := x) (by simp)
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  letI := hU.isLocalization_stalk (⟨x, hx⟩ : U)
  letI : IsArtinianRing Γ(X, U) :=
    IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨U, hU⟩
  exact IsArtinianRing.localization_artinian
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)

/-- In particular, a locally quasi-finite morphism has Artinian actual fibre
stalk rings; no quotient or dimension certificate is supplied. -/
theorem cubicClosedPointSerreFiniteZeroResidual_isArtinianRing_fibre_stalk
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (y : Y) (z : f.fiber y) :
    IsArtinianRing ((f.fiber y).presheaf.stalk z) :=
  cubicClosedPointSerreFiniteZeroResidual_isArtinianRing_stalk _ z

/-- A closed embedding of an actual quasi-finite fibre sends each point to
an actual closed point of the ambient fibre. -/
theorem cubicClosedPointSerreFiniteZeroResidual_closed_image_of_quasiFinite_fibre
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (y : Y) (i : f.fiber y ⟶ T) [IsClosedImmersion i] (z : f.fiber y) :
    IsClosed ({i z} : Set T) := by
  simpa only [Set.image_singleton] using i.isClosedEmbedding.isClosedMap
    ({z} : Set (f.fiber y)) isClosed_singleton

end PfaffianDescent
