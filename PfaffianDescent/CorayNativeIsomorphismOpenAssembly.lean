import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option autoImplicit false

/-- Restrict the SAME native morphism to an open covered by constructed
isomorphism opens. This is the ordinary local assembly used below. -/
theorem nativeMorphismRestrict_isIso_of_isomorphismOpenCover001
    {X T : Scheme.{u}} (F : X ⟶ T) (V : T.Opens)
    {ι : Type u} (U : ι → T.Opens)
    (hCover : V ≤ ⨆ i, U i) (hIso : ∀ i, IsIso (F ∣_ U i)) :
    IsIso (F ∣_ V) := by
  let P := MorphismProperty.isomorphisms Scheme.{u}
  let W := fun i => V.ι ⁻¹ᵁ U i
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := P) W
  · apply top_le_iff.mp
    intro x _
    have hx : x.1 ∈ ⨆ i, U i := hCover x.2
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    let R := V.ι ''ᵁ W i
    have hR : R ≤ U i := V.ι.image_preimage_le (U i)
    let A := (U i).ι ⁻¹ᵁ R
    have hImage : (U i).ι ''ᵁ A = R := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hR
    have hDouble : P ((F ∣_ U i) ∣_ A) :=
      IsZariskiLocalAtTarget.restrict (P := P) (hIso i) A
    have hSingle : P (F ∣_ R) := by
      have h := (P.arrow_mk_iso_iff (morphismRestrictRestrict F (U i) A)).mp hDouble
      rw [hImage] at h
      exact h
    exact (P.arrow_mk_iso_iff (morphismRestrictRestrict F V (W i))).mpr hSingle

end PfaffianDescent.Coray
