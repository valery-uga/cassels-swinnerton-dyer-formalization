import PfaffianDescent.RelativeHilbertFamily197

/-! Construct the exact relative197 ambient pair Cartesian square from
an actual original-base parameter square. This is a structural input for
global universal-family descent; no ambient comparison is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false

/-- Literal197 ambients carry every actual Cartesian parameter pair to
an actual Cartesian ambient pair. Both the ambient commutation and the
outer pullback are DERIVED from the original maps and native197 squares. -/
theorem relativeHilbertAmbientMap_cartesian_of_sliceCartesian001
    {X B : Scheme.{u}} (F : X ⟶ B) {W HU HV H : Over B}
    (i : W ⟶ HU) (t : W ⟶ HV) (u : HU ⟶ H) (v : HV ⟶ H)
    (hPair : IsPullback i.left t.left u.left v.left) :
    IsPullback (relativeHilbertAmbientMap197 F i) (relativeHilbertAmbientMap197 F t)
      (relativeHilbertAmbientMap197 F u) (relativeHilbertAmbientMap197 F v) := by
  have hComm : i ≫ u = t ≫ v := by
    apply Over.OverMorphism.ext
    exact hPair.w
  have hAmbientComm : relativeHilbertAmbientMap197 F i ≫ relativeHilbertAmbientMap197 F u =
      relativeHilbertAmbientMap197 F t ≫ relativeHilbertAmbientMap197 F v := by
    rw [← relativeHilbertAmbientMap_comp197, hComm, relativeHilbertAmbientMap_comp197]
  have hOuter : IsPullback (relativeHilbertAmbientMap197 F i)
      (relativeHilbertAmbientMap197 F t ≫ relativeHilbertFamily197 F HV)
      (relativeHilbertAmbientMap197 F u ≫ relativeHilbertFamily197 F H) v.left := by
    rw [relativeHilbertAmbientMap_fst197, relativeHilbertAmbientMap_fst197]
    exact (relativeHilbertAmbientMap_isPullback197 F i).paste_vert hPair
  exact hOuter.of_bot hAmbientComm (relativeHilbertAmbientMap_isPullback197 F v)

end PfaffianDescent
end
