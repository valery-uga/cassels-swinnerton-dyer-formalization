import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! SOURCE ONLY197. The original family is pulled back on the ACTUAL
slice category. Its map square is derived from native pullback pasting. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Actual family over an arbitrary original-base test scheme. -/
def relativeHilbertFamily197 {X B : Scheme.{u}} (F : X ⟶ B) (T : Over B) :
    pullback T.hom F ⟶ T.left := pullback.fst T.hom F

/-- Native slice pullback map on the actual ambient schemes. -/
def relativeHilbertAmbientMap197 {X B : Scheme.{u}} (F : X ⟶ B)
    {T0 T1 : Over B} (h : T0 ⟶ T1) :
    pullback T0.hom F ⟶ pullback T1.hom F :=
  ((Over.pullback F).map h).left

lemma relativeHilbertAmbientMap_fst197 {X B : Scheme.{u}} (F : X ⟶ B)
    {T0 T1 : Over B} (h : T0 ⟶ T1) :
    relativeHilbertAmbientMap197 F h ≫ relativeHilbertFamily197 F T1 =
      relativeHilbertFamily197 F T0 ≫ h.left := by
  simp [relativeHilbertAmbientMap197, relativeHilbertFamily197, Over.pullback_map_left,
    pullback.lift_fst]

lemma relativeHilbertAmbientMap_snd197 {X B : Scheme.{u}} (F : X ⟶ B)
    {T0 T1 : Over B} (h : T0 ⟶ T1) :
    relativeHilbertAmbientMap197 F h ≫ pullback.snd T1.hom F =
      pullback.snd T0.hom F := by
  simp [relativeHilbertAmbientMap197, Over.pullback_map_left, pullback.lift_snd]

lemma relativeHilbertAmbientMap_id197 {X B : Scheme.{u}} (F : X ⟶ B)
    (T : Over B) : relativeHilbertAmbientMap197 F (𝟙 T) = 𝟙 _ := by
  exact congrArg (fun h : (Over.pullback F).obj T ⟶ (Over.pullback F).obj T => h.left)
    ((Over.pullback F).map_id T)

lemma relativeHilbertAmbientMap_comp197 {X B : Scheme.{u}} (F : X ⟶ B)
    {T0 T1 T2 : Over B} (h : T0 ⟶ T1) (g : T1 ⟶ T2) :
    relativeHilbertAmbientMap197 F (h ≫ g) =
      relativeHilbertAmbientMap197 F h ≫ relativeHilbertAmbientMap197 F g := by
  exact congrArg (fun k : (Over.pullback F).obj T0 ⟶ (Over.pullback F).obj T2 => k.left)
    ((Over.pullback F).map_comp h g)

/-- A morphism of actual original-base test schemes induces a Cartesian
family square. No target Cartesian square is a caller premise. -/
lemma relativeHilbertAmbientMap_isPullback197
    {X B : Scheme.{u}} (F : X ⟶ B) {T0 T1 : Over B} (h : T0 ⟶ T1) :
    IsPullback (relativeHilbertAmbientMap197 F h)
      (relativeHilbertFamily197 F T0) (relativeHilbertFamily197 F T1) h.left := by
  have Hwhole : IsPullback
      (relativeHilbertAmbientMap197 F h ≫ pullback.snd T1.hom F)
      (relativeHilbertFamily197 F T0) F (h.left ≫ T1.hom) := by
    rw [relativeHilbertAmbientMap_snd197, Over.w h]
    exact (IsPullback.of_hasPullback T0.hom F).flip
  exact Hwhole.of_right (relativeHilbertAmbientMap_fst197 F h)
    (IsPullback.of_hasPullback T1.hom F).flip

end PfaffianDescent
