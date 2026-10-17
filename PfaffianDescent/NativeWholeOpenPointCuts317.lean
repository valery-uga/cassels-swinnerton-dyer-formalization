import PfaffianDescent.NativeFiniteFlatAmbientIsoTransport317
import PfaffianDescent.NativeOpenContainedFiniteFlatPointEquiv315

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Whole pushed ideal equality forces the whole native source into the open. -/
lemma nativeWholePointPushedOpen_range317 {X T : Scheme.{u}}
    (F : X ⟶ T) [IsSeparated F] (n : ℕ) (U : X.Opens)
    (Q : FiniteFlatHilbertPoint195 (U.ι ≫ F) n) (I : FiniteFlatHilbertPoint195 F n)
    (h : Q.val.map U.ι = I.val) : Set.range I.val.subschemeι ⊆ (U : Set X) := by
  have he : nativeFiniteFlatPointPushOpen314 U.ι F n Q = I :=
    Subtype.ext ((nativeFiniteFlatPointPushOpen_wholeIdeal314 U.ι F n Q).trans h)
  have hp := nativeFiniteFlatPointPushOpen_range315 U.ι F n Q
  have hr : Set.range I.val.subschemeι ⊆ Set.range U.ι :=
    Eq.mp (congrArg (fun J : FiniteFlatHilbertPoint195 F n =>
      Set.range J.val.subschemeι ⊆ Set.range U.ι) he) hp
  simpa only [Scheme.Opens.range_ι] using hr

variable {Y X T : Scheme.{u}} (F : X ⟶ T) [IsSeparated F] (n : ℕ)
variable (a : Y ⟶ X) [IsOpenImmersion a] (G : Y ⟶ T) (hG : a ≫ F = G)
variable (I : FiniteFlatHilbertPoint195 F n)
variable (Q : FiniteFlatHilbertPoint195 (a.opensRange.ι ≫ F) n)
variable (h : Q.val.map a.opensRange.ι = I.val)

include h in
lemma nativeWholePointPushedOpen_chartRange317 : Set.range I.val.subschemeι ⊆ Set.range a :=
  nativeWholePointPushedOpen_range317 F n a.opensRange Q I h

/-- The generic construction is elaborated BEFORE substituting original
Proj/normalized quotient types. Its open/separated dictionaries are explicit. -/
def nativeWholePointPushedOpen_chartPoint317 : FiniteFlatHilbertPoint195 G n :=
  nativeFiniteFlatPointProjectionEq317 hG n
    (nativeOpenContainedFiniteFlatPointLift315 a F n I
      (nativeWholePointPushedOpen_chartRange317 F n a I Q h))

lemma nativeWholePointPushedOpen_chartPoint_wholeIdeal317 :
    (nativeWholePointPushedOpen_chartPoint317 F n a G hG I Q h).val = I.val.comap a :=
  (nativeFiniteFlatPointProjectionEq_wholeIdeal317 hG n
    (nativeOpenContainedFiniteFlatPointLift315 a F n I
      (nativeWholePointPushedOpen_chartRange317 F n a I Q h))).trans
        (nativeOpenContainedFiniteFlatPointLift_comap315 a F n I
          (nativeWholePointPushedOpen_chartRange317 F n a I Q h))

end PfaffianDescent
end
