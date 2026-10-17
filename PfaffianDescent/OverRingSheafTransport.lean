import PfaffianDescent.SheafModulePushforwardExact

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- The explicit transport from the underlying over-site ring sheaf to the
commutative over-site ring sheaf is left exact. -/
theorem commRingSheafOverToRingSheafTransport_preservesFiniteLimits
    (R : Sheaf J CommRingCat.{u}) (X : C) :
    PreservesFiniteLimits
      (SheafOfModules.pushforward.{u} (J := J.over X) (K := J.over X)
        (S := commRingSheafToRingSheaf (commRingSheafOver R X))
        (R := (commRingSheafToRingSheaf R).over X) (F := 𝟭 (Over X))
        (commRingSheafOverToRingSheafIso R X).hom) := by
  exact SheafOfModules.pushforward_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency false in
theorem commRingSheafOverToRingSheafTransport_isLeftAdjoint
    (R : Sheaf J CommRingCat.{u}) (X : C) :
    (SheafOfModules.pushforward.{u} (J := J.over X) (K := J.over X)
        (S := commRingSheafToRingSheaf (commRingSheafOver R X))
        (R := (commRingSheafToRingSheaf R).over X) (F := 𝟭 (Over X))
        (commRingSheafOverToRingSheafIso R X).hom).IsLeftAdjoint := by
  let e := commRingSheafOverToRingSheafIso R X
  change (SheafOfModules.pushforward.{u} (J := J.over X) (K := J.over X)
        (S := commRingSheafToRingSheaf (commRingSheafOver R X))
        (R := (commRingSheafToRingSheaf R).over X) (F := 𝟭 (Over X))
        e.hom).IsLeftAdjoint
  letI : IsIso e.hom := e.isIso_hom
  letI : (𝟭 (Over X)).IsLeftAdjoint := Adjunction.id.isLeftAdjoint
  exact SheafOfModules.isLeftAdjoint_pushforward_of_isIso
    (F := 𝟭 (Over X)) (J := J.over X) (K := J.over X)
    (S := commRingSheafToRingSheaf (commRingSheafOver R X))
    (R := (commRingSheafToRingSheaf R).over X) e.hom

set_option backward.isDefEq.respectTransparency false in
theorem commRingSheafOverToRingSheafTransport_preservesFiniteColimits
    (R : Sheaf J CommRingCat.{u}) (X : C) :
    PreservesFiniteColimits
      (SheafOfModules.pushforward.{u} (J := J.over X) (K := J.over X)
        (S := commRingSheafToRingSheaf (commRingSheafOver R X))
        (R := (commRingSheafToRingSheaf R).over X) (F := 𝟭 (Over X))
        (commRingSheafOverToRingSheafIso R X).hom) := by
  let e := commRingSheafOverToRingSheafIso R X
  change PreservesFiniteColimits
    (SheafOfModules.pushforward.{u} (J := J.over X) (K := J.over X)
      (S := commRingSheafToRingSheaf (commRingSheafOver R X))
      (R := (commRingSheafToRingSheaf R).over X) (F := 𝟭 (Over X)) e.hom)
  letI : IsIso e.hom := e.isIso_hom
  letI : (𝟭 (Over X)).IsLeftAdjoint := Adjunction.id.isLeftAdjoint
  letI : (SheafOfModules.pushforward.{u} (J := J.over X) (K := J.over X)
      (S := commRingSheafToRingSheaf (commRingSheafOver R X))
      (R := (commRingSheafToRingSheaf R).over X) (F := 𝟭 (Over X)) e.hom).IsLeftAdjoint := by
    exact commRingSheafOverToRingSheafTransport_isLeftAdjoint R X
  infer_instance

set_option backward.isDefEq.respectTransparency false in
 theorem commRingSheafOverToRingSheafTransport_map_shortExact
    (R : Sheaf J CommRingCat.{u}) (X : C)
    (S : ShortComplex (SheafOfModules ((commRingSheafToRingSheaf R).over X)))
    (hS : S.ShortExact) :
    let G := SheafOfModules.pushforward.{u} (J := J.over X) (K := J.over X)
      (S := commRingSheafToRingSheaf (commRingSheafOver R X))
      (R := (commRingSheafToRingSheaf R).over X) (F := 𝟭 (Over X))
      (commRingSheafOverToRingSheafIso R X).hom
    let hG : G.PreservesZeroMorphisms := by
      letI : G.IsLeftAdjoint := by
        exact commRingSheafOverToRingSheafTransport_isLeftAdjoint R X
      exact Functor.preservesZeroMorphisms_of_isLeftAdjoint G
    (@ShortComplex.map _ _ _ _ _ _ S G hG).ShortExact := by
  let G := SheafOfModules.pushforward.{u} (J := J.over X) (K := J.over X)
      (S := commRingSheafToRingSheaf (commRingSheafOver R X))
      (R := (commRingSheafToRingSheaf R).over X) (F := 𝟭 (Over X))
      (commRingSheafOverToRingSheafIso R X).hom
  let hG : G.PreservesZeroMorphisms := by
    letI : G.IsLeftAdjoint := by
      exact commRingSheafOverToRingSheafTransport_isLeftAdjoint R X
    exact Functor.preservesZeroMorphisms_of_isLeftAdjoint G
  letI : G.PreservesZeroMorphisms := hG
  letI : PreservesFiniteLimits G := by
    exact commRingSheafOverToRingSheafTransport_preservesFiniteLimits R X
  letI : G.IsLeftAdjoint := by
    exact commRingSheafOverToRingSheafTransport_isLeftAdjoint R X
  letI : PreservesFiniteColimits G := by infer_instance
  exact hS.map_of_exact G

end SheafOfModules

end PfaffianDescent
