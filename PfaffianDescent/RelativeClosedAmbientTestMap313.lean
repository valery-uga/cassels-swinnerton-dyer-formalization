import PfaffianDescent.NativeClosedFiniteFlatPointEquiv313
import PfaffianDescent.RelativeHilbertFamily197

/-! SOURCE ONLY313. Original closed ambient and original family197 on ALL
native slice tests. Closed embedding, its entire kernel, and Cartesian
naturality squares are derived internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X B : Scheme.{u}} (j : Z ⟶ X) (F : X ⟶ B) (T : Over B)

def relativeClosedAmbientTestMap313 :
    pullback T.hom (j ≫ F) ⟶ pullback T.hom F :=
  pullback.lift (pullback.fst T.hom (j ≫ F))
    (pullback.snd T.hom (j ≫ F) ≫ j)
    ((pullback.condition (f := T.hom) (g := j ≫ F)).trans (Category.assoc _ _ _).symm)

lemma relativeClosedAmbientTestMap_toTest313 :
    relativeClosedAmbientTestMap313 j F T ≫ relativeHilbertFamily197 F T =
      relativeHilbertFamily197 (j ≫ F) T :=
  pullback.lift_fst _ _ _

lemma relativeClosedAmbientTestMap_toOriginal313 :
    relativeClosedAmbientTestMap313 j F T ≫ pullback.snd T.hom F =
      pullback.snd T.hom (j ≫ F) ≫ j :=
  pullback.lift_snd _ _ _

lemma relativeClosedAmbientTestMap_isPullback313 :
    IsPullback (relativeClosedAmbientTestMap313 j F T)
      (pullback.snd T.hom (j ≫ F)) (pullback.snd T.hom F) j := by
  have Houter : IsPullback (pullback.snd T.hom (j ≫ F))
      (relativeClosedAmbientTestMap313 j F T ≫ relativeHilbertFamily197 F T)
      (j ≫ F) T.hom := by
    rw [relativeClosedAmbientTestMap_toTest313]
    exact (IsPullback.of_hasPullback T.hom (j ≫ F)).flip
  exact (Houter.of_bot (relativeClosedAmbientTestMap_toOriginal313 j F T).symm
    (IsPullback.of_hasPullback T.hom F).flip).flip

variable [IsClosedImmersion j]

lemma relativeClosedAmbientTestMap_isClosedImmersion313 :
    IsClosedImmersion (relativeClosedAmbientTestMap313 j F T) :=
  MorphismProperty.of_isPullback (relativeClosedAmbientTestMap_isPullback313 j F T).flip
    (inferInstance : IsClosedImmersion j)

lemma relativeClosedAmbientTestMap_kernel313 :
    (relativeClosedAmbientTestMap313 j F T).ker = j.ker.comap (pullback.snd T.hom F) :=
  (wholeIdeal_comap_eq_of_isPullback195 (pullback.snd T.hom (j ≫ F))
    (relativeClosedAmbientTestMap313 j F T) j (pullback.snd T.hom F)
    (relativeClosedAmbientTestMap_isPullback313 j F T).flip).symm

omit [IsClosedImmersion j] in
set_option backward.isDefEq.respectTransparency.types false in
lemma relativeClosedAmbientTestMap_natural313 {T0 T1 : Over B} (a : T0 ⟶ T1) :
    relativeHilbertAmbientMap197 (j ≫ F) a ≫ relativeClosedAmbientTestMap313 j F T1 =
      relativeClosedAmbientTestMap313 j F T0 ≫ relativeHilbertAmbientMap197 F a := by
  apply pullback.hom_ext
  · change (relativeHilbertAmbientMap197 (j ≫ F) a ≫
        relativeClosedAmbientTestMap313 j F T1) ≫ relativeHilbertFamily197 F T1 =
      (relativeClosedAmbientTestMap313 j F T0 ≫ relativeHilbertAmbientMap197 F a) ≫
        relativeHilbertFamily197 F T1
    calc
      _ = relativeHilbertAmbientMap197 (j ≫ F) a ≫ relativeHilbertFamily197 (j ≫ F) T1 :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => relativeHilbertAmbientMap197 (j ≫ F) a ≫ k)
            (relativeClosedAmbientTestMap_toTest313 j F T1))
      _ = relativeHilbertFamily197 (j ≫ F) T0 ≫ a.left :=
        relativeHilbertAmbientMap_fst197 (j ≫ F) a
      _ = (relativeClosedAmbientTestMap313 j F T0 ≫ relativeHilbertFamily197 F T0) ≫ a.left :=
        congrArg (fun k => k ≫ a.left) (relativeClosedAmbientTestMap_toTest313 j F T0).symm
      _ = relativeClosedAmbientTestMap313 j F T0 ≫
          (relativeHilbertAmbientMap197 F a ≫ relativeHilbertFamily197 F T1) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => relativeClosedAmbientTestMap313 j F T0 ≫ k)
            (relativeHilbertAmbientMap_fst197 F a).symm)
      _ = _ := (Category.assoc _ _ _).symm
  · calc
      _ = relativeHilbertAmbientMap197 (j ≫ F) a ≫
          (pullback.snd T1.hom (j ≫ F) ≫ j) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => relativeHilbertAmbientMap197 (j ≫ F) a ≫ k)
            (relativeClosedAmbientTestMap_toOriginal313 j F T1))
      _ = (relativeHilbertAmbientMap197 (j ≫ F) a ≫ pullback.snd T1.hom (j ≫ F)) ≫ j :=
        (Category.assoc _ _ _).symm
      _ = pullback.snd T0.hom (j ≫ F) ≫ j :=
        congrArg (fun k => k ≫ j) (relativeHilbertAmbientMap_snd197 (j ≫ F) a)
      _ = relativeClosedAmbientTestMap313 j F T0 ≫ pullback.snd T0.hom F :=
        (relativeClosedAmbientTestMap_toOriginal313 j F T0).symm
      _ = relativeClosedAmbientTestMap313 j F T0 ≫
          (relativeHilbertAmbientMap197 F a ≫ pullback.snd T1.hom F) :=
        congrArg (fun k => relativeClosedAmbientTestMap313 j F T0 ≫ k)
          (relativeHilbertAmbientMap_snd197 F a).symm
      _ = _ := (Category.assoc _ _ _).symm

omit [IsClosedImmersion j] in
lemma relativeClosedAmbientPulledIdeal_natural313 {T0 T1 : Over B} (a : T0 ⟶ T1) :
    (j.ker.comap (pullback.snd T1.hom F)).comap (relativeHilbertAmbientMap197 F a) =
      j.ker.comap (pullback.snd T0.hom F) :=
  (j.ker.comap_comp (relativeHilbertAmbientMap197 F a) (pullback.snd T1.hom F)).symm.trans
    (congrArg j.ker.comap (relativeHilbertAmbientMap_snd197 F a))

set_option backward.isDefEq.respectTransparency.types false in
lemma relativeClosedAmbientTestMap_natural_isPullback313 {T0 T1 : Over B} (a : T0 ⟶ T1) :
    IsPullback (relativeHilbertAmbientMap197 (j ≫ F) a)
      (relativeClosedAmbientTestMap313 j F T0) (relativeClosedAmbientTestMap313 j F T1)
      (relativeHilbertAmbientMap197 F a) := by
  letI := relativeClosedAmbientTestMap_isClosedImmersion313 j F T0
  letI := relativeClosedAmbientTestMap_isClosedImmersion313 j F T1
  have hk : (relativeClosedAmbientTestMap313 j F T1).ker.comap
      (relativeHilbertAmbientMap197 F a) = (relativeClosedAmbientTestMap313 j F T0).ker :=
    (congrArg (fun K => K.comap (relativeHilbertAmbientMap197 F a))
      (relativeClosedAmbientTestMap_kernel313 j F T1)).trans
      ((relativeClosedAmbientPulledIdeal_natural313 j F a).trans
        (relativeClosedAmbientTestMap_kernel313 j F T0).symm)
  exact (isPullback_of_isClosedImmersion (relativeClosedAmbientTestMap313 j F T0)
    (relativeClosedAmbientTestMap313 j F T1) (relativeHilbertAmbientMap197 (j ≫ F) a)
    (relativeHilbertAmbientMap197 F a) (relativeClosedAmbientTestMap_natural313 j F a).symm hk).flip

end PfaffianDescent
end
