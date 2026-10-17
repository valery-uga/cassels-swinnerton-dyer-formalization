import PfaffianDescent.RelativeClosedAmbientTestMap313
import PfaffianDescent.NativeClosedWholeIdealBaseChange313
import PfaffianDescent.RelativeFiniteFlatHilbertFunctor197
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Logic.Equiv.Basic

/-! SOURCE ONLY313. Genuine natural equivalence on ALL native scheme tests:
families in the ORIGINAL closed ambient correspond to ambient families
containing its ENTIRE pulled defining ideal. No classification, inverse,
containment criterion for a polynomial locus, or representability premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z X B : Scheme.{u}} (j : Z ⟶ X) (F : X ⟶ B) (n : ℕ)

def relativeClosedAmbientContainedPoint313 (T : Over B) : Type u :=
  {P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n //
    j.ker.comap (pullback.snd T.hom F) ≤ P.val}

def relativeClosedAmbientContainedPointMap313 {T0 T1 : Over B} (a : T0 ⟶ T1)
    (P : relativeClosedAmbientContainedPoint313 j F n T1) :
    relativeClosedAmbientContainedPoint313 j F n T0 := by
  refine ⟨(relativeFiniteFlatHilbertFunctor197 F n).map a.op P.val, ?_⟩
  change j.ker.comap (pullback.snd T0.hom F) ≤
    P.val.val.comap (relativeHilbertAmbientMap197 F a)
  have hh := Scheme.IdealSheafData.comap_mono (relativeHilbertAmbientMap197 F a) P.property
  exact (relativeClosedAmbientPulledIdeal_natural313 j F a) ▸ hh

lemma relativeClosedAmbientContainedPointMap_wholeIdeal313 {T0 T1 : Over B} (a : T0 ⟶ T1)
    (P : relativeClosedAmbientContainedPoint313 j F n T1) :
    (relativeClosedAmbientContainedPointMap313 j F n a P).val.val =
      P.val.val.comap (relativeHilbertAmbientMap197 F a) := rfl

/-- Literal ambient195/197 subfunctor defined by whole-ideal containment. -/
def relativeClosedAmbientContainedFunctor313 : (Over B)ᵒᵖ ⥤ Type u where
  obj T := relativeClosedAmbientContainedPoint313 j F n T.unop
  map a := ↾fun P => relativeClosedAmbientContainedPointMap313 j F n a.unop P
  map_id T := by
    apply ConcreteCategory.ext_apply
    intro P
    apply Subtype.ext
    apply Subtype.ext
    change P.val.val.comap (relativeHilbertAmbientMap197 F (𝟙 T.unop)) = P.val.val
    exact (congrArg P.val.val.comap (relativeHilbertAmbientMap_id197 F T.unop)).trans
      P.val.val.comap_id
  map_comp a b := by
    apply ConcreteCategory.ext_apply
    intro P
    apply Subtype.ext
    apply Subtype.ext
    change P.val.val.comap (relativeHilbertAmbientMap197 F (a ≫ b).unop) =
      (P.val.val.comap (relativeHilbertAmbientMap197 F a.unop)).comap
        (relativeHilbertAmbientMap197 F b.unop)
    rw [unop_comp, relativeHilbertAmbientMap_comp197]
    exact P.val.val.comap_comp _ _

variable [IsClosedImmersion j]

set_option backward.isDefEq.respectTransparency.types false in
/-- Point equivalence retains ORIGINAL closed family j≫F on the actual test. -/
def relativeClosedAmbientPointEquiv313 (T : Over B) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (j ≫ F) T) n ≃
      relativeClosedAmbientContainedPoint313 j F n T := by
  letI := relativeClosedAmbientTestMap_isClosedImmersion313 j F T
  exact (nativeClosedFiniteFlatPointEquiv313 (relativeHilbertFamily197 (j ≫ F) T)
    (relativeHilbertFamily197 F T) (relativeClosedAmbientTestMap313 j F T)
    (relativeClosedAmbientTestMap_toTest313 j F T) n).trans
    (Equiv.subtypeEquivRight (fun P => Iff.of_eq
      (congrArg (fun J => J ≤ P.val) (relativeClosedAmbientTestMap_kernel313 j F T))))

lemma relativeClosedAmbientPointEquiv_wholeIdeal313 (T : Over B)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (j ≫ F) T) n) :
    ((relativeClosedAmbientPointEquiv313 j F n T) Q).val.val =
      Q.val.map (relativeClosedAmbientTestMap313 j F T) := rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma relativeClosedAmbientPointEquiv_inv_ambientIdeal313 (T : Over B)
    (P : relativeClosedAmbientContainedPoint313 j F n T) :
    ((relativeClosedAmbientPointEquiv313 j F n T).symm P).val.map
        (relativeClosedAmbientTestMap313 j F T) = P.val.val := by
  let e := relativeClosedAmbientPointEquiv313 j F n T
  exact (relativeClosedAmbientPointEquiv_wholeIdeal313 j F n T (e.symm P)).symm.trans
    (congrArg (fun Q : relativeClosedAmbientContainedPoint313 j F n T => Q.val.val)
      (e.apply_symm_apply P))

set_option backward.isDefEq.respectTransparency.types false in
/-- Arbitrary native test morphisms preserve the entire embedded family map. -/
lemma relativeClosedAmbientPointEquiv_natural313 {T0 T1 : Over B} (a : T0 ⟶ T1)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (j ≫ F) T1) n) :
    (relativeClosedAmbientPointEquiv313 j F n T0)
        ((relativeFiniteFlatHilbertFunctor197 (j ≫ F) n).map a.op Q) =
      relativeClosedAmbientContainedPointMap313 j F n a
        ((relativeClosedAmbientPointEquiv313 j F n T1) Q) := by
  letI := relativeClosedAmbientTestMap_isClosedImmersion313 j F T1
  apply Subtype.ext
  apply Subtype.ext
  change (Q.val.comap (relativeHilbertAmbientMap197 (j ≫ F) a)).map
      (relativeClosedAmbientTestMap313 j F T0) =
    (Q.val.map (relativeClosedAmbientTestMap313 j F T1)).comap
      (relativeHilbertAmbientMap197 F a)
  exact nativeClosedWholeIdeal_map_comap313 (relativeHilbertAmbientMap197 (j ≫ F) a)
    (relativeClosedAmbientTestMap313 j F T0) (relativeClosedAmbientTestMap313 j F T1)
    (relativeHilbertAmbientMap197 F a) (relativeClosedAmbientTestMap_natural_isPullback313 j F a)
    Q.val

/-- Genuine natural equivalence on ALL original scheme tests, using whole
ideals and original native197 maps in both directions. All n, no field premise. -/
def relativeClosedAmbientFiniteFlatFunctorIso313 :
    relativeFiniteFlatHilbertFunctor197 (j ≫ F) n ≅
      relativeClosedAmbientContainedFunctor313 j F n :=
  NatIso.ofComponents (fun T => (relativeClosedAmbientPointEquiv313 j F n T.unop).toIso)
    (by
      intro T0 T1 a
      apply ConcreteCategory.ext_apply
      intro Q
      change (relativeClosedAmbientPointEquiv313 j F n T1.unop)
          ((relativeFiniteFlatHilbertFunctor197 (j ≫ F) n).map a Q) =
        relativeClosedAmbientContainedPointMap313 j F n a.unop
          ((relativeClosedAmbientPointEquiv313 j F n T0.unop) Q)
      exact relativeClosedAmbientPointEquiv_natural313 j F n a.unop Q)

lemma relativeClosedAmbientFiniteFlatFunctorIso_wholeIdeal313 (T : Over B)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (j ≫ F) T) n) :
    ((relativeClosedAmbientFiniteFlatFunctorIso313 j F n).hom.app (.op T) Q).val.val =
      Q.val.map (relativeClosedAmbientTestMap313 j F T) := rfl

lemma relativeClosedAmbientFiniteFlatFunctorIso_inv_ambientIdeal313 (T : Over B)
    (P : relativeClosedAmbientContainedPoint313 j F n T) :
    ((relativeClosedAmbientFiniteFlatFunctorIso313 j F n).inv.app (.op T) P).val.map
        (relativeClosedAmbientTestMap313 j F T) = P.val.val :=
  relativeClosedAmbientPointEquiv_inv_ambientIdeal313 j F n T P

end PfaffianDescent
end
