import PfaffianDescent.RelativeOpenContainedPointEquiv315
import Mathlib.CategoryTheory.Types.Basic

/-! SOURCE ONLY315. Natural equivalence of ORIGINAL relative chart families
with the ENTIRE-open-contained ambient subfunctor on ALL scheme tests. This
is a point-functor theorem, not parameter-scheme representability. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X B : Scheme.{u}} (U : X.Opens) (F : X ⟶ B) (n : ℕ) [IsSeparated F]

/-- Actual Cartesian base change preserves the geometric entire-family condition. -/
def relativeOpenContainedPointMap315 {T0 T1 : Over B} (a : T0 ⟶ T1)
    (P : relativeOpenContainedPoint315 U F n T1) : relativeOpenContainedPoint315 U F n T0 := by
  let Q := (relativeOpenContainedPointEquiv315 U F n T1).symm P
  let Q0 := (relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n).map a.op Q
  have hP : relativeOpenFiniteFlatPointPush315 U F n T1 Q = P.val :=
    (relativeOpenContainedPointEquiv_push315 U F n T1 Q).symm.trans
      (congrArg Subtype.val ((relativeOpenContainedPointEquiv315 U F n T1).apply_symm_apply P))
  have hmap : (relativeFiniteFlatHilbertFunctor197 F n).map a.op P.val =
      ((relativeOpenContainedPointEquiv315 U F n T0) Q0).val :=
    (congrArg (fun R => (relativeFiniteFlatHilbertFunctor197 F n).map a.op R) hP).symm.trans
      ((relativeOpenFiniteFlatPointPush_natural315 U F n a Q).symm.trans
        (relativeOpenContainedPointEquiv_push315 U F n T0 Q0).symm)
  refine ⟨(relativeFiniteFlatHilbertFunctor197 F n).map a.op P.val, ?_⟩
  exact hmap.symm ▸ ((relativeOpenContainedPointEquiv315 U F n T0) Q0).property

lemma relativeOpenContainedPointMap_wholeIdeal315 {T0 T1 : Over B} (a : T0 ⟶ T1)
    (P : relativeOpenContainedPoint315 U F n T1) :
    (relativeOpenContainedPointMap315 U F n a P).val.val =
      P.val.val.comap (relativeHilbertAmbientMap197 F a) := rfl

/-- Native ambient subfunctor: the actual whole subscheme lies in the actual open chart. -/
def relativeOpenContainedFiniteFlatFunctor315 : (Over B)ᵒᵖ ⥤ Type u where
  obj T := relativeOpenContainedPoint315 U F n T.unop
  map a := ↾fun P => relativeOpenContainedPointMap315 U F n a.unop P
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

lemma relativeOpenContainedPointEquiv_natural315 {T0 T1 : Over B} (a : T0 ⟶ T1)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T1) n) :
    (relativeOpenContainedPointEquiv315 U F n T0)
      ((relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n).map a.op Q) =
    relativeOpenContainedPointMap315 U F n a ((relativeOpenContainedPointEquiv315 U F n T1) Q) := by
  apply Subtype.ext
  exact (relativeOpenContainedPointEquiv_push315 U F n T0
    ((relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n).map a.op Q)).trans
      ((relativeOpenFiniteFlatPointPush_natural315 U F n a Q).trans
        (congrArg (fun R => (relativeFiniteFlatHilbertFunctor197 F n).map a.op R)
          (relativeOpenContainedPointEquiv_push315 U F n T1 Q).symm))

/-- Genuine ALL-test natural equivalence, derived from original open factorization. -/
def relativeOpenContainedFiniteFlatFunctorIso315 :
    relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ relativeOpenContainedFiniteFlatFunctor315 U F n :=
  NatIso.ofComponents (fun T => (relativeOpenContainedPointEquiv315 U F n T.unop).toIso)
    (by
      intro T0 T1 a
      apply ConcreteCategory.ext_apply
      intro Q
      change (relativeOpenContainedPointEquiv315 U F n T1.unop)
          ((relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n).map a Q) =
        relativeOpenContainedPointMap315 U F n a.unop
          ((relativeOpenContainedPointEquiv315 U F n T0.unop) Q)
      exact relativeOpenContainedPointEquiv_natural315 U F n a.unop Q)

lemma relativeOpenContainedFiniteFlatFunctorIso_wholeIdeal315 (T : Over B)
    (Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (U.ι ≫ F) T) n) :
    ((relativeOpenContainedFiniteFlatFunctorIso315 U F n).hom.app (.op T) Q).val.val =
      Q.val.map (relativeClosedAmbientTestMap313 U.ι F T) :=
  relativeOpenContainedPointEquiv_wholeIdeal315 U F n T Q

lemma relativeOpenContainedFiniteFlatFunctorIso_inv_ambientIdeal315 (T : Over B)
    (P : relativeOpenContainedPoint315 U F n T) :
    ((relativeOpenContainedFiniteFlatFunctorIso315 U F n).inv.app (.op T) P).val.map
      (relativeClosedAmbientTestMap313 U.ι F T) = P.val.val :=
  relativeOpenContainedPointEquiv_inv_ambientIdeal315 U F n T P

lemma relativeOpenContainedFiniteFlatFunctorIso_inv_comap315 (T : Over B)
    (P : relativeOpenContainedPoint315 U F n T) :
    ((relativeOpenContainedFiniteFlatFunctorIso315 U F n).inv.app (.op T) P).val =
      P.val.val.comap (relativeClosedAmbientTestMap313 U.ι F T) :=
  relativeOpenContainedPointEquiv_inv_comap315 U F n T P

end PfaffianDescent
end
