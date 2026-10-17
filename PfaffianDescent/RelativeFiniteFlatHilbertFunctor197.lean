import PfaffianDescent.FiniteFlatHilbertBaseChangeLaws197
import PfaffianDescent.RelativeHilbertFamily197

/-! SOURCE ONLY197. Literal degree-n relative finite-flat Hilbert point
functor of the SAME original family on (Over B)^op. No representability,
local finite presentation, scheme smoothness, or henselian lift asserted. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Literal finite-flat degree-n closed-subscheme point functor. The test
object T uses its actual scheme map to the original base B; all maps are
whole ideal-sheaf pullback along the native ambient Cartesian map. -/
def relativeFiniteFlatHilbertFunctor197 {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ) :
    (Over B)ᵒᵖ ⥤ Type u where
  obj T := FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T.unop) n
  map h := ↾fun I => finiteFlatHilbertBaseChange195
    (relativeHilbertAmbientMap197 F h.unop)
    (relativeHilbertFamily197 F _) (relativeHilbertFamily197 F _) h.unop.left
    (relativeHilbertAmbientMap_isPullback197 F h.unop) n I
  map_id T := by
    apply ConcreteCategory.ext_apply
    intro I
    apply Subtype.ext
    change I.val.comap (relativeHilbertAmbientMap197 F (𝟙 T.unop)) = I.val
    rw [relativeHilbertAmbientMap_id197]
    exact I.val.comap_id
  map_comp f g := by
    apply ConcreteCategory.ext_apply
    intro I
    apply Subtype.ext
    change I.val.comap (relativeHilbertAmbientMap197 F (f ≫ g).unop) =
      (I.val.comap (relativeHilbertAmbientMap197 F f.unop)).comap
        (relativeHilbertAmbientMap197 F g.unop)
    rw [unop_comp, relativeHilbertAmbientMap_comp197]
    exact I.val.comap_comp (relativeHilbertAmbientMap197 F g.unop)
      (relativeHilbertAmbientMap197 F f.unop)

lemma relativeFiniteFlatHilbertFunctor197_obj
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ) (T : Over B) :
    (relativeFiniteFlatHilbertFunctor197 F n).obj (.op T) =
      FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n := rfl

/-- The actual functor map preserves the entire pulled-back ideal. -/
lemma relativeFiniteFlatHilbertFunctor197_map_ideal
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ)
    {T0 T1 : Over B} (h : T0 ⟶ T1)
    (I : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T1) n) :
    ((relativeFiniteFlatHilbertFunctor197 F n).map h.op I).val =
      I.val.comap (relativeHilbertAmbientMap197 F h) := rfl

/-- Exact compatibility with195's Cartesian base-change map on the
original family; not merely equality of support or isomorphism classes. -/
lemma relativeFiniteFlatHilbertFunctor197_map_eq_baseChange195
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ)
    {T0 T1 : Over B} (h : T0 ⟶ T1)
    (I : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T1) n) :
    (relativeFiniteFlatHilbertFunctor197 F n).map h.op I =
      finiteFlatHilbertBaseChange195 (relativeHilbertAmbientMap197 F h)
        (relativeHilbertFamily197 F T0) (relativeHilbertFamily197 F T1) h.left
        (relativeHilbertAmbientMap_isPullback197 F h) n I := rfl

end PfaffianDescent
