import PfaffianDescent.SmallCoverCechCoefficientMap
import PfaffianDescent.CubicQuadraticRestrictionDiagram

/-! # Actual intrinsic and pushforward Cech multiplication on a cubic -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

def cubicIntrinsicCechMultiplication
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m d : ℕ) (q : grading (equationIdeal p hp) d) :
    quotientNegativeTwistCechComplex (equationIdeal p hp) (m + d) ⟶
      quotientNegativeTwistCechComplex (equationIdeal p hp) m :=
  (CategoryTheory.cechComplexFunctor (quotientCoordinateOpen (equationIdeal p hp))).map
    (mulHomogeneousPresheaf (grading (equationIdeal p hp)) q m)

def cubicPushforwardCechMultiplication
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m d : ℕ) (q : grading (equationIdeal p hp) d) :
    cubicPushforwardNegativeTwistCechComplex K p hp (m + d) ⟶
      cubicPushforwardNegativeTwistCechComplex K p hp m :=
  smallCoverCechCoefficientMap (Proj PS).ringCatSheaf (p3StandardOpen K)
    ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
      (mulHomogeneous (grading (equationIdeal p hp)) q m))

set_option backward.isDefEq.respectTransparency false in
theorem cubicPushforwardCechTermComponentIso_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m d n : ℕ) (q : grading (equationIdeal p hp) d)
    (f : Fin (n + 1) → Fin 4) :
    ((PresheafOfModules.toPresheaf (Proj PS).ringCatSheaf.obj).map
      (((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
        (mulHomogeneous (grading (equationIdeal p hp)) q m)).val)).app
          (op (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen K (f a))) ≫
      (cubicPushforwardCechTermComponentIso K p hp m n f).hom =
    (cubicPushforwardCechTermComponentIso K p hp (m + d) n f).hom ≫
      (mulHomogeneousPresheaf (grading (equationIdeal p hp)) q m).app
        (op (∏ᶜ fun a : Fin (n + 1) =>
          quotientCoordinateOpen (equationIdeal p hp) (f a))) := by
  change (mulHomogeneousPresheaf (grading (equationIdeal p hp)) q m).app _ ≫
      (modulePresheaf (grading (equationIdeal p hp)) m).presheaf.map _ =
    (modulePresheaf (grading (equationIdeal p hp)) (m + d)).presheaf.map _ ≫
      (mulHomogeneousPresheaf (grading (equationIdeal p hp)) q m).app _
  exact ((mulHomogeneousPresheaf (grading (equationIdeal p hp)) q m).naturality _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual pushforward/intrinsic cochain identification commutes with
actual multiplication by every homogeneous section. -/
theorem cubicPushforwardCechTermIso_mulHomogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m d n : ℕ) (q : grading (equationIdeal p hp) d) :
    (cubicPushforwardCechMultiplication K p hp m d q).f n ≫
      (cubicPushforwardCechTermIso K p hp m n).hom =
    (cubicPushforwardCechTermIso K p hp (m + d) n).hom ≫
      (cubicIntrinsicCechMultiplication K p hp m d q).f n := by
  let a := (PresheafOfModules.toPresheaf (Proj PS).ringCatSheaf.obj).map
    (((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
      (mulHomogeneous (grading (equationIdeal p hp)) q m)).val)
  let b := mulHomogeneousPresheaf (grading (equationIdeal p hp)) q m
  change (CategoryTheory.Limits.Pi.map fun f : Fin (n + 1) → Fin 4 =>
      a.app (op (∏ᶜ fun i : Fin (n + 1) => p3StandardOpen K (f i)))) ≫
      (CategoryTheory.Limits.Pi.map fun f =>
        (cubicPushforwardCechTermComponentIso K p hp m n f).hom) =
    (CategoryTheory.Limits.Pi.map fun f =>
      (cubicPushforwardCechTermComponentIso K p hp (m + d) n f).hom) ≫
      (CategoryTheory.Limits.Pi.map fun f : Fin (n + 1) → Fin 4 =>
        b.app (op (∏ᶜ fun i : Fin (n + 1) =>
          quotientCoordinateOpen (equationIdeal p hp) (f i))))
  rw [CategoryTheory.Limits.Pi.map_comp_map, CategoryTheory.Limits.Pi.map_comp_map]
  congr 1

end PfaffianDescent.ProjectiveNegativeTwist
