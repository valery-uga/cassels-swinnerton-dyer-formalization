import PfaffianDescent.VoisinCubicCoordinatePreimage

/-!
# Termwise comparison of intrinsic and ambient-pushforward Cech complexes

On every ordered coordinate intersection, sections of the pushed-forward
cubic twist agree with intrinsic sections on the matching quotient
intersection.  This file packages those identifications term by term.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The raw Cech complex of the ambient pushforward of an intrinsic cubic
negative twist, on the four standard opens of projective three-space. -/
noncomputable def cubicPushforwardNegativeTwistCechComplex
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ) :
    CochainComplex AddCommGrpCat ℕ :=
  smallCoverCechComplex (Proj PS).ringCatSheaf (p3StandardOpen K)
    ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
      (sheafOfModules (grading (equationIdeal p hp)) m))

/-- The ambient-pushforward and intrinsic section groups agree on one
ordered coordinate intersection. -/
noncomputable def cubicPushforwardCechTermComponentIso
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    smallCoverCechTermFamily (Proj PS).ringCatSheaf (p3StandardOpen K)
        ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
          (sheafOfModules (grading (equationIdeal p hp)) m)) n f ≅
      quotientCechTermFamily (equationIdeal p hp) m n f := by
  let M := sheafOfModules (grading (equationIdeal p hp)) m
  let h := hypersurfaceToAmbient_preimage_p3CechProduct K p hp n f
  change M.presheaf.obj
      (op ((hypersurfaceToAmbient p hp) ⁻¹ᵁ
        (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen K (f a)))) ≅
    M.presheaf.obj
      (op (∏ᶜ fun a : Fin (n + 1) =>
        quotientCoordinateOpen (equationIdeal p hp) (f a)))
  exact (M.presheaf.mapIso (eqToIso h).op).symm

/-- In every cochain degree, the ambient-pushforward raw Cech term is
isomorphic to the intrinsic cubic-quotient raw Cech term. -/
noncomputable def cubicPushforwardCechTermIso
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m n : ℕ) :
    (cubicPushforwardNegativeTwistCechComplex K p hp m).X n ≅
      (quotientNegativeTwistCechComplex (equationIdeal p hp) m).X n := by
  change (∏ᶜ fun f : Fin (n + 1) → Fin 4 =>
      smallCoverCechTermFamily (Proj PS).ringCatSheaf (p3StandardOpen K)
        ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
          (sheafOfModules (grading (equationIdeal p hp)) m)) n f) ≅
    (∏ᶜ fun f : Fin (n + 1) → Fin 4 =>
      quotientCechTermFamily (equationIdeal p hp) m n f)
  exact Pi.mapIso fun f => cubicPushforwardCechTermComponentIso K p hp m n f

set_option backward.isDefEq.respectTransparency false in
/-- The componentwise pushforward/intrinsic identification commutes with one
Cech face restriction. -/
theorem cubicPushforwardCechTermComponentIso_naturality
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4) :
    let EA := (FormalCoproduct.mk _ (p3StandardOpen K)).cech
    let ES := (FormalCoproduct.mk _
      (quotientCoordinateOpen (equationIdeal p hp))).cech
    let M := sheafOfModules (grading (equationIdeal p hp)) m
    let P := ((Scheme.Modules.pushforward
      (hypersurfaceToAmbient p hp)).obj M).presheaf
    (cubicPushforwardCechTermComponentIso K p hp m n
        (cechDeleteTuple i f)).hom ≫
        M.presheaf.map ((ES.map (SimplexCategory.δ i).op).φ f).op =
      P.map ((EA.map (SimplexCategory.δ i).op).φ f).op ≫
        (cubicPushforwardCechTermComponentIso K p hp m (n + 1) f).hom := by
  dsimp only
  change
    (sheafOfModules (grading (equationIdeal p hp)) m).presheaf.map _ ≫
        (sheafOfModules (grading (equationIdeal p hp)) m).presheaf.map _ =
      (sheafOfModules (grading (equationIdeal p hp)) m).presheaf.map _ ≫
        (sheafOfModules (grading (equationIdeal p hp)) m).presheaf.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The termwise ambient-pushforward/intrinsic isomorphisms intertwine the
successive Cech differentials. -/
theorem cubicPushforwardCechTermIso_d_succ
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (m n : ℕ) :
    (cubicPushforwardCechTermIso K p hp m n).hom ≫
        (quotientNegativeTwistCechComplex
          (equationIdeal p hp) m).d n (n + 1) =
      (cubicPushforwardNegativeTwistCechComplex K p hp m).d n (n + 1) ≫
        (cubicPushforwardCechTermIso K p hp m (n + 1)).hom := by
  exact smallCoverCechPiMapIso_d_succ
    (Proj PS).ringCatSheaf
    (Proj (grading (equationIdeal p hp))).ringCatSheaf
    (p3StandardOpen K) (quotientCoordinateOpen (equationIdeal p hp))
    ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
      (sheafOfModules (grading (equationIdeal p hp)) m))
    (sheafOfModules (grading (equationIdeal p hp)) m)
    (fun q f => cubicPushforwardCechTermComponentIso K p hp m q f)
    (fun q i f =>
      cubicPushforwardCechTermComponentIso_naturality K p hp m q i f)
    n

/-- The raw Cech complex of the intrinsic cubic twist is isomorphic to the
raw Cech complex of its ambient pushforward on the coordinate cover. -/
noncomputable def cubicPushforwardNegativeTwistCechComplexIso
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (m : ℕ) :
    cubicPushforwardNegativeTwistCechComplex K p hp m ≅
      quotientNegativeTwistCechComplex (equationIdeal p hp) m :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => cubicPushforwardCechTermIso K p hp m n)
    (fun i j => by
      rintro (rfl : i + 1 = j)
      exact cubicPushforwardCechTermIso_d_succ K p hp m i)


end PfaffianDescent.ProjectiveNegativeTwist
