import PfaffianDescent.FiniteFlatHilbertTestPoints195
import AllCharacteristics.FiniteSubschemeFunctor
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.HopkinsLevitzki

/-! Source only279. Finite-flat test points on locally Noetherian bases have
native local finite presentation and are exactly genuine finite-subscheme data.
All equivalences and base changes retain the SAME entire ideal sheaf. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma finiteFlatHilbertPoint_locallyOfFinitePresentation279
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ) [IsLocallyNoetherian B]
    (I : FiniteFlatHilbertPoint195 F n) :
    LocallyOfFinitePresentation (I.val.subschemeι ≫ F) := by
  letI : IsFinite (I.val.subschemeι ≫ F) := I.property.1
  infer_instance

def finiteSubschemeDatumToHilbertPoint279
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ)
    (I : AllCharacteristics.FiniteSubschemeDatum F n) :
    FiniteFlatHilbertPoint195 F n :=
  ⟨I.val, I.property.1, I.property.2.1, I.property.2.2.2⟩

def finiteFlatHilbertPointToDatum279
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ) [IsLocallyNoetherian B]
    (I : FiniteFlatHilbertPoint195 F n) :
    AllCharacteristics.FiniteSubschemeDatum F n :=
  ⟨I.val, I.property.1, I.property.2.1,
    finiteFlatHilbertPoint_locallyOfFinitePresentation279 F n I, I.property.2.2⟩

def finiteFlatHilbertPointDatumEquiv279
    {X B : Scheme.{u}} (F : X ⟶ B) (n : ℕ) [IsLocallyNoetherian B] :
    FiniteFlatHilbertPoint195 F n ≃ AllCharacteristics.FiniteSubschemeDatum F n where
  toFun := finiteFlatHilbertPointToDatum279 F n
  invFun := finiteSubschemeDatumToHilbertPoint279 F n
  left_inv I := Subtype.ext rfl
  right_inv I := Subtype.ext rfl

lemma finiteSubschemeDatumToHilbertPoint_baseChange279
    {X0 X B0 B : Scheme.{u}}
    (d : X0 ⟶ X) (F0 : X0 ⟶ B0) (F : X ⟶ B) (b : B0 ⟶ B)
    (H : IsPullback d F0 F b) (n : ℕ)
    (I : AllCharacteristics.FiniteSubschemeDatum F n) :
    finiteSubschemeDatumToHilbertPoint279 F0 n
      (AllCharacteristics.FiniteSubschemeDatum.baseChange d b H I) =
    finiteFlatHilbertBaseChange195 d F0 F b H n
      (finiteSubschemeDatumToHilbertPoint279 F n I) :=
  Subtype.ext rfl

lemma finiteFlatHilbertPointToDatum_baseChange279
    {X0 X B0 B : Scheme.{u}} [IsLocallyNoetherian B0] [IsLocallyNoetherian B]
    (d : X0 ⟶ X) (F0 : X0 ⟶ B0) (F : X ⟶ B) (b : B0 ⟶ B)
    (H : IsPullback d F0 F b) (n : ℕ) (I : FiniteFlatHilbertPoint195 F n) :
    finiteFlatHilbertPointToDatum279 F0 n
      (finiteFlatHilbertBaseChange195 d F0 F b H n I) =
    AllCharacteristics.FiniteSubschemeDatum.baseChange d b H
      (finiteFlatHilbertPointToDatum279 F n I) :=
  Subtype.ext rfl

lemma finiteFlatHilbertPoint_artin_locallyOfFinitePresentation279
    {R : Type u} [CommRing R] [IsArtinianRing R] {X : Scheme.{u}}
    (F : X ⟶ Spec (.of R)) (n : ℕ) (I : FiniteFlatHilbertPoint195 F n) :
    LocallyOfFinitePresentation (I.val.subschemeι ≫ F) :=
  finiteFlatHilbertPoint_locallyOfFinitePresentation279 F n I

end PfaffianDescent
