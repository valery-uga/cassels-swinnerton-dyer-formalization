import PfaffianDescent.MonomialWholeIdealChartOverlapFunctor290

noncomputable section
namespace PfaffianDescent
open Module CategoryTheory
universe u v
variable {A : Type u} [CommRing A] {m n : ℕ}
variable (B C : Fin n → (Fin m →₀ ℕ))

/-- The second chart has the same literal ideal; its basis is derived from the determinant criterion. -/
def monomialOverlapSecondChart293 (x : MonomialWholeIdealChartOverlap290 (A := A) B C) :
    MonomialWholeIdealChart287 (A := A) C :=
  ⟨x.val.val, (wholeIdealMonomialTransitionDet_isUnit_iff290 x.val.val
    (monomialWholeIdealChartBasis287 B x.val) C).mp x.property⟩

lemma monomialOverlapSecondChart_ideal293
    (x : MonomialWholeIdealChartOverlap290 (A := A) B C) :
    (monomialOverlapSecondChart293 B C x).val = x.val.val := rfl

/-- Reverse the overlap using the original B basis on the unchanged ideal. -/
def monomialWholeIdealOverlapFlip293 (x : MonomialWholeIdealChartOverlap290 (A := A) B C) :
    MonomialWholeIdealChartOverlap290 (A := A) C B := by
  refine ⟨monomialOverlapSecondChart293 B C x, ?_⟩
  apply (wholeIdealMonomialTransitionDet_isUnit_iff290 x.val.val
    (monomialWholeIdealChartBasis287 C (monomialOverlapSecondChart293 B C x)) B).mpr
  exact ⟨monomialWholeIdealChartBasis287 B x.val,
    monomialWholeIdealChartBasis_apply287 B x.val⟩

lemma monomialWholeIdealOverlapFlip_ideal293
    (x : MonomialWholeIdealChartOverlap290 (A := A) B C) :
    (monomialWholeIdealOverlapFlip293 B C x).val.val = x.val.val := rfl

lemma monomialWholeIdealOverlapFlip_involution293
    (x : MonomialWholeIdealChartOverlap290 (A := A) B C) :
    monomialWholeIdealOverlapFlip293 C B (monomialWholeIdealOverlapFlip293 B C x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

def monomialWholeIdealOverlapFlipEquiv293 :
    MonomialWholeIdealChartOverlap290 (A := A) B C ≃
      MonomialWholeIdealChartOverlap290 (A := A) C B where
  toFun := monomialWholeIdealOverlapFlip293 B C
  invFun := monomialWholeIdealOverlapFlip293 C B
  left_inv := monomialWholeIdealOverlapFlip_involution293 B C
  right_inv := monomialWholeIdealOverlapFlip_involution293 C B

lemma monomialWholeIdealOverlapFlip_natural293
    {D : Type v} [CommRing D] (kB kC : Fin n) (hkB : B kB = 0) (hkC : C kC = 0)
    (f : A →+* D) (x : MonomialWholeIdealChartOverlap290 (A := A) B C) :
    monomialWholeIdealOverlapFlip293 B C (monomialWholeIdealChartOverlapMap290 B C kB hkB f x) =
      monomialWholeIdealChartOverlapMap290 C B kC hkC f (monomialWholeIdealOverlapFlip293 B C x) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- This natural isomorphism is constructed by literal same-ideal reversal. -/
def monomialWholeIdealOverlapFlipNatIso293
    (R : Type u) [CommRing R] (kB kC : Fin n) (hkB : B kB = 0) (hkC : C kC = 0) :
    monomialWholeIdealChartOverlapFunctor290 R m n B C kB hkB ≅
      monomialWholeIdealChartOverlapFunctor290 R m n C B kC hkC := by
  refine NatIso.ofComponents
    (fun D => (monomialWholeIdealOverlapFlipEquiv293 (A := D) B C).toIso) ?_
  intro D E f
  ext x
  exact monomialWholeIdealOverlapFlip_natural293 B C kB kC hkB hkC f.hom.toRingHom x

variable (D : Fin n → (Fin m →₀ ℕ))

/-- Triple membership is two constructed determinant unit conditions on the same first ideal. -/
def MonomialWholeIdealTripleOverlap293 :=
  {x : MonomialWholeIdealChartOverlap290 (A := A) B C //
    IsUnit (monomialWholeIdealChartTransitionDet290 B D x.val)}

def monomialTripleOverlapFirstLast293
    (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    MonomialWholeIdealChartOverlap290 (A := A) B D := ⟨x.val.val, x.property⟩

/-- The C/D edge is constructed from the proved C and D bases on the unchanged whole ideal. -/
def monomialTripleOverlapSecondLast293
    (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    MonomialWholeIdealChartOverlap290 (A := A) C D := by
  refine ⟨monomialOverlapSecondChart293 B C x.val, ?_⟩
  apply (wholeIdealMonomialTransitionDet_isUnit_iff290 x.val.val.val
    (monomialWholeIdealChartBasis287 C (monomialOverlapSecondChart293 B C x.val)) D).mpr
  exact (wholeIdealMonomialTransitionDet_isUnit_iff290 x.val.val.val
    (monomialWholeIdealChartBasis287 B x.val.val) D).mp x.property

/-- B→C→D and B→D have exactly the same whole-ideal chart datum. -/
lemma monomialTripleOverlap_triangle293
    (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    monomialOverlapSecondChart293 C D (monomialTripleOverlapSecondLast293 B C D x) =
      monomialOverlapSecondChart293 B D (monomialTripleOverlapFirstLast293 B C D x) := by
  apply Subtype.ext
  rfl

end PfaffianDescent
