import PfaffianDescent.OriginalAffineHilbertPullbackIdentity305
import PfaffianDescent.MonomialGlobalClassifyingUniqueness306

/-! SOURCE ONLY / UNCHECKED. Positive-rank classification of literal affine
finite-flat embedded families by actual fixed-R maps to the same glued H.
Existence and uniqueness are proved by the native305/306 constructions.
No representability, classification or uniqueness outcome is a hypothesis. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Native maps to the actual H, with the literal fixed-base equation. -/
def MonomialFixedBaseHom308
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (m n : ℕ) :=
  { g : Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n //
    g ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) }

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (m n : ℕ)

/-- The inverse classifier is the actual whole universal-family pullback. -/
def monomialFixedBasePointPullback308 (g : MonomialFixedBaseHom308 R A m n) :
    FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n :=
  fixedBaseUniversalFamilyPullback305 R m n g.val g.property

/-- Whole native pullback families determine their actual fixed-R H-maps. -/
lemma monomialFixedBasePointPullback_injective308 :
    Function.Injective (monomialFixedBasePointPullback308 R (A := A) m n) := by
  intro g h he
  apply Subtype.ext
  exact monomialGlobalClassifyingMap_unique306 R m n g.val h.val g.property h.property
    (congrArg Subtype.val he)

/-- Each actual positive-rank finite-flat195 family constructs a fixed-R map,
including the identity of the whole pulled universal ideal. -/
lemma nativeAffineHilbertPoint_fixedBaseHom_exists308
    (hn : 0 < n) (P : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n) :
    ∃ g : MonomialFixedBaseHom308 R A m n,
      P = monomialFixedBasePointPullback308 R m n g := by
  obtain ⟨g, hg, hP⟩ := actualAffineHilbertPoint_isGlobalUniversalPullback305 R P hn
  exact ⟨⟨g, hg⟩, hP⟩

/-- Chosen native classifying map, with existence supplied internally by305. -/
def nativeAffineHilbertPointClassifyingHom308 (hn : 0 < n)
    (P : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n) :
    MonomialFixedBaseHom308 R A m n :=
  Classical.choose (nativeAffineHilbertPoint_fixedBaseHom_exists308 R m n hn P)

lemma nativeAffineHilbertPointClassifyingHom_pullback308 (hn : 0 < n)
    (P : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n) :
    P = monomialFixedBasePointPullback308 R m n
      (nativeAffineHilbertPointClassifyingHom308 R m n hn P) :=
  Classical.choose_spec (nativeAffineHilbertPoint_fixedBaseHom_exists308 R m n hn P)

/-- Actual positive-rank affine classification equivalence. It is assembled
from the original family construction305 and native uniqueness306. -/
def nativeAffineHilbertClassificationEquiv308 (hn : 0 < n) :
    FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n ≃
      MonomialFixedBaseHom308 R A m n where
  toFun := nativeAffineHilbertPointClassifyingHom308 R m n hn
  invFun := monomialFixedBasePointPullback308 R m n
  left_inv P := (nativeAffineHilbertPointClassifyingHom_pullback308 R m n hn P).symm
  right_inv g := monomialFixedBasePointPullback_injective308 R m n
    (nativeAffineHilbertPointClassifyingHom_pullback308 R m n hn
      (monomialFixedBasePointPullback308 R m n g)).symm

/-- Classification retains the literal whole global universal ideal. -/
lemma nativeAffineHilbertClassificationEquiv_wholeIdeal308 (hn : 0 < n)
    (P : FiniteFlatHilbertPoint195 (nativePolynomialProjection300 A m) n) :
    P.val = (monomialCoefficientUniversalWholeIdeal300 R m n).comap
      (fixedBaseTestAmbientMap305 R m n
        ((nativeAffineHilbertClassificationEquiv308 R m n hn) P).val
        ((nativeAffineHilbertClassificationEquiv308 R m n hn) P).property) :=
  congrArg Subtype.val (nativeAffineHilbertPointClassifyingHom_pullback308 R m n hn P)

end PfaffianDescent
end
