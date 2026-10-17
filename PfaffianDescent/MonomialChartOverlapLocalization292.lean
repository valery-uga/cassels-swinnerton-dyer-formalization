import PfaffianDescent.LocalizationUnitLocusAlgHom292
import PfaffianDescent.MonomialWholeIdealChartOverlapFunctor290

noncomputable section
namespace PfaffianDescent
open CategoryTheory Opposite
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C : Fin n → (Fin m →₀ ℕ)) (k : Fin n) (hk : B k = 0)

/-- Determinants respect equality of actual whole-ideal chart points.
This cut is checked before any universal coefficient point is substituted. -/
private lemma monomialWholeIdealChartTransitionDet_congr292
    {A : Type u} [CommRing A]
    (x y : MonomialWholeIdealChart287 (A := A) B) (h : x = y) :
    monomialWholeIdealChartTransitionDet290 B C x =
      monomialWholeIdealChartTransitionDet290 B C y :=
  congrArg (fun z : MonomialWholeIdealChart287 (A := A) B =>
    monomialWholeIdealChartTransitionDet290 B C z) h

/-- Actual coefficient-point determinant naturality, before specializing
its arbitrary old coefficient point to the universal identity map. -/
private lemma cyclicCoefficientMonomialTransitionDet_natural292
    {A D : Type u} [CommRing A] [CommRing D] [Algebra R A] [Algebra R D]
    (p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A)
    (f : A →ₐ[R] D) :
    monomialWholeIdealChartTransitionDet290 B C
        (cyclicCoefficientWholeIdealChartEquiv287 (A := D) B k R hk (f.comp p)) =
      f (monomialWholeIdealChartTransitionDet290 B C
        (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p)) := by
  have hn : cyclicCoefficientWholeIdealChartEquiv287 (A := D) B k R hk (f.comp p) =
      monomialWholeIdealChartMap287 B k hk f.toRingHom
        (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p) :=
    cyclicCoefficientWholeIdealChartEquiv_natural287 B k R hk p f
  have hdet := monomialWholeIdealChartTransitionDet_congr292 (m := m) (n := n) (B := B) (C := C)
    (cyclicCoefficientWholeIdealChartEquiv287 (A := D) B k R hk (f.comp p))
    (monomialWholeIdealChartMap287 B k hk f.toRingHom
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p)) hn
  exact hdet.trans (monomialWholeIdealChartTransitionDet_map290 B C k hk
    f.toRingHom (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p))

/-- The actual universal point of the already represented first whole-ideal chart. -/
def universalMonomialWholeIdealChart292 :=
  cyclicCoefficientWholeIdealChartEquiv287
    (A := UniversalCyclicCoefficientAlgebra282 R m n B k) B k R hk
    (AlgHom.id R (UniversalCyclicCoefficientAlgebra282 R m n B k))

lemma universalMonomialWholeIdealChart_ideal292 :
    (universalMonomialWholeIdealChart292 R m n B k hk).val =
      universalCyclicWholeAmbientIdeal282 R m n B k := rfl

/-- This element is constructed from the actual universal quotient's two monomial tuples. -/
def universalMonomialOverlapDet292 :=
  monomialWholeIdealChartTransitionDet290 B C (universalMonomialWholeIdealChart292 R m n B k hk)

set_option backward.isDefEq.respectTransparency false in
lemma universalMonomialOverlapDet_evaluate292
    {A : Type u} [CommRing A] [Algebra R A]
    (p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) :
    monomialWholeIdealChartTransitionDet290 B C
        (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p) =
      p (universalMonomialOverlapDet292 R m n B C k hk) := by
  have h := cyclicCoefficientMonomialTransitionDet_natural292 (R := R) (m := m) (n := n)
    (B := B) (C := C) (k := k) (hk := hk)
    (A := UniversalCyclicCoefficientAlgebra282 R m n B k) (D := A)
    (AlgHom.id R (UniversalCyclicCoefficientAlgebra282 R m n B k)) p
  rw [AlgHom.comp_id] at h
  exact h

/-- Restrict the proved coefficient/chart bijection to the constructed unit locus. -/
def cyclicCoefficientUnitOverlapEquiv292
    (A : Type u) [CommRing A] [Algebra R A] :
    {p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A //
      IsUnit (p (universalMonomialOverlapDet292 R m n B C k hk))} ≃
      MonomialWholeIdealChartOverlap290 (A := A) B C :=
  (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk).subtypeEquiv
    (fun p => by rw [universalMonomialOverlapDet_evaluate292])

/-- The overlap coefficient ring is the genuine localization of the original cyclic coefficient ring. -/
abbrev MonomialOverlapCoefficientAlgebra292 :=
  Localization (Submonoid.powers (universalMonomialOverlapDet292 R m n B C k hk))

/-- Actual localization homomorphisms classify the same-ideal overlap, with proved inverse maps. -/
def monomialOverlapLocalizationAlgHomEquiv292
    (A : Type u) [CommRing A] [Algebra R A] :
    (MonomialOverlapCoefficientAlgebra292 R m n B C k hk →ₐ[R] A) ≃
      MonomialWholeIdealChartOverlap290 (A := A) B C :=
  (localizationAlgHomUnitEquiv292 R (universalMonomialOverlapDet292 R m n B C k hk)
    (MonomialOverlapCoefficientAlgebra292 R m n B C k hk) A).trans
    (cyclicCoefficientUnitOverlapEquiv292 R m n B C k hk A)

/-- Forward classification retains the literal ideal of the restricted original coefficient point. -/
lemma monomialOverlapLocalizationAlgHomEquiv_ideal292
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MonomialOverlapCoefficientAlgebra292 R m n B C k hk →ₐ[R] A) :
    (monomialOverlapLocalizationAlgHomEquiv292 R m n B C k hk A p).val.val =
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk
        (p.comp (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n B k)
          (MonomialOverlapCoefficientAlgebra292 R m n B C k hk)))).val := rfl

lemma monomialOverlapLocalizationAlgHomEquiv_natural292
    {A D : Type u} [CommRing A] [CommRing D] [Algebra R A] [Algebra R D]
    (p : MonomialOverlapCoefficientAlgebra292 R m n B C k hk →ₐ[R] A) (f : A →ₐ[R] D) :
    monomialOverlapLocalizationAlgHomEquiv292 R m n B C k hk D (f.comp p) =
      monomialWholeIdealChartOverlapMap290 B C k hk f.toRingHom
        (monomialOverlapLocalizationAlgHomEquiv292 R m n B C k hk A p) := by
  apply Subtype.ext
  change cyclicCoefficientWholeIdealChartEquiv287 (A := D) B k R hk
      (f.comp (p.comp (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n B k)
        (MonomialOverlapCoefficientAlgebra292 R m n B C k hk)))) =
    monomialWholeIdealChartMap287 B k hk f.toRingHom
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk
        (p.comp (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n B k)
          (MonomialOverlapCoefficientAlgebra292 R m n B C k hk))))
  exact cyclicCoefficientWholeIdealChartEquiv_natural287 B k R hk _ f

/-- The actual commutative R-algebra object representing the determinant overlap. -/
def monomialOverlapCoefficientObject292 : CommAlgCat.{u} R :=
  CommAlgCat.of R (MonomialOverlapCoefficientAlgebra292 R m n B C k hk)

def monomialOverlapLocalizationChartEquiv292 (A : CommAlgCat.{u} R) :
    (monomialOverlapCoefficientObject292 R m n B C k hk ⟶ A) ≃
      MonomialWholeIdealChartOverlap290 (A := A) B C where
  toFun p := monomialOverlapLocalizationAlgHomEquiv292 R m n B C k hk A p.hom
  invFun x := CommAlgCat.ofHom
    ((monomialOverlapLocalizationAlgHomEquiv292 R m n B C k hk A).symm x)
  left_inv p := by
    apply CommAlgCat.hom_ext
    exact (monomialOverlapLocalizationAlgHomEquiv292 R m n B C k hk A).left_inv p.hom
  right_inv x := (monomialOverlapLocalizationAlgHomEquiv292 R m n B C k hk A).right_inv x

/-- The localization represents290's overlap naturally; no representability premise is assumed. -/
def monomialOverlapLocalizationNatIso292 :
    coyoneda.obj (.op (monomialOverlapCoefficientObject292 R m n B C k hk)) ≅
      monomialWholeIdealChartOverlapFunctor290 R m n B C k hk := by
  refine NatIso.ofComponents
    (fun A => (monomialOverlapLocalizationChartEquiv292 R m n B C k hk A).toIso) ?_
  intro A D f
  ext p
  change monomialOverlapLocalizationAlgHomEquiv292 R m n B C k hk D (f.hom.comp p.hom) =
    monomialWholeIdealChartOverlapMap290 B C k hk f.hom.toRingHom
      (monomialOverlapLocalizationAlgHomEquiv292 R m n B C k hk A p.hom)
  exact monomialOverlapLocalizationAlgHomEquiv_natural292 R m n B C k hk p.hom f.hom

end PfaffianDescent
