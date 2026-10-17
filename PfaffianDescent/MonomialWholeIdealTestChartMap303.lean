import PfaffianDescent.MonomialCoefficientGluedBase300
import PfaffianDescent.MonomialCoefficientOverlapCartesian300
import PfaffianDescent.MonomialWholeIdealChartNaturality287
import PfaffianDescent.MonomialOverlapCoefficientPointTransport300
import PfaffianDescent.ActualAffineHilbertFixedBaseCover302

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Construct native Spec of an algebra point before original coefficient substitution. -/
private def nativeAlgHomSpecMap303
    (R : Type u) [CommRing R] {C A : Type u} [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A] (p : C →ₐ[R] A) : Spec (.of A) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom p.toRingHom)

private lemma nativeAlgHomSpecMap_comp303
    (R : Type u) [CommRing R] {C A D : Type u} [CommRing C] [CommRing A] [CommRing D]
    [Algebra R C] [Algebra R A] [Algebra R D] (p : C →ₐ[R] A) (f : A →ₐ[R] D) :
    nativeAlgHomSpecMap303 R f ≫ nativeAlgHomSpecMap303 R p =
      nativeAlgHomSpecMap303 R (f.comp p) := by
  dsimp only [nativeAlgHomSpecMap303]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Bound the scalar composition at the ordinary algebra-map boundary. -/
private lemma nativeAlgHomSpecMap_overBase303
    (R : Type u) [CommRing R] {C A : Type u} [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A] (p : C →ₐ[R] A) :
    nativeAlgHomSpecMap303 R p ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  algebraHomSpecMap_overBase298 p

/-- Discharge the original coefficient/base alias before inverse classification. -/
private lemma nativeCoefficientPointSpecMap_toBase303
    (R : Type u) [CommRing R] (m n : ℕ)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    {A : Type u} [CommRing A] [Algebra R A]
    (p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) :
    nativeAlgHomSpecMap303 R p ≫ monomialCoefficientChartToBase300 R m n B k =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  simpa only [monomialCoefficientChartToBase300] using
    (nativeAlgHomSpecMap_overBase303 R
      (C := UniversalCyclicCoefficientAlgebra282 R m n B k) (A := A) p)

private lemma nativeAlgHomSpecMap_congr303
    (R : Type u) [CommRing R] {C A : Type u} [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A] (p q : C →ₐ[R] A) (h : p = q) :
    nativeAlgHomSpecMap303 R p = nativeAlgHomSpecMap303 R q :=
  congrArg (nativeAlgHomSpecMap303 R) h

/-- Native contravariant Spec composition depends only on the three ring dictionaries.
No algebra-tower dictionaries enter this cut. -/
private lemma nativeRingHomSpecMap_comp_eq303
    {C L A : Type u} [CommRing C] [CommRing L] [CommRing A]
    (b : C →+* L) (p : L →+* A) (q : C →+* A) (h : p.comp b = q) :
    Spec.map (CommRingCat.ofHom p) ≫ Spec.map (CommRingCat.ofHom b) =
      Spec.map (CommRingCat.ofHom q) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- Compose and transport the Spec point law before any original coefficient substitution. -/
private lemma nativeAlgHomSpecMap_comp_eq303
    (R : Type u) [CommRing R] {C A D : Type u} [CommRing C] [CommRing A] [CommRing D]
    [Algebra R C] [Algebra R A] [Algebra R D]
    (p : C →ₐ[R] A) (f : A →ₐ[R] D) (q : C →ₐ[R] D) (h : f.comp p = q) :
    nativeAlgHomSpecMap303 R f ≫ nativeAlgHomSpecMap303 R p =
      nativeAlgHomSpecMap303 R q :=
  (nativeAlgHomSpecMap_comp303 R p f).trans (nativeAlgHomSpecMap_congr303 R _ _ h)

private lemma nativePrecomposeChartMap303
    {C : Type*} [Category C] {X Y Z H : C}
    (f : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (i : Z ⟶ H)
    (h : f ≫ p = q) : f ≫ (p ≫ i) = q ≫ i :=
  (Category.assoc f p i).symm.trans (congrArg (fun z => z ≫ i) h)

/-- Compose chart/base laws before any actual glued Scheme is supplied. -/
private lemma nativeChartPointOverBase303
    {C : Type*} [Category C] {X U H B : C}
    (p : X ⟶ U) (i : U ⟶ H) (h : H ⟶ B) (b : U ⟶ B) (s : X ⟶ B)
    (hi : i ≫ h = b) (hp : p ≫ b = s) : (p ≫ i) ≫ h = s :=
  (Category.assoc p i h).trans ((congrArg (fun z => p ≫ z) hi).trans hp)

/-- Pin the inverse coefficient point's domain before its scalar law is specialized. -/
private lemma nativeInverseCoefficientSpecMap_toBase303
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (i : MonomialCoefficientChartIndex300 m n)
    (x : MonomialWholeIdealChart287 (A := A) i.monomials) :
    nativeAlgHomSpecMap303 R
        ((cyclicCoefficientWholeIdealChartEquiv287 (A := A)
          i.monomials i.zeroIndex R i.zero_eq).symm x) ≫
        monomialCoefficientChartToBase300 R m n i.monomials i.zeroIndex =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  let p : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A :=
    (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
      i.monomials i.zeroIndex R i.zero_eq).symm x
  exact nativeCoefficientPointSpecMap_toBase303 R m n
    i.monomials i.zeroIndex (A := A) p

set_option backward.isDefEq.respectTransparency.types false in
/-- Prove the native glued-chart/base law for an arbitrary coefficient point,
before the original whole-ideal inverse classifier is substituted. -/
private lemma nativeCoefficientChartPoint_overBase303
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (i : MonomialCoefficientChartIndex300 m n)
    (p : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A) :
    (nativeAlgHomSpecMap303 R p ≫ monomialCoefficientGluedChartMap300 R m n i) ≫
        monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  nativeChartPointOverBase303
    (C := Scheme.{u})
    (X := Spec (.of A))
    (U := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)))
    (H := monomialCoefficientGluedScheme300 R m n) (B := Spec (.of R))
    (nativeAlgHomSpecMap303 R p) (monomialCoefficientGluedChartMap300 R m n i)
    (monomialCoefficientGluedToBase300 R m n)
    (monomialCoefficientChartToBase300 R m n i.monomials i.zeroIndex)
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (monomialCoefficientGluedChartMap_toBase300 R m n i)
    (nativeCoefficientPointSpecMap_toBase303 R m n i.monomials i.zeroIndex (A := A) p)

/-- Ordinary categorical replacement of one proved coefficient map before specialization. -/
private lemma nativeComposeReplaceRight303
    {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g h : Y ⟶ Z) (q : X ⟶ Z)
    (hg : g = h) (hf : f ≫ g = q) : f ≫ h = q :=
  (congrArg (fun z => f ≫ z) hg.symm).trans hf

set_option backward.isDefEq.respectTransparency.types false in
/-- Use the accepted actual overlap/scalar-map identification before inserting any test point. -/
private lemma nativeCoefficientLocalizationScalarSpec303
    (R : Type u) [CommRing R] {m n : ℕ} (i j : MonomialCoefficientChartIndex300 m n) :
    nativeAlgHomSpecMap303 R
        (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
          (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)) =
      monomialOverlapPrincipalOpenMap294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq := by
  have h : nativeAlgHomSpecMap303 R
      (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
        (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)) =
      monomialCoefficientOverlapToFirst300 R m n i j := rfl
  exact h.trans ((monomialCoefficientOverlapToFirst_original300 R m n i j).symm.trans
    (monomialOverlapPrincipalOpenIso_hom_fac294 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq))

/-- Exact native coefficient polynomial dictionary, without registering a new instance. -/
private def originalMatrixCoefficientPolynomialCommRing303
    (R : Type u) [CommRing R] (m n : ℕ) : CommRing (MatrixCoefficientPolynomial280 R m n) :=
  @AddMonoidAlgebra.commRing R (MatrixCoefficientIndex280 m n →₀ ℕ)
    ‹CommRing R› inferInstance

/-- Exact first native quotient dictionary, preserving its original ideal and operations. -/
private def originalCommutingCoefficientCommRing303
    (R : Type u) [CommRing R] (m n : ℕ) : CommRing (CommutingMatrixCoefficientAlgebra280 R m n) :=
  @Ideal.Quotient.commRing (MatrixCoefficientPolynomial280 R m n)
    (originalMatrixCoefficientPolynomialCommRing303 R m n) (commutingMatrixIdeal280 R m n)

/-- Exact second native quotient dictionary, preserving the whole cyclic coefficient relation ideal. -/
private def originalCyclicCoefficientCommRing303
    (R : Type u) [CommRing R] (m n : ℕ) (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    CommRing (UniversalCyclicCoefficientAlgebra282 R m n B k) :=
  @Ideal.Quotient.commRing (CommutingMatrixCoefficientAlgebra280 R m n)
    (originalCommutingCoefficientCommRing303 R m n) (universalCyclicCoefficientIdeal282 R m n B k)

set_option backward.isDefEq.respectTransparency.types false in
/-- Infer the actual ring-composition proof BEFORE its final categorical replacement context.
The explicit dictionaries are exactly the native polynomial and two quotient constructors. -/
private def nativeCoefficientRingSpecComposition303
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (i j : MonomialCoefficientChartIndex300 m n)
    (p : MonomialOverlapCoefficientAlgebra292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq →ₐ[R] A)
    (q : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A)
    (h : p.comp (Algebra.algHom R
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
      (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)) = q) :=
  @nativeRingHomSpecMap_comp_eq303
    (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
    (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq) A
    (originalCyclicCoefficientCommRing303 R m n i.monomials i.zeroIndex)
    (inferInstanceAs (CommRing (Localization.Away
      (universalMonomialOverlapDet292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq))))
    (inferInstance : CommRing A)
    (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
      (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)).toRingHom
    p.toRingHom q.toRingHom (congrArg AlgHom.toRingHom h)

set_option backward.isDefEq.respectTransparency.types false in
/-- Original restriction law at arbitrary coefficient points, before inverse classification. -/
private def nativeCoefficientLocalizationPointRestriction303
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (i j : MonomialCoefficientChartIndex300 m n)
    (p : MonomialOverlapCoefficientAlgebra292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq →ₐ[R] A)
    (q : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A)
    (h : p.comp (Algebra.algHom R
      (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
      (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)) = q) :=
  nativeComposeReplaceRight303 (C := Scheme.{u})
    (X := Spec (.of A))
    (Y := Spec (.of (MonomialOverlapCoefficientAlgebra292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq)))
    (Z := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)))
    (nativeAlgHomSpecMap303 R p)
    (nativeAlgHomSpecMap303 R
      (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
        (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)))
    (monomialOverlapPrincipalOpenMap294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)
    (nativeAlgHomSpecMap303 R q)
    (nativeCoefficientLocalizationScalarSpec303 R (m := m) (n := n) i j)
    (nativeCoefficientRingSpecComposition303 R (A := A) (m := m) (n := n) i j p q h)

set_option backward.isDefEq.respectTransparency.types false in
/-- Original reverse transition law at arbitrary points, before inverse classification. -/
private lemma nativeCoefficientLocalizationPointReverse303
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (i j : MonomialCoefficientChartIndex300 m n)
    (p : MonomialOverlapCoefficientAlgebra292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq →ₐ[R] A)
    (q : MonomialOverlapCoefficientAlgebra292 R m n
      j.monomials i.monomials j.zeroIndex j.zero_eq →ₐ[R] A)
    (h : p.comp (monomialOverlapForwardCoefficientMap293 R m n j.monomials i.monomials
      j.zeroIndex i.zeroIndex j.zero_eq i.zero_eq) = q) :
    nativeAlgHomSpecMap303 R p ≫
        (monomialOverlapAffineSchemeIso298 R m n i.monomials j.monomials
          i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom =
      nativeAlgHomSpecMap303 R q := by
  rw [monomialOverlapAffineSchemeIso_hom298]
  exact nativeAlgHomSpecMap_comp_eq303 R
    (C := MonomialOverlapCoefficientAlgebra292 R m n j.monomials i.monomials j.zeroIndex j.zero_eq)
    (A := MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)
    (D := A) (monomialOverlapForwardCoefficientMap293 R m n j.monomials i.monomials
      j.zeroIndex i.zeroIndex j.zero_eq i.zero_eq) p q h

variable (R : Type u) [CommRing R] {A D : Type u} [CommRing A] [CommRing D]
variable [Algebra R A] [Algebra R D] {m n : ℕ}

/-- The actual inverse coefficient classifier commutes with arbitrary scalar change. -/
lemma monomialWholeIdealInverseCoefficient_natural303
    (i : MonomialCoefficientChartIndex300 m n)
    (x : MonomialWholeIdealChart287 (A := A) i.monomials) (f : A →ₐ[R] D) :
    (cyclicCoefficientWholeIdealChartEquiv287 (A := D)
      i.monomials i.zeroIndex R i.zero_eq).symm
        (monomialWholeIdealChartMap287 i.monomials i.zeroIndex i.zero_eq f.toRingHom x) =
      f.comp ((cyclicCoefficientWholeIdealChartEquiv287 (A := A)
        i.monomials i.zeroIndex R i.zero_eq).symm x) := by
  apply (cyclicCoefficientWholeIdealChartEquiv287 (A := D)
    i.monomials i.zeroIndex R i.zero_eq).injective
  rw [Equiv.apply_symm_apply, cyclicCoefficientWholeIdealChartEquiv_natural287,
    Equiv.apply_symm_apply]

/-- Genuine fixed-R chart point map to the SAME native glued coefficient Scheme. -/
def monomialWholeIdealTestChartMap303
    (i : MonomialCoefficientChartIndex300 m n)
    (x : MonomialWholeIdealChart287 (A := A) i.monomials) :
    Spec (.of A) ⟶ monomialCoefficientGluedScheme300 R m n :=
  nativeAlgHomSpecMap303 R
    ((cyclicCoefficientWholeIdealChartEquiv287 (A := A)
      i.monomials i.zeroIndex R i.zero_eq).symm x) ≫
    monomialCoefficientGluedChartMap300 R m n i

/-- Scalar change of the ENTIRE chart ideal gives the original native precomposed Scheme map. -/
lemma monomialWholeIdealTestChartMap_natural303
    (i : MonomialCoefficientChartIndex300 m n)
    (x : MonomialWholeIdealChart287 (A := A) i.monomials) (f : A →ₐ[R] D) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ monomialWholeIdealTestChartMap303 R i x =
      monomialWholeIdealTestChartMap303 R i
        (monomialWholeIdealChartMap287 i.monomials i.zeroIndex i.zero_eq f.toRingHom x) := by
  apply nativePrecomposeChartMap303
  exact (nativeAlgHomSpecMap_comp303 R _ f).trans
    (nativeAlgHomSpecMap_congr303 R _ _
      (monomialWholeIdealInverseCoefficient_natural303 R i x f).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- Each test-chart map is an actual morphism over the SAME Spec R. -/
lemma monomialWholeIdealTestChartMap_toBase303
    (i : MonomialCoefficientChartIndex300 m n)
    (x : MonomialWholeIdealChart287 (A := A) i.monomials) :
    monomialWholeIdealTestChartMap303 R i x ≫ monomialCoefficientGluedToBase300 R m n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  dsimp only [monomialWholeIdealTestChartMap303]
  let p : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A :=
    (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
      i.monomials i.zeroIndex R i.zero_eq).symm x
  exact nativeCoefficientChartPoint_overBase303 R (A := A) (m := m) (n := n) i p

private lemma nativeGluedOverlapAfterIso303
    {C : Type*} [Category C] {L M V W U Z H : C}
    (eL : L ≅ V) (eM : M ≅ W) (a : L ⟶ M) (t : V ⟶ W)
    (fV : V ⟶ U) (fW : W ⟶ Z) (iU : U ⟶ H) (iZ : Z ⟶ H)
    (lV : L ⟶ U) (lW : M ⟶ Z)
    (hv : eL.hom ≫ fV = lV) (hw : eM.hom ≫ fW = lW)
    (ht : eL.hom ≫ t = a ≫ eM.hom)
    (hg : t ≫ fW ≫ iZ = fV ≫ iU) : lV ≫ iU = a ≫ lW ≫ iZ := by
  calc
    _ = eL.hom ≫ (fV ≫ iU) := by rw [← hv, Category.assoc]
    _ = eL.hom ≫ (t ≫ fW ≫ iZ) := congrArg (fun z => eL.hom ≫ z) hg.symm
    _ = (a ≫ eM.hom) ≫ fW ≫ iZ := by rw [← Category.assoc eL.hom t (fW ≫ iZ), ht]
    _ = _ := by rw [Category.assoc a eM.hom (fW ≫ iZ), ← Category.assoc eM.hom fW iZ, hw]

/-- The native two localized coefficient chart legs agree inside the SAME glued Scheme. -/
lemma monomialLocalizedGluedChartLegs303
    (i j : MonomialCoefficientChartIndex300 m n) :
    monomialOverlapPrincipalOpenMap294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq ≫
        monomialCoefficientGluedChartMap300 R m n i =
      (monomialOverlapAffineSchemeIso298 R m n i.monomials j.monomials
        i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom ≫
      monomialOverlapPrincipalOpenMap294 R m n j.monomials i.monomials j.zeroIndex j.zero_eq ≫
        monomialCoefficientGluedChartMap300 R m n j :=
  nativeGluedOverlapAfterIso303
    (monomialOverlapPrincipalOpenIso294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)
    (monomialOverlapPrincipalOpenIso294 R m n j.monomials i.monomials j.zeroIndex j.zero_eq)
    (monomialOverlapAffineSchemeIso298 R m n i.monomials j.monomials
      i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom
    (monomialOverlapPrincipalSchemeIso298 R m n i.monomials j.monomials
      i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom
    (monomialOverlapOriginalOpenInclusion300 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)
    (monomialOverlapOriginalOpenInclusion300 R m n j.monomials i.monomials j.zeroIndex j.zero_eq)
    (monomialCoefficientGluedChartMap300 R m n i) (monomialCoefficientGluedChartMap300 R m n j)
    _ _
    (monomialOverlapPrincipalOpenIso_hom_fac294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)
    (monomialOverlapPrincipalOpenIso_hom_fac294 R m n j.monomials i.monomials j.zeroIndex j.zero_eq)
    (monomialOverlapPrincipalSchemeIso_transport300 R m n i.monomials j.monomials
      i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq)
    (monomialCoefficientGluedChartMap_overlap300 R m n i j)

private lemma overlapInverseCoefficient_restrict303
    (i j : MonomialCoefficientChartIndex300 m n)
    (z : MonomialWholeIdealChartOverlap290 (A := A) i.monomials j.monomials) :
    ((monomialOverlapLocalizationAlgHomEquiv292 R m n i.monomials j.monomials
      i.zeroIndex i.zero_eq A).symm z).comp
        (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
          (MonomialOverlapCoefficientAlgebra292 R m n i.monomials j.monomials i.zeroIndex i.zero_eq)) =
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
        i.monomials i.zeroIndex R i.zero_eq).symm z.val := by
  apply (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
    i.monomials i.zeroIndex R i.zero_eq).injective
  rw [Equiv.apply_symm_apply]
  exact (monomialOverlapClassification_chart300 (R := R) (m := m) (n := n)
    (B := i.monomials) (C := j.monomials) (kB := i.zeroIndex) (hkB := i.zero_eq) _).symm.trans
    (congrArg Subtype.val ((monomialOverlapLocalizationAlgHomEquiv292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq A).apply_symm_apply z))

private lemma overlapInverseCoefficient_reverse303
    (i j : MonomialCoefficientChartIndex300 m n)
    (z : MonomialWholeIdealChartOverlap290 (A := A) i.monomials j.monomials) :
    ((monomialOverlapLocalizationAlgHomEquiv292 R m n i.monomials j.monomials
      i.zeroIndex i.zero_eq A).symm z).comp
        (monomialOverlapForwardCoefficientMap293 R m n j.monomials i.monomials
          j.zeroIndex i.zeroIndex j.zero_eq i.zero_eq) =
      (monomialOverlapLocalizationAlgHomEquiv292 R m n j.monomials i.monomials
        j.zeroIndex j.zero_eq A).symm (monomialWholeIdealOverlapFlip293 i.monomials j.monomials z) := by
  apply (monomialOverlapLocalizationAlgHomEquiv292 R m n j.monomials i.monomials
    j.zeroIndex j.zero_eq A).injective
  rw [Equiv.apply_symm_apply]
  exact (monomialOverlapReverseCoefficient_classifies300 (R := R) (m := m) (n := n)
    (B := i.monomials) (C := j.monomials) (kB := i.zeroIndex) (kC := j.zeroIndex)
    (hkB := i.zero_eq) (hkC := j.zero_eq) _).trans
    (congrArg (monomialWholeIdealOverlapFlip293 i.monomials j.monomials)
      ((monomialOverlapLocalizationAlgHomEquiv292 R m n i.monomials j.monomials
        i.zeroIndex i.zero_eq A).apply_symm_apply z))

/-- Inferred ordinary proof type of the original inverse restriction specialization. -/
private def overlapInverseCoefficientRestrictionSpec303
    (i j : MonomialCoefficientChartIndex300 m n)
    (z : MonomialWholeIdealChartOverlap290 (A := A) i.monomials j.monomials) :=
  nativeCoefficientLocalizationPointRestriction303 R (A := A) (m := m) (n := n) i j
    ((monomialOverlapLocalizationAlgHomEquiv292 R m n i.monomials j.monomials
      i.zeroIndex i.zero_eq A).symm z)
    ((cyclicCoefficientWholeIdealChartEquiv287 (A := A)
      i.monomials i.zeroIndex R i.zero_eq).symm z.val)
    (overlapInverseCoefficient_restrict303 R i j z)

/-- Inferred ordinary proof type of the original inverse reverse-transition specialization. -/
private def overlapInverseCoefficientReverseSpec303
    (i j : MonomialCoefficientChartIndex300 m n)
    (z : MonomialWholeIdealChartOverlap290 (A := A) i.monomials j.monomials) :=
  nativeCoefficientLocalizationPointReverse303 R (A := A) (m := m) (n := n) i j
    ((monomialOverlapLocalizationAlgHomEquiv292 R m n i.monomials j.monomials
      i.zeroIndex i.zero_eq A).symm z)
    ((monomialOverlapLocalizationAlgHomEquiv292 R m n j.monomials i.monomials
      j.zeroIndex j.zero_eq A).symm (monomialWholeIdealOverlapFlip293 i.monomials j.monomials z))
    (overlapInverseCoefficient_reverse303 R i j z)

/-- Genuine overlap classification makes the two ACTUAL test Scheme maps agree. -/
lemma monomialWholeIdealTestChartMap_overlap303
    (i j : MonomialCoefficientChartIndex300 m n)
    (z : MonomialWholeIdealChartOverlap290 (A := A) i.monomials j.monomials) :
    monomialWholeIdealTestChartMap303 R i z.val =
      monomialWholeIdealTestChartMap303 R j
        (monomialWholeIdealOverlapFlip293 i.monomials j.monomials z).val := by
  let p : MonomialOverlapCoefficientAlgebra292 R m n
      i.monomials j.monomials i.zeroIndex i.zero_eq →ₐ[R] A :=
    (monomialOverlapLocalizationAlgHomEquiv292 R m n i.monomials j.monomials
      i.zeroIndex i.zero_eq A).symm z
  let q : MonomialOverlapCoefficientAlgebra292 R m n
      j.monomials i.monomials j.zeroIndex j.zero_eq →ₐ[R] A :=
    (monomialOverlapLocalizationAlgHomEquiv292 R m n j.monomials i.monomials
      j.zeroIndex j.zero_eq A).symm (monomialWholeIdealOverlapFlip293 i.monomials j.monomials z)
  have hb := overlapInverseCoefficientRestrictionSpec303 R (A := A) i j z
  have hq := overlapInverseCoefficientReverseSpec303 R (A := A) i j z
  have hc := overlapInverseCoefficientRestrictionSpec303 R (A := A) j i
    (monomialWholeIdealOverlapFlip293 i.monomials j.monomials z)
  calc
    _ = nativeAlgHomSpecMap303 R p ≫
        (monomialOverlapPrincipalOpenMap294 R m n i.monomials j.monomials i.zeroIndex i.zero_eq ≫
          monomialCoefficientGluedChartMap300 R m n i) :=
      (nativePrecomposeChartMap303 _ _ _ _ hb).symm
    _ = nativeAlgHomSpecMap303 R p ≫
        ((monomialOverlapAffineSchemeIso298 R m n i.monomials j.monomials
          i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom ≫
        monomialOverlapPrincipalOpenMap294 R m n j.monomials i.monomials j.zeroIndex j.zero_eq ≫
          monomialCoefficientGluedChartMap300 R m n j) :=
      congrArg (fun f => nativeAlgHomSpecMap303 R p ≫ f) (monomialLocalizedGluedChartLegs303 R i j)
    _ = nativeAlgHomSpecMap303 R q ≫
        (monomialOverlapPrincipalOpenMap294 R m n j.monomials i.monomials j.zeroIndex j.zero_eq ≫
          monomialCoefficientGluedChartMap300 R m n j) :=
      nativePrecomposeChartMap303 _ _ _ _ hq
    _ = _ := nativePrecomposeChartMap303 _ _ _ _ hc

/-- Two genuine monomial charts on the SAME entire ideal construct overlap membership,
then give equal test maps to H; no Scheme-map compatibility is a premise. -/
lemma monomialWholeIdealTestChartMap_sameIdeal303
    (i j : MonomialCoefficientChartIndex300 m n)
    (x : MonomialWholeIdealChart287 (A := A) i.monomials)
    (y : MonomialWholeIdealChart287 (A := A) j.monomials) (h : x.val = y.val) :
    monomialWholeIdealTestChartMap303 R i x = monomialWholeIdealTestChartMap303 R j y := by
  have hy : ∃ b : Module.Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ x.val),
      ∀ l, b l = Ideal.Quotient.mk x.val (MvPolynomial.monomial (j.monomials l) 1) :=
    h.symm ▸ y.property
  let z : MonomialWholeIdealChartOverlap290 (A := A) i.monomials j.monomials :=
    ⟨x, (wholeIdealMonomialTransitionDet_isUnit_iff290 x.val
      (monomialWholeIdealChartBasis287 i.monomials x) j.monomials).mpr hy⟩
  have he : (monomialWholeIdealOverlapFlip293 i.monomials j.monomials z).val = y := by
    apply Subtype.ext
    exact (monomialWholeIdealOverlapFlip_ideal293 i.monomials j.monomials z).trans h
  exact (monomialWholeIdealTestChartMap_overlap303 R i j z).trans
    (congrArg (monomialWholeIdealTestChartMap303 R j) he)

/-- The accepted fixed-R coverage producer gives actual maps on its ORIGINAL affine patches.
Both the native family identity and base morphism are proved; no local-map premise is supplied. -/
lemma actualAffineHilbertPoint_fixedBaseCover_mapsToGlued303
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (hn : 0 < n) :
    ∃ (I : Ideal (MvPolynomial (Fin m) A))
      (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I))),
      ∃ hb : ∀ p : PrimeSpectrum A, ∃ s ∉ p.asIdeal, Nonempty
        (Module.Basis (Fin n) (Localization.Away s)
          (MvPolynomial (Fin m) (Localization.Away s) ⧸
            I.map (MvPolynomial.map (algebraMap A (Localization.Away s))))),
      P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      ∃ U : (Spec (.of A)).AffineOpenCover,
        U = localWholeQuotientMonomialAffineCover302 I hb hn ∧
        ∀ (i : LocalWholeQuotientBasisIndex302 I n) (q : MonomialBasisOpenIndex299 m n),
          let S := Localization.Away i.1
          let T := Localization.Away (wholeIdealMonomialTransitionDet290
            (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
          letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
          ∃ p : UniversalCyclicCoefficientAlgebra282 R m n q.val.1 q.val.2 →ₐ[R] T,
          ∃ g : Spec (.of T) ⟶ monomialCoefficientGluedScheme300 R m n,
            actualAffineHilbertPoint_monomialRestriction302 P I i q =
              cyclicCoefficientUniversalFamilyPullback302 R m n q.val.1 q.val.2 p ∧
            g ≫ monomialCoefficientGluedToBase300 R m n =
              Spec.map (CommRingCat.ofHom (R := R) (S := T)
                (@algebraMap R T
                  (@CommRing.toCommSemiring R (inferInstance : CommRing R))
                  (@CommRing.toCommSemiring T (inferInstance : CommRing T)).toSemiring
                  inferInstance)) ∧
            g = nativeAlgHomSpecMap303 R p ≫
              monomialCoefficientGluedChartMap300 R m n ⟨q.val.1, q.val.2, q.property⟩ := by
  obtain ⟨I, e, hb, h, U, hU, hp⟩ :=
    actualAffineHilbertPoint_fixedBaseUniversalMonomialAffineCover302 R P hn
  refine ⟨I, e, hb, h, U, hU, ?_⟩
  intro i q
  let S := Localization.Away i.1
  let T := Localization.Away (wholeIdealMonomialTransitionDet290
    (I.map (MvPolynomial.map (algebraMap A S))) i.2 q.val.1)
  letI : Algebra R T := fixedBaseCompositePatchAlgebra302 R A S T
  obtain ⟨p, hpoint⟩ := hp i q
  let a : MonomialCoefficientChartIndex300 m n := ⟨q.val.1, q.val.2, q.property⟩
  let x := cyclicCoefficientWholeIdealChartEquiv287 (A := T)
    a.monomials a.zeroIndex R a.zero_eq p
  refine ⟨p, monomialWholeIdealTestChartMap303 R a x, hpoint,
    monomialWholeIdealTestChartMap_toBase303 R a x, ?_⟩
  exact congrArg (fun f => f ≫ monomialCoefficientGluedChartMap300 R m n a)
    (nativeAlgHomSpecMap_congr303 R _ _
      ((cyclicCoefficientWholeIdealChartEquiv287 (A := T)
        a.monomials a.zeroIndex R a.zero_eq).symm_apply_apply p))

end PfaffianDescent
