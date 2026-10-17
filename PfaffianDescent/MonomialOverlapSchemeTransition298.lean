import PfaffianDescent.CommAlgebraSpecIso298
import PfaffianDescent.MonomialOverlapCoefficientSymmetry293
import PfaffianDescent.MonomialOverlapPrincipalOpen294

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Resolve the original open-inclusion instance before substituting any coefficient scheme. -/
private lemma nativeSchemeOpenInclusion298 {X : Scheme.{u}} (U : X.Opens) :
    IsOpenImmersion (Scheme.Opens.ι (X := X) U) := by
  infer_instance

/-- Opaque categorical associativity/factorization cut, before any original
coefficient Scheme or open-inclusion map is substituted. -/
private lemma nativeThreeFactorInclusion298
    {C : Type*} [Category C] {X Y Z W V : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (i : W ⟶ V) (d : Z ⟶ V)
    (hc : c ≫ i = d) :
    (a ≫ b ≫ c) ≫ i = a ≫ b ≫ d := by
  simp only [Category.assoc]
  exact congrArg (fun z => a ≫ b ≫ z) hc

/-- An original proved inverse-Iso equality gives the inverse composition
without rewriting a concrete Scheme Iso definition in the final caller. -/
private lemma nativeIsoReverseHomComp298
    {C : Type*} [Category C] {X Y : C}
    (e : X ≅ Y) (f : Y ≅ X) (h : e.symm = f) :
    e.hom ≫ f.hom = 𝟙 X := by
  have hh : e.inv = f.hom := congrArg (fun a => a.hom) h
  exact (congrArg (fun z => e.hom ≫ z) hh.symm).trans e.hom_inv_id

variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C : Fin n → (Fin m →₀ ℕ)) (kB kC : Fin n)
variable (hkB : B kB = 0) (hkC : C kC = 0)

/-- Reversing the two bases gives the inverse of the SAME constructed coefficient Iso. -/
lemma monomialOverlapCoefficientIso_symm298 :
    (monomialOverlapCoefficientIso293 R m n B C kB kC hkB hkC).symm =
      monomialOverlapCoefficientIso293 R m n C B kC kB hkC hkB := by
  apply Iso.ext
  apply CommAlgCat.hom_ext
  exact (monomialOverlapCoefficientIso_inv293 R m n B C kB kC hkB hkC).trans
    (monomialOverlapCoefficientIso_hom293 R m n C B kC kB hkC hkB).symm

/-- Actual transition from the B/C localization spectrum to the C/B spectrum.
Its coefficient map is the inverse of293's forward algebra map. -/
def monomialOverlapAffineSchemeIso298 :
    Spec (.of (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)) ≅
      Spec (.of (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC)) :=
  commAlgebraSpecIso298 (monomialOverlapCoefficientIso293 R m n B C kB kC hkB hkC)

lemma monomialOverlapAffineSchemeIso_hom298 :
    (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).hom =
      Spec.map (CommRingCat.ofHom
        (monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB).toRingHom) := by
  rw [monomialOverlapAffineSchemeIso298, commAlgebraSpecIso_hom298,
    monomialOverlapCoefficientIso_inv293]
  rfl

lemma monomialOverlapAffineSchemeIso_inv298 :
    (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).inv =
      Spec.map (CommRingCat.ofHom
        (monomialOverlapForwardCoefficientMap293 R m n B C kB kC hkB hkC).toRingHom) := by
  rw [monomialOverlapAffineSchemeIso298, commAlgebraSpecIso_inv298,
    monomialOverlapCoefficientIso_hom293]
  rfl

lemma monomialOverlapAffineSchemeIso_symm298 :
    (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).symm =
      monomialOverlapAffineSchemeIso298 R m n C B kC kB hkC hkB := by
  apply Iso.ext
  exact (monomialOverlapAffineSchemeIso_inv298 R m n B C kB kC hkB hkC).trans
    (monomialOverlapAffineSchemeIso_hom298 R m n C B kC kB hkC hkB).symm

lemma monomialOverlapAffineSchemeIso_overBase298 :
    (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (MonomialOverlapCoefficientAlgebra292 R m n C B kC hkC))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB))) :=
  commAlgebraSpecIso_overBase298
    (monomialOverlapCoefficientIso293 R m n B C kB kC hkB hkC)

/-- The original determinant principal-open subscheme, with its literal coefficient chart. -/
abbrev monomialOverlapPrincipalScheme298
    (R : Type u) [CommRing R] (m n : ℕ)
    (B C : Fin n → (Fin m →₀ ℕ)) (kB : Fin n) (hkB : B kB = 0) :=
  Scheme.Opens.toScheme
    (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B kB)))
    (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B C kB hkB))

/-- Actual pairwise transition between the two ORIGINAL determinant open subschemes. -/
def monomialOverlapPrincipalSchemeIso298 :
    monomialOverlapPrincipalScheme298 R m n B C kB hkB ≅
      monomialOverlapPrincipalScheme298 R m n C B kC hkC :=
  (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).symm ≪≫
    monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC ≪≫
    monomialOverlapPrincipalOpenIso294 R m n C B kC hkC

lemma monomialOverlapPrincipalSchemeIso_hom298 :
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom =
      (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).inv ≫
      (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).hom ≫
      (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).hom := rfl

lemma monomialOverlapPrincipalSchemeIso_inv298 :
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).inv =
      (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).inv ≫
      (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).inv ≫
      (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).hom := by
  simp only [monomialOverlapPrincipalSchemeIso298, Iso.trans_inv, Iso.symm_inv, Category.assoc]

lemma monomialOverlapPrincipalSchemeIso_symm298 :
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).symm =
      monomialOverlapPrincipalSchemeIso298 R m n C B kC kB hkC hkB := by
  apply Iso.ext
  calc
    _ = (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).inv ≫
        (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).inv ≫
        (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).hom :=
      monomialOverlapPrincipalSchemeIso_inv298 R m n B C kB kC hkB hkC
    _ = (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).inv ≫
        (monomialOverlapAffineSchemeIso298 R m n C B kC kB hkC hkB).hom ≫
        (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).hom :=
      congrArg (fun f =>
        (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).inv ≫ f ≫
        (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).hom)
        ((monomialOverlapAffineSchemeIso_inv298 R m n B C kB kC hkB hkC).trans
          (monomialOverlapAffineSchemeIso_hom298 R m n C B kC kB hkC hkB).symm)
    _ = _ := (monomialOverlapPrincipalSchemeIso_hom298 R m n C B kC kB hkC hkB).symm

/-- Exact target-chart inclusion square; all four maps are the native original maps. -/
lemma monomialOverlapPrincipalSchemeIso_hom_target_inclusion298 :
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom ≫
        (Scheme.Opens.ι
          (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n C kC)))
          (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n C B kC hkC))) =
      (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).inv ≫
        (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).hom ≫
        monomialOverlapPrincipalOpenMap294 R m n C B kC hkC := by
  rw [monomialOverlapPrincipalSchemeIso_hom298]
  exact nativeThreeFactorInclusion298
    (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).inv
    (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).hom
    (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).hom
    (Scheme.Opens.ι
      (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n C kC)))
      (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n C B kC hkC)))
    (monomialOverlapPrincipalOpenMap294 R m n C B kC hkC)
    (monomialOverlapPrincipalOpenIso_hom_fac294 R m n C B kC hkC)

/-- Exact source-chart inclusion square for the inverse transition. -/
lemma monomialOverlapPrincipalSchemeIso_inv_source_inclusion298 :
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).inv ≫
        (Scheme.Opens.ι
          (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B kB)))
          (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B C kB hkB))) =
      (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).inv ≫
        (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).inv ≫
        monomialOverlapPrincipalOpenMap294 R m n B C kB hkB := by
  rw [monomialOverlapPrincipalSchemeIso_inv298]
  exact nativeThreeFactorInclusion298
    (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).inv
    (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).inv
    (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).hom
    (Scheme.Opens.ι
      (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B kB)))
      (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B C kB hkB)))
    (monomialOverlapPrincipalOpenMap294 R m n B C kB hkB)
    (monomialOverlapPrincipalOpenIso_hom_fac294 R m n B C kB hkB)

lemma monomialOverlapPrincipalSchemeIso_hom_inv298 :
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom ≫
        (monomialOverlapPrincipalSchemeIso298 R m n C B kC kB hkC hkB).hom =
      𝟙 (monomialOverlapPrincipalScheme298 R m n B C kB hkB) := by
  exact nativeIsoReverseHomComp298
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC)
    (monomialOverlapPrincipalSchemeIso298 R m n C B kC kB hkC hkB)
    (monomialOverlapPrincipalSchemeIso_symm298 R m n B C kB kC hkB hkC)

lemma monomialOverlapPrincipalSchemeIso_inv_hom298 :
    (monomialOverlapPrincipalSchemeIso298 R m n C B kC kB hkC hkB).hom ≫
        (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom =
      𝟙 (monomialOverlapPrincipalScheme298 R m n C B kC hkC) :=
  monomialOverlapPrincipalSchemeIso_hom_inv298 R m n C B kC kB hkC hkB

/-- The same actual overlap's embedding into the second original coefficient affine chart. -/
def monomialOverlapPrincipalOtherMap298 :
    monomialOverlapPrincipalScheme298 R m n B C kB hkB ⟶
      Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n C kC)) :=
  (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom ≫
    (Scheme.Opens.ι
      (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n C kC)))
      (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n C B kC hkC)))

lemma monomialOverlapPrincipalOtherMap_isOpenImmersion298 :
    IsOpenImmersion (monomialOverlapPrincipalOtherMap298 R m n B C kB kC hkB hkC) := by
  letI : IsOpenImmersion (Scheme.Opens.ι
      (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n C kC)))
      (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n C B kC hkC))) :=
    nativeSchemeOpenInclusion298
      (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n C kC)))
      (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n C B kC hkC) :
        (Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n C kC))).Opens)
  unfold monomialOverlapPrincipalOtherMap298
  infer_instance

/-- The ring map underlying the geometric B→C transition preserves the literal whole ideal
in293's classifications, including nilpotents. Native family Cartesianity is a separate consumer. -/
lemma monomialOverlapAffineSchemeIso_hom_sameIdeal298 :
    (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC
        (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)
        (monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB)).val.val =
      (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB
        (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB)
        (AlgHom.id R (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB))).val.val :=
  monomialOverlapForwardCoefficientMap_sameIdeal293 R m n C B kC kB hkC hkB

end PfaffianDescent
