import PfaffianDescent.MonomialOverlapOriginalDiagonal300
import PfaffianDescent.MonomialTripleOriginalTransitionCocycle300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Ordinary monomial coefficient chart indices retain their actual tuple and original
zero-monomial position. No rank, family, transition or gluing outcome is an input. -/
structure MonomialCoefficientChartIndex300 (m n : ℕ) where
  monomials : Fin n → (Fin m →₀ ℕ)
  zeroIndex : Fin n
  zero_eq : monomials zeroIndex = 0

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- Genuine native Scheme gluing data of the ORIGINAL coefficient charts, ORIGINAL determinant
open inclusions, SAME298 pair transitions, and DERIVED300 actual triple maps.
All identities and geometric instance fields are proved internally. -/
def monomialCoefficientSchemeGlueData300 : Scheme.GlueData.{u} where
  J := ULift.{u} (MonomialCoefficientChartIndex300 m n)
  U i := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n i.down.monomials i.down.zeroIndex))
  V ij := monomialOverlapPrincipalScheme298 R m n ij.1.down.monomials ij.2.down.monomials
    ij.1.down.zeroIndex ij.1.down.zero_eq
  f i j := monomialOverlapOriginalOpenInclusion300 R m n i.down.monomials j.down.monomials
    i.down.zeroIndex i.down.zero_eq
  f_mono i j := by
    letI := monomialOverlapOriginalOpenInclusion_isOpenImmersion300 R m n
      i.down.monomials j.down.monomials i.down.zeroIndex i.down.zero_eq
    infer_instance
  f_hasPullback i j k := by infer_instance
  f_id i := monomialOverlapOriginalSelfInclusion_isIso300 R m n
    i.down.monomials i.down.zeroIndex i.down.zero_eq
  t i j := (monomialOverlapPrincipalSchemeIso298 R m n i.down.monomials j.down.monomials
    i.down.zeroIndex j.down.zeroIndex i.down.zero_eq j.down.zero_eq).hom
  t_id i := monomialOverlapPrincipalSchemeIso_self_hom300 R m n
    i.down.monomials i.down.zeroIndex i.down.zero_eq
  t' i j k := monomialTripleOriginalPullbackTransition300 R m n
    i.down.monomials j.down.monomials k.down.monomials i.down.zeroIndex j.down.zeroIndex i.down.zero_eq j.down.zero_eq
  t_fac i j k := monomialTripleOriginalPullbackTransition_fac300 R m n
    i.down.monomials j.down.monomials k.down.monomials i.down.zeroIndex j.down.zeroIndex i.down.zero_eq j.down.zero_eq
  cocycle i j k := monomialTripleOriginalPullbackTransition_cycle300 R m n
    i.down.monomials j.down.monomials k.down.monomials i.down.zeroIndex j.down.zeroIndex i.down.zero_eq j.down.zero_eq
    k.down.zeroIndex k.down.zero_eq
  f_open i j := monomialOverlapOriginalOpenInclusion_isOpenImmersion300 R m n
    i.down.monomials j.down.monomials i.down.zeroIndex i.down.zero_eq

/-- The actual glued Scheme constructed by the native Scheme.GlueData implementation. -/
def monomialCoefficientGluedScheme300 : Scheme.{u} :=
  (monomialCoefficientSchemeGlueData300 R m n).glued

/-- Original coefficient charts map by native open immersions into the actual glued Scheme. -/
def monomialCoefficientGluedChartMap300 (i : MonomialCoefficientChartIndex300 m n) :
    Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) ⟶
      monomialCoefficientGluedScheme300 R m n :=
  (monomialCoefficientSchemeGlueData300 R m n).ι ⟨i⟩

lemma monomialCoefficientGluedChartMap_isOpenImmersion300
    (i : MonomialCoefficientChartIndex300 m n) :
    IsOpenImmersion (monomialCoefficientGluedChartMap300 R m n i) := by
  exact Scheme.GlueData.ι_isOpenImmersion (monomialCoefficientSchemeGlueData300 R m n) ⟨i⟩

/-- The ORIGINAL determinant transition square commutes inside the actual glued Scheme. -/
lemma monomialCoefficientGluedChartMap_overlap300
    (i j : MonomialCoefficientChartIndex300 m n) :
    (monomialOverlapPrincipalSchemeIso298 R m n i.monomials j.monomials
        i.zeroIndex j.zeroIndex i.zero_eq j.zero_eq).hom ≫
      monomialOverlapOriginalOpenInclusion300 R m n j.monomials i.monomials
        j.zeroIndex j.zero_eq ≫ monomialCoefficientGluedChartMap300 R m n j =
      monomialOverlapOriginalOpenInclusion300 R m n i.monomials j.monomials
        i.zeroIndex i.zero_eq ≫ monomialCoefficientGluedChartMap300 R m n i :=
  (monomialCoefficientSchemeGlueData300 R m n).glue_condition ⟨i⟩ ⟨j⟩

/-- This is the genuine native open cover of the actually constructed Scheme. Its cover
property follows from Scheme gluing, independently of subsequent Hilbert-family coverage. -/
def monomialCoefficientGluedOpenCover300 :
    (monomialCoefficientGluedScheme300 R m n).OpenCover :=
  (monomialCoefficientSchemeGlueData300 R m n).openCover

end PfaffianDescent
